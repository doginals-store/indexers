//! Every inscription in the order it was made, numbered, and grouped by kind.
//!
//! Three layers, each with one job:
//!
//!  - `inscription_seq` is written as inscriptions are created: key (height,
//!    position in block), value the id, its kinds and the block time. Live
//!    blocks write it through the undo log, so a reorg removes what it undoes.
//!    Blocks indexed before this existed are filled in once by
//!    [`backfill_inscription_seq`], from the node's block lists.
//!  - [`run_inscription_numbering`] walks `inscription_seq` in chain order and
//!    gives each inscription its number, overall and within each kind. It only
//!    numbers blocks [`NUMBER_CONFIRMATIONS`] deep, so a reorg never has to take
//!    a number back, and it writes each step as one atomic batch together with
//!    its cursor, so a crash cannot number anything twice.
//!  - The readers page by number, so page 10,000 costs the same as page 1.
//!
//! Ids are always `<txid>i0` here: the genesis transaction (for a multi-part
//! Doginal, the first one of the chain) followed by i0.

use super::*;
use crate::store::{Batch, Tree};

/// Blocks a height must be buried under before its inscriptions are numbered.
pub const NUMBER_CONFIRMATIONS: u64 = 6;

/// Content kinds, as bit positions. An inscription can be in more than one:
/// a GIF is also an image.
pub const KIND_NAMES: [&str; 15] = [
  "image", "gif", "svg", "html", "text", "json", "code", "video", "audio", "model", "pdf", "font", "drc20", "dogemap",
  "other",
];

const K_IMAGE: u32 = 1 << 0;
const K_GIF: u32 = 1 << 1;
const K_SVG: u32 = 1 << 2;
const K_HTML: u32 = 1 << 3;
pub(crate) const K_TEXT: u32 = 1 << 4;
pub(crate) const K_JSON: u32 = 1 << 5;
const K_CODE: u32 = 1 << 6;
const K_VIDEO: u32 = 1 << 7;
const K_AUDIO: u32 = 1 << 8;
const K_MODEL: u32 = 1 << 9;
const K_PDF: u32 = 1 << 10;
const K_FONT: u32 = 1 << 11;
const K_DRC20: u32 = 1 << 12;
const K_DOGEMAP: u32 = 1 << 13;
const K_OTHER: u32 = 1 << 14;

pub fn kind_index(name: &str) -> Option<usize> {
  KIND_NAMES.iter().position(|k| *k == name)
}

pub fn kind_names(kinds: u32) -> Vec<&'static str> {
  KIND_NAMES
    .iter()
    .enumerate()
    .filter(|(i, _)| kinds & (1 << i) != 0)
    .map(|(_, k)| *k)
    .collect()
}

/// Whether a content type is text-like enough that its body decides the kind
/// (a DRC-20 operation or a dogemap claim rather than plain text).
pub fn needs_body(content_type: &str) -> bool {
  let ct = content_type.split(';').next().unwrap_or("").trim().to_ascii_lowercase();
  ct == "application/json" || (ct.starts_with("text/") && ct != "text/html" && ct != "text/css" && ct != "text/javascript")
}

fn is_drc20(body: &[u8]) -> bool {
  if body.len() > 4096 {
    return false;
  }
  serde_json::from_slice::<Value>(body)
    .ok()
    .and_then(|v| v.get("p").and_then(Value::as_str).map(|p| p.eq_ignore_ascii_case("drc-20")))
    .unwrap_or(false)
}

fn looks_like_json(body: &[u8]) -> bool {
  let t = body.trim_ascii_start();
  matches!(t.first(), Some(b'{') | Some(b'[')) && body.len() <= 1 << 20 && serde_json::from_slice::<Value>(body).is_ok()
}

/// The kinds an inscription belongs to. `body` matters only for text-like
/// types (see [`needs_body`]); pass `None` when it is not at hand.
pub fn kinds_of(content_type: &str, body: Option<&[u8]>) -> u32 {
  let ct = content_type.split(';').next().unwrap_or("").trim().to_ascii_lowercase();
  if ct.is_empty() {
    return K_OTHER;
  }
  if let Some(sub) = ct.strip_prefix("image/") {
    return K_IMAGE | if sub == "gif" { K_GIF } else { 0 } | if sub.starts_with("svg") { K_SVG } else { 0 };
  }
  if ct == "text/html" || ct == "application/xhtml+xml" {
    return K_HTML;
  }
  if ct.starts_with("video/") {
    return K_VIDEO;
  }
  if ct.starts_with("audio/") {
    return K_AUDIO;
  }
  if ct.starts_with("model/") {
    return K_MODEL;
  }
  if ct == "application/pdf" {
    return K_PDF;
  }
  if ct.starts_with("font/") || ct.starts_with("application/font-") || ct.starts_with("application/x-font") || ct == "application/vnd.ms-fontobject" {
    return K_FONT;
  }
  if matches!(
    ct.as_str(),
    "application/javascript"
      | "text/javascript"
      | "application/x-javascript"
      | "application/ecmascript"
      | "text/ecmascript"
      | "text/css"
      | "application/wasm"
      | "text/x-python"
      | "application/x-python"
      | "application/x-sh"
      | "text/x-rust"
      | "text/x-c"
      | "application/typescript"
  ) {
    return K_CODE;
  }
  if ct == "application/json" || ct.starts_with("text/") {
    if let Some(b) = body {
      if parse_dogemap_number(b).is_some() {
        return K_DOGEMAP;
      }
      if is_drc20(b) {
        return K_DRC20;
      }
      if ct == "application/json" || (ct == "text/plain" && looks_like_json(b)) {
        return K_JSON;
      }
    } else if ct == "application/json" {
      return K_JSON;
    }
    return K_TEXT;
  }
  K_OTHER
}

#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq)]
pub struct SeqEntry {
  pub id: String,
  pub kinds: u32,
  pub time: u64,
}

/// Where an inscription sits in chain order, and its number once numbered.
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq)]
pub struct Genesis {
  pub number: u64,
  pub height: u64,
  pub time: u64,
  pub kinds: u32,
}

#[derive(Debug, Serialize, Deserialize, Clone, Default)]
pub(crate) struct NumberingState {
  /// The last `inscription_seq` key numbered; empty before the first.
  pub(crate) cursor: Vec<u8>,
  /// Inscriptions numbered so far, which is also the next number.
  next: u64,
  /// The same, per kind.
  kind_next: Vec<u64>,
}

pub fn seq_key(height: u64, tx_index: u32) -> [u8; 12] {
  let mut k = [0u8; 12];
  k[..8].copy_from_slice(&height.to_be_bytes());
  k[8..].copy_from_slice(&tx_index.to_be_bytes());
  k
}

pub(crate) fn seq_height(key: &[u8]) -> u64 {
  key.get(..8).map(|b| u64::from_be_bytes(b.try_into().unwrap())).unwrap_or(0)
}

fn kind_key(kind: usize, n: u64) -> [u8; 9] {
  let mut k = [0u8; 9];
  k[0] = kind as u8;
  k[1..].copy_from_slice(&n.to_be_bytes());
  k
}

const SEQ_SINCE_KEY: &[u8] = b"inscription_seq_since";
const SEQ_BACKFILL_NEXT_KEY: &[u8] = b"inscription_seq_backfill_next";
const SEQ_BACKFILL_DONE_KEY: &[u8] = b"inscription_seq_backfill_v1";
const NUMBERING_KEY: &[u8] = b"inscription_numbering_v1";

pub(crate) fn db_of(config: &Config) -> Result<store::Db> {
  open_db(&config.db_path())
}

pub(crate) fn meta_u64(meta: &Tree, key: &[u8]) -> Result<Option<u64>> {
  meta.get(key)?.map(|v| decode_u64(v.as_ref())).transpose()
}

pub(crate) fn numbering_state(meta: &Tree) -> Result<NumberingState> {
  let mut st: NumberingState = match meta.get(NUMBERING_KEY)? {
    Some(raw) => bincode::deserialize(raw.as_ref()).context("decode numbering state")?,
    None => NumberingState::default(),
  };
  st.kind_next.resize(KIND_NAMES.len(), 0);
  Ok(st)
}

/// Called once at indexer start: inscriptions in blocks from here on are
/// recorded as they are indexed, and everything before is the backfill's.
pub(crate) fn mark_seq_since(meta: &Tree, next_height: u64) -> Result<()> {
  if meta.get(SEQ_SINCE_KEY)?.is_none() {
    meta.insert(SEQ_SINCE_KEY, encode_u64(next_height).to_vec())?;
  }
  Ok(())
}

/// The content kinds of a newly made inscription, as indexing sees it. A
/// delegate with no type of its own takes its delegate's.
pub(crate) fn kinds_for_new(
  inscriptions_by_id: &Tree,
  content_type: &str,
  body: &[u8],
  delegate: Option<&str>,
) -> Result<u32> {
  if content_type.trim().is_empty()
    && let Some(d) = delegate
    && let Some(raw) = inscriptions_by_id.get(d.as_bytes())?
  {
    let rec = decode_inscription_record(raw.as_ref())?;
    return Ok(kinds_of(&rec.content_type, None));
  }
  Ok(kinds_of(content_type, Some(body)))
}

pub(crate) fn seq_value(id: &str, kinds: u32, time: u64) -> Result<Vec<u8>> {
  Ok(bincode::serialize(&SeqEntry { id: id.to_string(), kinds, time })?)
}

// ---------------------------------------------------------------- backfill --

pub fn inscription_seq_backfill_done(config: &Config) -> Result<bool> {
  Ok(db_of(config)?.open_tree("meta")?.get(SEQ_BACKFILL_DONE_KEY)?.is_some())
}

struct FetchedBlock {
  height: u64,
  time: u64,
  txids: Vec<String>,
}

async fn fetch_block_txids(config: Config, height: u64, known_hash: Option<String>) -> Result<FetchedBlock> {
  let client = indexer_rpc_client()?;
  let hash = match known_hash {
    Some(h) => h,
    None => rpc_call(client, &config, "getblockhash", serde_json::json!([height])).await?,
  };
  let block: Value = rpc_call(client, &config, "getblock", serde_json::json!([hash, 1])).await?;
  let txids = block["tx"]
    .as_array()
    .map(|a| a.iter().filter_map(|t| t.as_str().map(str::to_string)).collect())
    .unwrap_or_default();
  Ok(FetchedBlock { height, time: block["time"].as_u64().unwrap_or(0), txids })
}

/// Records, for one stretch of blocks, every inscription whose genesis
/// transaction is in them. Returns how many were found.
///
/// Most inscriptions of 2023 are DRC-20 text, and telling a mint from plain
/// text means reading its body: one random read each, so they are spread
/// across cores instead of made one after another.
fn record_backfilled(db: &store::Db, blocks: Vec<FetchedBlock>, next_height: u64) -> Result<u64> {
  let by_id = db.open_tree("inscriptions_by_id")?;
  let content = db.open_tree("inscription_content")?;
  let seq = db.open_tree("inscription_seq")?;
  let meta = db.open_tree("meta")?;
  // A batched lookup per block, with the blocks spread across cores: a
  // single batch runs on one thread, and 2023 blocks carry a thousand
  // transactions or more each.
  let per_block: Vec<Result<Vec<([u8; 12], InscriptionRecord, u64)>>> = blocks
    .par_iter()
    .map(|block| {
      let ids: Vec<String> = block.txids.iter().map(|t| format!("{t}i0")).collect();
      let mut found = Vec::new();
      for (tx_index, raw) in by_id.multi_get(&ids)?.into_iter().enumerate() {
        if let Some(raw) = raw {
          found.push((seq_key(block.height, tx_index as u32), decode_inscription_record(raw.as_ref())?, block.time));
        }
      }
      Ok(found)
    })
    .collect();
  let mut rows: Vec<([u8; 12], InscriptionRecord, u64)> = Vec::new();
  for r in per_block {
    rows.extend(r?);
  }
  let kinds: Vec<Result<u32>> = rows
    .par_iter()
    .map(|(_, rec, _)| -> Result<u32> {
      if rec.content_type.trim().is_empty() {
        return Ok(match rec.delegate.as_deref().map(|d| by_id.get(d.as_bytes())).transpose()?.flatten() {
          Some(d) => kinds_of(&decode_inscription_record(d.as_ref())?.content_type, None),
          None => kinds_of("", None),
        });
      }
      if needs_body(&rec.content_type) {
        let body = content.get(rec.id.as_bytes())?.and_then(|c| decode_inscription_content(c.as_ref()).ok());
        return Ok(kinds_of(&rec.content_type, body.as_ref().map(|c| c.body.as_slice())));
      }
      Ok(kinds_of(&rec.content_type, None))
    })
    .collect();
  let mut batch = Batch::default();
  let found = rows.len() as u64;
  for ((key, rec, time), kinds) in rows.into_iter().zip(kinds) {
    batch.insert(&seq, key.to_vec(), seq_value(&rec.id, kinds?, time)?);
  }
  batch.insert(&meta, SEQ_BACKFILL_NEXT_KEY.to_vec(), encode_u64(next_height).to_vec());
  batch.commit(&meta)?;
  Ok(found)
}

/// One-off: records chain order for every inscription made before the
/// indexer started recording it, by walking those blocks' transaction lists
/// from the node. Resumable, and it runs alongside indexing.
pub async fn backfill_inscription_seq(config: Config) -> Result<()> {
  if inscription_seq_backfill_done(&config)? {
    return Ok(());
  }
  let db = db_of(&config)?;
  let meta = db.open_tree("meta")?;
  let blocks_tree = db.open_tree("blocks")?;
  // Set by the indexer when it starts, a moment after this task.
  let since = loop {
    if let Some(v) = meta_u64(&meta, SEQ_SINCE_KEY)? {
      break v;
    }
    sleep(Duration::from_secs(1)).await;
  };
  let first = config.first_inscription_height;
  let mut height = meta_u64(&meta, SEQ_BACKFILL_NEXT_KEY)?.unwrap_or(first).max(first);
  info!("inscription order backfill: blocks {} to {}, starting at {}", first, since.saturating_sub(1), height);
  let started = Instant::now();
  let (mut found, mut last_log) = (0u64, Instant::now());
  // The node serves RPC from a small work queue that the indexer shares, so
  // only a few requests are kept in flight.
  let lookahead = config.rpc_concurrency.clamp(4, 12);
  const STEP: usize = 200;
  let mut inflight: VecDeque<tokio::task::JoinHandle<Result<FetchedBlock>>> = VecDeque::new();
  let mut next_fetch = height;
  let mut fetched: Vec<FetchedBlock> = Vec::with_capacity(STEP);
  // One stretch is recorded while the next is fetched. Stretches still commit
  // in order, each with its resume point, because each waits for the last.
  let mut recording: Option<tokio::task::JoinHandle<Result<u64>>> = None;
  let (mut fetch_wait, mut record_wait) = (Duration::ZERO, Duration::ZERO);

  while height < since {
    while inflight.len() < lookahead && next_fetch < since {
      let hash = blocks_tree.get(encode_u64(next_fetch))?.and_then(|v| String::from_utf8(v.to_vec()).ok());
      inflight.push_back(tokio::spawn(fetch_block_txids(config.clone(), next_fetch, hash)));
      next_fetch += 1;
    }
    let Some(handle) = inflight.pop_front() else { break };
    let t = Instant::now();
    let block = handle.await.context("join block fetch")??;
    fetch_wait += t.elapsed();
    height = block.height + 1;
    fetched.push(block);
    if fetched.len() < STEP && height < since {
      continue;
    }
    if let Some(prev) = recording.take() {
      let t = Instant::now();
      found += prev.await.context("record backfill")??;
      record_wait += t.elapsed();
    }
    let db2 = db.clone();
    let batch = std::mem::take(&mut fetched);
    let upto = height;
    recording = Some(tokio::task::spawn_blocking(move || record_backfilled(&db2, batch, upto)));
    if last_log.elapsed() > Duration::from_secs(60) {
      last_log = Instant::now();
      info!(
        "inscription order backfill: at block {} of {}, {} inscriptions placed, {:.0?} elapsed (waited {:.0?} on the node, {:.0?} on the store)",
        height, since, found, started.elapsed(), fetch_wait, record_wait
      );
    }
  }
  if let Some(prev) = recording.take() {
    found += prev.await.context("record backfill")??;
  }
  meta.insert(SEQ_BACKFILL_DONE_KEY, b"1")?;
  db.flush()?;
  info!("inscription order backfill: done in {:.0?}, {} inscriptions placed", started.elapsed(), found);
  Ok(())
}

// --------------------------------------------------------------- numbering --

/// Numbers up to `max` more inscriptions, in chain order, down to `through`
/// height. Returns how many rows of `inscription_seq` it consumed.
fn number_some(db: &store::Db, through: u64, max: usize) -> Result<usize> {
  let meta = db.open_tree("meta")?;
  let seq = db.open_tree("inscription_seq")?;
  let numbers = db.open_tree("inscription_number")?;
  let kinds_tree = db.open_tree("inscription_kind_number")?;
  let genesis = db.open_tree("inscription_genesis")?;
  let mut st = numbering_state(&meta)?;

  let mut rows: Vec<(Vec<u8>, SeqEntry)> = Vec::new();
  let mut start = st.cursor.clone();
  if !start.is_empty() {
    start.push(0); // the key right after the cursor
  }
  seq.for_each_from(&start, |k, v| {
    if seq_height(k) > through || rows.len() >= max {
      return Ok(false);
    }
    rows.push((k.to_vec(), bincode::deserialize(v).context("decode seq entry")?));
    Ok(true)
  })?;
  if rows.is_empty() {
    return Ok(0);
  }

  let mut batch = Batch::default();
  let mut seen: HashSet<String> = HashSet::new();
  let consumed = rows.len();
  for (key, entry) in rows {
    st.cursor = key.clone();
    // A Doginal spread over several transactions can be seen twice: once by
    // the backfill at its first transaction, once live at its last. The first
    // sighting in chain order keeps the number.
    if !seen.insert(entry.id.clone()) || genesis.get(entry.id.as_bytes())?.is_some() {
      continue;
    }
    let number = st.next;
    st.next += 1;
    batch.insert(&numbers, number.to_be_bytes().to_vec(), entry.id.as_bytes().to_vec());
    for k in 0..KIND_NAMES.len() {
      if entry.kinds & (1 << k) != 0 {
        batch.insert(&kinds_tree, kind_key(k, st.kind_next[k]).to_vec(), entry.id.as_bytes().to_vec());
        st.kind_next[k] += 1;
      }
    }
    let g = Genesis { number, height: seq_height(&key), time: entry.time, kinds: entry.kinds };
    batch.insert(&genesis, entry.id.as_bytes().to_vec(), bincode::serialize(&g)?);
  }
  batch.insert(&meta, NUMBERING_KEY.to_vec(), bincode::serialize(&st)?);
  batch.commit(&meta)?;
  Ok(consumed)
}

/// Keeps inscription numbers up to date: catches up once the backfill is
/// done, then follows the chain [`NUMBER_CONFIRMATIONS`] blocks behind.
pub async fn run_inscription_numbering(config: Config) -> Result<()> {
  let db = db_of(&config)?;
  let meta = db.open_tree("meta")?;
  let mut announced = false;
  loop {
    if !inscription_seq_backfill_done(&config)? {
      sleep(Duration::from_secs(30)).await;
      continue;
    }
    let indexed = meta_u64(&meta, b"indexed_height")?.unwrap_or(0);
    let through = indexed.saturating_sub(NUMBER_CONFIRMATIONS);
    let db2 = db.clone();
    let consumed = tokio::task::spawn_blocking(move || number_some(&db2, through, 50_000))
      .await
      .context("numbering task")??;
    if consumed == 0 {
      if !announced {
        announced = true;
        let st = numbering_state(&meta)?;
        info!("inscription numbering: caught up, {} inscriptions numbered", st.next);
      }
      sleep(Duration::from_secs(15)).await;
    }
  }
}

// ----------------------------------------------------------------- readers --

#[derive(Debug, Serialize, Clone)]
pub struct ListedInscription {
  pub id: String,
  pub number: Option<u64>,
  pub height: u64,
  pub time: u64,
  pub kinds: u32,
}

#[derive(Debug, Serialize, Clone)]
pub struct InscriptionPage {
  /// Numbered inscriptions of this kind; pages run over these.
  pub total: u64,
  /// Whether every inscription is numbered, so `total` is the whole archive.
  pub complete: bool,
  pub items: Vec<ListedInscription>,
  /// Newest inscriptions, still too few blocks deep to have a number.
  pub pending: Vec<ListedInscription>,
}

#[derive(Debug, Serialize, Clone)]
pub struct NumberingStatus {
  pub backfill_done: bool,
  /// Next block the backfill will read, and where it stops.
  pub backfill_height: u64,
  pub backfill_until: u64,
  pub first_height: u64,
  pub numbered: u64,
  pub kind_counts: Vec<(String, u64)>,
}

pub fn numbering_status(config: &Config) -> Result<NumberingStatus> {
  let db = db_of(config)?;
  let meta = db.open_tree("meta")?;
  let st = numbering_state(&meta)?;
  let first = config.first_inscription_height;
  Ok(NumberingStatus {
    backfill_done: meta.get(SEQ_BACKFILL_DONE_KEY)?.is_some(),
    backfill_height: meta_u64(&meta, SEQ_BACKFILL_NEXT_KEY)?.unwrap_or(first),
    backfill_until: meta_u64(&meta, SEQ_SINCE_KEY)?.unwrap_or(0),
    first_height: first,
    numbered: st.next,
    kind_counts: KIND_NAMES.iter().zip(st.kind_next.iter()).map(|(k, n)| (k.to_string(), *n)).collect(),
  })
}

pub fn inscription_genesis(config: &Config, id: &str) -> Result<Option<Genesis>> {
  let db = db_of(config)?;
  match db.open_tree("inscription_genesis")?.get(id.as_bytes())? {
    Some(raw) => Ok(Some(bincode::deserialize(raw.as_ref())?)),
    None => Ok(None),
  }
}

pub fn inscription_id_by_number(config: &Config, number: u64) -> Result<Option<String>> {
  let db = db_of(config)?;
  Ok(
    db.open_tree("inscription_number")?
      .get(number.to_be_bytes())?
      .map(|v| String::from_utf8_lossy(v.as_ref()).to_string()),
  )
}

fn listed(genesis: &Tree, ids: Vec<String>) -> Result<Vec<ListedInscription>> {
  let raws = genesis.multi_get(&ids)?;
  let mut out = Vec::with_capacity(ids.len());
  for (id, raw) in ids.into_iter().zip(raws) {
    let g: Option<Genesis> = raw.map(|r| bincode::deserialize(r.as_ref())).transpose()?;
    out.push(ListedInscription {
      id,
      number: g.as_ref().map(|g| g.number),
      height: g.as_ref().map(|g| g.height).unwrap_or(0),
      time: g.as_ref().map(|g| g.time).unwrap_or(0),
      kinds: g.map(|g| g.kinds).unwrap_or(0),
    });
  }
  Ok(out)
}

/// Rows of `inscription_seq` newest first, from the end down to (not
/// including) `stop_at`, keeping those of `kind`; skips `skip`, takes `take`.
fn seq_newest(seq: &Tree, stop_at: &[u8], kind: Option<usize>, skip: usize, take: usize) -> Result<Vec<ListedInscription>> {
  let mut out = Vec::new();
  let mut skipped = 0usize;
  let mut walked = 0usize;
  seq.for_each_rev_from(b"", |k, v| {
    walked += 1;
    if (!stop_at.is_empty() && k <= stop_at) || out.len() >= take || walked > 200_000 {
      return Ok(false);
    }
    let e: SeqEntry = bincode::deserialize(v).context("decode seq entry")?;
    if kind.is_some_and(|i| e.kinds & (1 << i) == 0) {
      return Ok(true);
    }
    if skipped < skip {
      skipped += 1;
      return Ok(true);
    }
    out.push(ListedInscription { id: e.id, number: None, height: seq_height(k), time: e.time, kinds: e.kinds });
    Ok(true)
  })?;
  Ok(out)
}

/// One page of inscriptions, by number: `kind` filters to one kind, page 1
/// is the newest (or the oldest with `oldest_first`).
pub fn list_inscriptions(config: &Config, kind: Option<usize>, page: u64, limit: u64, oldest_first: bool) -> Result<InscriptionPage> {
  let db = db_of(config)?;
  let meta = db.open_tree("meta")?;
  let seq = db.open_tree("inscription_seq")?;
  let genesis = db.open_tree("inscription_genesis")?;
  let st = numbering_state(&meta)?;
  let complete = meta.get(SEQ_BACKFILL_DONE_KEY)?.is_some() && st.next > 0;
  let page = page.max(1);
  let limit = limit.clamp(1, 100);

  if !complete {
    // Still placing older inscriptions: show the ones recorded live, newest
    // first. Below that the backfill is part way through, so not in order.
    let since = meta_u64(&meta, SEQ_SINCE_KEY)?.unwrap_or(0);
    let stop_at = seq_key(since.saturating_sub(1), u32::MAX);
    let skip = ((page - 1) * limit) as usize;
    let items = seq_newest(&seq, &stop_at, kind, skip, limit as usize)?;
    return Ok(InscriptionPage { total: 0, complete: false, items, pending: Vec::new() });
  }

  let total = match kind {
    Some(k) => st.kind_next[k],
    None => st.next,
  };
  let (lo, hi) = if oldest_first {
    let lo = (page - 1).saturating_mul(limit).min(total);
    (lo, (lo + limit).min(total))
  } else {
    let hi = total.saturating_sub((page - 1).saturating_mul(limit));
    (hi.saturating_sub(limit), hi)
  };
  let mut ids: Vec<String> = Vec::new();
  if lo < hi {
    let (tree, start, end) = match kind {
      Some(k) => (db.open_tree("inscription_kind_number")?, kind_key(k, lo).to_vec(), kind_key(k, hi).to_vec()),
      None => (db.open_tree("inscription_number")?, lo.to_be_bytes().to_vec(), hi.to_be_bytes().to_vec()),
    };
    for row in tree.range(start..end)? {
      let (_, v) = row?;
      ids.push(String::from_utf8_lossy(v.as_ref()).to_string());
    }
  }
  if !oldest_first {
    ids.reverse();
  }
  let items = listed(&genesis, ids)?;
  let pending = if page == 1 && !oldest_first {
    seq_newest(&seq, &st.cursor, kind, 0, limit as usize)?
      .into_iter()
      // A multi-part Doginal already numbered from its first transaction.
      .filter(|i| genesis.get(i.id.as_bytes()).ok().flatten().is_none())
      .collect()
  } else {
    Vec::new()
  };
  Ok(InscriptionPage { total, complete, items, pending })
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn kinds_cover_common_types() {
    assert_eq!(kinds_of("image/png", None), K_IMAGE);
    assert_eq!(kinds_of("image/gif", None), K_IMAGE | K_GIF);
    assert_eq!(kinds_of("image/svg+xml;charset=utf-8", None), K_IMAGE | K_SVG);
    assert_eq!(kinds_of("text/html;charset=utf-8", None), K_HTML);
    assert_eq!(kinds_of("video/mp4", None), K_VIDEO);
    assert_eq!(kinds_of("audio/mpeg", None), K_AUDIO);
    assert_eq!(kinds_of("model/gltf-binary", None), K_MODEL);
    assert_eq!(kinds_of("application/pdf", None), K_PDF);
    assert_eq!(kinds_of("font/woff2", None), K_FONT);
    assert_eq!(kinds_of("text/javascript", None), K_CODE);
    assert_eq!(kinds_of("application/octet-stream", None), K_OTHER);
    assert_eq!(kinds_of("", None), K_OTHER);
    assert_eq!(kinds_of("text/plain", Some(b"hello")), K_TEXT);
    assert_eq!(kinds_of("text/plain", Some(b"6400000.dogemap")), K_DOGEMAP);
    assert_eq!(kinds_of("text/plain", Some(br#"{"p":"drc-20","op":"mint","tick":"dogi","amt":"1000"}"#)), K_DRC20);
    assert_eq!(kinds_of("application/json", Some(br#"{"p":"DRC-20","op":"deploy"}"#)), K_DRC20);
    assert_eq!(kinds_of("application/json", Some(br#"{"name":"x"}"#)), K_JSON);
    assert_eq!(kinds_of("text/plain", Some(br#"{"name":"x"}"#)), K_JSON);
    assert_eq!(kind_names(K_IMAGE | K_GIF), vec!["image", "gif"]);
    assert!(needs_body("text/plain;charset=utf-8") && needs_body("application/json") && !needs_body("text/html"));
  }

  #[test]
  fn numbering_pages_by_kind_and_skips_repeats() {
    let db = store::Db::temporary().expect("db");
    let seq = db.open_tree("inscription_seq").unwrap();
    let id = |n: u8| format!("{}i0", format!("{n:02x}").repeat(32));
    // Four inscriptions over three blocks; id 2 is seen again later, as a
    // multi-part Doginal is, and must keep its first number.
    let rows = [
      (100u64, 1u32, id(1), K_IMAGE),
      (100, 7, id(2), K_TEXT),
      (101, 0, id(3), K_IMAGE | K_GIF),
      (105, 2, id(2), K_TEXT),
      (130, 0, id(4), K_HTML),
    ];
    for (h, i, ident, kinds) in &rows {
      seq.insert(seq_key(*h, *i), seq_value(ident, *kinds, 1000 + h).unwrap()).unwrap();
    }
    // Only blocks up to 110 are deep enough.
    assert_eq!(number_some(&db, 110, 2).unwrap(), 2);
    assert_eq!(number_some(&db, 110, 100).unwrap(), 2);
    assert_eq!(number_some(&db, 110, 100).unwrap(), 0);
    let meta = db.open_tree("meta").unwrap();
    let st = numbering_state(&meta).unwrap();
    assert_eq!(st.next, 3, "the repeat of id 2 takes no number");
    assert_eq!(st.kind_next[kind_index("image").unwrap()], 2);
    assert_eq!(st.kind_next[kind_index("gif").unwrap()], 1);
    let g: Genesis = bincode::deserialize(db.open_tree("inscription_genesis").unwrap().get(id(3).as_bytes()).unwrap().unwrap().as_ref()).unwrap();
    assert_eq!((g.number, g.height, g.time), (2, 101, 1101));
    let images = db.open_tree("inscription_kind_number").unwrap();
    assert_eq!(images.get(kind_key(0, 1)).unwrap().unwrap().as_ref(), id(3).as_bytes());
    assert_eq!(number_some(&db, 200, 100).unwrap(), 1);
    assert_eq!(numbering_state(&meta).unwrap().next, 4);
  }
}
