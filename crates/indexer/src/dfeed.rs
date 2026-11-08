//! D:// (the DogeFeed protocol) v1: every post, comment, quote, edit and key
//! link (signed JSON inscriptions), and every like, branch, follow, tip,
//! reveal, delete and key revocation (payments with one signed 80-byte
//! OP_RETURN), checked with the `dproto` crate.
//!
//! It follows the main index block by block from `START`: inscriptions come
//! from chain order (`inscription_seq`) and their stored content, payments
//! from the block itself, with input addresses read from the node. Records
//! are kept in chain order, valid or not (invalid ones with the reason), and
//! nothing derived (counts, who follows whom, deletes, edits) is stored: it is
//! worked out when read, so a reorg only has to take records away. Records
//! count at six confirmations, as the standard says; until then they are
//! pending.
//!
//! One envelope detail: DogeFeed's builder splits a record's JSON over several
//! pushes of one Doginal piece, where standard Doginals parsing (ord-dogecoin,
//! and this index) keeps only the first push. The record is read from the
//! standard body joined with those pushes (`dproto::read_inscription`).

use std::collections::{HashMap, VecDeque};
use std::time::{Duration, Instant};

use anyhow::{Context, Result};
use dogeord_core::Config;
use dproto::{Detect, Op, Outpoint, PaymentTx, PostCandidate, Record, RecordType, Target, TxOut};
use serde::{Deserialize, Serialize};
use tokio::time::sleep;
use tracing::{info, warn};

use crate::insc_index::{self as ii, SeqEntry};
use crate::store::{self, Batch, Tree};
use crate::{RpcBlock, RpcTx, decode_inscription_content, indexer_rpc_client, rpc_call, to_satoshis};

/// First block read: before the first D:// v1 record (block 6,448,293).
pub const START: u64 = 6_440_000;
const STATE_KEY: &[u8] = b"dfeed_state_v1";
/// What stored records hold. Raising it clears them and reads D:// again
/// from START (a few minutes): 2 added the registrar key and reveal payouts.
const VERSION: u64 = 2;
const VERSION_KEY: &[u8] = b"dfeed_version";
/// Block hashes kept to notice a reorg.
const KEEP_HASHES: usize = 100;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct State {
  next_height: u64,
  hashes: VecDeque<(u64, String)>,
  records: u64,
  valid: u64,
}

/// One D:// record: an inscription or a payment, valid or not.
#[derive(Debug, Clone, Default, PartialEq, Serialize, Deserialize)]
pub struct DfRecord {
  pub txid: String,
  pub height: u64,
  pub tx_index: u32,
  pub time: u64,
  /// post, comment, quote, edit, keylink, like, branch, follow, tip, reveal,
  /// delete, keyrevoke; "unknown" for a D:// inscription too broken to tell.
  pub kind: String,
  pub inscription_id: Option<String>,
  /// Who signed it: `aip.addr`, or the address every input spends from.
  pub author: String,
  /// The account it counts for: the author, or the account that linked the
  /// author's CLI key for this op.
  pub account: String,
  /// What it points at: a post's inscription id, or an address (follow, key
  /// link, key revocation).
  pub target: Option<String>,
  pub text: Option<String>,
  #[serde(default)]
  pub media: Vec<String>,
  #[serde(default)]
  pub tags: Vec<String>,
  #[serde(default)]
  pub mentions: Vec<String>,
  /// `map.ts`, the author's clock: shown, never used for order.
  pub ts: Option<u64>,
  /// The record's JSON as read.
  pub body: Option<String>,
  pub label: Option<String>,
  #[serde(default)]
  pub ops: Vec<String>,
  /// Who it pays, and how much: from the OP_RETURN payment, or for a comment
  /// or quote, what its reveal pays the original author it answers.
  pub recipient: Option<String>,
  pub recipient_koinu: Option<u64>,
  /// What it pays DogeFeed.
  pub fee_koinu: Option<u64>,
  /// The registrar key (`kid`) whose signature on it verifies: DogeFeed's
  /// signature, showing it was issued through DogeFeed.
  #[serde(default)]
  pub registrar: Option<String>,
  /// Read from the body joined with the reveal's extra pushes.
  #[serde(default)]
  pub split_body: bool,
  pub valid: bool,
  pub reason: Option<String>,
  /// Index entries this record made, removed with it on a reorg.
  #[serde(default)]
  pub index_keys: Vec<String>,
}

/// A CLI key's link to an account.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct Link {
  account: String,
  ops: Vec<String>,
  from_height: u64,
  revoked_at: Option<u64>,
  /// The record that made it.
  seq: String,
}

struct Trees {
  meta: Tree,
  seq: Tree,
  content: Tree,
  rec: Tree,
  idx: Tree,
}

impl Trees {
  fn open(db: &store::Db) -> Result<Self> {
    Ok(Self {
      meta: db.open_tree("meta")?,
      seq: db.open_tree("inscription_seq")?,
      content: db.open_tree("inscription_content")?,
      rec: db.open_tree("dfeed_rec")?,
      idx: db.open_tree("dfeed_idx")?,
    })
  }
}

fn load_state(meta: &Tree) -> Result<State> {
  Ok(match meta.get(STATE_KEY)? {
    Some(raw) => serde_json::from_slice(raw.as_ref()).context("decode dfeed state")?,
    None => State { next_height: START, ..Default::default() },
  })
}

fn seq_hex(height: u64, tx_index: u32) -> String {
  hex::encode(ii::seq_key(height, tx_index))
}

fn get_rec(t: &Trees, key: &[u8]) -> Result<Option<DfRecord>> {
  t.rec.get(key)?.map(|v| serde_json::from_slice(v.as_ref()).context("decode dfeed record")).transpose()
}

fn link_of(t: &Trees, key: &str) -> Result<Option<Link>> {
  t.idx.get(format!("k|{key}"))?.map(|v| serde_json::from_slice(v.as_ref()).context("decode dfeed link")).transpose()
}

/// The account an author acts for in `op` at `height`.
fn account_for(t: &Trees, author: &str, op: &str, height: u64) -> Result<String> {
  Ok(match link_of(t, author)? {
    Some(l) if l.from_height <= height && l.revoked_at.is_none_or(|r| height < r) && l.ops.iter().any(|o| o == op) => l.account,
    _ => author.to_string(),
  })
}

/// The valid record an inscription id names.
fn by_inscription(t: &Trees, id: &str) -> Result<Option<DfRecord>> {
  match t.idx.get(format!("i|{id}"))? {
    Some(k) => get_rec(t, &hex::decode(k.as_ref()).context("dfeed index key")?),
    None => Ok(None),
  }
}

fn post_candidates(t: &Trees, target: &[u8; 11]) -> Vec<PostCandidate> {
  let mut out = Vec::new();
  let _ = t.idx.for_each_prefix(format!("p|{}|", hex::encode(target)), |k, _| {
    let seq = std::str::from_utf8(k).ok().and_then(|k| k.rsplit('|').next()).and_then(|s| hex::decode(s).ok());
    if let Some(Some(r)) = seq.map(|s| get_rec(t, &s).ok().flatten())
      && let Some(id) = r.inscription_id
    {
      out.push(PostCandidate { id, author: r.author });
    }
    Ok(true)
  });
  out
}

fn linked_keys(t: &Trees, account: &str) -> Vec<String> {
  let mut out = Vec::new();
  let prefix = format!("K|{account}|");
  let _ = t.idx.for_each_prefix(prefix.as_bytes(), |k, _| {
    if let Ok(s) = std::str::from_utf8(k) {
      out.push(s[prefix.len()..].to_string());
    }
    Ok(true)
  });
  out
}

fn outputs_of(tx: &RpcTx) -> Result<Vec<TxOut>> {
  tx.vout
    .iter()
    .map(|o| {
      Ok(TxOut {
        koinu: to_satoshis(o.value)?,
        script: hex::decode(o.script_pub_key.hex.as_deref().unwrap_or("")).context("output script hex")?,
      })
    })
    .collect()
}

fn script_sig_of(tx: &RpcTx) -> Option<Vec<u8>> {
  tx.vin.first()?.script_sig.as_ref().and_then(|s| hex::decode(&s.hex).ok())
}

fn has_dproto_op_return(tx: &RpcTx) -> bool {
  tx.vout.iter().any(|o| o.script_pub_key.hex.as_deref().is_some_and(|h| h.starts_with("6a4c50443a2f2f")))
}

/// Makes the record's index entries and writes it.
fn put(t: &Trees, batch: &mut Batch, mut r: DfRecord) -> Result<DfRecord> {
  let seq = seq_hex(r.height, r.tx_index);
  let mut keys = vec![format!("t|{}", r.txid), format!("a|{}|{seq}", r.account)];
  if r.author != r.account {
    keys.push(format!("a|{}|{seq}", r.author));
  }
  if r.valid {
    if let Some(id) = &r.inscription_id {
      keys.push(format!("i|{id}"));
      if RecordType::parse(&r.kind).is_some_and(RecordType::is_post_like)
        && let Some(target) = dproto::post_target(id)
      {
        keys.push(format!("p|{}|{seq}", hex::encode(target)));
      }
    }
    if let Some(target) = &r.target {
      keys.push(format!("g|{target}|{seq}"));
    }
  }
  for k in &keys {
    let v = if k.starts_with("i|") || k.starts_with("t|") { seq.clone().into_bytes() } else { Vec::new() };
    batch.insert(&t.idx, k.clone().into_bytes(), v);
  }
  r.index_keys = keys;
  batch.insert(&t.rec, ii::seq_key(r.height, r.tx_index).to_vec(), serde_json::to_vec(&r)?);
  Ok(r)
}

fn inscription_record(t: &Trees, height: u64, i: u32, time: u64, tx: &RpcTx, id: &str, rec: Record, split: bool, content_type: &str) -> Result<DfRecord> {
  let mut r = DfRecord {
    txid: tx.txid.clone(),
    height,
    tx_index: i,
    time,
    kind: rec.rtype.name().into(),
    inscription_id: Some(id.to_string()),
    author: rec.addr.clone(),
    account: account_for(t, &rec.addr, rec.rtype.name(), height)?,
    target: rec.reference.clone().or_else(|| rec.keylink.as_ref().map(|k| k.key.clone())),
    text: rec.text.clone(),
    media: rec.media.clone(),
    tags: rec.tags.clone(),
    mentions: rec.mentions.clone(),
    ts: Some(rec.ts),
    body: dproto::jcs(&rec.value).ok(),
    label: rec.keylink.as_ref().map(|k| k.label.clone()),
    ops: rec.keylink.as_ref().map(|k| k.ops.clone()).unwrap_or_default(),
    split_body: split,
    registrar: dproto::attestation_key(&rec).map(str::to_string),
    ..Default::default()
  };
  let outputs = outputs_of(tx)?;
  r.fee_koinu = Some(dproto::paid_to(&outputs, dproto::FEE_ADDRESS));
  if matches!(rec.rtype, RecordType::Comment | RecordType::Quote)
    && let Some(parent) = rec.reference.as_deref().map(|p| by_inscription(t, p)).transpose()?.flatten()
  {
    r.recipient_koinu = Some(dproto::paid_to(&outputs, &parent.author));
    r.recipient = Some(parent.author);
  }
  let check = || -> Result<(), String> {
    if content_type.split(';').next().unwrap_or("").trim() != "application/json" {
      return Err(format!("content type is {content_type:?}, not application/json"));
    }
    let mut parent_author = None;
    if let Some(reference) = &rec.reference {
      let parent = by_inscription(t, reference).map_err(|e| e.to_string())?.ok_or("what it points at is not a valid earlier D:// record")?;
      let ok = match rec.rtype {
        RecordType::Comment | RecordType::Quote => RecordType::parse(&parent.kind).is_some_and(RecordType::is_post_like),
        RecordType::Edit => RecordType::parse(&parent.kind).is_some_and(RecordType::is_post_like) && parent.account == r.account,
        _ => true,
      };
      if !ok {
        return Err(if rec.rtype == RecordType::Edit {
          "only the original author can edit it".into()
        } else {
          format!("it points at a {}, not a post", parent.kind)
        });
      }
      parent_author = Some(parent.author);
    }
    if let Some(k) = &rec.keylink {
      if dproto::address_hash(&k.key).is_none() {
        return Err("map.key is not a Dogecoin address".into());
      }
      if let Some(l) = link_of(t, &k.key).map_err(|e| e.to_string())?
        && l.revoked_at.is_none()
        && l.account != rec.addr
      {
        return Err(format!("that key is already linked to {}", l.account));
      }
    }
    let dests = [rec.addr.as_str(), r.account.as_str()];
    dproto::verify_inscription(&rec, &outputs, &dests, parent_author.as_deref())
  };
  match check() {
    Ok(()) => r.valid = true,
    Err(e) => r.reason = Some(e),
  }
  Ok(r)
}

/// Input addresses, read from the block itself or the node.
async fn input_addresses(config: &Config, tx: &RpcTx, local: &HashMap<&str, &RpcTx>, cache: &mut HashMap<String, RpcTx>) -> Result<Vec<Option<String>>> {
  let client = indexer_rpc_client()?;
  let mut out = Vec::new();
  for v in &tx.vin {
    let (Some(txid), Some(vout)) = (v.txid.as_deref(), v.vout) else {
      out.push(None);
      continue;
    };
    let prev = match local.get(txid) {
      Some(p) => (*p).clone(),
      None => {
        if !cache.contains_key(txid) {
          let p: RpcTx = rpc_call(client, config, "getrawtransaction", serde_json::json!([txid, true])).await?;
          cache.insert(txid.to_string(), p);
        }
        cache[txid].clone()
      }
    };
    let script = prev.vout.get(vout as usize).and_then(|o| o.script_pub_key.hex.as_deref()).and_then(|h| hex::decode(h).ok());
    out.push(script.and_then(|s| dproto::script_address(&s)));
  }
  Ok(out)
}

async fn payment_record(config: &Config, t: &Trees, height: u64, i: u32, time: u64, tx: &RpcTx, addrs: Vec<Option<String>>) -> Result<Option<DfRecord>> {
  let inputs: Vec<Outpoint> =
    tx.vin.iter().map(|v| Outpoint { txid: v.txid.clone().unwrap_or_default(), vout: v.vout.unwrap_or(0) }).collect();
  let outputs = outputs_of(tx)?;
  let _ = config;
  let ptx = PaymentTx { inputs: &inputs, input_addresses: &addrs, outputs: &outputs };
  let keys = |author: &str| linked_keys(t, author);
  let verdict = dproto::verify_payment_by_key(&ptx, |target| post_candidates(t, target), keys);
  let payer = addrs.first().cloned().flatten().unwrap_or_default();
  let mut r = DfRecord { txid: tx.txid.clone(), height, tx_index: i, time, author: payer.clone(), account: payer, ..Default::default() };
  match verdict {
    Ok(None) => return Ok(None),
    Err(e) => {
      r.kind = outputs
        .iter()
        .find_map(|o| dproto::op_return_payload(&o.script))
        .and_then(|p| dproto::decode_payload(&p))
        .map(|p| p.op.name().to_string())
        .unwrap_or_else(|| "unknown".into());
      r.reason = Some(e);
    }
    Ok(Some((p, kid))) => {
      r.registrar = Some(kid.to_string());
      r.kind = p.op.name().into();
      r.account = if p.op == Op::Keyrevoke { p.author.clone() } else { account_for(t, &p.author, p.op.name(), height)? };
      r.author = p.author;
      r.target = Some(match &p.target {
        Target::Post(id) | Target::Address(id) => id.clone(),
      });
      r.recipient = p.recipient.and_then(|(v, _)| outputs.get(v as usize)).and_then(|o| dproto::script_address(&o.script));
      r.recipient_koinu = p.recipient.map(|(_, k)| k);
      r.fee_koinu = Some(p.fee.1);
      r.valid = true;
      match (p.op, &p.target) {
        (Op::Delete, Target::Post(id)) => {
          if by_inscription(t, id)?.is_none_or(|post| post.account != r.account) {
            r.valid = false;
            r.reason = Some("only the original author can delete it".into());
          }
        }
        (Op::Keyrevoke, Target::Address(key)) => {
          if link_of(t, key)?.is_none_or(|l| l.account != r.author || l.revoked_at.is_some()) {
            r.valid = false;
            r.reason = Some("it revokes no live key of this account".into());
          }
        }
        _ => {}
      }
    }
  }
  Ok(Some(r))
}

/// Link changes a valid record makes, with the batch's other writes.
fn apply_links(t: &Trees, batch: &mut Batch, r: &DfRecord) -> Result<()> {
  if !r.valid {
    return Ok(());
  }
  let seq = seq_hex(r.height, r.tx_index);
  match (r.kind.as_str(), r.target.as_deref()) {
    ("keylink", Some(key)) => {
      let link = Link { account: r.author.clone(), ops: r.ops.clone(), from_height: r.height, revoked_at: None, seq };
      batch.insert(&t.idx, format!("k|{key}").into_bytes(), serde_json::to_vec(&link)?);
      batch.insert(&t.idx, format!("K|{}|{key}", r.author).into_bytes(), Vec::new());
    }
    ("keyrevoke", Some(key)) => {
      if let Some(mut l) = link_of(t, key)? {
        l.revoked_at = Some(r.height);
        batch.insert(&t.idx, format!("k|{key}").into_bytes(), serde_json::to_vec(&l)?);
      }
    }
    _ => {}
  }
  Ok(())
}

/// Reads one block's D:// records and writes them.
async fn index_block(config: &Config, t: &Trees, height: u64, block: &RpcBlock) -> Result<(u64, u64)> {
  let time = block.time.unwrap_or(0);
  // Inscriptions this block completes, by position.
  let mut completed: HashMap<u32, Vec<String>> = HashMap::new();
  t.seq.for_each_prefix(height.to_be_bytes(), |k, v| {
    let e: SeqEntry = bincode::deserialize(v).context("decode seq entry")?;
    completed.entry(u32::from_be_bytes(k[8..12].try_into().unwrap())).or_default().push(e.id);
    Ok(true)
  })?;
  let local: HashMap<&str, &RpcTx> = block.tx.iter().map(|x| (x.txid.as_str(), x)).collect();
  let mut cache = HashMap::new();
  let (mut n, mut valid) = (0, 0);
  for (i, tx) in block.tx.iter().enumerate() {
    let i = i as u32;
    let mut record = None;
    for id in completed.get(&i).into_iter().flatten() {
      let Some(raw) = t.content.get(id.as_bytes())? else { continue };
      let c = decode_inscription_content(raw.as_ref())?;
      if !c.content_type.to_ascii_lowercase().starts_with("application/json") {
        continue;
      }
      let script = script_sig_of(tx);
      let (d, split) = dproto::read_inscription(&c.body, script.as_deref());
      record = match d {
        Detect::NotDproto | Detect::UnknownVersion => None,
        Detect::Invalid(reason) => {
          let author = serde_json::from_slice::<serde_json::Value>(&c.body)
            .ok()
            .and_then(|v| v.pointer("/aip/addr").and_then(|a| a.as_str()).map(str::to_string))
            .unwrap_or_default();
          let kind = serde_json::from_slice::<serde_json::Value>(&c.body)
            .ok()
            .and_then(|v| v.pointer("/map/type").and_then(|a| a.as_str()).map(str::to_string))
            .filter(|k| RecordType::parse(k).is_some())
            .unwrap_or_else(|| "unknown".into());
          Some(DfRecord {
            txid: tx.txid.clone(),
            height,
            tx_index: i,
            time,
            kind,
            inscription_id: Some(id.clone()),
            account: author.clone(),
            author,
            split_body: split,
            reason: Some(reason),
            ..Default::default()
          })
        }
        Detect::Record(rec) => Some(inscription_record(t, height, i, time, tx, id, *rec, split, &c.content_type)?),
      };
      if record.is_some() {
        break;
      }
    }
    if record.is_none() && has_dproto_op_return(tx) {
      let addrs = input_addresses(config, tx, &local, &mut cache).await?;
      record = payment_record(config, t, height, i, time, tx, addrs).await?;
    }
    if let Some(r) = record {
      let mut batch = Batch::default();
      apply_links(t, &mut batch, &r)?;
      let r = put(t, &mut batch, r)?;
      batch.commit(&t.meta)?;
      n += 1;
      valid += r.valid as u64;
    }
  }
  Ok((n, valid))
}

/// Takes away every record from `height` on, newest first.
fn undo_from(t: &Trees, height: u64) -> Result<(u64, u64)> {
  let mut recs = Vec::new();
  t.rec.for_each_from(ii::seq_key(height, 0), |k, v| {
    recs.push((k.to_vec(), serde_json::from_slice::<DfRecord>(v).context("decode dfeed record")?));
    Ok(true)
  })?;
  let (mut n, mut valid) = (0, 0);
  for (key, r) in recs.into_iter().rev() {
    let mut batch = Batch::default();
    for k in &r.index_keys {
      batch.remove(&t.idx, k.clone().into_bytes());
    }
    if r.valid {
      match (r.kind.as_str(), r.target.as_deref()) {
        ("keylink", Some(k)) => {
          batch.remove(&t.idx, format!("k|{k}").into_bytes());
          batch.remove(&t.idx, format!("K|{}|{k}", r.author).into_bytes());
        }
        ("keyrevoke", Some(k)) => {
          if let Some(mut l) = link_of(t, k)? {
            l.revoked_at = None;
            batch.insert(&t.idx, format!("k|{k}").into_bytes(), serde_json::to_vec(&l)?);
          }
        }
        _ => {}
      }
    }
    batch.remove(&t.rec, key);
    batch.commit(&t.meta)?;
    n += 1;
    valid += r.valid as u64;
  }
  Ok((n, valid))
}

fn save(t: &Trees, st: &State) -> Result<()> {
  t.meta.insert(STATE_KEY, serde_json::to_vec(st)?)
}

/// Follows the main index, block by block, for good.
pub async fn run_dfeed_index(config: Config) -> Result<()> {
  let db = ii::db_of(&config)?;
  let t = Trees::open(&db)?;
  let client = indexer_rpc_client()?;
  if ii::meta_u64(&t.meta, VERSION_KEY)?.unwrap_or(1) < VERSION {
    t.rec.delete_range(vec![0u8], vec![0xffu8; 13])?;
    t.idx.delete_range(vec![0u8], vec![0xffu8])?;
    t.meta.remove(STATE_KEY)?;
    t.meta.insert(VERSION_KEY, VERSION.to_be_bytes())?;
    info!("d:// index: records are now version {VERSION}; reading D:// again from block {START}");
  }
  let mut st = load_state(&t.meta)?;
  info!("d:// index: starting at block {}, {} records ({} valid)", st.next_height, st.records, st.valid);
  let (mut last_log, mut caught_up) = (Instant::now(), false);
  loop {
    let indexed = ii::meta_u64(&t.meta, b"indexed_height")?.unwrap_or(0);
    if st.next_height > indexed {
      if !caught_up {
        caught_up = true;
        info!("d:// index: caught up at block {}, {} records ({} valid)", indexed, st.records, st.valid);
      }
      sleep(Duration::from_secs(2)).await;
      continue;
    }
    let h = st.next_height;
    let block = match crate::repair::fetch_block(client, &config, h).await {
      Ok(b) => b,
      Err(e) => {
        warn!("d:// index: block {h}: {e:#}");
        sleep(Duration::from_secs(10)).await;
        continue;
      }
    };
    // A reorg: the block before is no longer the one read.
    if let Some((ph, phash)) = st.hashes.back()
      && *ph + 1 == h
      && block.previousblockhash.as_deref() != Some(phash.as_str())
    {
      let back = *ph;
      let (n, v) = undo_from(&t, back)?;
      st.records -= n;
      st.valid -= v;
      st.hashes.pop_back();
      st.next_height = back;
      save(&t, &st)?;
      warn!("d:// index: reorg at block {back}: {n} records taken back");
      continue;
    }
    match index_block(&config, &t, h, &block).await {
      Ok((n, v)) => {
        st.records += n;
        st.valid += v;
      }
      Err(e) => {
        // What it wrote of the block goes, and the block is read again.
        let (n, v) = undo_from(&t, h)?;
        let _ = (n, v);
        warn!("d:// index: block {h} failed, reading it again: {e:#}");
        sleep(Duration::from_secs(10)).await;
        continue;
      }
    }
    st.hashes.push_back((h, block.hash.clone()));
    while st.hashes.len() > KEEP_HASHES {
      st.hashes.pop_front();
    }
    st.next_height = h + 1;
    save(&t, &st)?;
    caught_up = false;
    if last_log.elapsed() > Duration::from_secs(60) {
      last_log = Instant::now();
      info!("d:// index: at block {h}, {} records ({} valid)", st.records, st.valid);
    }
  }
}

// ---------------------------------------------------------------------------
// Reading

#[derive(Debug, Clone, Serialize)]
pub struct DfeedStatus {
  pub start_height: u64,
  /// The last block read.
  pub height: u64,
  pub records: u64,
  pub valid: u64,
  pub confirmations: u64,
}

fn trees(config: &Config) -> Result<Trees> {
  Trees::open(&ii::db_of(config)?)
}

pub fn dfeed_status(config: &Config) -> Result<DfeedStatus> {
  let t = trees(config)?;
  let st = load_state(&t.meta)?;
  Ok(DfeedStatus {
    start_height: START,
    height: st.next_height.saturating_sub(1),
    records: st.records,
    valid: st.valid,
    confirmations: dproto::CONFIRMATIONS,
  })
}

/// Records newest first, before `before` (a record's height and position),
/// keeping those `keep` says yes to.
pub fn dfeed_records(config: &Config, before: Option<(u64, u32)>, limit: usize, keep: impl Fn(&DfRecord) -> bool) -> Result<Vec<DfRecord>> {
  let t = trees(config)?;
  let start = match before {
    Some((h, i)) if i > 0 => ii::seq_key(h, i - 1).to_vec(),
    Some((h, _)) if h > 0 => ii::seq_key(h - 1, u32::MAX).to_vec(),
    Some(_) => return Ok(Vec::new()),
    None => vec![0xff; 12],
  };
  let mut out = Vec::new();
  t.rec.for_each_rev_from(start, |_, v| {
    let r: DfRecord = serde_json::from_slice(v).context("decode dfeed record")?;
    if keep(&r) {
      out.push(r);
    }
    Ok(out.len() < limit)
  })?;
  Ok(out)
}

fn by_index_prefix(t: &Trees, prefix: &str) -> Result<Vec<DfRecord>> {
  let mut keys = Vec::new();
  t.idx.for_each_prefix(prefix.as_bytes(), |k, _| {
    if let Some(s) = std::str::from_utf8(k).ok().and_then(|k| k.rsplit('|').next()).and_then(|s| hex::decode(s).ok()) {
      keys.push(s);
    }
    Ok(true)
  })?;
  keys.iter().filter_map(|k| get_rec(t, k).transpose()).collect()
}

/// Everything valid that points at an inscription or an address, oldest
/// first: comments, quotes, edits, likes, branches, tips, reveals, deletes,
/// follows.
pub fn dfeed_pointing_at(config: &Config, target: &str) -> Result<Vec<DfRecord>> {
  by_index_prefix(&trees(config)?, &format!("g|{target}|"))
}

/// Every record an address made or counts for, oldest first.
pub fn dfeed_by_account(config: &Config, address: &str) -> Result<Vec<DfRecord>> {
  by_index_prefix(&trees(config)?, &format!("a|{address}|"))
}

/// The record a transaction holds, valid or not.
pub fn dfeed_by_txid(config: &Config, txid: &str) -> Result<Option<DfRecord>> {
  let t = trees(config)?;
  match t.idx.get(format!("t|{txid}"))? {
    Some(k) => get_rec(&t, &hex::decode(k.as_ref()).context("dfeed index key")?),
    None => Ok(None),
  }
}

/// The valid record an inscription holds.
pub fn dfeed_by_inscription(config: &Config, id: &str) -> Result<Option<DfRecord>> {
  by_inscription(&trees(config)?, id)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::InscriptionContentRecord;

  /// The seven confirmed records of the v1 standard, read from the node's
  /// blocks as the live index reads them. Against the node; skipped by
  /// default: `cargo test -p dogeord-indexer mainnet_test_records -- --ignored`.
  #[tokio::test]
  #[ignore]
  async fn the_mainnet_test_records_index_as_valid() {
    let config = Config::from_env();
    let client = indexer_rpc_client().unwrap();
    let db = store::Db::temporary().unwrap();
    let t = Trees::open(&db).unwrap();
    // (height, inscription reveal txids in it)
    let blocks: [(u64, &[&str]); 6] = [
      (6448293, &["5eedf507d704e35c037060e4ac966262b6eae10ef89b9ce2be11d2ec2697c72e"]),
      (6448355, &[]),
      (6448365, &[]),
      (6448372, &[]),
      (6448381, &["f0e6d3405eee52590c742531839d392e7708359e87ca19b62eeac6ed5f7399fc"]),
      (6448391, &["42cba9e14346a85820d88f7c66e02cd0468b93a7d317706cc91efca37b76336d"]),
    ];
    let mut all = Vec::new();
    for (h, reveals) in blocks {
      let block = crate::repair::fetch_block(client, &config, h).await.unwrap();
      // The main index's view: chain order and the standard body.
      for txid in reveals {
        let i = block.tx.iter().position(|x| x.txid == *txid).unwrap() as u32;
        let pushes = dproto::script_pushes(&script_sig_of(&block.tx[i as usize]).unwrap()).unwrap();
        let id = format!("{txid}i0");
        t.seq.insert(ii::seq_key(h, i), ii::seq_value(&id, ii::K_JSON, 0).unwrap()).unwrap();
        let c = InscriptionContentRecord { content_type: "application/json".into(), body: pushes[4].clone(), delegate: None };
        t.content.insert(id.as_bytes(), bincode::serialize(&c).unwrap()).unwrap();
      }
      index_block(&config, &t, h, &block).await.unwrap();
    }
    t.rec.for_each_prefix(b"", |_, v| {
      all.push(serde_json::from_slice::<DfRecord>(v).unwrap());
      Ok(true)
    })
    .unwrap();
    let got: Vec<(String, bool, Option<String>)> = all.iter().map(|r| (r.kind.clone(), r.valid, r.reason.clone())).collect();
    assert_eq!(
      got,
      ["follow", "post", "like", "branch", "tip", "comment", "quote"].map(|k| (k.to_string(), true, None)).to_vec()
    );
    let post = format!("{}i0", "5eedf507d704e35c037060e4ac966262b6eae10ef89b9ce2be11d2ec2697c72e");
    let pointing = by_index_prefix(&t, &format!("g|{post}|")).unwrap();
    assert_eq!(pointing.iter().map(|r| r.kind.as_str()).collect::<Vec<_>>(), ["like", "branch", "tip", "comment", "quote"]);
    assert!(all.iter().filter(|r| r.inscription_id.is_some()).all(|r| r.split_body));
    // DogeFeed's note of Nov 8, 2026: every record carries its signature, and
    // the comment and quote pay the post's author 0.86 and DogeFeed 0.1 DOGE.
    assert!(all.iter().all(|r| r.registrar.as_deref() == Some("dfreg1")));
    for r in all.iter().filter(|r| matches!(r.kind.as_str(), "comment" | "quote")) {
      assert_eq!(
        (r.recipient.as_deref(), r.recipient_koinu, r.fee_koinu),
        (Some("DSi6So8MHAArNYSgWxhpVrU6PtfHgVa11N"), Some(86_000_000), Some(10_000_000)),
        "{}",
        r.kind
      );
    }
    let follow = &all[0];
    assert_eq!(
      (follow.author.as_str(), follow.target.as_deref(), follow.recipient_koinu, follow.fee_koinu),
      ("DSi6So8MHAArNYSgWxhpVrU6PtfHgVa11N", Some("DBMBjmyKSAKboj5NrXeER2rYWkpxETvUMn"), Some(88_000_000), Some(10_000_000))
    );
  }

  #[test]
  fn records_index_and_undo_cleanly() {
    let db = store::Db::temporary().unwrap();
    let t = Trees::open(&db).unwrap();
    let post_id = format!("{}i0", "ab".repeat(32));
    let post = DfRecord {
      txid: "ab".repeat(32),
      height: 10,
      tx_index: 3,
      kind: "post".into(),
      inscription_id: Some(post_id.clone()),
      author: "DA".into(),
      account: "DA".into(),
      valid: true,
      ..Default::default()
    };
    let like = DfRecord {
      txid: "cd".repeat(32),
      height: 11,
      tx_index: 1,
      kind: "like".into(),
      author: "DK".into(),
      account: "DB".into(),
      target: Some(post_id.clone()),
      valid: true,
      ..Default::default()
    };
    let link = DfRecord {
      txid: "ef".repeat(32),
      height: 11,
      tx_index: 0,
      kind: "keylink".into(),
      author: "DB".into(),
      account: "DB".into(),
      target: Some("DK".into()),
      ops: vec!["like".into()],
      valid: true,
      ..Default::default()
    };
    for r in [post, link, like] {
      let mut b = Batch::default();
      apply_links(&t, &mut b, &r).unwrap();
      put(&t, &mut b, r).unwrap();
      b.commit(&t.meta).unwrap();
    }
    assert_eq!(by_inscription(&t, &post_id).unwrap().unwrap().kind, "post");
    assert_eq!(post_candidates(&t, &dproto::post_target(&post_id).unwrap()).len(), 1);
    assert_eq!(by_index_prefix(&t, &format!("g|{post_id}|")).unwrap().len(), 1);
    assert_eq!(by_index_prefix(&t, "a|DB|").unwrap().len(), 2, "the link and the like counted for the account");
    assert_eq!(by_index_prefix(&t, "a|DK|").unwrap().len(), 1, "and the like under the key that paid");
    assert_eq!(account_for(&t, "DK", "like", 11).unwrap(), "DB");
    assert_eq!(account_for(&t, "DK", "follow", 11).unwrap(), "DK", "an op the link does not allow");
    assert_eq!(account_for(&t, "DK", "like", 10).unwrap(), "DK", "before the link");
    assert_eq!(linked_keys(&t, "DB"), vec!["DK".to_string()]);

    assert_eq!(undo_from(&t, 11).unwrap(), (2, 2));
    assert!(by_index_prefix(&t, &format!("g|{post_id}|")).unwrap().is_empty());
    assert!(link_of(&t, "DK").unwrap().is_none());
    assert!(by_index_prefix(&t, "a|DB|").unwrap().is_empty());
    assert_eq!(by_inscription(&t, &post_id).unwrap().unwrap().height, 10, "the earlier block stays");
    let mut left = 0;
    t.idx.for_each_prefix(b"", |_, _| {
      left += 1;
      Ok(true)
    }).unwrap();
    assert_eq!(left, 4, "the post's own entries: t, a, i, p");
  }
}
