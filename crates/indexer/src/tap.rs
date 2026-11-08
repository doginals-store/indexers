//! TAP tokens on Dogecoin, copied from Trac Systems' own index.
//!
//! TAP is Trac's protocol, and its Dogecoin state is published by Trac's
//! indexers over the Trac network. A local tap-reader (Trac's program,
//! `projects\tap-reader`, on the Dogecoin channel) serves that state over HTTP
//! on this computer. This module copies it into DogeOrd's store and keeps it
//! current, so the explorer shows exactly what the protocol's own index says:
//! every deployment, every holder's balance, and the activity lists
//! (transfers, sends, trades, internal operations, authorities, redeems, DMT
//! elements and mints).
//!
//! Every list on the reader only grows, in chain order. Each pass reads what
//! is new, and the last few records again in case a reorg changed them; a
//! list that got shorter has its extra records removed. Holders of a token are
//! read again whenever new activity names it, and all of them once an hour.
//! The 3.2M historical mints are copied in the background, newest kept current
//! first.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::time::{Duration, Instant};

use anyhow::{Context, Result, anyhow, bail};
use dogeord_core::{Config, setting};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use tracing::{info, warn};

use crate::insc_index as ii;
use crate::store::{self, Tree};

const STATE_KEY: &[u8] = b"tap_sync_v1";
/// How far the mint history has been copied from the front.
const BACKFILL_KEY: &[u8] = b"tap_mint_backfill_v1";
/// The pass and the mint history write the same counters; one at a time.
static WRITES: std::sync::Mutex<()> = std::sync::Mutex::new(());
/// Records per request; the reader's own maximum.
const PAGE: u64 = 500;
/// Records at the end of each list read again on every pass.
const TAIL: u64 = 20;
/// Requests to the reader at once.
const PARALLEL: usize = 8;
/// Mint pages copied per pass while the history is still coming in.
const MINT_BACKFILL_PAGES: u64 = 16;
const HOLDERS_EVERY: Duration = Duration::from_secs(3600);

/// The activity lists copied, as (kind, length route, list route).
const LISTS: &[(&str, &str, &str)] = &[
  ("transfer", "getTransferListLength", "getTransferList"),
  ("sent", "getSentListLength", "getSentList"),
  ("trade", "getTradesListLength", "getTradesList"),
  ("fill", "getTradesFilledListLength", "getTradesFilledList"),
  ("internal", "getAccumulatorListLength", "getAccumulatorList"),
  ("auth", "getAuthListLength", "getAuthList"),
  ("privilege", "getPrivilegeAuthListLength", "getPrivilegeAuthList"),
  ("redeem", "getRedeemListLength", "getRedeemList"),
  ("element", "getDmtElementsListLength", "getDmtElementsList"),
];
/// Every kind of activity record kept, deployments and mints included.
pub const TAP_KINDS: &[&str] = &["deploy", "mint", "transfer", "sent", "trade", "fill", "internal", "auth", "privilege", "redeem", "element"];

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct TapState {
  /// The reader's block height at the last pass.
  block: u64,
  /// Records copied of each list, by kind (deploy and the lists above).
  lens: HashMap<String, u64>,
  /// Mints: copied from the front up to `mint_low`, and kept current from
  /// `mint_high` on. The history in between is filled in the background.
  mint_low: u64,
  mint_high: u64,
  mint_started: bool,
  /// Where the live copy began; the history is complete once `mint_low`
  /// reaches it.
  #[serde(default)]
  mint_live_from: u64,
  /// Whether every token's holders have been read at least once.
  holders_done: bool,
  /// Unix seconds of the last pass and the last full holder refresh.
  synced_at: u64,
  holders_at: u64,
}

struct Trees {
  meta: Tree,
  deploy: Tree,
  holders: Tree,
  account: Tree,
  event: Tree,
  tick_event: Tree,
  addr_event: Tree,
  count: Tree,
}

impl Trees {
  fn open(db: &store::Db) -> Result<Self> {
    Ok(Self {
      meta: db.open_tree("meta")?,
      deploy: db.open_tree("tap_deploy")?,
      holders: db.open_tree("tap_holders")?,
      account: db.open_tree("tap_account")?,
      event: db.open_tree("tap_event")?,
      tick_event: db.open_tree("tap_tick_event")?,
      addr_event: db.open_tree("tap_addr_event")?,
      count: db.open_tree("tap_count")?,
    })
  }
}

/// A token's holder, as Trac's index states it. Amounts are whole numbers in
/// the token's smallest unit (see the deployment's `dec`).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TapHolder {
  pub address: String,
  pub balance: String,
  pub transferable: Option<String>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct TokenStats {
  holders: u64,
  /// What can still be minted, from the reader.
  left: Option<String>,
  refreshed_block: u64,
}

fn load_state(meta: &Tree) -> Result<TapState> {
  Ok(match meta.get(STATE_KEY)? {
    Some(raw) => serde_json::from_slice(raw.as_ref()).context("decode tap state")?,
    None => TapState::default(),
  })
}

fn save_state(meta: &Tree, st: &TapState) -> Result<()> {
  meta.insert(STATE_KEY, serde_json::to_vec(st)?)
}

fn now() -> u64 {
  std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_secs()).unwrap_or(0)
}

// ---------- the reader ----------

#[derive(Clone)]
struct Reader {
  base: reqwest::Url,
  client: reqwest::Client,
}

impl Reader {
  fn new() -> Result<Self> {
    let base = setting("TAP_READER_URL").unwrap_or_else(|| "http://localhost:5099".to_string());
    Ok(Self {
      base: reqwest::Url::parse(&base).with_context(|| format!("bad TAP reader url {base}"))?,
      // The reader fetches from the Trac network on demand; a first read of a
      // page can take most of a minute.
      client: reqwest::Client::builder().timeout(Duration::from_secs(600)).build()?,
    })
  }

  /// GET /route/segment..., with segments percent-encoded, and its `result`.
  async fn get(&self, parts: &[&str], query: &[(&str, String)]) -> Result<Value> {
    // A segment made only of dots (the ticker ".") is a "this folder" or
    // "parent folder" step to every URL library, even percent-encoded, so it
    // would reach the wrong route. Those go out with the path exactly as
    // written.
    if parts.iter().any(|p| is_dot_segment(p)) {
      return self.get_raw(parts, query).await;
    }
    let mut url = self.base.clone();
    {
      let mut segs = url.path_segments_mut().map_err(|_| anyhow!("TAP reader url cannot take a path"))?;
      segs.clear();
      for p in parts {
        segs.push(p);
      }
    }
    if !query.is_empty() {
      url.query_pairs_mut().extend_pairs(query.iter().map(|(k, v)| (*k, v.as_str())));
    }
    let resp = self.client.get(url.clone()).send().await.with_context(|| format!("TAP reader {}", url.path()))?;
    let status = resp.status();
    let body: Value = resp.json().await.with_context(|| format!("TAP reader {}: not JSON", url.path()))?;
    if !status.is_success() {
      bail!("TAP reader {} answered {status}: {}", url.path(), body.get("message").and_then(Value::as_str).unwrap_or(""));
    }
    body.get("result").cloned().ok_or_else(|| anyhow!("TAP reader {}: no result", url.path()))
  }

  /// The same GET over a plain HTTP/1.1 connection, the path sent verbatim.
  async fn get_raw(&self, parts: &[&str], query: &[(&str, String)]) -> Result<Value> {
    use tokio::io::{AsyncReadExt, AsyncWriteExt};
    let host = self.base.host_str().ok_or_else(|| anyhow!("TAP reader url has no host"))?.to_string();
    let port = self.base.port_or_known_default().unwrap_or(80);
    if self.base.scheme() != "http" {
      bail!("TAP reader: a ticker made of dots needs a plain http reader url");
    }
    let mut path = String::new();
    for p in parts {
      path.push('/');
      path.push_str(&encode_segment(p));
    }
    if !query.is_empty() {
      path.push('?');
      path.push_str(&query.iter().map(|(k, v)| format!("{}={}", encode_segment(k), encode_segment(v))).collect::<Vec<_>>().join("&"));
    }
    let fut = async {
      let mut s = tokio::net::TcpStream::connect((host.as_str(), port)).await?;
      let req = format!("GET {path} HTTP/1.1\r\nHost: {host}:{port}\r\nAccept: application/json\r\nAccept-Encoding: identity\r\nConnection: close\r\n\r\n");
      s.write_all(req.as_bytes()).await?;
      let mut raw = Vec::new();
      s.read_to_end(&mut raw).await?;
      Ok::<_, anyhow::Error>(raw)
    };
    let raw = tokio::time::timeout(Duration::from_secs(600), fut).await.map_err(|_| anyhow!("TAP reader {path}: timed out"))??;
    let split = raw.windows(4).position(|w| w == b"\r\n\r\n").ok_or_else(|| anyhow!("TAP reader {path}: bad response"))?;
    let head = String::from_utf8_lossy(&raw[..split]).to_ascii_lowercase();
    let mut body = raw[split + 4..].to_vec();
    if head.lines().any(|l| l.starts_with("transfer-encoding:") && l.contains("chunked")) {
      body = dechunk(&body)?;
    }
    let status_ok = head.lines().next().is_some_and(|l| l.split_whitespace().nth(1).is_some_and(|c| c.starts_with('2')));
    let v: Value = serde_json::from_slice(&body).with_context(|| format!("TAP reader {path}: not JSON"))?;
    if !status_ok {
      bail!("TAP reader {path}: {}", v.get("message").and_then(Value::as_str).unwrap_or("error"));
    }
    v.get("result").cloned().ok_or_else(|| anyhow!("TAP reader {path}: no result"))
  }

  async fn length(&self, route: &str) -> Result<u64> {
    as_u64(&self.get(&[route], &[]).await?).ok_or_else(|| anyhow!("TAP reader {route}: not a length"))
  }

  /// Records [from, to) of a list, in pages fetched in parallel. Ordered.
  async fn range(&self, route: &str, extra: &[&str], from: u64, to: u64) -> Result<Vec<Value>> {
    let mut starts: Vec<u64> = (from..to).step_by(PAGE as usize).collect();
    let mut out: Vec<(u64, Vec<Value>)> = Vec::new();
    while !starts.is_empty() {
      let batch: Vec<u64> = starts.drain(..starts.len().min(PARALLEL)).collect();
      let mut set = tokio::task::JoinSet::new();
      for start in batch {
        let me = self.clone();
        let route = route.to_string();
        let extra: Vec<String> = extra.iter().map(|s| s.to_string()).collect();
        let max = PAGE.min(to - start);
        set.spawn(async move {
          let parts: Vec<&str> = std::iter::once(route.as_str()).chain(extra.iter().map(String::as_str)).collect();
          let v = me.get(&parts, &[("offset", start.to_string()), ("max", max.to_string())]).await?;
          let arr = match v {
            Value::Array(a) => a,
            Value::Null => Vec::new(),
            other => bail!("TAP reader {route}: not a list: {}", truncate(&other.to_string(), 120)),
          };
          Ok::<_, anyhow::Error>((start, arr))
        });
      }
      while let Some(r) = set.join_next().await {
        out.push(r.map_err(|e| anyhow!("TAP reader task: {e}"))??);
      }
    }
    out.sort_by_key(|(s, _)| *s);
    let mut all = Vec::new();
    for (start, page) in out {
      let want = PAGE.min(to - start) as usize;
      if page.len() < want && start + (page.len() as u64) < to {
        bail!("TAP reader {route}: short page at {start} ({} of {want})", page.len());
      }
      all.extend(page);
    }
    Ok(all)
  }
}

fn is_dot_segment(s: &str) -> bool {
  !s.is_empty() && s.bytes().all(|b| b == b'.')
}

/// Percent-encodes everything but letters, digits and `-_~`, dots included,
/// so nothing in the result reads as a path step.
fn encode_segment(s: &str) -> String {
  let mut out = String::with_capacity(s.len() * 3);
  for b in s.bytes() {
    if b.is_ascii_alphanumeric() || b"-_~".contains(&b) {
      out.push(b as char);
    } else {
      out.push_str(&format!("%{b:02X}"));
    }
  }
  out
}

/// Decodes an HTTP/1.1 chunked body.
fn dechunk(mut b: &[u8]) -> Result<Vec<u8>> {
  let mut out = Vec::new();
  loop {
    let eol = b.windows(2).position(|w| w == b"\r\n").ok_or_else(|| anyhow!("bad chunked body"))?;
    let size_str = String::from_utf8_lossy(&b[..eol]);
    let size = usize::from_str_radix(size_str.split(';').next().unwrap_or("").trim(), 16).context("bad chunk size")?;
    b = &b[eol + 2..];
    if size == 0 {
      return Ok(out);
    }
    if b.len() < size + 2 {
      bail!("chunked body cut short");
    }
    out.extend_from_slice(&b[..size]);
    b = &b[size + 2..];
  }
}

fn as_u64(v: &Value) -> Option<u64> {
  v.as_u64().or_else(|| v.as_str().and_then(|s| s.parse().ok()))
}

fn truncate(s: &str, n: usize) -> String {
  s.chars().take(n).collect()
}

// ---------- keys ----------

fn pos_key(prefix: &[u8], pos: u64) -> Vec<u8> {
  let mut k = prefix.to_vec();
  k.extend_from_slice(&pos.to_be_bytes());
  k
}

fn event_key(kind: &str, pos: u64) -> Vec<u8> {
  pos_key(format!("{kind}\0").as_bytes(), pos)
}

fn tick_prefix(tick: &str, kind: &str) -> Vec<u8> {
  format!("{tick}\0{kind}\0").into_bytes()
}

fn addr_prefix(addr: &str, kind: &str) -> Vec<u8> {
  format!("{addr}\0{kind}\0").into_bytes()
}

fn tick_count_key(tick: &str, kind: &str) -> Vec<u8> {
  format!("t\0{tick}\0{kind}").into_bytes()
}

fn addr_count_key(addr: &str, kind: &str) -> Vec<u8> {
  format!("a\0{addr}\0{kind}").into_bytes()
}

fn account_key(addr: &str, tick: &str) -> Vec<u8> {
  format!("{addr}\0{tick}").into_bytes()
}

/// A ticker as Trac keys it: lowercased. Tickers are short user text; one with
/// a NUL in it (which would break these keys) is left out of the indexes.
pub fn tap_tick_key(tick: &str) -> Option<String> {
  let t = tick.to_lowercase();
  (!t.is_empty() && !t.contains('\0') && t.chars().count() <= 64).then_some(t)
}

fn get_u64(tree: &Tree, key: &[u8]) -> Result<u64> {
  Ok(tree.get(key)?.map(|v| crate::decode_u64(v.as_ref())).transpose()?.unwrap_or(0))
}

fn add_u64(tree: &Tree, key: &[u8], delta: i64) -> Result<()> {
  let v = get_u64(tree, key)?;
  let n = if delta >= 0 { v.saturating_add(delta as u64) } else { v.saturating_sub(delta.unsigned_abs()) };
  tree.insert(key, crate::encode_u64(n))
}

/// Tickers and addresses a record names, for its indexes.
fn names_of(v: &Value) -> (BTreeSet<String>, BTreeSet<String>) {
  let mut ticks = BTreeSet::new();
  let mut addrs = BTreeSet::new();
  let mut tick = |s: Option<&str>| {
    if let Some(t) = s.and_then(tap_tick_key) {
      ticks.insert(t);
    }
  };
  for k in ["tick", "atick", "stick"] {
    tick(v.get(k).and_then(Value::as_str));
  }
  if let Some(arr) = v.get("auth").and_then(Value::as_array) {
    for t in arr {
      tick(t.as_str());
    }
  }
  if let Some(items) = v.pointer("/rdm/items").and_then(Value::as_array) {
    for it in items {
      tick(it.get("tick").and_then(Value::as_str));
      if let Some(a) = it.get("address").and_then(Value::as_str) {
        addrs.insert(a.to_string());
      }
    }
  }
  for k in ["addr", "taddr", "saddr", "iaddr", "fee_rcv"] {
    if let Some(a) = v.get(k).and_then(Value::as_str).filter(|a| !a.is_empty() && !a.contains('\0')) {
      addrs.insert(a.to_string());
    }
  }
  (ticks, addrs)
}

// ---------- writing ----------

/// Puts record `pos` of a list, replacing (and un-indexing) what was there.
fn put_event(t: &Trees, kind: &str, pos: u64, v: &Value) -> Result<(BTreeSet<String>, bool)> {
  let key = event_key(kind, pos);
  let raw = serde_json::to_vec(v)?;
  let mut touched = BTreeSet::new();
  if let Some(old) = t.event.get(&key)? {
    if old.as_ref() == raw.as_slice() {
      return Ok((touched, false));
    }
    if let Ok(oldv) = serde_json::from_slice::<Value>(old.as_ref()) {
      touched.extend(unindex(t, kind, pos, &oldv)?);
    }
  }
  t.event.insert(&key, &raw)?;
  let (ticks, addrs) = names_of(v);
  for tk in &ticks {
    t.tick_event.insert(pos_key(&tick_prefix(tk, kind), pos), [])?;
    add_u64(&t.count, &tick_count_key(tk, kind), 1)?;
  }
  for a in &addrs {
    t.addr_event.insert(pos_key(&addr_prefix(a, kind), pos), [])?;
    add_u64(&t.count, &addr_count_key(a, kind), 1)?;
  }
  touched.extend(ticks);
  Ok((touched, true))
}

fn unindex(t: &Trees, kind: &str, pos: u64, v: &Value) -> Result<BTreeSet<String>> {
  let (ticks, addrs) = names_of(v);
  for tk in &ticks {
    t.tick_event.remove(pos_key(&tick_prefix(tk, kind), pos))?;
    add_u64(&t.count, &tick_count_key(tk, kind), -1)?;
  }
  for a in &addrs {
    t.addr_event.remove(pos_key(&addr_prefix(a, kind), pos))?;
    add_u64(&t.count, &addr_count_key(a, kind), -1)?;
  }
  Ok(ticks)
}

/// Removes records [from, to) of a list: the list got shorter (a reorg).
fn drop_events(t: &Trees, kind: &str, from: u64, to: u64) -> Result<BTreeSet<String>> {
  let mut touched = BTreeSet::new();
  for pos in from..to {
    let key = event_key(kind, pos);
    if let Some(old) = t.event.get(&key)? {
      if let Ok(v) = serde_json::from_slice::<Value>(old.as_ref()) {
        touched.extend(unindex(t, kind, pos, &v)?);
      }
      t.event.remove(&key)?;
    }
  }
  Ok(touched)
}

/// Copies records [from, to) of a list. Returns the tokens they name.
async fn copy_range(r: &Reader, t: &Trees, kind: &str, route: &str, from: u64, to: u64) -> Result<BTreeSet<String>> {
  let mut touched = BTreeSet::new();
  if from >= to {
    return Ok(touched);
  }
  let records = r.range(route, &[], from, to).await?;
  let _w = WRITES.lock().unwrap_or_else(|e| e.into_inner());
  for (i, v) in records.iter().enumerate() {
    let pos = from + i as u64;
    let (ticks, _) = put_event(t, kind, pos, v)?;
    touched.extend(ticks);
    if kind == "deploy" {
      if let Some(tk) = v.get("tick").and_then(Value::as_str).and_then(tap_tick_key) {
        t.deploy.insert(tk.as_bytes(), serde_json::to_vec(v)?)?;
      }
    }
  }
  Ok(touched)
}

/// One list: what is new, the tail again, and a shrink if it got shorter.
async fn sync_list(r: &Reader, t: &Trees, st: &mut TapState, kind: &str, len_route: &str, route: &str) -> Result<BTreeSet<String>> {
  let len = r.length(len_route).await?;
  let have = st.lens.get(kind).copied().unwrap_or(0);
  let mut touched = BTreeSet::new();
  if len < have {
    warn!("tap: {kind} list shrank from {have} to {len} (reorg); dropping the extra records");
    touched.extend(drop_events(t, kind, len, have)?);
  }
  let from = have.min(len).saturating_sub(TAIL);
  touched.extend(copy_range(r, t, kind, route, from, len).await?);
  st.lens.insert(kind.to_string(), len);
  Ok(touched)
}

/// Mints: the end kept current, the history filled in from the front.
async fn sync_mints(r: &Reader, t: &Trees, st: &mut TapState) -> Result<BTreeSet<String>> {
  let len = r.length("getMintListLength").await?;
  let mut touched = BTreeSet::new();
  if !st.mint_started {
    st.mint_started = true;
    // The live copy starts a little back, so the first pass reads real records.
    st.mint_live_from = len.saturating_sub(TAIL);
    st.mint_high = st.mint_live_from;
  }
  if len < st.mint_high {
    warn!("tap: mint list shrank from {} to {len} (reorg)", st.mint_high);
    touched.extend(drop_events(t, "mint", len, st.mint_high)?);
    st.mint_high = len;
    st.mint_live_from = st.mint_live_from.min(len);
  }
  let from = st.mint_high.saturating_sub(TAIL);
  touched.extend(copy_range(r, t, "mint", "getMintList", from, len).await?);
  st.mint_high = len;
  st.lens.insert("mint".to_string(), len);
  Ok(touched)
}

/// The mint history before the live copy began, from the front, in its own
/// task: a first read of a page can take minutes, and nothing else should
/// wait for that. Its progress is kept apart from the main state so the two
/// tasks never overwrite each other's.
async fn run_mint_backfill(r: Reader, t: Trees) -> Result<()> {
  loop {
    let st = load_state(&t.meta)?;
    if !st.mint_started {
      tokio::time::sleep(Duration::from_secs(30)).await;
      continue;
    }
    let low = get_u64(&t.meta, BACKFILL_KEY)?;
    if low >= st.mint_live_from {
      info!("tap: mint history copied ({} mints before the live copy)", st.mint_live_from);
      return Ok(());
    }
    let to = (low + MINT_BACKFILL_PAGES * PAGE).min(st.mint_live_from);
    match r.range("getMintList", &[], low, to).await {
      Ok(records) => {
        let _w = WRITES.lock().unwrap_or_else(|e| e.into_inner());
        for (i, v) in records.iter().enumerate() {
          put_event(&t, "mint", low + i as u64, v)?;
        }
        t.meta.insert(BACKFILL_KEY, crate::encode_u64(to))?;
      }
      Err(e) => {
        warn!("tap: mint history at {low}: {e:#}; retrying in a minute");
        tokio::time::sleep(Duration::from_secs(60)).await;
      }
    }
  }
}

/// Tokens whose holders are read at once. A first read of each comes from the
/// Trac network and can take most of a minute, so one at a time is far too
/// slow for 390 tokens.
const TOKENS_AT_ONCE: usize = 16;

/// A token's holders and what is left to mint, as read from the reader.
struct TokenData {
  holders: Vec<TapHolder>,
  left: Option<String>,
}

/// Reads a token's holders and what is left to mint, and updates the
/// per-address index to match.
#[cfg(test)]
async fn refresh_token(r: &Reader, t: &Trees, tick: &str, block: u64) -> Result<()> {
  let data = fetch_token(r, tick).await?;
  write_token(t, tick, data, block)
}

/// Reads many tokens, `TOKENS_AT_ONCE` at a time, writing each as it comes.
async fn refresh_tokens(r: &Reader, t: &Trees, ticks: &[String], block: u64) {
  for chunk in ticks.chunks(TOKENS_AT_ONCE) {
    let mut set = tokio::task::JoinSet::new();
    for tk in chunk {
      let (r, tk) = (r.clone(), tk.clone());
      set.spawn(async move {
        let res = fetch_token(&r, &tk).await;
        (tk, res)
      });
    }
    while let Some(done) = set.join_next().await {
      match done {
        Ok((tk, Ok(data))) => {
          if let Err(e) = write_token(t, &tk, data, block) {
            warn!("tap: holders of {tk}: {e:#}");
          }
        }
        Ok((tk, Err(e))) => warn!("tap: holders of {tk}: {e:#}"),
        Err(e) => warn!("tap: holder task: {e}"),
      }
    }
  }
}

async fn fetch_token(r: &Reader, tick: &str) -> Result<TokenData> {
  let n = r.length_of("getHoldersLength", tick).await?;
  let rows = if n == 0 { Vec::new() } else { r.range("getHolders", &[tick], 0, n).await? };
  let mut holders: Vec<TapHolder> = Vec::with_capacity(rows.len());
  for row in rows {
    let Some(address) = row.get("address").and_then(Value::as_str) else { continue };
    let str_of = |v: Option<&Value>| v.and_then(|v| v.as_str().map(str::to_string).or_else(|| v.as_u64().map(|n| n.to_string())));
    holders.push(TapHolder {
      address: address.to_string(),
      balance: str_of(row.get("balance")).unwrap_or_else(|| "0".to_string()),
      transferable: str_of(row.get("transferable")),
    });
  }
  let left = match r.get(&["getMintTokensLeft", tick], &[]).await? {
    Value::String(s) => Some(s),
    Value::Number(n) => Some(n.to_string()),
    _ => None,
  };
  Ok(TokenData { holders, left })
}

fn write_token(t: &Trees, tick: &str, data: TokenData, block: u64) -> Result<()> {
  let TokenData { holders, left } = data;
  let _w = WRITES.lock().unwrap_or_else(|e| e.into_inner());
  // Addresses that no longer hold it lose their row.
  let old: Vec<TapHolder> = match t.holders.get(tick.as_bytes())? {
    Some(raw) => serde_json::from_slice(raw.as_ref()).unwrap_or_default(),
    None => Vec::new(),
  };
  let now_held: HashSet<&str> = holders.iter().map(|h| h.address.as_str()).collect();
  for h in &old {
    if !now_held.contains(h.address.as_str()) {
      t.account.remove(account_key(&h.address, tick))?;
    }
  }
  for h in &holders {
    t.account.insert(account_key(&h.address, tick), serde_json::to_vec(h)?)?;
  }
  t.holders.insert(tick.as_bytes(), serde_json::to_vec(&holders)?)?;
  let stats = TokenStats { holders: holders.len() as u64, left, refreshed_block: block };
  t.count.insert(format!("s\0{tick}").as_bytes(), serde_json::to_vec(&stats)?)?;
  Ok(())
}

impl Reader {
  async fn length_of(&self, route: &str, arg: &str) -> Result<u64> {
    as_u64(&self.get(&[route, arg], &[]).await?).ok_or_else(|| anyhow!("TAP reader {route}/{arg}: not a length"))
  }
}

/// One pass over everything but the mint history.
async fn sync_once(r: &Reader, t: &Trees, st: &mut TapState) -> Result<()> {
  let block = as_u64(&r.get(&["getCurrentBlock"], &[]).await?).ok_or_else(|| anyhow!("TAP reader: no current block"))?;
  let mut touched = BTreeSet::new();
  touched.extend(sync_list(r, t, st, "deploy", "getDeploymentsLength", "getDeployments").await?);
  save_state(&t.meta, st)?;
  for (kind, len_route, route) in LISTS {
    touched.extend(sync_list(r, t, st, kind, len_route, route).await?);
    save_state(&t.meta, st)?;
  }
  touched.extend(sync_mints(r, t, st).await?);
  save_state(&t.meta, st)?;

  // Holders: everything the first time and hourly, otherwise what moved.
  let full = !st.holders_done || now().saturating_sub(st.holders_at) >= HOLDERS_EVERY.as_secs();
  let ticks: Vec<String> = if full {
    let mut all = Vec::new();
    t.deploy.for_each_prefix(b"", |k, _| {
      all.push(String::from_utf8_lossy(k).into_owned());
      Ok(true)
    })?;
    all
  } else {
    touched.into_iter().filter(|tk| t.deploy.get(tk.as_bytes()).ok().flatten().is_some()).collect()
  };
  let started = Instant::now();
  refresh_tokens(r, t, &ticks, block).await;
  if full {
    st.holders_done = true;
    st.holders_at = now();
    info!("tap: holders of {} tokens read in {:.0?}", ticks.len(), started.elapsed());
  }
  st.block = block;
  st.synced_at = now();
  save_state(&t.meta, st)?;
  Ok(())
}

/// Keeps the TAP copy current, forever. Waits and retries while the reader is
/// not running.
pub async fn run_tap_sync(config: Config) -> Result<()> {
  let r = Reader::new()?;
  let db = ii::db_of(&config)?;
  let t = Trees::open(&db)?;
  let mut st = load_state(&t.meta)?;
  // The mint history copies alongside, at its own pace.
  let (r2, db2) = (r.clone(), db.clone());
  tokio::spawn(async move {
    loop {
      let res = match Trees::open(&db2) {
        Ok(t2) => run_mint_backfill(r2.clone(), t2).await,
        Err(e) => Err(e),
      };
      match res {
        Ok(()) => return,
        Err(e) => {
          warn!("tap: mint history stopped ({e:#}); restarting in a minute");
          tokio::time::sleep(Duration::from_secs(60)).await;
        }
      }
    }
  });
  let mut waiting_logged = false;
  loop {
    match sync_once(&r, &t, &mut st).await {
      Ok(()) => {
        waiting_logged = false;
        tokio::time::sleep(Duration::from_secs(30)).await;
      }
      Err(e) => {
        if !waiting_logged {
          warn!("tap: cannot read the TAP reader yet ({e:#}); retrying every minute");
          waiting_logged = true;
        }
        tokio::time::sleep(Duration::from_secs(60)).await;
      }
    }
  }
}

// ---------- reading ----------

#[derive(Debug, Clone, Serialize)]
pub struct TapStatus {
  /// The block Trac's index had reached at the last pass, and when that was.
  pub block: u64,
  pub synced_at: u64,
  pub tokens: u64,
  /// Records copied of each kind.
  pub counts: HashMap<String, u64>,
  /// Mint history copied so far, of the total.
  pub mints_copied: u64,
  pub mints_total: u64,
  pub holders_ready: bool,
}

pub fn tap_status(config: &Config) -> Result<TapStatus> {
  let t = Trees::open(&ii::db_of(config)?)?;
  let st = load_state(&t.meta)?;
  let mut counts = st.lens.clone();
  let mint_total = st.lens.get("mint").copied().unwrap_or(0);
  // The history from the front, plus everything since the live copy began.
  let low = get_u64(&t.meta, BACKFILL_KEY)?.min(st.mint_live_from);
  let copied = low + mint_total.saturating_sub(st.mint_live_from);
  counts.insert("mint".to_string(), mint_total);
  Ok(TapStatus {
    block: st.block,
    synced_at: st.synced_at,
    tokens: st.lens.get("deploy").copied().unwrap_or(0),
    counts,
    mints_copied: copied.min(mint_total),
    mints_total: mint_total,
    holders_ready: st.holders_done,
  })
}

/// A token: its deployment as Trac records it, plus holders and supply.
#[derive(Debug, Clone, Serialize)]
pub struct TapToken {
  pub tick: String,
  pub deployment: Value,
  pub holders: u64,
  /// What can still be minted, and so what has been (max minus left).
  pub left: Option<String>,
  pub minted: Option<String>,
  pub counts: HashMap<String, u64>,
}

fn minted(dep: &Value, left: Option<&str>) -> Option<String> {
  let max: u128 = dep.get("max").and_then(Value::as_str)?.parse().ok()?;
  let left: u128 = left?.parse().ok()?;
  Some(max.saturating_sub(left).to_string())
}

fn token_of(t: &Trees, tick: &str, dep: Value) -> Result<TapToken> {
  let stats: TokenStats = match t.count.get(format!("s\0{tick}").as_bytes())? {
    Some(raw) => serde_json::from_slice(raw.as_ref()).unwrap_or_default(),
    None => TokenStats::default(),
  };
  let mut counts = HashMap::new();
  for k in TAP_KINDS {
    let n = get_u64(&t.count, &tick_count_key(tick, k))?;
    if n > 0 {
      counts.insert(k.to_string(), n);
    }
  }
  Ok(TapToken {
    tick: tick.to_string(),
    minted: minted(&dep, stats.left.as_deref()),
    deployment: dep,
    holders: stats.holders,
    left: stats.left,
    counts,
  })
}

/// Every token, in deployment order.
pub fn tap_tokens(config: &Config) -> Result<Vec<TapToken>> {
  let t = Trees::open(&ii::db_of(config)?)?;
  let mut out = Vec::new();
  t.deploy.for_each_prefix(b"", |k, v| {
    let tick = String::from_utf8_lossy(k).into_owned();
    if let Ok(dep) = serde_json::from_slice::<Value>(v) {
      out.push((tick, dep));
    }
    Ok(true)
  })?;
  let mut tokens = out.into_iter().map(|(tick, dep)| token_of(&t, &tick, dep)).collect::<Result<Vec<_>>>()?;
  tokens.sort_by_key(|tk| tk.deployment.get("blck").and_then(Value::as_u64).unwrap_or(u64::MAX));
  Ok(tokens)
}

pub fn tap_token(config: &Config, tick: &str) -> Result<Option<TapToken>> {
  let Some(tick) = tap_tick_key(tick) else { return Ok(None) };
  let t = Trees::open(&ii::db_of(config)?)?;
  match t.deploy.get(tick.as_bytes())? {
    Some(raw) => Ok(Some(token_of(&t, &tick, serde_json::from_slice(raw.as_ref())?)?)),
    None => Ok(None),
  }
}

/// A page of a token's holders, largest first, and how many there are.
pub fn tap_holders(config: &Config, tick: &str, offset: usize, limit: usize) -> Result<(Vec<TapHolder>, usize)> {
  let Some(tick) = tap_tick_key(tick) else { return Ok((Vec::new(), 0)) };
  let t = Trees::open(&ii::db_of(config)?)?;
  let mut all: Vec<TapHolder> = match t.holders.get(tick.as_bytes())? {
    Some(raw) => serde_json::from_slice(raw.as_ref())?,
    None => Vec::new(),
  };
  // Largest first, by the whole-number balance; address breaks ties.
  all.sort_by(|a, b| {
    let (x, y) = (a.balance.parse::<u128>().unwrap_or(0), b.balance.parse::<u128>().unwrap_or(0));
    y.cmp(&x).then_with(|| a.address.cmp(&b.address))
  });
  let total = all.len();
  Ok((all.into_iter().skip(offset).take(limit).collect(), total))
}

/// An address's tokens with their balances.
pub fn tap_account(config: &Config, address: &str) -> Result<Vec<(String, TapHolder)>> {
  if address.is_empty() || address.contains('\0') {
    return Ok(Vec::new());
  }
  let t = Trees::open(&ii::db_of(config)?)?;
  let prefix = format!("{address}\0");
  let mut out = Vec::new();
  t.account.for_each_prefix(prefix.as_bytes(), |k, v| {
    let tick = String::from_utf8_lossy(&k[prefix.len()..]).into_owned();
    if let Ok(h) = serde_json::from_slice::<TapHolder>(v) {
      out.push((tick, h));
    }
    Ok(true)
  })?;
  Ok(out)
}

/// Whose activity to list.
pub enum TapScope<'a> {
  All,
  Token(&'a str),
  Address(&'a str),
}

/// A page of one kind of activity, newest first, and how many there are.
pub fn tap_activity(config: &Config, kind: &str, scope: TapScope, offset: usize, limit: usize) -> Result<(Vec<Value>, u64)> {
  if !TAP_KINDS.contains(&kind) {
    bail!("unknown activity kind {kind}");
  }
  let t = Trees::open(&ii::db_of(config)?)?;
  let mut positions: Vec<u64> = Vec::new();
  let (index, prefix, total) = match scope {
    TapScope::All => {
      let st = load_state(&t.meta)?;
      let total = if kind == "mint" { st.lens.get("mint").copied().unwrap_or(0) } else { st.lens.get(kind).copied().unwrap_or(0) };
      (&t.event, format!("{kind}\0").into_bytes(), total)
    }
    TapScope::Token(tick) => {
      let Some(tick) = tap_tick_key(tick) else { return Ok((Vec::new(), 0)) };
      let total = get_u64(&t.count, &tick_count_key(&tick, kind))?;
      (&t.tick_event, tick_prefix(&tick, kind), total)
    }
    TapScope::Address(addr) => {
      if addr.is_empty() || addr.contains('\0') {
        return Ok((Vec::new(), 0));
      }
      let total = get_u64(&t.count, &addr_count_key(addr, kind))?;
      (&t.addr_event, addr_prefix(addr, kind), total)
    }
  };
  // Newest first: walk back from the end of the prefix.
  let mut end = prefix.clone();
  end.extend_from_slice(&[0xff; 9]);
  let mut skipped = 0usize;
  index.for_each_rev_from(&end, |k, _| {
    if !k.starts_with(&prefix) {
      return Ok(false);
    }
    if k.len() != prefix.len() + 8 {
      return Ok(true);
    }
    if skipped < offset {
      skipped += 1;
      return Ok(true);
    }
    positions.push(u64::from_be_bytes(k[prefix.len()..].try_into().expect("8 bytes")));
    Ok(positions.len() < limit)
  })?;
  let mut out = Vec::with_capacity(positions.len());
  for pos in positions {
    if let Some(raw) = t.event.get(event_key(kind, pos))? {
      let mut v: Value = serde_json::from_slice(raw.as_ref())?;
      if let Some(o) = v.as_object_mut() {
        o.insert("kind".to_string(), Value::String(kind.to_string()));
      }
      out.push(v);
    }
  }
  Ok((out, total))
}

#[cfg(test)]
mod tests {
  use super::*;
  use serde_json::json;

  fn trees() -> (store::Db, Trees) {
    let db = store::Db::temporary().unwrap();
    let t = Trees::open(&db).unwrap();
    (db, t)
  }

  #[test]
  fn records_are_indexed_by_every_token_and_address_they_name() {
    let fill = json!({"addr": "DA", "saddr": "DB", "tick": "RAT", "stick": "boobs", "fee_rcv": "DC", "amt": "1"});
    let (ticks, addrs) = names_of(&fill);
    assert_eq!(ticks.into_iter().collect::<Vec<_>>(), ["boobs", "rat"]);
    assert_eq!(addrs.into_iter().collect::<Vec<_>>(), ["DA", "DB", "DC"]);
    let redeem = json!({"addr": "DA", "iaddr": "DI", "rdm": {"items": [{"tick": "gib", "amt": "1", "address": "DR"}]}});
    let (ticks, addrs) = names_of(&redeem);
    assert_eq!(ticks.into_iter().collect::<Vec<_>>(), ["gib"]);
    assert_eq!(addrs.into_iter().collect::<Vec<_>>(), ["DA", "DI", "DR"]);
    let auth = json!({"addr": "DA", "auth": ["Mjolnir", "strombreaker"]});
    assert_eq!(names_of(&auth).0.into_iter().collect::<Vec<_>>(), ["mjolnir", "strombreaker"]);
    assert!(tap_tick_key("a\0b").is_none() && tap_tick_key("").is_none());
    assert_eq!(tap_tick_key("TAP").as_deref(), Some("tap"));
  }

  #[test]
  fn rewriting_a_record_keeps_counts_right_and_a_shrink_removes_it() {
    let (_db, t) = trees();
    let a = json!({"tick": "tap", "addr": "DA", "amt": "1"});
    let b = json!({"tick": "tap", "addr": "DA", "taddr": "DB", "amt": "1"});
    put_event(&t, "sent", 0, &a).unwrap();
    // The same record again (the tail is read every pass): nothing changes.
    assert!(!put_event(&t, "sent", 0, &a).unwrap().1);
    assert_eq!(get_u64(&t.count, &tick_count_key("tap", "sent")).unwrap(), 1);
    // A reorg changed it: old names out, new names in.
    put_event(&t, "sent", 0, &b).unwrap();
    assert_eq!(get_u64(&t.count, &tick_count_key("tap", "sent")).unwrap(), 1);
    assert_eq!(get_u64(&t.count, &addr_count_key("DB", "sent")).unwrap(), 1);
    put_event(&t, "sent", 1, &a).unwrap();
    assert_eq!(get_u64(&t.count, &addr_count_key("DA", "sent")).unwrap(), 2);
    // The list got shorter.
    drop_events(&t, "sent", 1, 2).unwrap();
    assert_eq!(get_u64(&t.count, &addr_count_key("DA", "sent")).unwrap(), 1);
    assert!(t.event.get(event_key("sent", 1)).unwrap().is_none());
  }

  /// Against the local tap-reader, so skipped by default:
  /// `cargo test -p dogeord-indexer tap_copy -- --ignored`.
  #[tokio::test]
  #[ignore]
  async fn tap_copy_matches_the_reader() {
    let (_db, t) = trees();
    let r = Reader::new().unwrap();
    let mut st = TapState::default();
    sync_list(&r, &t, &mut st, "deploy", "getDeploymentsLength", "getDeployments").await.unwrap();
    for (kind, len_route, route) in LISTS {
      sync_list(&r, &t, &mut st, kind, len_route, route).await.unwrap();
    }
    // Every list copied in full, record for record.
    for (kind, len_route, _) in LISTS.iter().chain([&("deploy", "getDeploymentsLength", "")]) {
      let want = r.length(len_route).await.unwrap();
      assert_eq!(st.lens[*kind], want, "{kind}");
      if want > 0 {
        assert!(t.event.get(event_key(kind, want - 1)).unwrap().is_some(), "{kind}: last record");
        assert!(t.event.get(event_key(kind, want)).unwrap().is_none(), "{kind}: nothing past the end");
      }
    }
    // A second pass changes nothing.
    let before = t.count.get(tick_count_key("tap", "transfer")).unwrap();
    for (kind, len_route, route) in LISTS {
      sync_list(&r, &t, &mut st, kind, len_route, route).await.unwrap();
    }
    assert_eq!(t.count.get(tick_count_key("tap", "transfer")).unwrap(), before);

    // One token's holders, balance for balance.
    refresh_token(&r, &t, "tap", 0).await.unwrap();
    let raw = t.holders.get(b"tap").unwrap().unwrap();
    let holders: Vec<TapHolder> = serde_json::from_slice(raw.as_ref()).unwrap();
    assert_eq!(holders.len() as u64, r.length_of("getHoldersLength", "tap").await.unwrap());
    for h in holders.iter().take(5) {
      let bal = r.get(&["getBalance", &h.address, "tap"], &[]).await.unwrap();
      assert_eq!(bal.as_str().map(str::to_string).or_else(|| bal.as_u64().map(|n| n.to_string())).as_deref(), Some(h.balance.as_str()), "{}", h.address);
      let acct: TapHolder = serde_json::from_slice(t.account.get(account_key(&h.address, "tap")).unwrap().unwrap().as_ref()).unwrap();
      assert_eq!(acct.balance, h.balance);
    }
    // The token's transfer count matches the reader's per-token list.
    let want = r.length_of("getTickerTransferListLength", "tap").await.unwrap();
    assert_eq!(get_u64(&t.count, &tick_count_key("tap", "transfer")).unwrap(), want);
  }

  #[test]
  fn dot_tickers_and_chunked_bodies() {
    assert!(is_dot_segment(".") && is_dot_segment("..") && !is_dot_segment("a.b") && !is_dot_segment(""));
    assert_eq!(encode_segment("."), "%2E");
    assert_eq!(encode_segment(" 🐸 "), "%20%F0%9F%90%B8%20");
    assert_eq!(encode_segment("tap"), "tap");
    assert_eq!(dechunk(b"4\r\nWiki\r\n5;x=y\r\npedia\r\n0\r\n\r\n").unwrap(), b"Wikipedia");
    assert!(dechunk(b"9\r\nshort\r\n").is_err());
  }

  /// The ticker "." against the local reader; skipped by default.
  #[tokio::test]
  #[ignore]
  async fn tap_dot_ticker_reaches_its_own_route() {
    let r = Reader::new().unwrap();
    assert_eq!(r.length_of("getHoldersLength", ".").await.unwrap(), 1);
    let dep = r.get(&["getDeployment", "."], &[]).await.unwrap();
    assert_eq!(dep["tick"], ".");
  }

  #[test]
  fn minted_is_max_minus_left() {
    assert_eq!(minted(&json!({"max": "21000000"}), Some("20000000")).as_deref(), Some("1000000"));
    assert_eq!(minted(&json!({"max": "18446744073709551615"}), Some("18446744073709518536")).as_deref(), Some("33079"));
    assert_eq!(minted(&json!({"max": "x"}), Some("1")), None);
    assert_eq!(minted(&json!({"max": "5"}), None), None);
  }
}
