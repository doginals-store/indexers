mod store;
mod insc_index;
mod dns;

pub use dns::{
  ClaimEntry, DnsConfigView, DnsListed, DnsName, DnsNameView, DnsPage, DnsRecords, DnsRole, DnsStatus, DnsSupply, dns_claims,
  FEATURED_NAMESPACES, dns_featured, dns_get, dns_list, dns_names_of, dns_namespaces, dns_primary, dns_role, dns_status, dns_supply, normalize_name,
  run_dns_index,
};

pub use insc_index::{
  Genesis, InscriptionPage, KIND_NAMES, ListedInscription, NumberingStatus, backfill_inscription_seq, inscription_genesis,
  inscription_id_by_number, inscription_seq_backfill_done, kind_index, kind_names, list_inscriptions, numbering_status,
  kinds_of, run_inscription_numbering,
};

use crate::store::IVec as IVecOwned;

use anyhow::{Context, Result, anyhow, bail};
use once_cell::sync::Lazy;
use rayon::prelude::*;
use reqwest::Client;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use spookyord_core::{Config, StatusResponse};
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::VecDeque;
use std::collections::hash_map::Entry as HashEntry;
use std::str;
use std::sync::Arc;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering as AtomicOrdering};
use std::time::Instant;
use tokio::sync::{RwLock, watch};
use tokio::task::JoinSet;
use tokio::time::{Duration, sleep};
use tracing::{debug, info, warn};

/// Phase timers, to establish which part of the sequential indexing path is
/// actually hot before trying to parallelise anything. Nanoseconds, reset each
/// time they are reported.
/// Bytes written per tree, to find what is actually generating index volume.
static BYTES_PARTIAL_CHAIN: AtomicU64 = AtomicU64::new(0);
static BYTES_CONTENT: AtomicU64 = AtomicU64::new(0);
static BYTES_UNDO: AtomicU64 = AtomicU64::new(0);

/// Time inside the per-input prefix scan of inscriptions_by_outpoint, and how
/// many such scans were issued. Split out of the inputs phase because it is the
/// one operation performed per transaction input that is an iterator seek
/// rather than a point lookup.
static SCAN_NS: AtomicU64 = AtomicU64::new(0);
static SCAN_COUNT: AtomicU64 = AtomicU64::new(0);

/// The read that UndoRecorder performs before every write, to capture the
/// value it would need to restore on rollback.
static UNDO_READ_NS: AtomicU64 = AtomicU64::new(0);
static UNDO_READ_COUNT: AtomicU64 = AtomicU64::new(0);
/// The actual store writes.
static STORE_WRITE_NS: AtomicU64 = AtomicU64::new(0);
static STORE_WRITE_COUNT: AtomicU64 = AtomicU64::new(0);

static PHASE_INPUTS_NS: AtomicU64 = AtomicU64::new(0);
static PHASE_SCRIPT_NS: AtomicU64 = AtomicU64::new(0);
static PHASE_OUTPUTS_NS: AtomicU64 = AtomicU64::new(0);
static PHASE_COMMIT_NS: AtomicU64 = AtomicU64::new(0);

static DRC20_PROTOCOL: Lazy<String> = Lazy::new(|| "drc-20".to_string());
const DUNE_CLAIM_BIT: u128 = 1 << 48;
const DUNE_MAX_LIMIT: u128 = u64::MAX as u128;

#[derive(Debug, Clone)]
pub struct SharedState {
  inner: Arc<RwLock<IndexerState>>,
}

#[derive(Debug, Clone)]
struct IndexerState {
  network: String,
  protocol_start_height: u64,
  chain_tip: u64,
  indexed_height: u64,
  indexing: bool,
  db_path: String,
}

#[derive(Debug, Serialize, Deserialize)]
struct UtxoRecord {
  satoshis: u64,
  address: String,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct InscriptionRecord {
  pub id: String,
  pub txid: String,
  pub vout: u32,
  pub offset: u64,
  pub satoshis: u64,
  /// MIME type as declared in the envelope. May be empty: delegate-only
  /// inscriptions and some text claims leave content type unset. Callers must
  /// not treat empty as "missing inscription".
  pub content_type: String,
  pub address: String,
  /// When set, content endpoints should serve the content of this inscription
  /// instead. Binary encoding is the 32-byte txid (display-reversed) plus an
  /// optional little-endian index; stored here as the usual `txid iN` string.
  #[serde(default)]
  pub delegate: Option<String>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct InscriptionContentRecord {
  /// Declared MIME; empty string when the envelope omitted it. Never filtered
  /// by allow-list - any declared type (or none) is stored as-is so clients
  /// can decide how to render.
  pub content_type: String,
  pub body: Vec<u8>,
  #[serde(default)]
  pub delegate: Option<String>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
struct Drc20TokenInfo {
  tick: String,
  supply: u128,
  minted: u128,
  limit_per_mint: u128,
  decimals: u8,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
struct Drc20Balance {
  tick: String,
  overall: u128,
  transferable: u128,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
struct Drc20Transferable {
  inscription_id: String,
  tick: String,
  amount: u128,
  owner: String,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct Drc20Holding {
  pub tick: String,
  pub available: String,
  pub transferable: String,
  pub total: String,
  /// Amounts above are raw integers scaled by 10^decimals.
  #[serde(default)]
  pub decimals: u8,
}

/// A claimed dogemap: inscription content of the form `<block number>.dogemap`.
///
/// `number` is the Dogecoin block being claimed. `owner` tracks the address
/// currently holding the claiming inscription and is updated whenever that
/// inscription moves, so it is current rather than the original minter.
/// `block_height` / `block_time` record where the claim was made, not where
/// the claimed block is.
#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct DogemapEntry {
  pub number: u64,
  pub inscription_id: String,
  pub txid: String,
  pub owner: String,
  pub block_height: u64,
  pub block_time: u64,
}

/// Suffix identifying a dogemap claim.
pub const DOGEMAP_SUFFIX: &str = "dogemap";

/// Parses `<number>.dogemap` out of inscription content.
///
/// Deliberately strict, because a claim that parses here becomes a permanent
/// first-come-wins allocation:
///
/// - the suffix is matched case-insensitively (`123.DOGEMAP` is valid, matching
///   how bitmap-style claims are treated elsewhere)
/// - surrounding whitespace is ignored, since inscribers frequently include a
///   trailing newline
/// - leading zeros are rejected: `007.dogemap` and `7.dogemap` would otherwise
///   be two distinct texts claiming one block
/// - a leading `+`, or any other numeric decoration, is rejected for the same
///   reason (`u64::from_str` would otherwise accept `+7`)
///
/// Content type is intentionally NOT checked. Dogemap inscriptions are made
/// with a variety of text mime types and no type at all, so filtering on it
/// would silently drop valid claims.
fn parse_dogemap_number(body: &[u8]) -> Option<u64> {
  let text = std::str::from_utf8(body).ok()?.trim();

  let (number_part, suffix) = text.rsplit_once('.')?;
  if !suffix.eq_ignore_ascii_case(DOGEMAP_SUFFIX) {
    return None;
  }

  let number_str = number_part.trim();
  if number_str.is_empty() || !number_str.bytes().all(|b| b.is_ascii_digit()) {
    return None;
  }
  // "0" is legitimate (the genesis block); "01" is not.
  if number_str.len() > 1 && number_str.starts_with('0') {
    return None;
  }

  number_str.parse::<u64>().ok()
}

/// Index key for the per-owner dogemap listing.
///
/// The number is zero-padded so the key sorts numerically within an address,
/// which lets the address listing be served by an ordered range scan.
fn dogemap_address_key(address: &str, number: u64) -> String {
  format!("{}|{:020}", address, number)
}

/// Records a dogemap claim, if it is valid.
///
/// Returns whether the claim was taken. Two rules decide that:
///
/// 1. A block that does not exist yet cannot be claimed. Without this check a
///    single inscription could claim an arbitrarily large number and squat a
///    block years before it is mined.
/// 2. First claim wins, permanently. Ordering is the order blocks and
///    transactions are indexed in, which is consensus order, so this is
///    deterministic across reindexes.
///
/// Every write goes through the UndoRecorder, so a reorg that removes the
/// claiming transaction also releases the number for re-claiming.
#[allow(clippy::too_many_arguments)]
fn apply_dogemap_claim_with_undo(
  dogemap_by_number: &store::Tree,
  dogemap_by_inscription: &store::Tree,
  dogemap_by_address: &store::Tree,
  number: u64,
  inscription_id: &str,
  txid: &str,
  owner: &str,
  height: u64,
  block_time: u64,
  undo: &mut UndoRecorder,
) -> Result<bool> {
  if number > height {
    return Ok(false);
  }

  let number_key = encode_u64(number);
  if dogemap_by_number.get(number_key)?.is_some() {
    return Ok(false);
  }

  let entry = DogemapEntry {
    number,
    inscription_id: inscription_id.to_string(),
    txid: txid.to_string(),
    owner: owner.to_string(),
    block_height: height,
    block_time,
  };

  undo.insert(
    "dogemap_by_number",
    dogemap_by_number,
    &number_key,
    bincode::serialize(&entry)?,
  )?;
  undo.insert(
    "dogemap_by_inscription",
    dogemap_by_inscription,
    inscription_id.as_bytes(),
    number_key.to_vec(),
  )?;
  if !owner.is_empty() {
    undo.insert(
      "dogemap_by_address",
      dogemap_by_address,
      dogemap_address_key(owner, number).as_bytes(),
      Vec::<u8>::new(),
    )?;
  }

  Ok(true)
}

/// Re-points a dogemap at its new owner when the claiming inscription moves.
///
/// Ownership of a dogemap is ownership of the inscription that claimed it, so
/// this must run on every move of an inscription that holds a claim - otherwise
/// the index would keep reporting the original minter forever.
fn move_dogemap_owner_with_undo(
  dogemap_by_number: &store::Tree,
  dogemap_by_inscription: &store::Tree,
  dogemap_by_address: &store::Tree,
  inscription_id: &str,
  new_owner: &str,
  undo: &mut UndoRecorder,
) -> Result<()> {
  let Some(number_key) = dogemap_by_inscription.get(inscription_id.as_bytes())? else {
    return Ok(());
  };
  let Some(raw) = dogemap_by_number.get(&number_key)? else {
    return Ok(());
  };

  let mut entry: DogemapEntry =
    bincode::deserialize(raw.as_ref()).context("decode dogemap entry")?;
  if entry.owner == new_owner {
    return Ok(());
  }

  if !entry.owner.is_empty() {
    undo.remove(
      "dogemap_by_address",
      dogemap_by_address,
      dogemap_address_key(&entry.owner, entry.number).as_bytes(),
    )?;
  }

  entry.owner = new_owner.to_string();
  undo.insert(
    "dogemap_by_number",
    dogemap_by_number,
    &number_key,
    bincode::serialize(&entry)?,
  )?;

  if !new_owner.is_empty() {
    undo.insert(
      "dogemap_by_address",
      dogemap_by_address,
      dogemap_address_key(new_owner, entry.number).as_bytes(),
      Vec::<u8>::new(),
    )?;
  }

  Ok(())
}

#[derive(Debug, Clone)]
struct CarriedInscription {
  id: String,
  absolute_offset: u64,
  content_type: String,
  delegate: Option<String>,
}

#[derive(Debug)]
enum Drc20Action {
  Deploy {
    tick: String,
    max_supply: String,
    mint_limit: Option<String>,
    decimals: Option<String>,
  },
  Mint {
    tick: String,
    amount: String,
  },
  TransferInscribe {
    tick: String,
    amount: String,
  },
}

impl SharedState {
  pub fn new() -> Self {
    Self {
      inner: Arc::new(RwLock::new(IndexerState {
        network: "unknown".to_string(),
        protocol_start_height: 0,
        chain_tip: 0,
        indexed_height: 0,
        indexing: false,
        db_path: String::new(),
      })),
    }
  }

  pub async fn status(&self) -> StatusResponse {
    let s = self.inner.read().await;
    let lag = s.chain_tip.saturating_sub(s.indexed_height);
    let remaining_blocks = lag;
    let done = s
      .indexed_height
      .saturating_sub(s.protocol_start_height)
      .saturating_add(1);
    let total = s
      .chain_tip
      .saturating_sub(s.protocol_start_height)
      .saturating_add(1)
      .max(1);
    let progress_percent = (done as f64 / total as f64 * 100.0).clamp(0.0, 100.0);
    let phase = if lag == 0 {
      "realtime".to_string()
    } else {
      "backfill".to_string()
    };

    StatusResponse {
      network: s.network.clone(),
      protocol_start_height: s.protocol_start_height,
      chain_tip: s.chain_tip,
      indexed_height: s.indexed_height,
      remaining_blocks,
      progress_percent,
      phase,
      lag,
      indexing: s.indexing,
      db_path: s.db_path.clone(),
    }
  }

  async fn set_network(&self, network: String) {
    self.inner.write().await.network = network;
  }

  async fn set_protocol_start_height(&self, h: u64) {
    self.inner.write().await.protocol_start_height = h;
  }

  async fn set_tip(&self, tip: u64) {
    self.inner.write().await.chain_tip = tip;
  }

  async fn set_indexed_height(&self, h: u64) {
    self.inner.write().await.indexed_height = h;
  }

  async fn set_indexing(&self, v: bool) {
    self.inner.write().await.indexing = v;
  }

  async fn set_db_path(&self, p: String) {
    self.inner.write().await.db_path = p;
  }
}

#[derive(Debug, Deserialize)]
struct JsonRpcResponse<T> {
  result: Option<T>,
  error: Option<JsonRpcError>,
}

#[derive(Debug, Deserialize)]
struct JsonRpcError {
  message: String,
}

#[derive(Debug, Deserialize)]
struct BlockchainInfo {
  chain: String,
  blocks: u64,
}

#[derive(Debug, Serialize)]
struct JsonRpcRequest<'a> {
  jsonrpc: &'static str,
  id: &'static str,
  method: &'a str,
  params: serde_json::Value,
}

#[derive(Debug, Deserialize)]
struct RpcBlock {
  hash: String,
  previousblockhash: Option<String>,
  /// Full transactions, fetched with `getblock <hash> 2`.
  ///
  /// This was previously `Vec<String>` (txids from verbosity 1), with a
  /// follow-up `getrawtransaction` per transaction. That cost 1+N round trips
  /// per block and left the indexer waiting on RPC rather than working:
  /// measured at 62 blocks/sec with CPU at 13% and disk at 22%.
  ///
  /// Verbosity 2 returns the same transaction objects embedded in the block
  /// response, so one call replaces all N. Benchmarked over 20 real blocks
  /// (257 transactions), sequentially and with no concurrency:
  ///
  ///   verbosity 2          : 6.6 ms/block
  ///   verbosity 1 + per-tx : 49.8 ms/block   (7.5x slower)
  ///
  /// The node reads the block from disk either way; the per-transaction path
  /// additionally does a txindex lookup and a re-read for every transaction.
  tx: Vec<RpcTx>,
  /// Block timestamp, recorded on dogemap claims. Optional so that a node
  /// response without it cannot fail the whole block decode - the timestamp is
  /// metadata only and never affects whether a claim is valid.
  #[serde(default)]
  time: Option<u64>,
}

#[derive(Debug, Deserialize, Clone)]
struct RpcTx {
  txid: String,
  vin: Vec<RpcVin>,
  vout: Vec<RpcVout>,
}

#[derive(Debug, Deserialize, Clone)]
struct RpcVin {
  txid: Option<String>,
  vout: Option<u32>,
  #[serde(rename = "scriptSig")]
  script_sig: Option<RpcScriptSig>,
}

#[derive(Debug, Deserialize, Clone)]
struct RpcScriptSig {
  hex: String,
}

#[derive(Debug, Deserialize, Clone)]
struct RpcVout {
  value: f64,
  n: u32,
  #[serde(rename = "scriptPubKey")]
  script_pub_key: RpcScriptPubKey,
}

#[derive(Debug, Deserialize, Clone)]
struct RpcScriptPubKey {
  asm: Option<String>,
  hex: Option<String>,
  addresses: Option<Vec<String>>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
struct DuneMeta {
  id: String,
  name: String,
  symbol: String,
  divisibility: u8,
}

#[derive(Debug, Serialize, Deserialize, Clone, Default)]
struct DuneTerms {
  cap: Option<u128>,
  limit: Option<u128>,
  height_start: Option<u64>,
  height_end: Option<u64>,
  offset_start: Option<u64>,
  offset_end: Option<u64>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
struct DuneEntryLite {
  id: String,
  etched_height: u64,
  premine: u128,
  supply: u128,
  burned: u128,
  mints: u128,
  terms: Option<DuneTerms>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct DuneHolding {
  pub id: String,
  pub name: String,
  pub symbol: String,
  pub divisibility: u8,
  pub balance: String,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
pub struct DuneUtxo {
  pub txid: String,
  pub vout: u32,
  pub balance: String,
  pub satoshis: u64,
}

#[derive(Debug, Default)]
struct ParsedDunestone {
  pointer: Option<usize>,
  edicts: Vec<(u128, u128, u128)>, // (id, amount, output)
  etching: Option<ParsedEtching>,
  cenotaph: bool,
}

#[derive(Debug)]
struct ParsedEtching {
  dune: Option<u128>,
  divisibility: u8,
  spacers: u32,
  symbol: Option<char>,
  premine: u128,
  terms: Option<DuneTerms>,
}

#[derive(Debug, Clone)]
struct ParsedInscriptionData {
  content_type: String,
  body: Vec<u8>,
  delegate: Option<String>,
  inscription_txid: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PartialInscriptionChain {
  start_txid: String,
  scripts: Vec<Vec<u8>>,
}

#[derive(Debug, Serialize, Deserialize, Clone)]
struct UndoOp {
  tree: String,
  key: Vec<u8>,
  previous: Option<Vec<u8>>,
}

#[derive(Debug, Default)]
struct UndoRecorder {
  originals: HashMap<(String, Vec<u8>), Option<Vec<u8>>>,
}

impl UndoRecorder {
  fn record_key(&mut self, tree_name: &str, tree: &store::Tree, key: &[u8]) -> Result<()> {
    let composite = (tree_name.to_string(), key.to_vec());
    match self.originals.entry(composite) {
      HashEntry::Occupied(_) => Ok(()),
      HashEntry::Vacant(v) => {
        let t = Instant::now();
        let prev = tree.get(key)?.map(|x| x.to_vec());
        UNDO_READ_NS.fetch_add(t.elapsed().as_nanos() as u64, AtomicOrdering::Relaxed);
        UNDO_READ_COUNT.fetch_add(1, AtomicOrdering::Relaxed);
        v.insert(prev);
        Ok(())
      }
    }
  }

  fn insert(
    &mut self,
    tree_name: &str,
    tree: &store::Tree,
    key: &[u8],
    value: Vec<u8>,
  ) -> Result<()> {
    self.record_key(tree_name, tree, key)?;
    let t = Instant::now();
    tree.insert(key, value)?;
    STORE_WRITE_NS.fetch_add(t.elapsed().as_nanos() as u64, AtomicOrdering::Relaxed);
    STORE_WRITE_COUNT.fetch_add(1, AtomicOrdering::Relaxed);
    Ok(())
  }

  /// Inserts a key that cannot already exist, skipping the read that `insert`
  /// performs to capture the previous value.
  ///
  /// ONLY valid for keys derived from a newly created transaction output:
  /// (txid, vout) is unique, so no prior value can exist for them. Using this
  /// on any other key would record an undo entry claiming the key was absent,
  /// and a rollback would then delete live data instead of restoring it.
  ///
  /// Worth doing because the read is on the hot path: phase timing attributed
  /// ~58% of indexing time to the output loop, and at ~630 transactions per
  /// block every one of those reads was a guaranteed miss.
  ///
  /// If the same key is touched again later in the block, the first recorded
  /// state wins - which is still "absent", so rollback stays correct.
  fn insert_new(
    &mut self,
    tree_name: &str,
    tree: &store::Tree,
    key: &[u8],
    value: Vec<u8>,
  ) -> Result<()> {
    self
      .originals
      .entry((tree_name.to_string(), key.to_vec()))
      .or_insert(None);
    tree.insert(key, value)?;
    Ok(())
  }

  fn remove(&mut self, tree_name: &str, tree: &store::Tree, key: &[u8]) -> Result<()> {
    self.record_key(tree_name, tree, key)?;
    tree.remove(key)?;
    Ok(())
  }

  /// Removes a key whose current value the caller already holds.
  ///
  /// `remove` re-reads the value purely to record what a rollback would need to
  /// restore. Where the caller has just read it, that second read is pure
  /// waste - and it is not cheap: measured at 12.1 us each, ~2,900 per block,
  /// 24-32% of all indexing time.
  ///
  /// `previous` MUST be the value currently stored under `key`, or rollback
  /// will restore the wrong thing. Only pass a value obtained by reading this
  /// key, or one guaranteed by construction.
  fn remove_known(
    &mut self,
    tree_name: &str,
    tree: &store::Tree,
    key: &[u8],
    previous: Option<Vec<u8>>,
  ) -> Result<()> {
    self
      .originals
      .entry((tree_name.to_string(), key.to_vec()))
      .or_insert(previous);
    tree.remove(key)?;
    Ok(())
  }

  fn into_ops(self) -> Vec<UndoOp> {
    self
      .originals
      .into_iter()
      .map(|((tree, key), previous)| UndoOp {
        tree,
        key,
        previous,
      })
      .collect()
  }
}

pub async fn run_indexer(
  config: Config,
  state: SharedState,
  mut shutdown: watch::Receiver<bool>,
) -> Result<()> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let meta = db.open_tree("meta")?;
  let blocks = db.open_tree("blocks")?;
  let utxo_by_outpoint = db.open_tree("utxo_by_outpoint")?;
  let outpoints_by_address = db.open_tree("outpoints_by_address")?;
  let inscriptions_by_id = db.open_tree("inscriptions_by_id")?;
  let inscriptions_by_outpoint = db.open_tree("inscriptions_by_outpoint")?;
  let inscriptions_by_address = db.open_tree("inscriptions_by_address")?;
  let inscription_content = db.open_tree("inscription_content")?;
  let partial_inscription_chain = db.open_tree("partial_inscription_chain")?;
  let drc20_token_info = db.open_tree("drc20_token_info")?;
  let drc20_balance = db.open_tree("drc20_balance")?;
  let drc20_transferable_by_id = db.open_tree("drc20_transferable_by_id")?;
  let dune_meta_by_id = db.open_tree("dune_meta_by_id")?;
  let dune_entry_by_id = db.open_tree("dune_entry_by_id")?;
  let dune_balances_by_outpoint = db.open_tree("dune_balances_by_outpoint")?;
  // Dogemap: number -> entry is the authoritative claim record. The other two
  // are indexes: by_inscription lets an inscription move be resolved back to
  // its claim in O(1), by_address backs per-wallet listing.
  let dogemap_by_number = db.open_tree("dogemap_by_number")?;
  let dogemap_by_inscription = db.open_tree("dogemap_by_inscription")?;
  let dogemap_by_address = db.open_tree("dogemap_by_address")?;
  let drc20_deploy = db.open_tree("drc20_deploy")?;
  let token_activity = db.open_tree("token_activity")?;
  let inscription_seq = db.open_tree("inscription_seq")?;
  let undo_by_height = db.open_tree("undo_by_height")?;

  state.set_db_path(db_path.clone()).await;

  let client = Client::builder().build().context("build reqwest client")?;
  let info: BlockchainInfo = rpc_call(&client, &config, "getblockchaininfo", serde_json::json!([])).await?;
  state.set_network(info.chain.clone()).await;
  state.set_tip(info.blocks).await;

  let protocol_start = config.protocol_start_height();
  state.set_protocol_start_height(protocol_start).await;

  let mut next_height = match meta.get(b"indexed_height")? {
    Some(v) => decode_u64(v.as_ref())? + 1,
    None => protocol_start,
  };

  // Reconcile any heights applied beyond the recorded indexed_height.
  //
  // Flushes are batched (SPOOKY_FLUSH_INTERVAL), so an unclean stop can leave
  // a block's writes durable while the indexed_height that follows them is
  // not. Resuming would then apply that block a second time, and DRC-20
  // balance updates are additive - a double apply silently inflates balances
  // rather than failing loudly.
  //
  // Every block records its undo log before advancing indexed_height, so any
  // undo entry at or above next_height marks a block to roll back. Highest
  // first, so each rollback sees the state its undo log was captured against.
  {
    let mut stale: Vec<u64> = Vec::new();
    // Keys only: the undo tree is retained in full at ~1 MB per block, so its
    // values must never be materialised during a scan.
    for k in undo_by_height.keys_from(encode_u64(next_height))? {
      let h = decode_u64(k.as_ref())?;
      if h >= next_height {
        stale.push(h);
      }
    }
    stale.sort_unstable();
    for h in stale.into_iter().rev() {
      warn!(
        "rolling back height {} applied beyond recorded indexed_height {}",
        h,
        next_height.saturating_sub(1)
      );
      rollback_one_height(&db, &blocks, &meta, &undo_by_height, h)?;
    }
  }

  state.set_indexed_height(next_height.saturating_sub(1)).await;
  // Token activity is recorded from this block on; earlier activity was
  // indexed before recording existed. Written once, on the first start.
  if meta.get(ACTIVITY_SINCE_KEY)?.is_none() {
    meta.insert(ACTIVITY_SINCE_KEY, encode_u64(next_height).to_vec())?;
  }
  insc_index::mark_seq_since(&meta, next_height)?;
  info!("starting sync from height {} (protocol start {})", next_height, protocol_start);

  // Undo logs are retained only as far back as a reorg could plausibly reach.
  //
  // Measured: ~1 MB of undo per block at inscription-era density. Kept forever
  // that is ~1.6 TB over the remaining chain, before sled's own space
  // amplification - and it is dead weight, since rollback is only ever invoked
  // for the recent tip. Dogecoin Core will not hand us a reorg thousands of
  // blocks deep; if it somehow did, the indexer would need a resync anyway.
  // How far back undo logs are kept, in blocks. 0 disables pruning entirely.
  //
  // IMPORTANT: this prunes ROLLBACK HISTORY ONLY. Indexed data - UTXOs,
  // inscriptions, DRC-20 balances, dune balances, dogemap claims - is never
  // touched. The undo tree exists solely so a reorg can walk a block back; a
  // height whose undo log has been pruned simply cannot be rolled back, which
  // is irrelevant for blocks buried tens of thousands deep.
  //
  // 1,000 blocks is about 17 hours at Dogecoin's one-minute target - far beyond
  // any reorg the network has produced.
  //
  // This was 50,000 and that was a bad call: undo runs 2-16 MB per block in the
  // inscription era, so 50,000 blocks is up to 732 GB of rollback history. The
  // index had reached 228 GB, and carrying that volume also slowed indexing,
  // since RocksDB had far more data to cache and compact.
  let undo_retention: u64 = std::env::var("SPOOKY_UNDO_RETENTION_BLOCKS")
    .ok()
    .and_then(|v| v.parse().ok())
    .unwrap_or(1_000);
  // Restored from disk. Starting at 0 meant every restart re-swept the entire
  // undo keyspace from genesis.
  let mut undo_pruned_below = match meta.get(b"undo_pruned_below")? {
    Some(v) => decode_u64(v.as_ref()).unwrap_or(0),
    None => 0,
  };

  let mut blocks_since_flush = 0u64;
  let mut cached_tip = 0u64;
  let mut blocks_since_tip_refresh = u64::MAX; // force a refresh on entry
  let tip_refresh_interval = 200u64;

  // Block prefetch pipeline.
  //
  // Indexing must stay strictly sequential (each block's UTXO and balance
  // updates depend on the previous one), but fetching a block and parsing its
  // JSON does not. Measured on this machine, that fetch+parse work had the
  // indexer pinned at 73% of a single core with the node at 12% and 15 cores
  // idle - a ~2 MB JSON response per block at inscription-era density.
  //
  // Tasks are spawned ahead and awaited in submission order, so blocks still
  // arrive strictly in height order while their fetch and deserialisation
  // overlap across cores.
  let lookahead = config.rpc_concurrency.max(1);
  let mut inflight: VecDeque<(u64, tokio::task::JoinHandle<Result<RpcBlock>>)> = VecDeque::new();
  let mut next_fetch = next_height;

  // Discards prefetched work. Required whenever the chain the prefetch was
  // built against stops being the chain we are indexing - i.e. on reorg.
  macro_rules! reset_prefetch {
    ($from:expr) => {{
      for (_, handle) in inflight.drain(..) {
        handle.abort();
      }
      next_fetch = $from;
    }};
  }

  loop {
    if *shutdown.borrow() {
      state.set_indexing(false).await;
      // Flushes are batched, so a clean shutdown must force one or the last
      // interval's blocks would be rolled back on next start.
      db.flush()?;
      info!("shutdown signal received before fetch, exiting indexer loop");
      return Ok(());
    }

    state.set_indexing(true).await;

    // Refresh the tip only when it matters, not once per block.
    //
    // During backfill this loop runs many times per second while the chain
    // advances roughly once a minute, so polling getblockcount every iteration
    // added a round trip per block for a value that had not changed. Refresh
    // when the cached tip is reached (so "caught up" is never stale) or after
    // tip_refresh_interval blocks.
    if cached_tip <= next_height || blocks_since_tip_refresh >= tip_refresh_interval {
      cached_tip = rpc_call(&client, &config, "getblockcount", serde_json::json!([])).await?;
      blocks_since_tip_refresh = 0;
      state.set_tip(cached_tip).await;
    }
    let tip = cached_tip;

    if next_height > tip {
      state.set_indexing(false).await;
      tokio::select! {
        _ = sleep(Duration::from_secs(2)) => {}
        _ = shutdown.changed() => {
          state.set_indexing(false).await;
          db.flush()?;
          info!("shutdown signal received while idle, exiting indexer loop");
          return Ok(());
        }
      }
      continue;
    }
    if let Some(stop_height) = config.stop_height
      && next_height > stop_height
    {
      state.set_indexing(false).await;
      db.flush()?;
      info!(
        "reached configured stop height {}, current next_height {}, exiting",
        stop_height, next_height
      );
      return Ok(());
    }

    // Top up the prefetch window. Never fetch past the tip or the configured
    // stop height, or we would block on a getblockhash for a block that does
    // not exist yet.
    let fetch_ceiling = match config.stop_height {
      Some(stop) => tip.min(stop),
      None => tip,
    };
    while inflight.len() < lookahead && next_fetch <= fetch_ceiling {
      let h = next_fetch;
      let client = client.clone();
      let cfg = config.clone();
      inflight.push_back((
        h,
        tokio::spawn(async move {
          let hash: String =
            rpc_call(&client, &cfg, "getblockhash", serde_json::json!([h])).await?;
          // Verbosity 2: block header plus every transaction in one response.
          // See RpcBlock::tx for why this replaces the per-transaction loop.
          let block: RpcBlock =
            rpc_call(&client, &cfg, "getblock", serde_json::json!([hash, 2])).await?;
          Ok::<RpcBlock, anyhow::Error>(block)
        }),
      ));
      next_fetch += 1;
    }

    // Take the block for the height we are about to index. The queue is in
    // submission order, so the front is always the oldest outstanding height;
    // anything else means the pipeline desynchronised and must be rebuilt.
    let block: RpcBlock = match inflight.pop_front() {
      Some((h, handle)) if h == next_height => handle.await.context("join block fetch")??,
      Some((h, handle)) => {
        warn!("prefetch out of order: expected height {next_height}, queued {h}; rebuilding");
        handle.abort();
        reset_prefetch!(next_height);
        continue;
      }
      None => {
        reset_prefetch!(next_height);
        continue;
      }
    };

    if next_height > protocol_start {
      let prev_indexed = blocks.get(encode_u64(next_height - 1))?;
      if let (Some(prev_hash_bytes), Some(prev_blockhash)) = (prev_indexed, block.previousblockhash.clone()) {
        let expected = String::from_utf8(prev_hash_bytes.to_vec()).context("invalid stored block hash utf8")?;
        if expected != prev_blockhash {
          info!(
            "reorg detected at height {}: expected prev hash {}, node reported {}",
            next_height, expected, prev_blockhash
          );
          rollback_one_height(&db, &blocks, &meta, &undo_by_height, next_height - 1)?;
          next_height = next_height.saturating_sub(1);
          state.set_indexed_height(next_height.saturating_sub(1)).await;
          // Anything already prefetched belongs to the chain we just walked
          // back from, so it must be discarded rather than indexed.
          db.flush()?;
          blocks_since_flush = 0;
          reset_prefetch!(next_height);
          continue;
        }
      }
    }

    // Borrow rather than clone: at ~330 transactions and ~535 KB per block in
    // the inscription era, deep-copying the whole transaction vector per block
    // is pure waste.
    let txs = &block.tx;

    let mut undo = UndoRecorder::default();
    index_block(
      &config,
      &txs,
      &utxo_by_outpoint,
      &outpoints_by_address,
      &inscriptions_by_id,
      &inscriptions_by_outpoint,
      &inscriptions_by_address,
      &inscription_content,
      &partial_inscription_chain,
      &drc20_token_info,
      &drc20_balance,
      &drc20_transferable_by_id,
      &dune_meta_by_id,
      &dune_entry_by_id,
      &dune_balances_by_outpoint,
      &dogemap_by_number,
      &dogemap_by_inscription,
      &dogemap_by_address,
      &drc20_deploy,
      &token_activity,
      &inscription_seq,
      next_height,
      block.time.unwrap_or(0),
      &mut undo,
    )?;

    let commit_start = Instant::now();
    let undo_ops = undo.into_ops();
    // Order matters and is relied on by the startup reconciliation above: the
    // undo log is durable before indexed_height advances past it, so any block
    // that survives a crash without its indexed_height can always be rolled
    // back.
    let undo_blob = bincode::serialize(&undo_ops)?;
    BYTES_UNDO.fetch_add(undo_blob.len() as u64, AtomicOrdering::Relaxed);
    undo_by_height.insert(encode_u64(next_height), undo_blob)?;
    blocks.insert(encode_u64(next_height), block.hash.as_bytes())?;
    meta.insert(b"indexed_height", encode_u64(next_height).to_vec())?;

    // Flush periodically rather than every block. An fsync per block dominated
    // per-block cost during backfill. Always flush once caught up to the tip,
    // so a live node is durable per block and the API never lags reality.
    blocks_since_flush += 1;
    if blocks_since_flush >= config.flush_interval || next_height >= tip {
      // Drop undo logs past the reorg horizon, when a horizon is configured.
      // Disabled by default: full undo history is retained.
      if undo_retention > 0 && next_height > undo_retention {
        let prune_below = next_height - undo_retention;
        if prune_below > undo_pruned_below {
          // A single range tombstone. Never scan this range: undo records are
          // tens of MB each, and reading them to delete them one by one wedged
          // the indexer on a 21-transaction block.
          undo_by_height.delete_range(encode_u64(undo_pruned_below), encode_u64(prune_below))?;
          undo_pruned_below = prune_below;
          // Persist the watermark so a restart does not redo the whole sweep
          // from zero.
          meta.insert(b"undo_pruned_below", encode_u64(undo_pruned_below).to_vec())?;
        }
      }

      db.flush()?;
      blocks_since_flush = 0;
    }
    blocks_since_tip_refresh += 1;
    PHASE_COMMIT_NS.fetch_add(commit_start.elapsed().as_nanos() as u64, AtomicOrdering::Relaxed);

    state.set_indexed_height(next_height).await;

    if next_height % 200 == 0 {
      let inp = PHASE_INPUTS_NS.swap(0, AtomicOrdering::Relaxed);
      let scr = PHASE_SCRIPT_NS.swap(0, AtomicOrdering::Relaxed);
      let out = PHASE_OUTPUTS_NS.swap(0, AtomicOrdering::Relaxed);
      let com = PHASE_COMMIT_NS.swap(0, AtomicOrdering::Relaxed);
      let total = (inp + scr + out + com).max(1);
      info!(
        "phase split over 200 blocks: inputs {:.1}% script/inscription {:.1}% outputs {:.1}% commit {:.1}% (total {} ms)",
        inp as f64 / total as f64 * 100.0,
        scr as f64 / total as f64 * 100.0,
        out as f64 / total as f64 * 100.0,
        com as f64 / total as f64 * 100.0,
        total / 1_000_000,
      );
      let urn = UNDO_READ_NS.swap(0, AtomicOrdering::Relaxed);
      let urc = UNDO_READ_COUNT.swap(0, AtomicOrdering::Relaxed).max(1);
      let swn = STORE_WRITE_NS.swap(0, AtomicOrdering::Relaxed);
      let swc = STORE_WRITE_COUNT.swap(0, AtomicOrdering::Relaxed).max(1);
      info!(
        "undo reads {} ({:.1} us each) = {:.1}% | store writes {} ({:.1} us each) = {:.1}%",
        urc,
        urn as f64 / urc as f64 / 1000.0,
        urn as f64 / total as f64 * 100.0,
        swc,
        swn as f64 / swc as f64 / 1000.0,
        swn as f64 / total as f64 * 100.0,
      );
      let sn = SCAN_NS.swap(0, AtomicOrdering::Relaxed);
      let sc = SCAN_COUNT.swap(0, AtomicOrdering::Relaxed).max(1);
      info!(
        "per-input prefix scans over 200 blocks: {} scans, {} ms total ({:.1} us each) = {:.1}% of block time",
        sc,
        sn / 1_000_000,
        sn as f64 / sc as f64 / 1000.0,
        sn as f64 / total as f64 * 100.0,
      );
      let bpc = BYTES_PARTIAL_CHAIN.swap(0, AtomicOrdering::Relaxed);
      let bct = BYTES_CONTENT.swap(0, AtomicOrdering::Relaxed);
      let bun = BYTES_UNDO.swap(0, AtomicOrdering::Relaxed);
      info!(
        "bytes written over 200 blocks: partial_chain {} MB ({} MB/block) content {} MB undo {} MB",
        bpc / 1_048_576,
        bpc / 200 / 1_048_576,
        bct / 1_048_576,
        bun / 1_048_576,
      );
    }

    if next_height % 100 == 0 {
      info!("indexed height {} / tip {}", next_height, tip);
    }

    next_height += 1;
  }
}

/// Fetches transactions individually by txid, `rpc_concurrency` at a time.
///
/// No longer used by the indexer: `getblock <hash> 2` returns the same
/// transactions in a single call, which benchmarked 7.5x faster (see
/// RpcBlock::tx). Retained because it is the only path that works against a
/// node without `txindex`-backed block verbosity 2, and as a reference for
/// fetching arbitrary transactions outside the block loop.
#[allow(dead_code)]
async fn fetch_block_transactions(client: &Client, config: &Config, txids: &[String]) -> Result<Vec<RpcTx>> {
  if txids.is_empty() {
    return Ok(Vec::new());
  }

  let concurrency = config.rpc_concurrency.max(1);
  let mut joinset = JoinSet::new();
  let mut next_submit = 0usize;
  let mut results: Vec<Option<RpcTx>> = Vec::with_capacity(txids.len());
  results.resize_with(txids.len(), || None);

  while next_submit < txids.len() || !joinset.is_empty() {
    while next_submit < txids.len() && joinset.len() < concurrency {
      let idx = next_submit;
      let txid = txids[idx].clone();
      let client = client.clone();
      let cfg = config.clone();
      joinset.spawn(async move {
        let tx: RpcTx = rpc_call(&client, &cfg, "getrawtransaction", serde_json::json!([txid, true])).await?;
        Ok::<(usize, RpcTx), anyhow::Error>((idx, tx))
      });
      next_submit += 1;
    }

    let Some(joined) = joinset.join_next().await else {
      break;
    };
    let (idx, tx) = joined.context("join tx fetch task")??;
    results[idx] = Some(tx);
  }

  results
    .into_iter()
    .map(|x| x.ok_or_else(|| anyhow!("missing transaction fetch result")))
    .collect()
}

fn rollback_one_height(
  db: &store::Db,
  blocks: &store::Tree,
  meta: &store::Tree,
  undo_by_height: &store::Tree,
  height: u64,
) -> Result<()> {
  let key = encode_u64(height);
  let Some(raw) = undo_by_height.get(key)? else {
    bail!("reorg rollback missing undo log at height {height}");
  };
  let ops: Vec<UndoOp> = bincode::deserialize(raw.as_ref())?;
  for op in ops.into_iter().rev() {
    let tree = db.open_tree(&op.tree)?;
    match op.previous {
      Some(v) => {
        tree.insert(op.key, v)?;
      }
      None => {
        tree.remove(op.key)?;
      }
    }
  }

  blocks.remove(key)?;
  undo_by_height.remove(key)?;
  if height == 0 {
    meta.remove(b"indexed_height")?;
  } else {
    meta.insert(b"indexed_height", encode_u64(height - 1).to_vec())?;
  }
  db.flush()?;
  Ok(())
}

/// Per-output values that depend only on the transaction, not on index state.
struct PreparedOut {
  satoshis: u64,
  address: String,
  outpoint: String,
  utxo_bytes: Vec<u8>,
  /// Empty when the output has no address.
  addr_key: String,
}

/// Per-transaction values that depend only on the transaction.
struct PreparedTx {
  /// Aligned with `tx.vin`; None where the input has no prevout (coinbase).
  vin_outpoints: Vec<Option<String>>,
  /// Decoded scriptSig of vin[0], the inscription envelope carrier.
  script_sig: Option<Vec<u8>>,
  /// Aligned with `tx.vout`.
  outs: Vec<PreparedOut>,
}

fn prepare_tx(tx: &RpcTx) -> Result<PreparedTx> {
  let vin_outpoints = tx
    .vin
    .iter()
    .map(|vin| match (&vin.txid, vin.vout) {
      (Some(txid), Some(vout)) => Some(outpoint_key(txid, vout)),
      _ => None,
    })
    .collect();

  let mut outs = Vec::with_capacity(tx.vout.len());
  for vout in &tx.vout {
    let satoshis = to_satoshis(vout.value)?;
    let address = vout
      .script_pub_key
      .addresses
      .as_ref()
      .and_then(|v| v.first())
      .cloned()
      .unwrap_or_default();
    let outpoint = outpoint_key(&tx.txid, vout.n);
    let utxo_bytes = bincode::serialize(&UtxoRecord {
      satoshis,
      address: address.clone(),
    })?;
    let addr_key = if address.is_empty() {
      String::new()
    } else {
      address_outpoint_key(&address, &tx.txid, vout.n)
    };
    outs.push(PreparedOut {
      satoshis,
      address,
      outpoint,
      utxo_bytes,
      addr_key,
    });
  }

  Ok(PreparedTx {
    vin_outpoints,
    script_sig: decode_script_sig_bytes(tx),
    outs,
  })
}

/// Dedicated worker pool for the prepare phase.
///
/// Sized by SPOOKY_INDEX_THREADS, default 10 on this 16-core machine. A
/// dedicated pool rather than rayon's global one so the indexer's parallelism
/// is explicit and bounded, leaving cores for the sequential apply loop, the
/// block prefetcher, RocksDB's background compaction, and the node itself.
static PREPARE_POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();

fn prepare_pool() -> &'static rayon::ThreadPool {
  PREPARE_POOL.get_or_init(|| {
    let threads = std::env::var("SPOOKY_INDEX_THREADS")
      .ok()
      .and_then(|v| v.parse::<usize>().ok())
      .filter(|v| *v > 0)
      .unwrap_or(10);
    info!("prepare pool: {} worker threads", threads);
    rayon::ThreadPoolBuilder::new()
      .num_threads(threads)
      .thread_name(|i| format!("prepare-{i}"))
      .build()
      .expect("build prepare thread pool")
  })
}

/// Precomputes the state-independent part of a block in parallel.
///
/// Indexing itself must stay sequential - a transaction can spend an output
/// created earlier in the same block, and each block depends on the previous.
/// But hex-decoding scriptSigs, formatting outpoint and address keys, and
/// bincode-serialising UTXO records depend only on the transaction, and phase
/// timing showed those dominating the two hot phases while 15 cores idled.
///
/// Doing them up front, in parallel, leaves the sequential loop with just the
/// store operations and the state machine.
fn prepare_block(txs: &[RpcTx]) -> Result<Vec<PreparedTx>> {
  // Small blocks are not worth dispatching to the pool.
  if txs.len() < 64 {
    return txs.iter().map(prepare_tx).collect();
  }

  prepare_pool().install(|| txs.par_iter().map(prepare_tx).collect::<Result<Vec<_>>>())
}

#[allow(clippy::too_many_arguments)]
fn index_block(
  config: &Config,
  txs: &[RpcTx],
  utxo_by_outpoint: &store::Tree,
  outpoints_by_address: &store::Tree,
  inscriptions_by_id: &store::Tree,
  inscriptions_by_outpoint: &store::Tree,
  inscriptions_by_address: &store::Tree,
  inscription_content: &store::Tree,
  partial_inscription_chain: &store::Tree,
  drc20_token_info: &store::Tree,
  drc20_balance: &store::Tree,
  drc20_transferable_by_id: &store::Tree,
  dune_meta_by_id: &store::Tree,
  dune_entry_by_id: &store::Tree,
  dune_balances_by_outpoint: &store::Tree,
  dogemap_by_number: &store::Tree,
  dogemap_by_inscription: &store::Tree,
  dogemap_by_address: &store::Tree,
  drc20_deploy: &store::Tree,
  token_activity: &store::Tree,
  inscription_seq: &store::Tree,
  height: u64,
  block_time: u64,
  undo: &mut UndoRecorder,
) -> Result<()> {
  // State-independent work, computed across cores before the sequential pass.
  let prepared = prepare_block(txs)?;

  // Prefetch every UTXO this block spends, in one batched read.
  //
  // The inputs phase measured ~49% of indexing time, almost all of it point
  // lookups of outputs created in EARLIER blocks. Those do not depend on
  // anything this block does, so they can be fetched up front together instead
  // of one at a time down the critical path.
  //
  // Correctness: an input spending an output created earlier in this same
  // block will be absent here (the prefetch ran before any of this block's
  // writes), and the sequential pass falls back to a live read on a miss. A
  // key present in the prefetch cannot have been written earlier in the block,
  // because a UTXO is created once and only removed when spent - so a cache
  // hit is always current.
  let mut utxo_prefetch: HashMap<&str, IVecOwned> = HashMap::new();
  {
    let mut keys: Vec<&str> = Vec::new();
    for prep in &prepared {
      for k in prep.vin_outpoints.iter().flatten() {
        keys.push(k.as_str());
      }
    }
    keys.sort_unstable();
    keys.dedup();
    if !keys.is_empty() {
      let values = utxo_by_outpoint.multi_get(&keys)?;
      for (k, v) in keys.into_iter().zip(values) {
        if let Some(v) = v {
          utxo_prefetch.insert(k, v);
        }
      }
    }
  }

  for (tx_index, tx) in txs.iter().enumerate() {
    let prep = &prepared[tx_index];
    let mut carried = Vec::<CarriedInscription>::new();
    let mut input_value = 0u64;

    let inputs_start = Instant::now();
    for (vin_index, vin) in tx.vin.iter().enumerate() {
      let (Some(prev_txid), Some(prev_vout)) = (&vin.txid, vin.vout) else {
        continue;
      };

      let prev_outpoint = prep.vin_outpoints[vin_index]
        .as_deref()
        .expect("prevout key precomputed for every input carrying a prevout");

      let prev_key = prev_outpoint.as_bytes();
      // Prefetched above; a miss means the output was created earlier in this
      // same block, so fall back to a live read.
      let old = match utxo_prefetch.get(prev_outpoint) {
        Some(v) => Some(v.clone()),
        None => utxo_by_outpoint.get(prev_key)?,
      };
      if let Some(old) = old {
        // The value is already in hand from the prefetch or the read above, so
        // the undo record does not need to re-read it.
        undo.remove_known(
          "utxo_by_outpoint",
          utxo_by_outpoint,
          prev_key,
          Some(old.to_vec()),
        )?;

        let record: UtxoRecord = bincode::deserialize(old.as_ref()).context("decode utxo record")?;
        if !record.address.is_empty() {
          let addr_key = address_outpoint_key(&record.address, prev_txid, prev_vout);
          // Written as encode_u64(satoshis) when this output was created, under
          // the same non-empty-address condition, so its current value is known
          // without reading it.
          undo.remove_known(
            "outpoints_by_address",
            outpoints_by_address,
            addr_key.as_bytes(),
            Some(encode_u64(record.satoshis).to_vec()),
          )?;
        }

        // One point lookup, not an iterator seek.
        //
        // This used to be scan_prefix("{outpoint}|") over per-inscription keys.
        // Measured on the live index: ~2,100 of those per block at 40.6 us each,
        // 29.7% of all indexing time. Seeks cannot use bloom filters and must
        // position in every LSM level, so the cost grew with the database.
        // Storing the whole list under the outpoint makes it a point get, which
        // the store serves at ~1.4M/s against ~25k/s for seeks.
        let scan_start = Instant::now();
        let existing = inscriptions_by_outpoint.get(prev_key)?;
        SCAN_NS.fetch_add(scan_start.elapsed().as_nanos() as u64, AtomicOrdering::Relaxed);
        SCAN_COUNT.fetch_add(1, AtomicOrdering::Relaxed);

        let entries: Vec<(u64, String)> = match &existing {
          Some(raw) => {
            bincode::deserialize(raw.as_ref()).context("decode inscriptions_by_outpoint")?
          }
          None => Vec::new(),
        };
        let had_entries = !entries.is_empty();

        for (rel_offset, inscription_id) in entries {

          if let Some(raw) = inscriptions_by_id.get(inscription_id.as_bytes())? {
            let rec = decode_inscription_record(raw.as_ref())?;
            if !rec.address.is_empty() {
              let addr_insc_key = format!("{}|{}", rec.address, rec.id);
              undo.remove(
                "inscriptions_by_address",
                inscriptions_by_address,
                addr_insc_key.as_bytes(),
              )?;
            }

            carried.push(CarriedInscription {
              id: rec.id,
              absolute_offset: input_value.saturating_add(rel_offset),
              content_type: rec.content_type,
              delegate: rec.delegate,
            });
          }
        }

        // The whole list lives under one key now, so spending the output is a
        // single remove instead of one per inscription.
        if had_entries {
          // `existing` is the value just read for this key.
          undo.remove_known(
            "inscriptions_by_outpoint",
            inscriptions_by_outpoint,
            prev_key,
            existing.as_ref().map(|v| v.to_vec()),
          )?;
        }

        input_value = input_value.saturating_add(record.satoshis);
      }
    }

    let mut dune_events = Vec::new();
    process_dunes(
      tx,
      tx_index,
      height,
      dune_meta_by_id,
      dune_entry_by_id,
      dune_balances_by_outpoint,
      undo,
      &mut dune_events,
    )?;
    for e in dune_events {
      let event = ActivityEvent {
        kind: e.kind.to_string(),
        amount: e.amount.to_string(),
        from: String::new(),
        to: String::new(),
        inscription_id: String::new(),
        txid: tx.txid.clone(),
        height,
        time: block_time,
      };
      record_activity(token_activity, undo, &dune_scope(&e.dune_id), tx_index, e.kind, &event)?;
    }

    PHASE_INPUTS_NS.fetch_add(inputs_start.elapsed().as_nanos() as u64, AtomicOrdering::Relaxed);

    let script_start = Instant::now();
    let parsed_inscription = process_inscription_candidate(
      tx,
      prep.script_sig.as_deref(),
      partial_inscription_chain,
      undo,
    )?;
    let new_inscription_id = parsed_inscription
      .as_ref()
      .map(|p| format!("{}i0", p.inscription_txid));
    if let Some(parsed) = parsed_inscription.as_ref() {
      if carried.iter().all(|c| c.absolute_offset != 0) {
        let inscription_id = format!("{}i0", parsed.inscription_txid);
        carried.push(CarriedInscription {
          id: inscription_id.clone(),
          absolute_offset: 0,
          content_type: parsed.content_type.clone(),
          delegate: parsed.delegate.clone(),
        });

        if config.content_store == "full" {
          let content = InscriptionContentRecord {
            content_type: parsed.content_type.clone(),
            body: parsed.body.clone(),
            delegate: parsed.delegate.clone(),
          };
          let serialized = bincode::serialize(&content)?;
          BYTES_CONTENT.fetch_add(serialized.len() as u64, AtomicOrdering::Relaxed);
          undo.insert(
            "inscription_content",
            inscription_content,
            inscription_id.as_bytes(),
            serialized,
          )?;
        }

        // Chain order, for numbering. The key is this block's height and this
        // transaction's place in it, so nothing can be there already.
        let kinds = insc_index::kinds_for_new(
          inscriptions_by_id,
          &parsed.content_type,
          &parsed.body,
          parsed.delegate.as_deref(),
        )?;
        undo.insert_new(
          "inscription_seq",
          inscription_seq,
          &insc_index::seq_key(height, tx_index as u32),
          insc_index::seq_value(&inscription_id, kinds, block_time)?,
        )?;
      }
    }

    carried.sort_by_key(|c| c.absolute_offset);
    PHASE_SCRIPT_NS.fetch_add(script_start.elapsed().as_nanos() as u64, AtomicOrdering::Relaxed);

    let outputs_start = Instant::now();
    let mut output_start = 0u64;
    let mut assigned = vec![false; carried.len()];

    for (vout_index, vout) in tx.vout.iter().enumerate() {
      // All of this was precomputed in parallel by prepare_block: satoshi
      // conversion, outpoint and address key strings, and the serialized UTXO
      // record. The sequential pass only performs the store writes.
      let pout = &prep.outs[vout_index];
      let satoshis = pout.satoshis;
      let outpoint = &pout.outpoint;
      let address = &pout.address;

      // Both keys are derived from this transaction's (txid, vout), which is
      // new by construction - so skip the undo read.
      undo.insert_new(
        "utxo_by_outpoint",
        utxo_by_outpoint,
        outpoint.as_bytes(),
        pout.utxo_bytes.clone(),
      )?;
      if !address.is_empty() {
        undo.insert_new(
          "outpoints_by_address",
          outpoints_by_address,
          pout.addr_key.as_bytes(),
          encode_u64(satoshis).to_vec(),
        )?;
      }

      let output_end = output_start.saturating_add(satoshis);
      // Inscriptions landing on this output, written as one list under the
      // outpoint key rather than one key each.
      let mut outpoint_inscriptions: Vec<(u64, String)> = Vec::new();

      for (i, c) in carried.iter().enumerate() {
        if c.absolute_offset >= output_start && c.absolute_offset < output_end {
          let offset = c.absolute_offset - output_start;
          let rec = InscriptionRecord {
            id: c.id.clone(),
            txid: tx.txid.clone(),
            vout: vout.n,
            offset,
            satoshis,
            content_type: c.content_type.clone(),
            address: address.clone(),
            delegate: c.delegate.clone(),
          };

          undo.insert(
            "inscriptions_by_id",
            inscriptions_by_id,
            rec.id.as_bytes(),
            bincode::serialize(&rec)?,
          )?;
          outpoint_inscriptions.push((offset, rec.id.clone()));
          if !rec.address.is_empty() {
            let addr_insc_key = format!("{}|{}", rec.address, rec.id);
            undo.insert(
              "inscriptions_by_address",
              inscriptions_by_address,
              addr_insc_key.as_bytes(),
              Vec::<u8>::new(),
            )?;
          }

          if let Some(parsed) = parsed_inscription.as_ref()
            && new_inscription_id.as_deref() == Some(rec.id.as_str())
            && rec.offset == 0
          {
            if let Some(action) = parse_drc20_action(&rec.content_type, &parsed.body) {
              let applied = apply_drc20_new_action_with_undo(
                drc20_token_info,
                drc20_balance,
                drc20_transferable_by_id,
                &rec.address,
                &rec.id,
                action,
                Some(&mut *undo),
              )?;
              if let Some(applied) = applied {
                let (tick, kind, amount, from, to) = match &applied {
                  Drc20Applied::Deploy { tick, supply } => (tick, "deploy", *supply, String::new(), rec.address.clone()),
                  Drc20Applied::Mint { tick, amount } => (tick, "mint", *amount, String::new(), rec.address.clone()),
                  Drc20Applied::Inscribe { tick, amount } => (tick, "inscribe-transfer", *amount, rec.address.clone(), String::new()),
                };
                if let Drc20Applied::Deploy { .. } = applied {
                  let deploy = Drc20Deploy {
                    inscription_id: rec.id.clone(),
                    txid: tx.txid.clone(),
                    deployer: rec.address.clone(),
                    height,
                    time: block_time,
                  };
                  undo.insert("drc20_deploy", drc20_deploy, tick.as_bytes(), bincode::serialize(&deploy)?)?;
                }
                let event = ActivityEvent {
                  kind: kind.to_string(),
                  amount: amount.to_string(),
                  from,
                  to,
                  inscription_id: rec.id.clone(),
                  txid: tx.txid.clone(),
                  height,
                  time: block_time,
                };
                record_activity(token_activity, undo, &drc20_scope(tick), tx_index, &format!("{}|{kind}", rec.id), &event)?;
              }
            }

            // Dogemap claim. Same position as the DRC-20 hook: a newly created
            // inscription sitting at offset 0 of this output.
            if let Some(number) = parse_dogemap_number(&parsed.body) {
              let claimed = apply_dogemap_claim_with_undo(
                dogemap_by_number,
                dogemap_by_inscription,
                dogemap_by_address,
                number,
                &rec.id,
                &tx.txid,
                &rec.address,
                height,
                block_time,
                undo,
              )?;
              if claimed {
                debug!("dogemap {} claimed by {} at height {}", number, rec.id, height);
              }
            }
          }

          if rec.id != format!("{}i0", tx.txid) {
            let moved = process_drc20_transfer_move_with_undo(
              drc20_balance,
              drc20_transferable_by_id,
              &rec.id,
              &rec.address,
              Some(&mut *undo),
            )?;
            if let Some(m) = moved {
              let event = ActivityEvent {
                kind: "transfer".to_string(),
                amount: m.amount.to_string(),
                from: m.from,
                to: m.to,
                inscription_id: rec.id.clone(),
                txid: tx.txid.clone(),
                height,
                time: block_time,
              };
              record_activity(token_activity, undo, &drc20_scope(&m.tick), tx_index, &format!("{}|transfer", rec.id), &event)?;
            }

            // A dogemap is owned by whoever holds the claiming inscription, so
            // a move of that inscription is a transfer of the dogemap.
            move_dogemap_owner_with_undo(
              dogemap_by_number,
              dogemap_by_inscription,
              dogemap_by_address,
              &rec.id,
              &rec.address,
              undo,
            )?;
          }

          assigned[i] = true;
        }
      }

      // One write for every inscription on this output. The key is this
      // transaction's outpoint, so it is new by construction.
      if !outpoint_inscriptions.is_empty() {
        undo.insert_new(
          "inscriptions_by_outpoint",
          inscriptions_by_outpoint,
          outpoint.as_bytes(),
          bincode::serialize(&outpoint_inscriptions)?,
        )?;
      }

      output_start = output_end;
    }

    for (i, c) in carried.iter().enumerate() {
      if assigned[i] {
        continue;
      }

      let lost = InscriptionRecord {
        id: c.id.clone(),
        txid: tx.txid.clone(),
        vout: u32::MAX,
        offset: c.absolute_offset,
        satoshis: 0,
        content_type: c.content_type.clone(),
        address: String::new(),
        delegate: c.delegate.clone(),
      };
      undo.insert(
        "inscriptions_by_id",
        inscriptions_by_id,
        lost.id.as_bytes(),
        bincode::serialize(&lost)?,
      )?;
    }
    PHASE_OUTPUTS_NS.fetch_add(outputs_start.elapsed().as_nanos() as u64, AtomicOrdering::Relaxed);
  }

  Ok(())
}

/// Where, when and by whom a DRC-20 token was deployed.
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq)]
pub struct Drc20Deploy {
  pub inscription_id: String,
  pub txid: String,
  /// Address the deploy inscription was created at.
  pub deployer: String,
  pub height: u64,
  pub time: u64,
}

/// One protocol event for a token, as recorded while indexing. Amounts are
/// raw integers (scaled by the token's decimals or divisibility), as strings.
#[derive(Debug, Serialize, Deserialize, Clone, PartialEq, Eq)]
pub struct ActivityEvent {
  pub kind: String,
  pub amount: String,
  pub from: String,
  pub to: String,
  pub inscription_id: String,
  pub txid: String,
  pub height: u64,
  pub time: u64,
}

pub fn drc20_scope(tick: &str) -> String {
  format!("T|{tick}")
}

pub fn dune_scope(dune_id: &str) -> String {
  format!("D|{dune_id}")
}

/// Keys sort newest first: by height, then by position in the block, both
/// inverted so a forward scan reads the latest events first and can stop.
/// Ticks are exactly four bytes and dune ids contain no '|', so a scope plus
/// '|' is an unambiguous prefix.
fn activity_key(scope: &str, height: u64, tx_index: usize, discriminator: &str) -> String {
  format!(
    "{scope}|{:020}|{:010}|{discriminator}",
    u64::MAX - height,
    u32::MAX - (tx_index as u32)
  )
}

/// Records one event. Through the undo log, so a reorg or crash rollback
/// removes it along with the state change it describes.
fn record_activity(
  tree: &store::Tree,
  undo: &mut UndoRecorder,
  scope: &str,
  tx_index: usize,
  discriminator: &str,
  event: &ActivityEvent,
) -> Result<()> {
  let key = activity_key(scope, event.height, tx_index, discriminator);
  undo.insert("token_activity", tree, key.as_bytes(), bincode::serialize(event)?)
}

/// Something a transaction did to a dune, reported for the activity record.
/// Collecting these never changes how balances are computed.
#[derive(Debug, Clone, PartialEq, Eq)]
struct DuneEvent {
  dune_id: String,
  kind: &'static str,
  amount: u128,
}

fn process_dunes(
  tx: &RpcTx,
  tx_index: usize,
  height: u64,
  dune_meta_by_id: &store::Tree,
  dune_entry_by_id: &store::Tree,
  dune_balances_by_outpoint: &store::Tree,
  undo: &mut UndoRecorder,
  events: &mut Vec<DuneEvent>,
) -> Result<()> {
  let mut unallocated: HashMap<String, u128> = HashMap::new();
  let mut mintable_remaining: HashMap<String, u128> = HashMap::new();
  let mut mintable_limit: HashMap<String, u128> = HashMap::new();

  // Pull dune balances from spent inputs into unallocated map.
  for vin in &tx.vin {
    let (Some(prev_txid), Some(prev_vout)) = (&vin.txid, vin.vout) else {
      continue;
    };
    let prefix = format!("{}:{}|", prev_txid, prev_vout);
    let mut remove_keys = Vec::new();
    for item in dune_balances_by_outpoint.scan_prefix(prefix.as_bytes())? {
      let (k, v) = item?;
      let key = String::from_utf8(k.to_vec()).context("invalid dune outpoint key utf8")?;
      let dune_id = key
        .split('|')
        .nth(1)
        .ok_or_else(|| anyhow!("invalid dune outpoint key format"))?
        .to_string();
      let amt = decode_u128(v.as_ref())?;
      *unallocated.entry(dune_id).or_default() += amt;
      remove_keys.push(k);
    }
    for k in remove_keys {
      undo.remove(
        "dune_balances_by_outpoint",
        dune_balances_by_outpoint,
        k.as_ref(),
      )?;
    }
  }

  // What the inputs carried in, before this transaction adds or mints any.
  let spent: Vec<(String, u128)> = unallocated
    .iter()
    .filter(|(_, a)| **a > 0)
    .map(|(id, a)| (id.clone(), *a))
    .collect();
  let report_spent = |events: &mut Vec<DuneEvent>, kind: &'static str| {
    for (dune_id, amount) in &spent {
      events.push(DuneEvent { dune_id: dune_id.clone(), kind, amount: *amount });
    }
  };

  let Some(dunestone) = parse_dunestone(tx) else {
    // no protocol message; default pass-through remains in unallocated and is assigned below
    assign_unallocated_default(tx, unallocated, None, dune_balances_by_outpoint, undo)?;
    report_spent(events, "transfer");
    return Ok(());
  };

  let mut issued_dune_id: Option<String> = None;
  if let Some(etch) = dunestone.etching {
    let numeric = etch
      .dune
      .unwrap_or_else(|| ((height as u128) << 16) | (tx_index as u128 & 0xFFFF));
    let name = dune_name(numeric);
    let dune_id = format!("DOGECOIN:{name}");
    let meta = DuneMeta {
      id: dune_id.clone(),
      name: apply_spacers(&name, etch.spacers),
      symbol: etch.symbol.map(|c| c.to_string()).unwrap_or_default(),
      divisibility: etch.divisibility,
    };
    if dune_meta_by_id.get(dune_id.as_bytes())?.is_none() {
      undo.insert(
        "dune_meta_by_id",
        dune_meta_by_id,
        dune_id.as_bytes(),
        bincode::serialize(&meta)?,
      )?;
      events.push(DuneEvent { dune_id: dune_id.clone(), kind: "etch", amount: etch.premine });
    }
    let entry = DuneEntryLite {
      id: dune_id.clone(),
      etched_height: height,
      premine: etch.premine,
      supply: etch.premine,
      burned: 0,
      mints: 0,
      terms: if dunestone.cenotaph { None } else { etch.terms.clone() },
    };
    if dune_entry_by_id.get(dune_id.as_bytes())?.is_none() {
      undo.insert(
        "dune_entry_by_id",
        dune_entry_by_id,
        dune_id.as_bytes(),
        bincode::serialize(&entry)?,
      )?;
    }
    if etch.premine > 0 {
      *unallocated.entry(dune_id.clone()).or_default() += etch.premine;
    }
    issued_dune_id = Some(dune_id.clone());
  }

  if dunestone.cenotaph {
    // Cenotaph burns all unallocated input balances by not allocating them.
    report_spent(events, "burn");
    return Ok(());
  }

  for (id, amount, output) in dunestone.edicts {
    let mut from_claim = false;
    let target_dune = if id == 0 {
      match &issued_dune_id {
        Some(x) => x.clone(),
        None => continue,
      }
    } else if let Some(claimed) = dune_claim_target(id) {
      let target = format!("DOGECOIN:{}", dune_name(claimed));
      let Some(raw_entry) = dune_entry_by_id.get(target.as_bytes())? else {
        continue;
      };
      let entry: DuneEntryLite = bincode::deserialize(raw_entry.as_ref())?;
      let Some(limit) = dune_mintable_limit(&entry, height) else {
        continue;
      };
      mintable_limit.entry(target.clone()).or_insert(limit);
      mintable_remaining.entry(target.clone()).or_insert(limit);
      from_claim = true;
      target
    } else {
      // interpret as numeric dune id for lookups if previously etched.
      let as_name = dune_name(id);
      let as_id = format!("DOGECOIN:{as_name}");
      if dune_meta_by_id.get(as_id.as_bytes())?.is_none() {
        continue;
      }
      as_id
    };

    let bal = if from_claim {
      mintable_remaining.entry(target_dune.clone()).or_default()
    } else {
      unallocated.entry(target_dune.clone()).or_default()
    };
    if *bal == 0 {
      continue;
    }

    if output == tx.vout.len() as u128 {
      let destinations: Vec<usize> = tx
        .vout
        .iter()
        .enumerate()
        .filter_map(|(i, v)| (!is_op_return(v)).then_some(i))
        .collect();
      if destinations.is_empty() {
        continue;
      }
      if amount == 0 {
        let each = *bal / destinations.len() as u128;
        let rem = (*bal % destinations.len() as u128) as usize;
        for (i, out) in destinations.iter().enumerate() {
          let a = if i < rem { each + 1 } else { each };
          if a > 0 {
            add_dune_to_output(tx, *out, &target_dune, a, dune_balances_by_outpoint, undo)?;
            *bal = bal.saturating_sub(a);
          }
        }
      } else {
        for out in destinations {
          let a = amount.min(*bal);
          if a == 0 {
            break;
          }
          add_dune_to_output(tx, out, &target_dune, a, dune_balances_by_outpoint, undo)?;
          *bal = bal.saturating_sub(a);
        }
      }
    } else {
      let Ok(output) = usize::try_from(output) else {
        continue;
      };
      let a = if amount == 0 { *bal } else { amount.min(*bal) };
      if a > 0 {
        add_dune_to_output(tx, output, &target_dune, a, dune_balances_by_outpoint, undo)?;
        *bal = bal.saturating_sub(a);
      }
    }
  }

  for (dune_id, remaining) in mintable_remaining {
    let Some(limit) = mintable_limit.get(&dune_id).copied() else {
      continue;
    };
    let minted = limit.saturating_sub(remaining);
    if minted == 0 {
      continue;
    }
    let Some(raw_entry) = dune_entry_by_id.get(dune_id.as_bytes())? else {
      continue;
    };
    let mut entry: DuneEntryLite = bincode::deserialize(raw_entry.as_ref())?;
    entry.supply = entry.supply.saturating_add(minted);
    entry.mints = entry.mints.saturating_add(1);
    undo.insert(
      "dune_entry_by_id",
      dune_entry_by_id,
      dune_id.as_bytes(),
      bincode::serialize(&entry)?,
    )?;
    events.push(DuneEvent { dune_id: dune_id.clone(), kind: "mint", amount: minted });
  }

  assign_unallocated_default(
    tx,
    unallocated,
    dunestone.pointer,
    dune_balances_by_outpoint,
    undo,
  )?;
  report_spent(events, "transfer");

  Ok(())
}

fn assign_unallocated_default(
  tx: &RpcTx,
  unallocated: HashMap<String, u128>,
  pointer: Option<usize>,
  dune_balances_by_outpoint: &store::Tree,
  undo: &mut UndoRecorder,
) -> Result<()> {
  let default = pointer
    .filter(|p| *p < tx.vout.len())
    .or_else(|| {
      tx.vout
        .iter()
        .enumerate()
        .find_map(|(i, v)| (!is_op_return(v)).then_some(i))
    });

  let Some(default_vout) = default else {
    return Ok(());
  };

  for (dune_id, amount) in unallocated {
    if amount == 0 {
      continue;
    }
    add_dune_to_output(tx, default_vout, &dune_id, amount, dune_balances_by_outpoint, undo)?;
  }
  Ok(())
}

fn add_dune_to_output(
  tx: &RpcTx,
  vout: usize,
  dune_id: &str,
  amount: u128,
  dune_balances_by_outpoint: &store::Tree,
  undo: &mut UndoRecorder,
) -> Result<()> {
  if vout >= tx.vout.len() || is_op_return(&tx.vout[vout]) {
    return Ok(());
  }
  let key = format!("{}:{}|{}", tx.txid, tx.vout[vout].n, dune_id);
  let prior = dune_balances_by_outpoint
    .get(key.as_bytes())?
    .map(|v| decode_u128(v.as_ref()))
    .transpose()?
    .unwrap_or(0);
  undo.insert(
    "dune_balances_by_outpoint",
    dune_balances_by_outpoint,
    key.as_bytes(),
    encode_u128(prior + amount).to_vec(),
  )?;
  Ok(())
}

fn is_op_return(vout: &RpcVout) -> bool {
  vout
    .script_pub_key
    .asm
    .as_deref()
    .map(|asm| asm.starts_with("OP_RETURN"))
    .unwrap_or(false)
}

fn parse_drc20_action(content_type: &str, body: &[u8]) -> Option<Drc20Action> {
  if !(content_type.starts_with("text/plain") || content_type.starts_with("application/json")) {
    return None;
  }
  if body.len() < 40 {
    return None;
  }

  let s = str::from_utf8(body).ok()?;
  let v: Value = serde_json::from_str(s).ok()?;

  if v.get("p")?.as_str()? != DRC20_PROTOCOL.as_str() {
    return None;
  }

  match v.get("op")?.as_str()? {
    "deploy" => Some(Drc20Action::Deploy {
      tick: v.get("tick")?.as_str()?.to_string(),
      max_supply: v.get("max")?.as_str()?.to_string(),
      mint_limit: v.get("lim").and_then(|x| x.as_str()).map(|x| x.to_string()),
      decimals: v.get("dec").and_then(|x| x.as_str()).map(|x| x.to_string()),
    }),
    "mint" => Some(Drc20Action::Mint {
      tick: v.get("tick")?.as_str()?.to_string(),
      amount: v.get("amt")?.as_str()?.to_string(),
    }),
    "transfer" => Some(Drc20Action::TransferInscribe {
      tick: v.get("tick")?.as_str()?.to_string(),
      amount: v.get("amt")?.as_str()?.to_string(),
    }),
    _ => None,
  }
}

fn parse_dunestone(tx: &RpcTx) -> Option<ParsedDunestone> {
  let payload = tx
    .vout
    .iter()
    .find_map(dune_payload_from_output)?;

  let (integers, mut cenotaph) = decode_dune_varints(&payload);
  if integers.is_empty() {
    return Some(ParsedDunestone {
      cenotaph,
      ..ParsedDunestone::default()
    });
  }

  let mut fields: HashMap<u128, u128> = HashMap::new();
  let mut edicts = Vec::<(u128, u128, u128)>::new();

  let mut i = 0usize;
  while i + 1 < integers.len() {
    let tag = integers[i];
    if tag == 0 {
      let mut last_id = 0u128;
      let rest = &integers[i + 1..];
      for chunk in rest.chunks_exact(3) {
        let id = last_id.saturating_add(chunk[0]);
        let amount = chunk[1];
        let output = chunk[2];
        if !is_valid_dune_id(id) || output > tx.vout.len() as u128 {
          cenotaph = true;
          continue;
        }
        edicts.push((id, amount, output));
        last_id = id;
      }
      if !rest.len().is_multiple_of(3) {
        cenotaph = true;
      }
      break;
    }
    let value = integers[i + 1];
    fields.entry(tag).or_insert(value);
    i += 2;
  }
  if i + 1 == integers.len() {
    cenotaph = true;
  }

  // Unknown even tags are cenotaph.
  for tag in fields.keys() {
    if tag % 2 == 0 && !matches!(*tag, 2 | 4 | 6 | 8 | 10 | 12 | 14 | 16 | 18 | 20 | 22 | 254) {
      cenotaph = true;
      break;
    }
  }

  // Flags with unknown bits are cenotaph.
  if let Some(flags) = fields.get(&2).copied() {
    let known = 1u128 | 2u128 | 4u128;
    if flags & !known != 0 {
      cenotaph = true;
    }
  }

  let pointer = fields.get(&12).and_then(|v| usize::try_from(*v).ok());
  let flags = fields.get(&2).copied().unwrap_or_default();
  let has_etching = flags & 1u128 != 0;
  let has_terms = flags & 2u128 != 0;

  let divisibility = fields
    .get(&1)
    .and_then(|d| u8::try_from(*d).ok())
    .filter(|d| *d <= 38)
    .unwrap_or(0);
  let dune = fields.get(&4).copied();
  let spacers = fields
    .get(&3)
    .and_then(|s| u32::try_from(*s).ok())
    .unwrap_or(0);
  let symbol = fields
    .get(&5)
    .and_then(|s| u32::try_from(*s).ok())
    .and_then(char::from_u32);
  let premine = fields.get(&22).copied().unwrap_or(0);
  let limit = fields.get(&6).copied().map(|v| v.min(DUNE_MAX_LIMIT));
  let cap = fields.get(&20).copied();
  let height_start = fields.get(&14).and_then(|v| u64::try_from(*v).ok());
  let height_end = fields.get(&18).and_then(|v| u64::try_from(*v).ok());
  let offset_start = fields.get(&16).and_then(|v| u64::try_from(*v).ok());
  let offset_end = fields.get(&8).and_then(|v| u64::try_from(*v).ok());

  let etching = if has_etching || dune.is_some() || premine > 0 {
    Some(ParsedEtching {
      dune,
      divisibility,
      spacers,
      symbol,
      premine,
      terms: has_terms.then_some(DuneTerms {
        cap,
        limit,
        height_start,
        height_end,
        offset_start,
        offset_end,
      }),
    })
  } else {
    None
  };

  let mut out = ParsedDunestone {
    pointer,
    edicts,
    etching,
    cenotaph,
  };

  if premine > 0 {
    // Mirror Wonky's behavior of adding a premine edict id=0 amount=premine output=1.
    out.edicts.push((0, premine, 1));
  }

  Some(out)
}

fn dune_payload_from_output(vout: &RpcVout) -> Option<Vec<u8>> {
  if let Some(script_hex) = vout.script_pub_key.hex.as_deref()
    && let Ok(script) = hex::decode(script_hex)
    && let Ok(payload) = dune_payload_from_script_bytes(&script)
  {
    return payload;
  }

  if !is_op_return(vout) {
    return None;
  }

  let asm = vout.script_pub_key.asm.as_deref()?;
  let mut tokens = asm.split_whitespace();
  if tokens.next()? != "OP_RETURN" {
    return None;
  }
  if tokens.next()? != "44" {
    return None;
  }
  let mut payload = Vec::new();
  for t in tokens {
    if t.starts_with("OP_") {
      continue;
    }
    if let Ok(bytes) = hex::decode(t) {
      payload.extend_from_slice(&bytes);
    }
  }
  Some(payload)
}

fn dune_payload_from_script_bytes(script: &[u8]) -> Result<Option<Vec<u8>>> {
  let mut i = 0usize;
  let Some(op) = script.get(i).copied() else {
    return Ok(None);
  };
  i += 1;
  if op != 0x6a {
    return Ok(None);
  }

  let Some(marker) = script_read_push(script, &mut i)? else {
    return Ok(None);
  };
  if marker != [0x44] {
    return Ok(None);
  }

  let mut payload = Vec::new();
  while i < script.len() {
    let op = script[i];
    i += 1;
    if (1..=0x4e).contains(&op) {
      if let Some(data) = script_read_push_with_opcode(script, &mut i, op)? {
        payload.extend_from_slice(data);
      }
    }
  }
  Ok(Some(payload))
}

fn script_read_push<'a>(script: &'a [u8], i: &mut usize) -> Result<Option<&'a [u8]>> {
  let Some(op) = script.get(*i).copied() else {
    return Ok(None);
  };
  *i += 1;
  script_read_push_with_opcode(script, i, op)
}

fn script_read_push_with_opcode<'a>(
  script: &'a [u8],
  i: &mut usize,
  op: u8,
) -> Result<Option<&'a [u8]>> {
  let len = match op {
    0x01..=0x4b => op as usize,
    0x4c => {
      let Some(v) = script.get(*i).copied() else {
        bail!("truncated pushdata1");
      };
      *i += 1;
      v as usize
    }
    0x4d => {
      let Some(bytes) = script.get(*i..*i + 2) else {
        bail!("truncated pushdata2");
      };
      *i += 2;
      u16::from_le_bytes([bytes[0], bytes[1]]) as usize
    }
    0x4e => {
      let Some(bytes) = script.get(*i..*i + 4) else {
        bail!("truncated pushdata4");
      };
      *i += 4;
      u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]) as usize
    }
    _ => return Ok(None),
  };
  let Some(data) = script.get(*i..*i + len) else {
    bail!("truncated push bytes");
  };
  *i += len;
  Ok(Some(data))
}

fn decode_dune_varints(payload: &[u8]) -> (Vec<u128>, bool) {
  let mut out = Vec::new();
  let mut i = 0usize;
  let mut cenotaph = false;
  while i < payload.len() {
    let (n, len, truncated) = dune_varint_decode(&payload[i..]);
    if truncated {
      cenotaph = true;
      break;
    }
    if len == 0 {
      break;
    }
    out.push(n);
    i += len;
  }
  (out, cenotaph)
}

fn dune_varint_decode(buffer: &[u8]) -> (u128, usize, bool) {
  let mut n = 0u128;
  let mut i = 0usize;
  loop {
    let Some(b) = buffer.get(i).copied() else {
      return (n, i, i > 0);
    };
    let b = u128::from(b);
    n = n.saturating_mul(128);
    if b < 128 {
      return (n.saturating_add(b), i + 1, false);
    }
    n = n.saturating_add(b - 127);
    i += 1;
  }
}

fn is_valid_dune_id(id: u128) -> bool {
  let height = id >> 16;
  let index = id & 0xFFFF;
  !(height == 0 && index > 0)
}

fn dune_claim_target(id: u128) -> Option<u128> {
  (id & DUNE_CLAIM_BIT != 0).then_some(id ^ DUNE_CLAIM_BIT)
}

fn dune_mintable_limit(entry: &DuneEntryLite, height: u64) -> Option<u128> {
  let terms = entry.terms.as_ref()?;

  let start_rel = terms.offset_start.map(|o| entry.etched_height.saturating_add(o));
  let start = match (start_rel, terms.height_start) {
    (Some(a), Some(b)) => Some(a.max(b)),
    (Some(a), None) => Some(a),
    (None, Some(b)) => Some(b),
    (None, None) => None,
  };

  if let Some(s) = start
    && height < s
  {
    return None;
  }

  let end_rel = terms.offset_end.map(|o| entry.etched_height.saturating_add(o));
  let end = match (end_rel, terms.height_end) {
    (Some(a), Some(b)) => Some(a.min(b)),
    (Some(a), None) => Some(a),
    (None, Some(b)) => Some(b),
    (None, None) => None,
  };

  if let Some(e) = end
    && height >= e
  {
    return None;
  }

  if let Some(cap) = terms.cap {
    if entry.mints >= cap {
      return None;
    }
  } else if entry.mints >= u128::MAX {
    return None;
  }

  Some(terms.limit.unwrap_or_default())
}

fn dune_name(mut n: u128) -> String {
  if n == u128::MAX {
    return "BCGDENLQRQWDSLRUGSNLBTMFIJAV".to_string();
  }
  n = n.saturating_add(1);
  let mut symbol = String::new();
  while n > 0 {
    let ch = (b'A' + ((n - 1) % 26) as u8) as char;
    symbol.push(ch);
    n = (n - 1) / 26;
  }
  symbol.chars().rev().collect()
}

fn apply_spacers(name: &str, spacers: u32) -> String {
  let mut out = String::new();
  for (i, c) in name.chars().enumerate() {
    out.push(c);
    if i < name.len().saturating_sub(1) && (spacers & (1 << i)) != 0 {
      out.push('\u{2022}');
    }
  }
  out
}

fn apply_drc20_new_action(
  token_tree: &store::Tree,
  balance_tree: &store::Tree,
  transferable_tree: &store::Tree,
  address: &str,
  inscription_id: &str,
  action: Drc20Action,
) -> Result<()> {
  apply_drc20_new_action_with_undo(
    token_tree,
    balance_tree,
    transferable_tree,
    address,
    inscription_id,
    action,
    None,
  )
  .map(|_| ())
}

/// What a DRC-20 inscription did, when it was accepted. Returned so the
/// caller can record it; deciding validity stays entirely in here.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Drc20Applied {
  Deploy { tick: String, supply: u128 },
  Mint { tick: String, amount: u128 },
  Inscribe { tick: String, amount: u128 },
}

/// The deploy rules, shared by indexing and the deploy backfill so both
/// accept exactly the same deploys: decimals default to 18 and may not exceed
/// it, supply must be non-zero, and the per-mint limit defaults to the supply
/// and must be non-zero. Returns (supply, limit, decimals).
fn validate_drc20_deploy(max_supply: &str, mint_limit: Option<&str>, decimals: Option<&str>) -> Option<(u128, u128, u8)> {
  let dec = decimals.unwrap_or("18").parse::<u8>().ok()?;
  if dec > 18 {
    return None;
  }
  let supply = parse_decimal_amount(max_supply, dec).ok()?;
  if supply == 0 {
    return None;
  }
  let limit = parse_decimal_amount(mint_limit.unwrap_or(max_supply), dec).ok()?;
  if limit == 0 {
    return None;
  }
  Some((supply, limit, dec))
}

fn apply_drc20_new_action_with_undo(
  token_tree: &store::Tree,
  balance_tree: &store::Tree,
  transferable_tree: &store::Tree,
  address: &str,
  inscription_id: &str,
  action: Drc20Action,
  mut undo: Option<&mut UndoRecorder>,
) -> Result<Option<Drc20Applied>> {
  if address.is_empty() {
    return Ok(None);
  }

  let applied = match action {
    Drc20Action::Deploy {
      tick,
      max_supply,
      mint_limit,
      decimals,
    } => {
      let Ok(tick) = canonical_tick(&tick) else {
        return Ok(None);
      };
      let tk = token_key(&tick);
      if token_tree.get(tk.as_bytes())?.is_some() {
        return Ok(None);
      }

      let Some((supply, limit, dec)) =
        validate_drc20_deploy(&max_supply, mint_limit.as_deref(), decimals.as_deref())
      else {
        return Ok(None);
      };

      let info = Drc20TokenInfo {
        tick,
        supply,
        minted: 0,
        limit_per_mint: limit,
        decimals: dec,
      };

      if let Some(u) = undo.as_deref_mut() {
        u.insert(
          "drc20_token_info",
          token_tree,
          tk.as_bytes(),
          bincode::serialize(&info)?,
        )?;
      } else {
        token_tree.insert(tk.as_bytes(), bincode::serialize(&info)?)?;
      }
      Drc20Applied::Deploy { tick: info.tick, supply }
    }
    Drc20Action::Mint { tick, amount } => {
      let Ok(tick) = canonical_tick(&tick) else {
        return Ok(None);
      };
      let tk = token_key(&tick);
      let Some(raw) = token_tree.get(tk.as_bytes())? else {
        return Ok(None);
      };
      let mut info: Drc20TokenInfo = bincode::deserialize(raw.as_ref())?;

      let Ok(amt) = parse_decimal_amount(&amount, info.decimals) else {
        return Ok(None);
      };
      if amt == 0 {
        return Ok(None);
      }
      if amt > info.limit_per_mint {
        return Ok(None);
      }
      if info.minted >= info.supply {
        return Ok(None);
      }

      let allowed = std::cmp::min(amt, info.supply.saturating_sub(info.minted));
      if allowed == 0 {
        return Ok(None);
      }

      info.minted = info.minted.saturating_add(allowed);
      if let Some(u) = undo.as_deref_mut() {
        u.insert(
          "drc20_token_info",
          token_tree,
          tk.as_bytes(),
          bincode::serialize(&info)?,
        )?;
      } else {
        token_tree.insert(tk.as_bytes(), bincode::serialize(&info)?)?;
      }

      let bk = balance_key(address, &tick);
      let mut bal = match balance_tree.get(bk.as_bytes())? {
        Some(v) => bincode::deserialize::<Drc20Balance>(v.as_ref())?,
        None => Drc20Balance {
          tick: tick.clone(),
          overall: 0,
          transferable: 0,
        },
      };
      bal.overall = bal.overall.saturating_add(allowed);
      if let Some(u) = undo.as_deref_mut() {
        u.insert(
          "drc20_balance",
          balance_tree,
          bk.as_bytes(),
          bincode::serialize(&bal)?,
        )?;
      } else {
        balance_tree.insert(bk.as_bytes(), bincode::serialize(&bal)?)?;
      }
      Drc20Applied::Mint { tick, amount: allowed }
    }
    Drc20Action::TransferInscribe { tick, amount } => {
      let Ok(tick) = canonical_tick(&tick) else {
        return Ok(None);
      };
      let tk = token_key(&tick);
      let Some(raw) = token_tree.get(tk.as_bytes())? else {
        return Ok(None);
      };
      let info: Drc20TokenInfo = bincode::deserialize(raw.as_ref())?;

      let Ok(amt) = parse_decimal_amount(&amount, info.decimals) else {
        return Ok(None);
      };
      if amt == 0 || amt > info.supply {
        return Ok(None);
      }

      let bk = balance_key(address, &tick);
      let Some(raw_bal) = balance_tree.get(bk.as_bytes())? else {
        return Ok(None);
      };
      let mut bal: Drc20Balance = bincode::deserialize(raw_bal.as_ref())?;
      let available = bal.overall.saturating_sub(bal.transferable);
      if available < amt {
        return Ok(None);
      }

      bal.transferable = bal.transferable.saturating_add(amt);
      if let Some(u) = undo.as_deref_mut() {
        u.insert(
          "drc20_balance",
          balance_tree,
          bk.as_bytes(),
          bincode::serialize(&bal)?,
        )?;
      } else {
        balance_tree.insert(bk.as_bytes(), bincode::serialize(&bal)?)?;
      }

      let lock = Drc20Transferable {
        inscription_id: inscription_id.to_string(),
        tick: tick.clone(),
        amount: amt,
        owner: address.to_string(),
      };
      if let Some(u) = undo.as_deref_mut() {
        u.insert(
          "drc20_transferable_by_id",
          transferable_tree,
          inscription_id.as_bytes(),
          bincode::serialize(&lock)?,
        )?;
      } else {
        transferable_tree.insert(inscription_id.as_bytes(), bincode::serialize(&lock)?)?;
      }
      Drc20Applied::Inscribe { tick, amount: amt }
    }
  };

  Ok(Some(applied))
}

fn process_drc20_transfer_move(
  balance_tree: &store::Tree,
  transferable_tree: &store::Tree,
  inscription_id: &str,
  destination_address: &str,
) -> Result<()> {
  process_drc20_transfer_move_with_undo(
    balance_tree,
    transferable_tree,
    inscription_id,
    destination_address,
    None,
  )
  .map(|_| ())
}

/// A completed DRC-20 transfer, returned so the caller can record it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Drc20Moved {
  tick: String,
  amount: u128,
  from: String,
  to: String,
}

fn process_drc20_transfer_move_with_undo(
  balance_tree: &store::Tree,
  transferable_tree: &store::Tree,
  inscription_id: &str,
  destination_address: &str,
  mut undo: Option<&mut UndoRecorder>,
) -> Result<Option<Drc20Moved>> {
  let Some(raw_lock) = transferable_tree.get(inscription_id.as_bytes())? else {
    return Ok(None);
  };
  let lock: Drc20Transferable = bincode::deserialize(raw_lock.as_ref())?;

  let from_bk = balance_key(&lock.owner, &lock.tick);
  let Some(raw_from) = balance_tree.get(from_bk.as_bytes())? else {
    if let Some(u) = undo.as_deref_mut() {
      u.remove("drc20_transferable_by_id", transferable_tree, inscription_id.as_bytes())?;
    } else {
      transferable_tree.remove(inscription_id.as_bytes())?;
    }
    return Ok(None);
  };
  let mut from: Drc20Balance = bincode::deserialize(raw_from.as_ref())?;

  if from.overall < lock.amount || from.transferable < lock.amount {
    if let Some(u) = undo.as_deref_mut() {
      u.remove("drc20_transferable_by_id", transferable_tree, inscription_id.as_bytes())?;
    } else {
      transferable_tree.remove(inscription_id.as_bytes())?;
    }
    return Ok(None);
  }

  from.overall = from.overall.saturating_sub(lock.amount);
  from.transferable = from.transferable.saturating_sub(lock.amount);
  if let Some(u) = undo.as_deref_mut() {
    u.insert(
      "drc20_balance",
      balance_tree,
      from_bk.as_bytes(),
      bincode::serialize(&from)?,
    )?;
  } else {
    balance_tree.insert(from_bk.as_bytes(), bincode::serialize(&from)?)?;
  }

  // Same behavior as Wonky's redirect-to-sender when sent to coinbase/no receiver.
  let receiver = if destination_address.is_empty() {
    lock.owner.clone()
  } else {
    destination_address.to_string()
  };

  let to_bk = balance_key(&receiver, &lock.tick);
  let mut to = match balance_tree.get(to_bk.as_bytes())? {
    Some(v) => bincode::deserialize::<Drc20Balance>(v.as_ref())?,
    None => Drc20Balance {
      tick: lock.tick.clone(),
      overall: 0,
      transferable: 0,
    },
  };
  to.overall = to.overall.saturating_add(lock.amount);
  if let Some(u) = undo.as_deref_mut() {
    u.insert(
      "drc20_balance",
      balance_tree,
      to_bk.as_bytes(),
      bincode::serialize(&to)?,
    )?;
    u.remove("drc20_transferable_by_id", transferable_tree, inscription_id.as_bytes())?;
  } else {
    balance_tree.insert(to_bk.as_bytes(), bincode::serialize(&to)?)?;
    transferable_tree.remove(inscription_id.as_bytes())?;
  }
  Ok(Some(Drc20Moved {
    tick: lock.tick,
    amount: lock.amount,
    from: lock.owner,
    to: receiver,
  }))
}

fn canonical_tick(tick: &str) -> Result<String> {
  if tick.as_bytes().len() != 4 {
    bail!("invalid tick length");
  }
  Ok(tick.to_ascii_uppercase())
}

fn parse_decimal_amount(s: &str, decimals: u8) -> Result<u128> {
  let s = s.trim();
  if s.is_empty() {
    bail!("empty amount");
  }
  if s.starts_with('-') {
    bail!("negative amount");
  }

  let mut parts = s.split('.');
  let int_part = parts.next().unwrap_or_default();
  let frac_part = parts.next();
  if parts.next().is_some() {
    bail!("invalid decimal format");
  }

  if int_part.is_empty() || !int_part.chars().all(|c| c.is_ascii_digit()) {
    bail!("invalid integer part");
  }

  let int_val: u128 = int_part.parse().map_err(|_| anyhow!("integer overflow"))?;
  let base = 10u128.pow(decimals.into());
  let mut value = int_val.checked_mul(base).ok_or_else(|| anyhow!("amount overflow"))?;

  if let Some(frac) = frac_part {
    if !frac.chars().all(|c| c.is_ascii_digit()) {
      bail!("invalid fractional part");
    }
    if frac.len() > decimals as usize {
      bail!("too many decimal places");
    }

    let mut frac_norm = frac.to_string();
    while frac_norm.len() < decimals as usize {
      frac_norm.push('0');
    }

    if !frac_norm.is_empty() {
      let frac_val: u128 = frac_norm.parse().map_err(|_| anyhow!("fraction overflow"))?;
      value = value.checked_add(frac_val).ok_or_else(|| anyhow!("amount overflow"))?;
    }
  }

  Ok(value)
}

fn token_key(tick: &str) -> String {
  format!("T|{tick}")
}

fn balance_key(address: &str, tick: &str) -> String {
  format!("B|{address}|{tick}")
}

fn decode_script_sig_bytes(tx: &RpcTx) -> Option<Vec<u8>> {
  let vin0 = tx.vin.first()?;
  let script_hex = vin0.script_sig.as_ref()?.hex.as_str();
  hex::decode(script_hex).ok()
}

#[derive(Debug)]
enum InscriptionParseOutcome {
  None,
  Partial,
  /// content_type, body, optional delegate inscription id.
  Complete(String, Vec<u8>, Option<String>),
}

/// Tag 11 in the ordinals field map: the inscription this one delegates to.
const TAG_DELEGATE: u8 = 11;

/// Decode a binary inscription id field (delegate/parent) into the display
/// form `txid iN`.
///
/// On-chain bytes are the raw 32-byte txid in internal order (the reverse of
/// the usual hex display) followed by a little-endian index with trailing
/// zeroes omitted. Rejects values that are too short, too long, or that pad
/// with a trailing zero outside the fixed 4-byte form - matching pepecoin/
/// wonky-ord so we do not invent ids that other indexers would drop.
fn decode_inscription_id_field(value: &[u8]) -> Option<String> {
  if value.len() < 32 || value.len() > 36 {
    return None;
  }
  let (txid_bytes, index_bytes) = value.split_at(32);
  if let Some(last) = index_bytes.last() {
    // Accept fixed 4-byte encoding (trailing zeroes ok) or variable length
    // with no trailing zero padding.
    if index_bytes.len() != 4 && *last == 0 {
      return None;
    }
  }
  let txid: String = txid_bytes
    .iter()
    .rev()
    .map(|b| format!("{b:02x}"))
    .collect();
  let mut index_arr = [0u8; 4];
  for (i, b) in index_bytes.iter().enumerate() {
    index_arr[i] = *b;
  }
  let index = u32::from_le_bytes(index_arr);
  Some(format!("{txid}i{index}"))
}

/// After the body is complete, remaining single-byte-key push pairs are tags.
/// Only tag 11 (delegate) is consumed today; unknown tags are ignored so new
/// fields do not break parsing.
fn parse_trailing_fields(push_datas: &[Vec<u8>], start: usize) -> Option<String> {
  let mut delegate: Option<String> = None;
  let mut i = start;
  while i + 1 < push_datas.len() {
    let key = &push_datas[i];
    if key.len() != 1 {
      break;
    }
    let value = &push_datas[i + 1];
    if key[0] == TAG_DELEGATE {
      // First delegate wins; later ones are ignored (same as take() on a map
      // that keeps the first value for a non-chunked tag).
      if delegate.is_none() {
        delegate = decode_inscription_id_field(value);
      }
    }
    i += 2;
  }
  delegate
}

/// `script_sig` is the pre-decoded scriptSig from `prepare_block`; that hex
/// decode is pure and is done in parallel ahead of this sequential pass.
fn process_inscription_candidate(
  tx: &RpcTx,
  script_sig: Option<&[u8]>,
  partial_inscription_chain: &store::Tree,
  undo: &mut UndoRecorder,
) -> Result<Option<ParsedInscriptionData>> {
  let Some(script) = script_sig.map(|s| s.to_vec()) else {
    return Ok(None);
  };

  let prev_txid = tx.vin.first().and_then(|vin| vin.txid.clone());
  let mut chain = if let Some(prev) = prev_txid.as_deref() {
    match partial_inscription_chain.get(prev.as_bytes())? {
      Some(raw) => {
        undo.remove(
          "partial_inscription_chain",
          partial_inscription_chain,
          prev.as_bytes(),
        )?;
        bincode::deserialize::<PartialInscriptionChain>(raw.as_ref())?
      }
      None => PartialInscriptionChain {
        start_txid: tx.txid.clone(),
        scripts: Vec::new(),
      },
    }
  } else {
    PartialInscriptionChain {
      start_txid: tx.txid.clone(),
      scripts: Vec::new(),
    }
  };

  chain.scripts.push(script);

  match parse_inscription_outcome(&chain.scripts) {
    InscriptionParseOutcome::Complete(content_type, body, delegate) => {
      Ok(Some(ParsedInscriptionData {
        content_type,
        body,
        delegate,
        inscription_txid: chain.start_txid,
      }))
    }
    InscriptionParseOutcome::Partial => {
      let serialized = bincode::serialize(&chain)?;
      BYTES_PARTIAL_CHAIN.fetch_add(serialized.len() as u64, AtomicOrdering::Relaxed);
      undo.insert(
        "partial_inscription_chain",
        partial_inscription_chain,
        tx.txid.as_bytes(),
        serialized,
      )?;
      Ok(None)
    }
    InscriptionParseOutcome::None => Ok(None),
  }
}

fn parse_inscription_outcome(scripts: &[Vec<u8>]) -> InscriptionParseOutcome {
  let Some(first) = scripts.first() else {
    return InscriptionParseOutcome::None;
  };
  let Some(mut push_datas) = decode_push_datas(first) else {
    return InscriptionParseOutcome::None;
  };

  if push_datas.len() < 3 || push_datas[0].as_slice() != b"ord" {
    return InscriptionParseOutcome::None;
  }

  let Some(mut npieces) = push_data_to_number(&push_datas[1]) else {
    return InscriptionParseOutcome::None;
  };
  if npieces == 0 {
    return InscriptionParseOutcome::None;
  }

  // Content type is optional. Empty push, missing MIME, or non-UTF-8 bytes all
  // become "" rather than rejecting the inscription - delegate-only envelopes
  // (e.g. doggy.market bone collection) declare neither type nor body.
  let content_type = str::from_utf8(&push_datas[2])
    .map(|s| s.to_string())
    .unwrap_or_default();
  let mut body = Vec::new();
  let mut script_idx = 0usize;
  let mut idx = 3usize;

  loop {
    while npieces > 0 && idx + 1 < push_datas.len() {
      let Some(next) = push_data_to_number(&push_datas[idx]) else {
        break;
      };
      if next != npieces - 1 {
        break;
      }
      body.extend_from_slice(&push_datas[idx + 1]);
      npieces -= 1;
      idx += 2;
    }

    if npieces == 0 {
      let delegate = parse_trailing_fields(&push_datas, idx);
      return InscriptionParseOutcome::Complete(content_type, body, delegate);
    }

    script_idx += 1;
    if script_idx >= scripts.len() {
      return InscriptionParseOutcome::Partial;
    }

    let Some(next_script_pushes) = decode_push_datas(&scripts[script_idx]) else {
      return InscriptionParseOutcome::None;
    };
    push_datas = next_script_pushes;
    if push_datas.len() < 2 {
      return InscriptionParseOutcome::None;
    }
    let Some(next) = push_data_to_number(&push_datas[0]) else {
      return InscriptionParseOutcome::None;
    };
    if next != npieces - 1 {
      return InscriptionParseOutcome::None;
    }
    idx = 0;
  }
}

fn decode_push_datas(script: &[u8]) -> Option<Vec<Vec<u8>>> {
  let mut bytes = script;
  let mut push_datas = Vec::new();

  while !bytes.is_empty() {
    if bytes[0] == 0 {
      push_datas.push(vec![]);
      bytes = &bytes[1..];
      continue;
    }

    if (81..=96).contains(&bytes[0]) {
      push_datas.push(vec![bytes[0] - 80]);
      bytes = &bytes[1..];
      continue;
    }

    if (1..=75).contains(&bytes[0]) {
      let len = usize::from(bytes[0]);
      if bytes.len() < len + 1 {
        return None;
      }
      push_datas.push(bytes[1..1 + len].to_vec());
      bytes = &bytes[1 + len..];
      continue;
    }

    if bytes[0] == 76 {
      if bytes.len() < 2 {
        return None;
      }
      let len = usize::from(bytes[1]);
      if bytes.len() < len + 2 {
        return None;
      }
      push_datas.push(bytes[2..2 + len].to_vec());
      bytes = &bytes[2 + len..];
      continue;
    }

    if bytes[0] == 77 {
      if bytes.len() < 3 {
        return None;
      }
      let len = usize::from(u16::from_le_bytes([bytes[1], bytes[2]]));
      if bytes.len() < len + 3 {
        return None;
      }
      push_datas.push(bytes[3..3 + len].to_vec());
      bytes = &bytes[3 + len..];
      continue;
    }

    if bytes[0] == 78 {
      if bytes.len() < 5 {
        return None;
      }
      let len = u32::from_le_bytes([bytes[1], bytes[2], bytes[3], bytes[4]]) as usize;
      if bytes.len() < len + 5 {
        return None;
      }
      push_datas.push(bytes[5..5 + len].to_vec());
      bytes = &bytes[5 + len..];
      continue;
    }

    // Doginal scriptSigs can contain trailing non-push opcodes (for example
    // OP_DROP chains). We only need the push prefix for inscription parsing.
    if push_datas.is_empty() {
      return None;
    }
    break;
  }

  Some(push_datas)
}

fn push_data_to_number(data: &[u8]) -> Option<usize> {
  if data.is_empty() {
    return Some(0);
  }

  if data.len() > 8 {
    return None;
  }

  let mut buf = [0u8; 8];
  buf[..data.len()].copy_from_slice(data);
  Some(u64::from_le_bytes(buf) as usize)
}

fn to_satoshis(value: f64) -> Result<u64> {
  if value.is_sign_negative() {
    return Err(anyhow!("negative output value"));
  }
  let sats = (value * 100_000_000.0).round();
  if sats < 0.0 || sats > u64::MAX as f64 {
    return Err(anyhow!("value out of range"));
  }
  Ok(sats as u64)
}

fn outpoint_key(txid: &str, vout: u32) -> String {
  format!("{txid}:{vout}")
}

fn address_outpoint_key(address: &str, txid: &str, vout: u32) -> String {
  format!("{address}|{txid}:{vout}")
}

fn encode_u64(v: u64) -> [u8; 8] {
  v.to_be_bytes()
}

fn decode_u64(b: &[u8]) -> Result<u64> {
  if b.len() != 8 {
    warn!("invalid u64 byte length: {}", b.len());
    return Err(anyhow!("invalid u64 bytes"));
  }
  let mut arr = [0u8; 8];
  arr.copy_from_slice(b);
  Ok(u64::from_be_bytes(arr))
}

fn encode_u128(v: u128) -> [u8; 16] {
  v.to_be_bytes()
}

fn decode_u128(b: &[u8]) -> Result<u128> {
  if b.len() != 16 {
    return Err(anyhow!("invalid u128 bytes"));
  }
  let mut arr = [0u8; 16];
  arr.copy_from_slice(b);
  Ok(u128::from_be_bytes(arr))
}

pub fn list_spendable_utxos_for_address(config: &Config, address: &str) -> Result<Vec<(String, u64)>> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let outpoints_by_address = db.open_tree("outpoints_by_address")?;
  let inscriptions_by_outpoint = db.open_tree("inscriptions_by_outpoint")?;
  let dune_balances_by_outpoint = db.open_tree("dune_balances_by_outpoint")?;

  let prefix = format!("{address}|");
  let mut candidates = Vec::new();
  for item in outpoints_by_address.scan_prefix(prefix.as_bytes())? {
    let (k, v) = item?;
    let key = String::from_utf8(k.to_vec()).context("invalid address/outpoint key utf8")?;
    let outpoint = key
      .split_once('|')
      .map(|(_, op)| op.to_string())
      .ok_or_else(|| anyhow!("invalid address outpoint key format"))?;
    candidates.push((outpoint, decode_u64(v.as_ref())?));
  }

  // Very few outpoints hold dunes, so read those once rather than seeking for
  // every candidate. The inscription check below still costs a read per outpoint
  // and dominates on a heavy address (about 50 s at ~800k inscriptions), which
  // is why the explorer only calls this from its UTXO tab.
  let mut dune_outpoints = HashSet::new();
  for item in dune_balances_by_outpoint.scan_prefix(b"")? {
    let (k, _v) = item?;
    let key = String::from_utf8(k.to_vec()).context("invalid dune key utf8")?;
    if let Some((outpoint, _)) = key.split_once('|') {
      dune_outpoints.insert(outpoint.to_string());
    }
  }

  let mut utxos = Vec::new();
  for chunk in candidates.chunks(4096) {
    // Inscriptions for an outpoint are stored as one list under the outpoint key.
    let keys: Vec<&str> = chunk.iter().map(|(outpoint, _)| outpoint.as_str()).collect();
    let inscribed = inscriptions_by_outpoint.multi_get(&keys)?;
    for ((outpoint, sats), hit) in chunk.iter().zip(inscribed) {
      if hit.is_none() && !dune_outpoints.contains(outpoint) {
        utxos.push((outpoint.clone(), *sats));
      }
    }
  }

  Ok(utxos)
}

pub fn list_inscriptions_for_address(
  config: &Config,
  address: &str,
  page: usize,
  limit: usize,
) -> Result<(usize, Vec<InscriptionRecord>)> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let inscriptions_by_address = db.open_tree("inscriptions_by_address")?;
  let inscriptions_by_id = db.open_tree("inscriptions_by_id")?;

  let prefix = format!("{address}|");
  let mut ids = Vec::new();
  for item in inscriptions_by_address.scan_prefix(prefix.as_bytes())? {
    let (k, _v) = item?;
    let key = String::from_utf8(k.to_vec()).context("invalid inscriptions_by_address key utf8")?;
    if let Some((_, id)) = key.split_once('|') {
      ids.push(id.to_string());
    }
  }

  ids.sort();
  ids.reverse();

  let total = ids.len();
  let start = page.saturating_sub(1).saturating_mul(limit);
  let end = std::cmp::min(start.saturating_add(limit), total);

  if start >= total {
    return Ok((total, Vec::new()));
  }

  let mut out = Vec::new();
  for id in &ids[start..end] {
    if let Some(raw) = inscriptions_by_id.get(id.as_bytes())? {
      out.push(decode_inscription_record(raw.as_ref())?);
    }
  }

  Ok((total, out))
}

pub fn get_inscription(config: &Config, inscription_id: &str) -> Result<Option<InscriptionRecord>> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let inscriptions_by_id = db.open_tree("inscriptions_by_id")?;

  let Some(raw) = inscriptions_by_id.get(inscription_id.as_bytes())? else {
    return Ok(None);
  };

  Ok(Some(decode_inscription_record(raw.as_ref())?))
}

pub fn get_inscription_content(
  config: &Config,
  inscription_id: &str,
) -> Result<Option<InscriptionContentRecord>> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let inscription_content = db.open_tree("inscription_content")?;
  let inscriptions_by_id = db.open_tree("inscriptions_by_id")?;

  // Follow delegate chain. Protocol: content of a delegate is served in place
  // of this inscription (type + body). Cap depth against cycles.
  const MAX_DELEGATE_HOPS: usize = 5;
  let mut current_id = inscription_id.to_string();
  let mut seen = std::collections::HashSet::new();
  seen.insert(current_id.clone());

  for _ in 0..=MAX_DELEGATE_HOPS {
    // Resolve metadata (including delegate) from content row or inscription row.
    let (content_type, body, delegate) = if let Some(raw) =
      inscription_content.get(current_id.as_bytes())?
    {
      let rec = decode_inscription_content(raw.as_ref())?;
      (rec.content_type, rec.body, rec.delegate)
    } else if let Some(raw) = inscriptions_by_id.get(current_id.as_bytes())? {
      let meta = decode_inscription_record(raw.as_ref())?;
      (meta.content_type, Vec::new(), meta.delegate)
    } else {
      return Ok(None);
    };

    match delegate {
      Some(next) if seen.insert(next.clone()) => {
        // Always follow when present - even if this row also has a body.
        current_id = next;
      }
      _ => {
        // Terminal: no delegate, cycle, or hop exhausted after follow attempts.
        // If we never loaded a content row for this id, there is nothing to
        // serve (metadata-only with no further hop).
        if body.is_empty() && inscription_content.get(current_id.as_bytes())?.is_none() {
          return Ok(None);
        }
        return Ok(Some(InscriptionContentRecord {
          content_type,
          body,
          delegate: None,
        }));
      }
    }
  }

  Ok(None)
}

/// Decode content records written both before and after the delegate field
/// was added. Old indexes only store (content_type, body); missing the third
/// field must not 500 the content endpoint.
fn decode_inscription_content(raw: &[u8]) -> Result<InscriptionContentRecord> {
  if let Ok(rec) = bincode::deserialize::<InscriptionContentRecord>(raw) {
    return Ok(rec);
  }
  #[derive(Deserialize)]
  struct Legacy {
    content_type: String,
    body: Vec<u8>,
  }
  let leg: Legacy = bincode::deserialize(raw).context("decode inscription content")?;
  Ok(InscriptionContentRecord {
    content_type: leg.content_type,
    body: leg.body,
    delegate: None,
  })
}

/// Same dual-format story as content: records written before `delegate` was
/// added still deserialize.
fn decode_inscription_record(raw: &[u8]) -> Result<InscriptionRecord> {
  if let Ok(rec) = bincode::deserialize::<InscriptionRecord>(raw) {
    return Ok(rec);
  }
  #[derive(Deserialize)]
  struct Legacy {
    id: String,
    txid: String,
    vout: u32,
    offset: u64,
    satoshis: u64,
    content_type: String,
    address: String,
  }
  let leg: Legacy = bincode::deserialize(raw).context("decode inscription record")?;
  Ok(InscriptionRecord {
    id: leg.id,
    txid: leg.txid,
    vout: leg.vout,
    offset: leg.offset,
    satoshis: leg.satoshis,
    content_type: leg.content_type,
    address: leg.address,
    delegate: None,
  })
}

pub fn list_drc20_holdings(config: &Config, address: &str) -> Result<Vec<Drc20Holding>> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let balance_tree = db.open_tree("drc20_balance")?;
  let token_tree = db.open_tree("drc20_token_info")?;

  let prefix = format!("B|{address}|");
  let mut out = Vec::new();
  for item in balance_tree.scan_prefix(prefix.as_bytes())? {
    let (_k, v) = item?;
    let bal: Drc20Balance = bincode::deserialize(v.as_ref())?;
    if bal.overall == 0 {
      continue;
    }
    let decimals = match token_tree.get(token_key(&bal.tick).as_bytes())? {
      Some(raw) => bincode::deserialize::<Drc20TokenInfo>(raw.as_ref())?.decimals,
      None => 0,
    };
    let available = bal.overall.saturating_sub(bal.transferable);
    out.push(Drc20Holding {
      tick: bal.tick,
      available: available.to_string(),
      transferable: bal.transferable.to_string(),
      total: bal.overall.to_string(),
      decimals,
    });
  }

  out.sort_by(|a, b| a.tick.cmp(&b.tick));
  Ok(out)
}

/// Looks up a single dogemap by block number. `None` means unclaimed.
pub fn get_dogemap(config: &Config, number: u64) -> Result<Option<DogemapEntry>> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let tree = db.open_tree("dogemap_by_number")?;

  match tree.get(encode_u64(number))? {
    Some(raw) => Ok(Some(
      bincode::deserialize(raw.as_ref()).context("decode dogemap entry")?,
    )),
    None => Ok(None),
  }
}

/// Lists dogemaps currently owned by an address, in ascending number order.
///
/// Reads the by_address index for the numbers, then resolves each against the
/// authoritative by_number tree. The extra lookup is deliberate: it means a
/// stale index key can never invent ownership, it can only be skipped.
pub fn list_dogemaps_for_address(config: &Config, address: &str) -> Result<Vec<DogemapEntry>> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let by_address = db.open_tree("dogemap_by_address")?;
  let by_number = db.open_tree("dogemap_by_number")?;

  let prefix = format!("{address}|");
  let mut out = Vec::new();
  for item in by_address.scan_prefix(prefix.as_bytes())? {
    let (key, _) = item?;
    let key_str = String::from_utf8_lossy(key.as_ref()).to_string();
    let Some((_, number_str)) = key_str.rsplit_once('|') else {
      continue;
    };
    let Ok(number) = number_str.trim_start_matches('0').parse::<u64>().or_else(|_| {
      // A key of all zeros is dogemap 0, whose trimmed form is empty.
      if number_str.bytes().all(|b| b == b'0') {
        Ok(0)
      } else {
        Err(())
      }
    }) else {
      continue;
    };

    if let Some(raw) = by_number.get(encode_u64(number))? {
      let entry: DogemapEntry =
        bincode::deserialize(raw.as_ref()).context("decode dogemap entry")?;
      if entry.owner == address {
        out.push(entry);
      }
    }
  }

  out.sort_by_key(|e| e.number);
  Ok(out)
}

/// Approximate number of dogemaps claimed.
///
/// Estimated rather than counted: an exact count walks all ~5.6M keys, which
/// pulled the whole tree through the block cache and spiked the process from
/// 6 GB to 16 GB when served from an API handler.
pub fn dogemap_count(config: &Config) -> Result<u64> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  db.open_tree("dogemap_by_number")?.approximate_len()
}

/// Exact number of claimed dogemaps. A full pass over the claims, so callers
/// cache it; `dogemap_count` is RocksDB's estimate and can run several percent
/// high, enough to exceed the number of blocks that exist.
pub fn dogemap_count_exact(config: &Config) -> Result<u64> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let mut n = 0u64;
  db.open_tree("dogemap_by_number")?.for_each_prefix(b"", |_, _| {
    n += 1;
    Ok(true)
  })?;
  Ok(n)
}

pub fn list_dune_holdings(config: &Config, address: &str) -> Result<Vec<DuneHolding>> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let outpoints_by_address = db.open_tree("outpoints_by_address")?;
  let dune_balances_by_outpoint = db.open_tree("dune_balances_by_outpoint")?;
  let dune_meta_by_id = db.open_tree("dune_meta_by_id")?;

  // Walks dune balances and tests ownership, rather than seeking dunes for every
  // outpoint of the address: see list_spendable_utxos_for_address.
  let mut aggregate: HashMap<String, u128> = HashMap::new();
  for d in dune_balances_by_outpoint.scan_prefix(b"")? {
    let (dk, dv) = d?;
    let dk = String::from_utf8(dk.to_vec()).context("invalid dune key utf8")?;
    let (outpoint, dune_id) = dk
      .split_once('|')
      .ok_or_else(|| anyhow!("invalid dune balance key"))?;
    let owner_key = format!("{address}|{outpoint}");
    if outpoints_by_address.get(owner_key.as_bytes())?.is_none() {
      continue;
    }
    *aggregate.entry(dune_id.to_string()).or_default() += decode_u128(dv.as_ref())?;
  }

  let mut holdings = Vec::new();
  for (dune_id, balance) in aggregate {
    if balance == 0 {
      continue;
    }
    if let Some(raw_meta) = dune_meta_by_id.get(dune_id.as_bytes())? {
      let meta: DuneMeta = bincode::deserialize(raw_meta.as_ref())?;
      holdings.push(DuneHolding {
        id: meta.id,
        name: meta.name,
        symbol: meta.symbol,
        divisibility: meta.divisibility,
        balance: balance.to_string(),
      });
    }
  }
  holdings.sort_by(|a, b| a.id.cmp(&b.id));
  Ok(holdings)
}

pub fn list_dune_utxos(config: &Config, address: &str, dune_id: &str) -> Result<Vec<DuneUtxo>> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let outpoints_by_address = db.open_tree("outpoints_by_address")?;
  let dune_balances_by_outpoint = db.open_tree("dune_balances_by_outpoint")?;
  let prefix = format!("{address}|");

  let mut out = Vec::new();
  for item in outpoints_by_address.scan_prefix(prefix.as_bytes())? {
    let (k, v) = item?;
    let key = String::from_utf8(k.to_vec()).context("invalid address key utf8")?;
    let outpoint = key
      .split_once('|')
      .map(|(_, op)| op.to_string())
      .ok_or_else(|| anyhow!("invalid outpoint key"))?;
    let sats = decode_u64(v.as_ref())?;

    let dune_key = format!("{outpoint}|{dune_id}");
    let Some(raw_amt) = dune_balances_by_outpoint.get(dune_key.as_bytes())? else {
      continue;
    };
    let balance = decode_u128(raw_amt.as_ref())?;
    if balance == 0 {
      continue;
    }

    if let Some((txid, vout)) = outpoint.split_once(':')
      && let Ok(vout) = vout.parse::<u32>()
    {
      out.push(DuneUtxo {
        txid: txid.to_string(),
        vout,
        balance: balance.to_string(),
        satoshis: sats,
      });
    }
  }
  Ok(out)
}

/// Writes raw rows through the same shared store handle the read functions
/// use, then flushes. For tests in other crates: RocksDB cannot be opened a
/// second time by a process that already holds it.
#[doc(hidden)]
pub fn seed_rows(config: &Config, rows: &[(&str, Vec<u8>, Vec<u8>)]) -> Result<()> {
  let db = open_db(&format!("{}/spookyord.rocksdb", config.data_dir))?;
  for (tree, key, value) in rows {
    db.open_tree(tree)?.insert(key, value)?;
  }
  db.flush()
}

/// Fetches inscriptions by id, preserving order and skipping unknown ids.
///
/// The explorer checks every transaction of a block at once, so this goes
/// through multi_get rather than one point get per id.
pub fn find_inscriptions(config: &Config, ids: &[String]) -> Result<Vec<InscriptionRecord>> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let inscriptions_by_id = db.open_tree("inscriptions_by_id")?;

  let mut out = Vec::new();
  for raw in inscriptions_by_id.multi_get(ids)?.into_iter().flatten() {
    out.push(decode_inscription_record(raw.as_ref())?);
  }
  Ok(out)
}

/// Token-level DRC-20 data. Amounts are raw integers scaled by 10^decimals,
/// exactly as stored, so clients format them without losing precision.
#[derive(Debug, Serialize, Clone)]
pub struct Drc20TokenSummary {
  pub tick: String,
  pub supply: String,
  pub minted: String,
  pub limit_per_mint: String,
  pub decimals: u8,
  pub minted_percent: f64,
}

/// Every deployed DRC-20 token. This is a full scan, so callers should cache.
pub fn list_drc20_tokens(config: &Config) -> Result<Vec<Drc20TokenSummary>> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let token_tree = db.open_tree("drc20_token_info")?;

  let mut out = Vec::new();
  for item in token_tree.scan_prefix(b"")? {
    let (_k, v) = item?;
    let info: Drc20TokenInfo = bincode::deserialize(v.as_ref())?;
    let minted_percent = if info.supply == 0 {
      0.0
    } else {
      (info.minted as f64 / info.supply as f64) * 100.0
    };
    out.push(Drc20TokenSummary {
      tick: info.tick,
      supply: info.supply.to_string(),
      minted: info.minted.to_string(),
      limit_per_mint: info.limit_per_mint.to_string(),
      decimals: info.decimals,
      minted_percent,
    });
  }
  Ok(out)
}

/// Token-level dune data, joined from the metadata and entry trees.
#[derive(Debug, Serialize, Clone)]
pub struct DuneSummary {
  pub id: String,
  pub name: String,
  pub symbol: String,
  pub divisibility: u8,
  pub etched_height: u64,
  pub premine: String,
  pub supply: String,
  pub burned: String,
  pub mints: String,
  pub cap: Option<String>,
  pub limit: Option<String>,
}

/// Every etched dune. This is a full scan, so callers should cache.
pub fn list_dunes(config: &Config) -> Result<Vec<DuneSummary>> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let dune_meta_by_id = db.open_tree("dune_meta_by_id")?;
  let dune_entry_by_id = db.open_tree("dune_entry_by_id")?;

  let mut out = Vec::new();
  for item in dune_meta_by_id.scan_prefix(b"")? {
    let (k, v) = item?;
    let meta: DuneMeta = bincode::deserialize(v.as_ref())?;
    let Some(raw_entry) = dune_entry_by_id.get(k.to_vec())? else {
      continue;
    };
    let entry: DuneEntryLite = bincode::deserialize(raw_entry.as_ref())?;
    out.push(DuneSummary {
      id: meta.id,
      name: meta.name,
      symbol: meta.symbol,
      divisibility: meta.divisibility,
      etched_height: entry.etched_height,
      premine: entry.premine.to_string(),
      supply: entry.supply.to_string(),
      burned: entry.burned.to_string(),
      mints: entry.mints.to_string(),
      cap: entry.terms.as_ref().and_then(|t| t.cap).map(|v| v.to_string()),
      limit: entry.terms.as_ref().and_then(|t| t.limit).map(|v| v.to_string()),
    });
  }
  Ok(out)
}

/// One DRC-20 holder: raw amounts, scaled by 10^decimals.
#[derive(Debug, Serialize, Clone)]
pub struct Drc20HolderRow {
  pub address: String,
  pub total: String,
  pub transferable: String,
}

/// Holders of one tick: how many, and the largest first.
#[derive(Debug, Serialize, Clone, Default)]
pub struct Drc20Holders {
  pub holders: usize,
  /// Sum of every holder's balance, raw.
  pub held: String,
  pub top: Vec<Drc20HolderRow>,
}

/// Holders of one tick, keeping the `keep` largest.
///
/// Balances are keyed by address first (`B|address|tick`), so listing one
/// tick's holders means reading every balance. The pass is streamed and skips
/// other ticks by key suffix before decoding anything; callers cache the
/// result per tick. Holding every tick's list in memory instead would approach
/// the size of the whole balance tree.
pub fn drc20_holders(config: &Config, tick: &str, keep: usize) -> Result<Drc20Holders> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let balance_tree = db.open_tree("drc20_balance")?;

  let suffix = format!("|{tick}");
  let mut holders = 0usize;
  let mut held: u128 = 0;
  // Sorted descending and trimmed as it goes, so memory is bounded by `keep`.
  let mut top: Vec<(u128, u128, String)> = Vec::new();

  balance_tree.for_each_prefix(b"B|", |k, v| {
    if !k.ends_with(suffix.as_bytes()) {
      return Ok(true);
    }
    let bal: Drc20Balance = bincode::deserialize(v)?;
    // The suffix test alone would also match an address ending in "|tick".
    if bal.tick != tick || bal.overall == 0 {
      return Ok(true);
    }
    let key = str::from_utf8(k).context("balance key utf8")?;
    let address = key
      .strip_prefix("B|")
      .and_then(|rest| rest.strip_suffix(suffix.as_str()))
      .ok_or_else(|| anyhow!("invalid balance key {key}"))?
      .to_string();
    holders += 1;
    held = held.saturating_add(bal.overall);
    if top.len() < keep || top.last().is_some_and(|(min, _, _)| bal.overall > *min) {
      let pos = top.partition_point(|(amt, _, _)| *amt >= bal.overall);
      top.insert(pos, (bal.overall, bal.transferable, address));
      top.truncate(keep);
    }
    Ok(true)
  })?;

  Ok(Drc20Holders {
    holders,
    held: held.to_string(),
    top: top
      .into_iter()
      .map(|(total, transferable, address)| Drc20HolderRow {
        address,
        total: total.to_string(),
        transferable: transferable.to_string(),
      })
      .collect(),
  })
}

/// Full detail for one dune: summary, mint terms and every holder.
#[derive(Debug, Serialize, Clone)]
pub struct DuneDetail {
  #[serde(flatten)]
  pub summary: DuneSummary,
  pub height_start: Option<u64>,
  pub height_end: Option<u64>,
  pub offset_start: Option<u64>,
  pub offset_end: Option<u64>,
  pub holders: Vec<DuneHolderRow>,
  /// Units held in unspent outputs, raw.
  pub circulating: String,
}

#[derive(Debug, Serialize, Clone)]
pub struct DuneHolderRow {
  pub address: String,
  pub balance: String,
  pub outputs: usize,
}

/// One dune with its holders. Dune balances live on outputs, and few outputs
/// hold any, so this walks the balance tree and resolves each output's owner.
pub fn get_dune_detail(config: &Config, dune_id: &str) -> Result<Option<DuneDetail>> {
  let db_path = format!("{}/spookyord.rocksdb", config.data_dir);
  let db = open_db(&db_path)?;
  let dune_meta_by_id = db.open_tree("dune_meta_by_id")?;
  let dune_entry_by_id = db.open_tree("dune_entry_by_id")?;
  let dune_balances_by_outpoint = db.open_tree("dune_balances_by_outpoint")?;
  let utxo_by_outpoint = db.open_tree("utxo_by_outpoint")?;

  let Some(raw_meta) = dune_meta_by_id.get(dune_id.as_bytes())? else {
    return Ok(None);
  };
  let Some(raw_entry) = dune_entry_by_id.get(dune_id.as_bytes())? else {
    return Ok(None);
  };
  let meta: DuneMeta = bincode::deserialize(raw_meta.as_ref())?;
  let entry: DuneEntryLite = bincode::deserialize(raw_entry.as_ref())?;
  let terms = entry.terms.clone().unwrap_or_default();

  let mut by_owner: HashMap<String, (u128, usize)> = HashMap::new();
  let mut circulating: u128 = 0;
  for item in dune_balances_by_outpoint.scan_prefix(b"")? {
    let (k, v) = item?;
    let key = String::from_utf8(k.to_vec()).context("invalid dune key utf8")?;
    let Some((outpoint, id)) = key.split_once('|') else {
      continue;
    };
    if id != dune_id {
      continue;
    }
    let amount = decode_u128(v.as_ref())?;
    circulating = circulating.saturating_add(amount);
    let owner = match utxo_by_outpoint.get(outpoint.as_bytes())? {
      Some(raw) => bincode::deserialize::<UtxoRecord>(raw.as_ref())
        .map(|u| u.address)
        .unwrap_or_default(),
      None => String::new(),
    };
    let slot = by_owner.entry(owner).or_insert((0, 0));
    slot.0 = slot.0.saturating_add(amount);
    slot.1 += 1;
  }
  let mut ranked: Vec<(u128, String, usize)> = by_owner
    .into_iter()
    .map(|(address, (balance, outputs))| (balance, address, outputs))
    .collect();
  ranked.sort_by(|a, b| b.0.cmp(&a.0).then_with(|| a.1.cmp(&b.1)));
  let holders = ranked
    .into_iter()
    .map(|(balance, address, outputs)| DuneHolderRow { address, balance: balance.to_string(), outputs })
    .collect();

  Ok(Some(DuneDetail {
    summary: DuneSummary {
      id: meta.id,
      name: meta.name,
      symbol: meta.symbol,
      divisibility: meta.divisibility,
      etched_height: entry.etched_height,
      premine: entry.premine.to_string(),
      supply: entry.supply.to_string(),
      burned: entry.burned.to_string(),
      mints: entry.mints.to_string(),
      cap: terms.cap.map(|v| v.to_string()),
      limit: terms.limit.map(|v| v.to_string()),
    },
    height_start: terms.height_start,
    height_end: terms.height_end,
    offset_start: terms.offset_start,
    offset_end: terms.offset_end,
    holders,
    circulating: circulating.to_string(),
  }))
}

// ---- token detail: deploys, activity, holder counts, etchings ----

pub fn get_drc20_deploy(config: &Config, tick: &str) -> Result<Option<Drc20Deploy>> {
  let db = open_db(&format!("{}/spookyord.rocksdb", config.data_dir))?;
  match db.open_tree("drc20_deploy")?.get(tick.as_bytes())? {
    Some(raw) => Ok(Some(bincode::deserialize(raw.as_ref())?)),
    None => Ok(None),
  }
}

/// A page of a token's activity, newest first, and whether more follows.
pub fn list_activity(config: &Config, scope: &str, offset: usize, limit: usize) -> Result<(Vec<ActivityEvent>, bool)> {
  let db = open_db(&format!("{}/spookyord.rocksdb", config.data_dir))?;
  let tree = db.open_tree("token_activity")?;
  let mut seen = 0usize;
  let mut out = Vec::new();
  let mut more = false;
  tree.for_each_prefix(format!("{scope}|"), |_, v| {
    if seen < offset {
      seen += 1;
      return Ok(true);
    }
    if out.len() == limit {
      more = true;
      return Ok(false);
    }
    out.push(bincode::deserialize::<ActivityEvent>(v)?);
    Ok(true)
  })?;
  Ok((out, more))
}

/// Holder count for every DRC-20 tick, in one pass over the balances.
pub fn drc20_holder_counts(config: &Config) -> Result<HashMap<String, u32>> {
  let db = open_db(&format!("{}/spookyord.rocksdb", config.data_dir))?;
  let mut counts: HashMap<String, u32> = HashMap::new();
  db.open_tree("drc20_balance")?.for_each_prefix(b"B|", |_, v| {
    let bal: Drc20Balance = bincode::deserialize(v)?;
    if bal.overall > 0 {
      *counts.entry(bal.tick).or_default() += 1;
    }
    Ok(true)
  })?;
  Ok(counts)
}

/// Holder count for every dune: distinct owners of the outputs holding it.
pub fn dune_holder_counts(config: &Config) -> Result<HashMap<String, u32>> {
  let db = open_db(&format!("{}/spookyord.rocksdb", config.data_dir))?;
  let balances = db.open_tree("dune_balances_by_outpoint")?;
  let utxos = db.open_tree("utxo_by_outpoint")?;
  let mut owners: HashMap<String, HashSet<String>> = HashMap::new();
  for item in balances.scan_prefix(b"")? {
    let (k, v) = item?;
    if decode_u128(v.as_ref())? == 0 {
      continue;
    }
    let key = String::from_utf8(k.to_vec()).context("invalid dune key utf8")?;
    let Some((outpoint, dune_id)) = key.split_once('|') else {
      continue;
    };
    let owner = match utxos.get(outpoint.as_bytes())? {
      Some(raw) => bincode::deserialize::<UtxoRecord>(raw.as_ref()).map(|u| u.address).unwrap_or_default(),
      None => String::new(),
    };
    owners.entry(dune_id.to_string()).or_default().insert(owner);
  }
  Ok(owners.into_iter().map(|(id, set)| (id, set.len() as u32)).collect())
}

/// Where a dune was etched, read back from the etching block.
#[derive(Debug, Serialize, Clone)]
pub struct DuneEtching {
  pub txid: String,
  pub time: u64,
  /// Owner of the etching transaction's first input: who paid for it.
  pub etched_by: Option<String>,
  /// Where the premine went. None when edicts split it, or a cenotaph burnt it.
  pub premine_to: Option<String>,
  pub premine_burned: bool,
}

fn indexer_rpc_client() -> Result<&'static Client> {
  static CLIENT: OnceLock<Client> = OnceLock::new();
  if let Some(c) = CLIENT.get() {
    return Ok(c);
  }
  let built = Client::builder().timeout(Duration::from_secs(60)).build().context("build rpc client")?;
  Ok(CLIENT.get_or_init(|| built))
}

fn vout_address(vout: &RpcVout) -> Option<String> {
  vout.script_pub_key.addresses.as_ref().and_then(|a| a.first()).cloned()
}

/// Finds the transaction that etched `dune_id` in block `etched_height`,
/// using the same name derivation as indexing: an explicit name, or the
/// height and position of the etching transaction.
pub async fn find_dune_etching(config: &Config, dune_id: &str, etched_height: u64) -> Result<Option<DuneEtching>> {
  let client = indexer_rpc_client()?;
  let hash: String = rpc_call(client, config, "getblockhash", serde_json::json!([etched_height])).await?;
  let block: RpcBlock = rpc_call(client, config, "getblock", serde_json::json!([hash, 2])).await?;
  for (tx_index, tx) in block.tx.iter().enumerate() {
    let Some(stone) = parse_dunestone(tx) else {
      continue;
    };
    let Some(etch) = stone.etching.as_ref() else {
      continue;
    };
    let numeric = etch
      .dune
      .unwrap_or_else(|| ((etched_height as u128) << 16) | (tx_index as u128 & 0xFFFF));
    if format!("DOGECOIN:{}", dune_name(numeric)) != dune_id {
      continue;
    }
    let premine_burned = stone.cenotaph && etch.premine > 0;
    let split = stone.edicts.iter().any(|(id, _, _)| *id == 0);
    let premine_to = if etch.premine == 0 || stone.cenotaph || split {
      None
    } else {
      stone
        .pointer
        .filter(|p| *p < tx.vout.len())
        .or_else(|| tx.vout.iter().position(|v| !is_op_return(v)))
        .and_then(|i| vout_address(&tx.vout[i]))
    };
    let etched_by = match (tx.vin.first().and_then(|v| v.txid.clone()), tx.vin.first().and_then(|v| v.vout)) {
      (Some(prev), Some(n)) => {
        let prev_tx: RpcTx = rpc_call(client, config, "getrawtransaction", serde_json::json!([prev, true])).await?;
        prev_tx.vout.iter().find(|o| o.n == n).and_then(vout_address)
      }
      _ => None,
    };
    return Ok(Some(DuneEtching { txid: tx.txid.clone(), time: block.time.unwrap_or(0), etched_by, premine_to, premine_burned }));
  }
  Ok(None)
}

const DEPLOY_BACKFILL_KEY: &[u8] = b"drc20_deploy_backfill_v1";
const ACTIVITY_SINCE_KEY: &[u8] = b"activity_since";

/// First block whose token activity was recorded, once recording has begun.
pub fn activity_since(config: &Config) -> Result<Option<u64>> {
  let db = open_db(&format!("{}/spookyord.rocksdb", config.data_dir))?;
  match db.open_tree("meta")?.get(ACTIVITY_SINCE_KEY)? {
    Some(raw) => Ok(Some(decode_u64(raw.as_ref())?)),
    None => Ok(None),
  }
}

pub fn drc20_deploy_backfill_done(config: &Config) -> Result<bool> {
  let db = open_db(&format!("{}/spookyord.rocksdb", config.data_dir))?;
  Ok(db.open_tree("meta")?.get(DEPLOY_BACKFILL_KEY)?.is_some())
}

/// One-off: records deploy details for tokens deployed before deploys were
/// recorded during indexing. Runs alongside the indexer and only ever adds
/// rows that are missing.
///
/// Every stored inscription is read once, and a deploy inscription is a
/// candidate for a tick only if it passes the same validation as indexing and
/// its supply, limit and decimals equal what the index holds for that tick:
/// the accepted deploy is what created those values. Among candidates the
/// earliest in chain order is the deploy, as first deploy wins.
pub async fn backfill_drc20_deploys(config: Config) -> Result<()> {
  if drc20_deploy_backfill_done(&config)? {
    return Ok(());
  }
  info!("drc20 deploy backfill: scanning stored inscriptions for past deploys");
  let started = Instant::now();
  let scan_config = config.clone();
  let candidates = tokio::task::spawn_blocking(move || -> Result<HashMap<String, Vec<String>>> {
    let db = open_db(&format!("{}/spookyord.rocksdb", scan_config.data_dir))?;
    let content = db.open_tree("inscription_content")?;
    let tokens = db.open_tree("drc20_token_info")?;
    let deploys = db.open_tree("drc20_deploy")?;
    let mut by_tick: HashMap<String, Vec<String>> = HashMap::new();
    let mut scanned = 0u64;
    content.for_each_prefix(b"", |k, v| {
      scanned += 1;
      if scanned % 5_000_000 == 0 {
        info!("drc20 deploy backfill: {} inscriptions read", scanned);
      }
      // Deploys are a few hundred bytes of JSON; skip images unread.
      if v.len() > 4096 {
        return Ok(true);
      }
      let Ok(rec) = decode_inscription_content(v) else {
        return Ok(true);
      };
      let Some(Drc20Action::Deploy { tick, max_supply, mint_limit, decimals }) = parse_drc20_action(&rec.content_type, &rec.body) else {
        return Ok(true);
      };
      let Ok(tick) = canonical_tick(&tick) else {
        return Ok(true);
      };
      let Some((supply, limit, dec)) = validate_drc20_deploy(&max_supply, mint_limit.as_deref(), decimals.as_deref()) else {
        return Ok(true);
      };
      let Some(raw) = tokens.get(token_key(&tick).as_bytes())? else {
        return Ok(true);
      };
      let info: Drc20TokenInfo = bincode::deserialize(raw.as_ref())?;
      if (info.supply, info.limit_per_mint, info.decimals) != (supply, limit, dec) || deploys.get(tick.as_bytes())?.is_some() {
        return Ok(true);
      }
      by_tick.entry(tick).or_default().push(String::from_utf8_lossy(k).to_string());
      Ok(true)
    })?;
    info!("drc20 deploy backfill: {} inscriptions read, {} ticks to resolve", scanned, by_tick.len());
    Ok(by_tick)
  })
  .await
  .context("deploy scan task")??;

  let client = indexer_rpc_client()?;
  let db = open_db(&format!("{}/spookyord.rocksdb", config.data_dir))?;
  let deploys = db.open_tree("drc20_deploy")?;
  let mut headers: HashMap<String, (u64, u64)> = HashMap::new();
  let mut positions: HashMap<String, Vec<String>> = HashMap::new();
  let (mut recorded, mut unresolved) = (0usize, 0usize);

  for (i, (tick, ids)) in candidates.into_iter().enumerate() {
    if i > 0 && i % 5000 == 0 {
      info!("drc20 deploy backfill: {} ticks resolved", i);
    }
    // Step 1: where each candidate was confirmed.
    let mut resolved: Vec<(u64, String, Drc20Deploy)> = Vec::new(); // (height, block hash, deploy)
    for id in ids {
      let Some(txid) = id.strip_suffix("i0") else {
        continue;
      };
      let Ok(tx) = rpc_call::<Value>(client, &config, "getrawtransaction", serde_json::json!([txid, true])).await else {
        continue;
      };
      let Some(hash) = tx["blockhash"].as_str().map(str::to_string) else {
        continue;
      };
      let (height, time) = match headers.get(&hash) {
        Some(h) => *h,
        None => {
          let header: Value = rpc_call(client, &config, "getblockheader", serde_json::json!([hash])).await?;
          let h = (header["height"].as_u64().unwrap_or(0), header["time"].as_u64().unwrap_or(0));
          headers.insert(hash.clone(), h);
          h
        }
      };
      // The inscription starts on the reveal's first output, and the deploy
      // is credited to whoever that output pays.
      let deployer = tx["vout"][0]["scriptPubKey"]["addresses"][0].as_str().unwrap_or("").to_string();
      resolved.push((height, hash, Drc20Deploy { inscription_id: id.clone(), txid: txid.to_string(), deployer, height, time }));
    }

    // Step 2: the earliest. Position in the block breaks a tie on height and
    // is only fetched when there is one.
    let best = match resolved.iter().map(|(h, _, _)| *h).min() {
      None => None,
      Some(min) => {
        let mut tied: Vec<(String, Drc20Deploy)> =
          resolved.into_iter().filter(|(h, _, _)| *h == min).map(|(_, hash, d)| (hash, d)).collect();
        if tied.len() == 1 {
          tied.pop().map(|(_, d)| d)
        } else {
          let hash = tied[0].0.clone();
          if !positions.contains_key(&hash) {
            let block: Value = rpc_call(client, &config, "getblock", serde_json::json!([hash, 1])).await?;
            let txids = block["tx"].as_array().map(|a| a.iter().filter_map(|t| t.as_str().map(str::to_string)).collect()).unwrap_or_default();
            positions.insert(hash.clone(), txids);
          }
          let order = &positions[&hash];
          tied
            .into_iter()
            .min_by_key(|(_, d)| order.iter().position(|t| *t == d.txid).unwrap_or(usize::MAX))
            .map(|(_, d)| d)
        }
      }
    };
    match best {
      Some(deploy) if deploys.get(tick.as_bytes())?.is_none() => {
        deploys.insert(tick.as_bytes(), bincode::serialize(&deploy)?)?;
        recorded += 1;
      }
      Some(_) => {}
      None => unresolved += 1,
    }
  }

  db.open_tree("meta")?.insert(DEPLOY_BACKFILL_KEY, b"1")?;
  db.flush()?;
  info!(
    "drc20 deploy backfill: done in {:.0?}: {} deploys recorded, {} ticks unresolved",
    started.elapsed(),
    recorded,
    unresolved
  );
  Ok(())
}

/// Single node RPC for the API layer, failing fast.
///
/// Deliberately not `rpc_call`: the node answers an unknown txid or hash with
/// HTTP 500, which `rpc_call` treats as transient and retries for seconds. That
/// is right for the indexer but would stall every failed explorer lookup.
pub async fn node_rpc(config: &Config, method: &str, params: Value) -> Result<Value> {
  static CLIENT: OnceLock<Client> = OnceLock::new();
  let client = match CLIENT.get() {
    Some(client) => client,
    None => {
      let built = Client::builder()
        .timeout(Duration::from_secs(20))
        .build()
        .context("build rpc client")?;
      CLIENT.get_or_init(|| built)
    }
  };

  let req = JsonRpcRequest {
    jsonrpc: "1.0",
    id: "spookyord-api",
    method,
    params,
  };
  let resp: JsonRpcResponse<Value> = client
    .post(&config.rpc_url)
    .basic_auth(&config.rpc_user, Some(&config.rpc_password))
    .json(&req)
    .send()
    .await
    .context("send rpc request")?
    .json()
    .await
    .context("decode rpc json")?;

  if let Some(err) = resp.error {
    return Err(anyhow!("rpc error: {}", err.message));
  }
  resp.result.ok_or_else(|| anyhow!("missing rpc result for method {method}"))
}

async fn rpc_call<T: for<'de> Deserialize<'de>>(
  client: &Client,
  cfg: &Config,
  method: &str,
  params: serde_json::Value,
) -> Result<T> {
  let mut attempt = 0u32;
  loop {
    attempt += 1;
    let req = JsonRpcRequest {
      jsonrpc: "1.0",
      id: "spookyord",
      method,
      params: params.clone(),
    };

    let call = async {
      let resp: JsonRpcResponse<T> = client
        .post(&cfg.rpc_url)
        .basic_auth(&cfg.rpc_user, Some(&cfg.rpc_password))
        .json(&req)
        .send()
        .await
        .context("send rpc request")?
        .error_for_status()
        .context("rpc http status error")?
        .json()
        .await
        .context("decode rpc json")?;

      if let Some(err) = resp.error {
        return Err(anyhow!("rpc error: {}", err.message));
      }

      resp.result.ok_or_else(|| anyhow!("missing rpc result for method {method}"))
    }
    .await;

    match call {
      Ok(v) => return Ok(v),
      Err(err) => {
        let retryable = err
          .chain()
          .find_map(|cause| cause.downcast_ref::<reqwest::Error>())
          .map(|e| e.is_timeout() || matches!(e.status(), Some(s) if s.is_server_error()))
          .unwrap_or(false);

        if retryable && attempt < 8 {
          let delay_ms = (100u64).saturating_mul(2u64.saturating_pow(attempt - 1)).min(5_000);
          warn!(
            "transient rpc failure on {} (attempt {}/8): {}. retrying in {}ms",
            method, attempt, err, delay_ms
          );
          sleep(Duration::from_millis(delay_ms)).await;
          continue;
        }

        return Err(err);
      }
    }
  }
}

fn open_db(db_path: &str) -> Result<store::Db> {
  static DB: OnceLock<store::Db> = OnceLock::new();
  // Serialises the first open. RocksDB can be opened once per process, and
  // without this two callers starting together (the indexer and the deploy
  // backfill, at launch) both saw "not open yet", both opened, and the second
  // failed on the lock and took the process down.
  static OPENING: std::sync::Mutex<()> = std::sync::Mutex::new(());

  if let Some(db) = DB.get() {
    return Ok(db.clone());
  }
  let _opening = OPENING.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
  if let Some(db) = DB.get() {
    return Ok(db.clone());
  }

  // RocksDB, via the sled-shaped shim in store.rs.
  //
  // Phase timing put ~85% of indexing wall time inside the old sled store
  // (57% writing outputs, 28% reading inputs) against ~13% parsing, with the
  // process under one core - the store, not CPU, was the constraint. sled also
  // amplified ~1 MB of logical writes per block into ~16 MB on disk.
  //
  // SPOOKY_SLED_CACHE_MB is still honoured as the sizing knob so existing
  // launch scripts keep working; it now sizes RocksDB write buffers.
  let cache_mb: usize = std::env::var("SPOOKY_SLED_CACHE_MB")
    .ok()
    .and_then(|v| v.parse().ok())
    .filter(|v| *v > 0)
    .unwrap_or(4096);

  let db = store::Db::open(db_path, cache_mb)?;
  info!("rocksdb opened at {} (sizing hint {} MB)", db_path, cache_mb);

  // One-off migration for an index built before bloom filters were configured.
  // Filters live inside each SST, so existing files keep the old format until
  // rewritten; without this, point lookups against already-indexed data keep
  // scanning every file in every level.
  if std::env::var("SPOOKY_COMPACT_ON_START").is_ok() {
    info!("compacting all column families to apply current table options (one-off, slow)");
    let t = std::time::Instant::now();
    db.compact_all()?;
    info!("compaction finished in {:.1}s", t.elapsed().as_secs_f64());
  }
  let _ = DB.set(db.clone());
  Ok(db)
}

#[cfg(test)]
mod dogemap_tests {
  use super::*;

  fn db() -> store::Db {
    store::Db::temporary().unwrap()
  }

  #[test]
  fn parses_plain_claim() {
    assert_eq!(parse_dogemap_number(b"123.dogemap"), Some(123));
  }

  #[test]
  fn suffix_is_case_insensitive() {
    assert_eq!(parse_dogemap_number(b"123.DOGEMAP"), Some(123));
    assert_eq!(parse_dogemap_number(b"123.DogeMap"), Some(123));
  }

  #[test]
  fn surrounding_whitespace_is_ignored() {
    assert_eq!(parse_dogemap_number(b"  456.dogemap \n"), Some(456));
  }

  #[test]
  fn block_zero_is_claimable() {
    assert_eq!(parse_dogemap_number(b"0.dogemap"), Some(0));
  }

  #[test]
  fn rejects_leading_zeros() {
    // Otherwise "007.dogemap" and "7.dogemap" are two texts claiming one block.
    assert_eq!(parse_dogemap_number(b"007.dogemap"), None);
    assert_eq!(parse_dogemap_number(b"00.dogemap"), None);
  }

  #[test]
  fn rejects_non_numeric_and_decorated_numbers() {
    assert_eq!(parse_dogemap_number(b"+7.dogemap"), None);
    assert_eq!(parse_dogemap_number(b"-7.dogemap"), None);
    assert_eq!(parse_dogemap_number(b"1 2.dogemap"), None);
    // "1.5" splits to number_part "1.5", which is not all digits.
    assert_eq!(parse_dogemap_number(b"1.5.dogemap"), None);
  }

  #[test]
  fn rejects_wrong_or_missing_suffix() {
    assert_eq!(parse_dogemap_number(b"123.bitmap"), None);
    assert_eq!(parse_dogemap_number(b"123"), None);
    assert_eq!(parse_dogemap_number(b".dogemap"), None);
    assert_eq!(parse_dogemap_number(b""), None);
  }

  #[test]
  fn rejects_non_utf8() {
    assert_eq!(parse_dogemap_number(&[0xff, 0xfe, 0x2e]), None);
  }

  #[test]
  fn first_claim_wins_and_later_claims_are_rejected() {
    let db = db();
    let by_number = db.open_tree("dogemap_by_number").unwrap();
    let by_insc = db.open_tree("dogemap_by_inscription").unwrap();
    let by_addr = db.open_tree("dogemap_by_address").unwrap();
    let mut undo = UndoRecorder::default();

    let first = apply_dogemap_claim_with_undo(
      &by_number, &by_insc, &by_addr, 42, "aaai0", "aaa", "DAddr1", 100, 1, &mut undo,
    )
    .unwrap();
    assert!(first, "first claim should be accepted");

    let second = apply_dogemap_claim_with_undo(
      &by_number, &by_insc, &by_addr, 42, "bbbi0", "bbb", "DAddr2", 101, 2, &mut undo,
    )
    .unwrap();
    assert!(!second, "second claim on same number must be rejected");

    let stored: DogemapEntry =
      bincode::deserialize(&by_number.get(encode_u64(42)).unwrap().unwrap()).unwrap();
    assert_eq!(stored.inscription_id, "aaai0");
    assert_eq!(stored.owner, "DAddr1");
  }

  #[test]
  fn cannot_claim_a_future_block() {
    let db = db();
    let by_number = db.open_tree("dogemap_by_number").unwrap();
    let by_insc = db.open_tree("dogemap_by_inscription").unwrap();
    let by_addr = db.open_tree("dogemap_by_address").unwrap();
    let mut undo = UndoRecorder::default();

    // Claiming block 500 while indexing height 100 must not be allowed.
    let claimed = apply_dogemap_claim_with_undo(
      &by_number, &by_insc, &by_addr, 500, "aaai0", "aaa", "DAddr1", 100, 1, &mut undo,
    )
    .unwrap();
    assert!(!claimed);
    assert!(by_number.get(encode_u64(500)).unwrap().is_none());

    // The current height itself is claimable.
    let at_tip = apply_dogemap_claim_with_undo(
      &by_number, &by_insc, &by_addr, 100, "cccti0", "ccc", "DAddr1", 100, 1, &mut undo,
    )
    .unwrap();
    assert!(at_tip);
  }

  #[test]
  fn ownership_follows_the_inscription() {
    let db = db();
    let by_number = db.open_tree("dogemap_by_number").unwrap();
    let by_insc = db.open_tree("dogemap_by_inscription").unwrap();
    let by_addr = db.open_tree("dogemap_by_address").unwrap();
    let mut undo = UndoRecorder::default();

    apply_dogemap_claim_with_undo(
      &by_number, &by_insc, &by_addr, 7, "aaai0", "aaa", "DOld", 10, 1, &mut undo,
    )
    .unwrap();
    assert!(by_addr.get(dogemap_address_key("DOld", 7).as_bytes()).unwrap().is_some());

    move_dogemap_owner_with_undo(&by_number, &by_insc, &by_addr, "aaai0", "DNew", &mut undo)
      .unwrap();

    let stored: DogemapEntry =
      bincode::deserialize(&by_number.get(encode_u64(7)).unwrap().unwrap()).unwrap();
    assert_eq!(stored.owner, "DNew");
    // The stale owner index must be gone, or the old address still lists it.
    assert!(by_addr.get(dogemap_address_key("DOld", 7).as_bytes()).unwrap().is_none());
    assert!(by_addr.get(dogemap_address_key("DNew", 7).as_bytes()).unwrap().is_some());
  }

  #[test]
  fn moving_an_inscription_without_a_claim_is_a_noop() {
    let db = db();
    let by_number = db.open_tree("dogemap_by_number").unwrap();
    let by_insc = db.open_tree("dogemap_by_inscription").unwrap();
    let by_addr = db.open_tree("dogemap_by_address").unwrap();
    let mut undo = UndoRecorder::default();

    move_dogemap_owner_with_undo(&by_number, &by_insc, &by_addr, "unknowni0", "DNew", &mut undo)
      .unwrap();
    assert_eq!(by_number.len().unwrap(), 0);
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn test_db() -> store::Db {
    store::Db::temporary().expect("open temp rocksdb")
  }

  fn enc_varint(mut n: u128) -> Vec<u8> {
    let mut out = [0u8; 19];
    let mut i = 18usize;
    loop {
      let mut byte = n.to_le_bytes()[0] & 0b0111_1111;
      if i < 18 {
        byte |= 0b1000_0000;
      }
      out[i] = byte;
      if n < 0b1000_0000 {
        break;
      }
      n = n / 128 - 1;
      i = i.saturating_sub(1);
    }
    out[i..].to_vec()
  }

  fn dune_asm(integers: &[u128]) -> String {
    let mut payload = Vec::new();
    for n in integers {
      payload.extend_from_slice(&enc_varint(*n));
    }
    format!("OP_RETURN 44 {}", hex::encode(payload))
  }

  fn p2pkh_like_output(n: u32, value: f64, address: &str) -> RpcVout {
    RpcVout {
      value,
      n,
      script_pub_key: RpcScriptPubKey {
        asm: Some("OP_DUP OP_HASH160".to_string()),
        hex: None,
        addresses: Some(vec![address.to_string()]),
      },
    }
  }

  fn op_return_output(n: u32, asm: String) -> RpcVout {
    RpcVout {
      value: 0.0,
      n,
      script_pub_key: RpcScriptPubKey {
        asm: Some(asm),
        hex: None,
        addresses: None,
      },
    }
  }

  fn get_balance(tree: &store::Tree, address: &str, tick: &str) -> Drc20Balance {
    let k = balance_key(address, tick);
    let raw = tree.get(k.as_bytes()).unwrap().unwrap();
    bincode::deserialize(raw.as_ref()).unwrap()
  }

  fn push(data: &[u8]) -> Vec<u8> {
    assert!(data.len() <= 75);
    let mut out = Vec::with_capacity(data.len() + 1);
    out.push(data.len() as u8);
    out.extend_from_slice(data);
    out
  }

  fn script_from_pushes(pushes: &[&[u8]], trailing_op: Option<u8>) -> Vec<u8> {
    let mut script = Vec::new();
    for p in pushes {
      script.extend_from_slice(&push(p));
    }
    if let Some(op) = trailing_op {
      script.push(op);
    }
    script
  }

  #[test]
  fn dunes_premine_allocates_to_default_output() {
    let db = test_db();
    let dune_meta = db.open_tree("dune_meta_by_id").unwrap();
    let dune_entry = db.open_tree("dune_entry_by_id").unwrap();
    let dune_balances = db.open_tree("dune_balances_by_outpoint").unwrap();
    let mut undo = UndoRecorder::default();

    let tx = RpcTx {
      txid: "txpremine".to_string(),
      vin: vec![],
      vout: vec![
        op_return_output(0, dune_asm(&[2, 1, 4, 1, 22, 50])),
        p2pkh_like_output(1, 1.0, "DADDR1"),
      ],
    };

    process_dunes(
      &tx,
      1,
      5_084_000,
      &dune_meta,
      &dune_entry,
      &dune_balances,
      &mut undo,
      &mut Vec::new(),
    )
    .unwrap();

    let dune_id = "DOGECOIN:B";
    let meta_raw = dune_meta.get(dune_id.as_bytes()).unwrap().unwrap();
    let meta: DuneMeta = bincode::deserialize(meta_raw.as_ref()).unwrap();
    assert_eq!(meta.id, dune_id);

    let bal_key = "txpremine:1|DOGECOIN:B";
    let bal_raw = dune_balances.get(bal_key.as_bytes()).unwrap().unwrap();
    assert_eq!(decode_u128(bal_raw.as_ref()).unwrap(), 50);
  }

  #[test]
  fn dunes_cenotaph_burns_unallocated_inputs() {
    let db = test_db();
    let dune_meta = db.open_tree("dune_meta_by_id").unwrap();
    let dune_entry = db.open_tree("dune_entry_by_id").unwrap();
    let dune_balances = db.open_tree("dune_balances_by_outpoint").unwrap();
    let mut undo = UndoRecorder::default();

    dune_balances
      .insert("prevtx:0|DOGECOIN:B".as_bytes(), encode_u128(100).to_vec())
      .unwrap();

    // Body with output=9 while tx has only 2 outputs => cenotaph.
    let tx = RpcTx {
      txid: "txburn".to_string(),
      vin: vec![RpcVin {
        txid: Some("prevtx".to_string()),
        vout: Some(0),
        script_sig: None,
      }],
      vout: vec![
        op_return_output(0, dune_asm(&[0, 0, 10, 9])),
        p2pkh_like_output(1, 1.0, "DADDR1"),
      ],
    };

    process_dunes(
      &tx,
      0,
      5_084_001,
      &dune_meta,
      &dune_entry,
      &dune_balances,
      &mut undo,
      &mut Vec::new(),
    )
    .unwrap();

    assert!(dune_balances
      .get("prevtx:0|DOGECOIN:B".as_bytes())
      .unwrap()
      .is_none());
    assert!(dune_balances
      .scan_prefix("txburn:".as_bytes())
      .unwrap()
      .is_empty());
  }

  #[test]
  fn rollback_restores_previous_state_from_undo_log() {
    let db = test_db();
    let meta = db.open_tree("meta").unwrap();
    let blocks = db.open_tree("blocks").unwrap();
    let undo_by_height = db.open_tree("undo_by_height").unwrap();
    let utxo = db.open_tree("utxo_by_outpoint").unwrap();

    utxo.insert(b"k", b"old".as_slice()).unwrap();

    let mut undo = UndoRecorder::default();
    undo
      .insert("utxo_by_outpoint", &utxo, b"k", b"new".to_vec())
      .unwrap();

    let height = 42u64;
    undo_by_height
      .insert(encode_u64(height), bincode::serialize(&undo.into_ops()).unwrap())
      .unwrap();
    blocks.insert(encode_u64(height), b"blockhash").unwrap();
    meta.insert(b"indexed_height", encode_u64(height).to_vec()).unwrap();

    rollback_one_height(&db, &blocks, &meta, &undo_by_height, height).unwrap();

    assert_eq!(utxo.get(b"k").unwrap().as_deref(), Some(&b"old"[..]));
    assert!(blocks.get(encode_u64(height)).unwrap().is_none());
    assert!(undo_by_height.get(encode_u64(height)).unwrap().is_none());
    assert_eq!(
      decode_u64(meta.get(b"indexed_height").unwrap().unwrap().as_ref()).unwrap(),
      height - 1
    );
  }

  #[test]
  fn dunes_claim_mints_and_updates_supply() {
    let db = test_db();
    let dune_meta = db.open_tree("dune_meta_by_id").unwrap();
    let dune_entry = db.open_tree("dune_entry_by_id").unwrap();
    let dune_balances = db.open_tree("dune_balances_by_outpoint").unwrap();
    let mut undo = UndoRecorder::default();

    let dune_id = "DOGECOIN:B";
    let meta = DuneMeta {
      id: dune_id.to_string(),
      name: "B".to_string(),
      symbol: String::new(),
      divisibility: 0,
    };
    let entry = DuneEntryLite {
      id: dune_id.to_string(),
      etched_height: 5_084_000,
      premine: 0,
      supply: 0,
      burned: 0,
      mints: 0,
      terms: Some(DuneTerms {
        cap: Some(2),
        limit: Some(100),
        height_start: None,
        height_end: None,
        offset_start: None,
        offset_end: None,
      }),
    };
    dune_meta
      .insert(dune_id.as_bytes(), bincode::serialize(&meta).unwrap())
      .unwrap();
    dune_entry
      .insert(dune_id.as_bytes(), bincode::serialize(&entry).unwrap())
      .unwrap();

    let claim_id = 1u128 | DUNE_CLAIM_BIT;
    let tx = RpcTx {
      txid: "txclaim".to_string(),
      vin: vec![],
      vout: vec![
        op_return_output(0, dune_asm(&[0, claim_id, 30, 1])),
        p2pkh_like_output(1, 1.0, "DADDR1"),
      ],
    };

    process_dunes(
      &tx,
      0,
      5_084_010,
      &dune_meta,
      &dune_entry,
      &dune_balances,
      &mut undo,
      &mut Vec::new(),
    )
    .unwrap();

    let bal_key = "txclaim:1|DOGECOIN:B";
    let bal_raw = dune_balances.get(bal_key.as_bytes()).unwrap().unwrap();
    assert_eq!(decode_u128(bal_raw.as_ref()).unwrap(), 30);

    let entry_raw = dune_entry.get(dune_id.as_bytes()).unwrap().unwrap();
    let updated: DuneEntryLite = bincode::deserialize(entry_raw.as_ref()).unwrap();
    assert_eq!(updated.supply, 30);
    assert_eq!(updated.mints, 1);
  }

  #[test]
  fn drc20_deploy_mint_transfer_lifecycle() {
    let db = test_db();
    let token_tree = db.open_tree("drc20_token_info").unwrap();
    let balance_tree = db.open_tree("drc20_balance").unwrap();
    let transferable_tree = db.open_tree("drc20_transferable_by_id").unwrap();

    // deploy
    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc0",
      Drc20Action::Deploy {
        tick: "dogi".to_string(),
        max_supply: "1000".to_string(),
        mint_limit: Some("100".to_string()),
        decimals: Some("0".to_string()),
      },
    )
    .unwrap();

    // duplicate deploy ignored
    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc1",
      Drc20Action::Deploy {
        tick: "DOGI".to_string(),
        max_supply: "999999".to_string(),
        mint_limit: Some("999".to_string()),
        decimals: Some("0".to_string()),
      },
    )
    .unwrap();

    let tk = token_key("DOGI");
    let info_raw = token_tree.get(tk.as_bytes()).unwrap().unwrap();
    let info: Drc20TokenInfo = bincode::deserialize(info_raw.as_ref()).unwrap();
    assert_eq!(info.supply, 1000);
    assert_eq!(info.limit_per_mint, 100);
    assert_eq!(info.decimals, 0);

    // mint 80
    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc2",
      Drc20Action::Mint {
        tick: "dogi".to_string(),
        amount: "80".to_string(),
      },
    )
    .unwrap();

    let b = get_balance(&balance_tree, "DADDR1", "DOGI");
    assert_eq!(b.overall, 80);
    assert_eq!(b.transferable, 0);

    // transfer inscribe 30 (locks transferable)
    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "txinsc3i0",
      Drc20Action::TransferInscribe {
        tick: "DOGI".to_string(),
        amount: "30".to_string(),
      },
    )
    .unwrap();

    let b = get_balance(&balance_tree, "DADDR1", "DOGI");
    assert_eq!(b.overall, 80);
    assert_eq!(b.transferable, 30);

    // move transfer inscription to receiver => settles transfer
    process_drc20_transfer_move(&balance_tree, &transferable_tree, "txinsc3i0", "DADDR2").unwrap();

    let b1 = get_balance(&balance_tree, "DADDR1", "DOGI");
    let b2 = get_balance(&balance_tree, "DADDR2", "DOGI");
    assert_eq!(b1.overall, 50);
    assert_eq!(b1.transferable, 0);
    assert_eq!(b2.overall, 30);
    assert_eq!(b2.transferable, 0);
    assert!(transferable_tree.get("txinsc3i0".as_bytes()).unwrap().is_none());
  }

  #[test]
  fn drc20_mint_enforces_limit_and_supply() {
    let db = test_db();
    let token_tree = db.open_tree("drc20_token_info").unwrap();
    let balance_tree = db.open_tree("drc20_balance").unwrap();
    let transferable_tree = db.open_tree("drc20_transferable_by_id").unwrap();

    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc0",
      Drc20Action::Deploy {
        tick: "ABCD".to_string(),
        max_supply: "100".to_string(),
        mint_limit: Some("60".to_string()),
        decimals: Some("0".to_string()),
      },
    )
    .unwrap();

    // over per-mint limit -> ignored
    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc1",
      Drc20Action::Mint {
        tick: "ABCD".to_string(),
        amount: "61".to_string(),
      },
    )
    .unwrap();
    assert!(balance_tree.scan_prefix("B|DADDR1|ABCD".as_bytes()).unwrap().is_empty());

    // mint 60 + mint 60 => second should cap to remaining 40
    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc2",
      Drc20Action::Mint {
        tick: "ABCD".to_string(),
        amount: "60".to_string(),
      },
    )
    .unwrap();
    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc3",
      Drc20Action::Mint {
        tick: "ABCD".to_string(),
        amount: "60".to_string(),
      },
    )
    .unwrap();

    let b = get_balance(&balance_tree, "DADDR1", "ABCD");
    assert_eq!(b.overall, 100);
    assert_eq!(b.transferable, 0);
  }

  #[test]
  fn drc20_transfer_lock_requires_available_balance() {
    let db = test_db();
    let token_tree = db.open_tree("drc20_token_info").unwrap();
    let balance_tree = db.open_tree("drc20_balance").unwrap();
    let transferable_tree = db.open_tree("drc20_transferable_by_id").unwrap();

    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc0",
      Drc20Action::Deploy {
        tick: "LOCK".to_string(),
        max_supply: "1000".to_string(),
        mint_limit: Some("1000".to_string()),
        decimals: Some("0".to_string()),
      },
    )
    .unwrap();

    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc1",
      Drc20Action::Mint {
        tick: "LOCK".to_string(),
        amount: "50".to_string(),
      },
    )
    .unwrap();

    // lock 40 ok
    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc_lock_ok",
      Drc20Action::TransferInscribe {
        tick: "LOCK".to_string(),
        amount: "40".to_string(),
      },
    )
    .unwrap();
    assert!(transferable_tree
      .get("insc_lock_ok".as_bytes())
      .unwrap()
      .is_some());

    // lock 20 should fail: available is only 10 now
    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc_lock_fail",
      Drc20Action::TransferInscribe {
        tick: "LOCK".to_string(),
        amount: "20".to_string(),
      },
    )
    .unwrap();
    assert!(transferable_tree
      .get("insc_lock_fail".as_bytes())
      .unwrap()
      .is_none());
  }

  #[test]
  fn drc20_transfer_to_empty_destination_redirects_to_sender() {
    let db = test_db();
    let token_tree = db.open_tree("drc20_token_info").unwrap();
    let balance_tree = db.open_tree("drc20_balance").unwrap();
    let transferable_tree = db.open_tree("drc20_transferable_by_id").unwrap();

    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc0",
      Drc20Action::Deploy {
        tick: "RDIR".to_string(),
        max_supply: "100".to_string(),
        mint_limit: Some("100".to_string()),
        decimals: Some("0".to_string()),
      },
    )
    .unwrap();

    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc1",
      Drc20Action::Mint {
        tick: "RDIR".to_string(),
        amount: "50".to_string(),
      },
    )
    .unwrap();

    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc_transfer",
      Drc20Action::TransferInscribe {
        tick: "RDIR".to_string(),
        amount: "20".to_string(),
      },
    )
    .unwrap();

    process_drc20_transfer_move(&balance_tree, &transferable_tree, "insc_transfer", "").unwrap();

    let b1 = get_balance(&balance_tree, "DADDR1", "RDIR");
    assert_eq!(b1.overall, 50);
    assert_eq!(b1.transferable, 0);
  }

  #[test]
  fn drc20_parser_rejects_invalid_and_short_payloads() {
    let short = br#"{"p":"drc-20"}"#;
    assert!(parse_drc20_action("application/json", short).is_none());

    let wrong_p = br#"{"p":"foo","op":"mint","tick":"DOGI","amt":"1"}"#;
    assert!(parse_drc20_action("application/json", wrong_p).is_none());

    let wrong_ct = br#"{"p":"drc-20","op":"mint","tick":"DOGI","amt":"1"}"#;
    assert!(parse_drc20_action("image/png", wrong_ct).is_none());

    let bad_json = br#"{"p":"drc-20","op":"mint","tick":"DOGI","amt":"1""#;
    assert!(parse_drc20_action("application/json", bad_json).is_none());
  }

  #[test]
  fn drc20_decimal_scale_is_enforced() {
    let db = test_db();
    let token_tree = db.open_tree("drc20_token_info").unwrap();
    let balance_tree = db.open_tree("drc20_balance").unwrap();
    let transferable_tree = db.open_tree("drc20_transferable_by_id").unwrap();

    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc0",
      Drc20Action::Deploy {
        tick: "DECI".to_string(),
        max_supply: "10.00".to_string(),
        mint_limit: Some("5.00".to_string()),
        decimals: Some("2".to_string()),
      },
    )
    .unwrap();

    // valid scale
    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc1",
      Drc20Action::Mint {
        tick: "DECI".to_string(),
        amount: "1.23".to_string(),
      },
    )
    .unwrap();

    // invalid scale (3 > 2) should be ignored
    apply_drc20_new_action(
      &token_tree,
      &balance_tree,
      &transferable_tree,
      "DADDR1",
      "insc2",
      Drc20Action::Mint {
        tick: "DECI".to_string(),
        amount: "1.234".to_string(),
      },
    )
    .unwrap();

    let b = get_balance(&balance_tree, "DADDR1", "DECI");
    assert_eq!(b.overall, 123);
    assert_eq!(b.transferable, 0);
  }

  #[test]
  fn inscription_parser_accepts_trailing_pushes_and_completes_multiscript() {
    let script0 = script_from_pushes(
      &[
        b"ord",
        &[2],
        b"image/png",
        &[1],
        b"abc",
        b"junk-signature-push",
      ],
      Some(0x75), // OP_DROP
    );
    let script1 = script_from_pushes(
      &[
        &[0],
        b"def",
        b"junk-pubkey-push",
      ],
      Some(0x75), // OP_DROP
    );

    match parse_inscription_outcome(&[script0, script1]) {
      InscriptionParseOutcome::Complete(content_type, body, delegate) => {
        assert_eq!(content_type, "image/png");
        assert_eq!(body, b"abcdef");
        assert!(delegate.is_none());
      }
      _ => panic!("expected complete inscription parse"),
    }
  }

  #[test]
  fn inscription_parser_accepts_empty_content_type_and_delegate() {
    // Real doginals envelope used by delegate-only inscriptions (e.g.
    // ff9ce158…i0 on doggy.market):
    //   "ord"  OP_1  (empty type)  OP_0  (empty body)  OP_11  <32-byte id>
    // npieces=1, content type empty, body empty, tag 11 = delegate.
    let mut delegate_bytes = [0u8; 32];
    // Internal (reversed) form of babc46e7…c07deb
    let display =
      hex::decode("babc46e7095a90c814d4c161b1d9d47f921c566ea93ad483d78741cc27c07deb").unwrap();
    for (i, b) in display.iter().rev().enumerate() {
      delegate_bytes[i] = *b;
    }

    let script = script_from_pushes(
      &[
        b"ord",
        &[1],
        &[], // empty content type
        &[0],
        &[], // empty body
        &[11],
        &delegate_bytes,
      ],
      None,
    );

    match parse_inscription_outcome(&[script]) {
      InscriptionParseOutcome::Complete(content_type, body, delegate) => {
        assert_eq!(content_type, "");
        assert!(body.is_empty());
        assert_eq!(
          delegate.as_deref(),
          Some("babc46e7095a90c814d4c161b1d9d47f921c566ea93ad483d78741cc27c07debi0")
        );
      }
      other => panic!("expected complete delegate inscription, got {other:?}"),
    }
  }

  #[test]
  fn inscription_parser_accepts_null_content_type_non_utf8() {
    // Non-UTF-8 content type must not drop the inscription; type becomes "".
    let script = script_from_pushes(
      &[
        b"ord",
        &[1],
        &[0xff, 0xfe], // invalid UTF-8
        &[0],
        b"hi",
      ],
      None,
    );
    match parse_inscription_outcome(&[script]) {
      InscriptionParseOutcome::Complete(content_type, body, delegate) => {
        assert_eq!(content_type, "");
        assert_eq!(body, b"hi");
        assert!(delegate.is_none());
      }
      other => panic!("expected complete, got {other:?}"),
    }
  }

  #[test]
  fn decode_inscription_id_field_roundtrip() {
    let display =
      hex::decode("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f").unwrap();
    let mut raw = [0u8; 32];
    for (i, b) in display.iter().rev().enumerate() {
      raw[i] = *b;
    }
    assert_eq!(
      decode_inscription_id_field(&raw).as_deref(),
      Some("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1fi0")
    );
    // With index 1 little-endian, trailing zeros omitted → single 0x01 byte.
    let mut with_index = raw.to_vec();
    with_index.push(1);
    assert_eq!(
      decode_inscription_id_field(&with_index).as_deref(),
      Some("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1fi1")
    );
  }

  #[test]
  fn process_inscription_candidate_stitches_chain_by_vin0_prev_txid() {
    let db = test_db();
    let partial = db.open_tree("partial_inscription_chain").unwrap();
    let mut undo = UndoRecorder::default();

    let script0 = script_from_pushes(
      &[
        b"ord",
        &[2],
        b"image/png",
        &[1],
        b"abc",
      ],
      Some(0x75),
    );
    let tx0 = RpcTx {
      txid: "tx0".to_string(),
      vin: vec![RpcVin {
        txid: Some("prev".to_string()),
        vout: Some(0),
        script_sig: Some(RpcScriptSig {
          hex: hex::encode(script0),
        }),
      }],
      vout: vec![],
    };

    let first =
      process_inscription_candidate(&tx0, decode_script_sig_bytes(&tx0).as_deref(), &partial, &mut undo)
        .unwrap();
    assert!(first.is_none());
    assert!(partial.get("tx0".as_bytes()).unwrap().is_some());

    let script1 = script_from_pushes(
      &[
        &[0],
        b"def",
      ],
      Some(0x75),
    );
    let tx1 = RpcTx {
      txid: "tx1".to_string(),
      vin: vec![RpcVin {
        txid: Some("tx0".to_string()),
        vout: Some(0),
        script_sig: Some(RpcScriptSig {
          hex: hex::encode(script1),
        }),
      }],
      vout: vec![],
    };

    let second =
      process_inscription_candidate(&tx1, decode_script_sig_bytes(&tx1).as_deref(), &partial, &mut undo)
        .unwrap();
    let parsed = second.expect("expected completed inscription");
    assert_eq!(parsed.inscription_txid, "tx0");
    assert_eq!(parsed.content_type, "image/png");
    assert_eq!(parsed.body, b"abcdef");
    assert!(partial.get("tx0".as_bytes()).unwrap().is_none());
  }

  #[test]
  fn spendable_utxos_excludes_inscription_outpoints() {
    let uniq = format!(
      "spookyord-test-{}",
      std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos()
    );
    let dir = std::env::temp_dir().join(uniq);
    std::fs::create_dir_all(&dir).unwrap();
    let db_path = dir.join("spookyord.rocksdb");
    let db = store::Db::open(db_path.to_str().unwrap(), 64).unwrap();
    let outpoints = db.open_tree("outpoints_by_address").unwrap();
    let insc_by_outpoint = db.open_tree("inscriptions_by_outpoint").unwrap();
    let dune_by_outpoint = db.open_tree("dune_balances_by_outpoint").unwrap();

    outpoints
      .insert("DADDR|txa:0".as_bytes(), encode_u64(1000).to_vec())
      .unwrap();
    outpoints
      .insert("DADDR|txb:1".as_bytes(), encode_u64(2000).to_vec())
      .unwrap();
    outpoints
      .insert("DADDR|txc:2".as_bytes(), encode_u64(3000).to_vec())
      .unwrap();
    // New schema: one key per outpoint holding the list of (offset, id).
    // Previously this was one key per inscription, read back with a prefix
    // scan; that scan cost 40.6 us per transaction input on the live index.
    insc_by_outpoint
      .insert(
        "txb:1".as_bytes(),
        bincode::serialize(&vec![(0u64, "insc1".to_string())]).unwrap(),
      )
      .unwrap();
    dune_by_outpoint
      .insert("txc:2|DOGECOIN:TEST".as_bytes(), encode_u128(55).to_vec())
      .unwrap();

    // The store handle is process-wide (open_db), so the holder and dune
    // readers are exercised against this same seeded index rather than in
    // tests of their own, which would silently read whichever opened first.
    let balances = db.open_tree("drc20_balance").unwrap();
    for (key, tick, overall, transferable) in [
      ("B|DADDR|ABCD", "ABCD", 500u128, 100u128),
      ("B|DOTHER|ABCD", "ABCD", 900, 0),
      ("B|DZERO|ABCD", "ABCD", 0, 0),
      ("B|DADDR|WXYZ", "WXYZ", 7, 0),
    ] {
      let bal = Drc20Balance { tick: tick.to_string(), overall, transferable };
      balances.insert(key.as_bytes(), bincode::serialize(&bal).unwrap()).unwrap();
    }
    let utxos = db.open_tree("utxo_by_outpoint").unwrap();
    for (outpoint, address) in [("txc:2", "DADDR"), ("txd:0", "DOTHER")] {
      let rec = UtxoRecord { satoshis: 1000, address: address.to_string() };
      utxos.insert(outpoint.as_bytes(), bincode::serialize(&rec).unwrap()).unwrap();
    }
    dune_by_outpoint
      .insert("txd:0|DOGECOIN:TEST".as_bytes(), encode_u128(45).to_vec())
      .unwrap();
    let meta = DuneMeta { id: "DOGECOIN:TEST".into(), name: "TEST•DUNE".into(), symbol: "T".into(), divisibility: 0 };
    db.open_tree("dune_meta_by_id").unwrap()
      .insert(b"DOGECOIN:TEST", bincode::serialize(&meta).unwrap()).unwrap();
    let entry = DuneEntryLite {
      id: "DOGECOIN:TEST".into(),
      etched_height: 100,
      premine: 0,
      supply: 100,
      burned: 0,
      mints: 2,
      terms: Some(DuneTerms { cap: Some(10), limit: Some(50), height_start: None, height_end: Some(500), offset_start: Some(5), offset_end: None }),
    };
    db.open_tree("dune_entry_by_id").unwrap()
      .insert(b"DOGECOIN:TEST", bincode::serialize(&entry).unwrap()).unwrap();
    drop(balances);
    drop(utxos);

    db.flush().unwrap();
    drop(insc_by_outpoint);
    drop(dune_by_outpoint);
    drop(outpoints);
    drop(db);

    let cfg = Config {
      rpc_url: String::new(),
      rpc_user: String::new(),
      rpc_password: String::new(),
      rpc_concurrency: 1,
      bind_addr: String::new(),
      data_dir: dir.to_string_lossy().to_string(),
      first_inscription_height: 0,
      first_dune_height: 0,
      stop_height: None,
      content_store: "full".to_string(),
      flush_interval: 1,
    };

    // The launch-time race: the first opens of the shared store happen
    // concurrently (the indexer and the deploy backfill both open at start),
    // and every one of them must get the one handle, not a lock error.
    let db_file = format!("{}/spookyord.rocksdb", cfg.data_dir);
    let openers: Vec<_> = (0..8).map(|_| { let p = db_file.clone(); std::thread::spawn(move || open_db(&p).map(|_| ())) }).collect();
    for o in openers {
      o.join().unwrap().expect("every concurrent first open succeeds");
    }

    let mut rows = list_spendable_utxos_for_address(&cfg, "DADDR").unwrap();
    rows.sort_by(|a, b| a.0.cmp(&b.0));
    assert_eq!(rows, vec![("txa:0".to_string(), 1000)]);

    // Holders: largest first, zero balances skipped, other ticks ignored.
    let h = drc20_holders(&cfg, "ABCD", 500).unwrap();
    assert_eq!(h.holders, 2);
    assert_eq!(h.held, "1400");
    let order: Vec<(&str, &str, &str)> =
      h.top.iter().map(|r| (r.address.as_str(), r.total.as_str(), r.transferable.as_str())).collect();
    assert_eq!(order, vec![("DOTHER", "900", "0"), ("DADDR", "500", "100")]);
    assert_eq!(drc20_holders(&cfg, "ABCD", 1).unwrap().top.len(), 1, "keep bounds the list");
    assert_eq!(drc20_holders(&cfg, "WXYZ", 500).unwrap().holders, 1);
    assert_eq!(drc20_holders(&cfg, "NONE", 500).unwrap().holders, 0);

    // Dune detail: owners resolved through their outputs, largest first.
    let d = get_dune_detail(&cfg, "DOGECOIN:TEST").unwrap().expect("dune exists");
    assert_eq!(d.summary.name, "TEST•DUNE");
    assert_eq!(d.summary.cap.as_deref(), Some("10"));
    assert_eq!((d.height_end, d.offset_start), (Some(500), Some(5)));
    assert_eq!(d.circulating, "100");
    let holders: Vec<(&str, &str)> = d.holders.iter().map(|x| (x.address.as_str(), x.balance.as_str())).collect();
    assert_eq!(holders, vec![("DADDR", "55"), ("DOTHER", "45")]);
    assert!(get_dune_detail(&cfg, "DOGECOIN:MISSING").unwrap().is_none());
  }

  #[test]
  fn deploy_validation_matches_the_indexing_rules() {
    assert_eq!(validate_drc20_deploy("1000", Some("100"), Some("0")), Some((1000, 100, 0)));
    // Decimals default to 18, the limit to the supply.
    let e18 = 10u128.pow(18);
    assert_eq!(validate_drc20_deploy("5", None, None), Some((5 * e18, 5 * e18, 18)));
    assert_eq!(validate_drc20_deploy("1000", Some("100"), Some("19")), None, "over 18 decimals");
    assert_eq!(validate_drc20_deploy("0", None, Some("0")), None, "zero supply");
    assert_eq!(validate_drc20_deploy("10", Some("0"), Some("0")), None, "zero limit");
    assert_eq!(validate_drc20_deploy("ten", None, Some("0")), None, "not a number");
  }

  #[test]
  fn drc20_actions_report_exactly_what_was_accepted() {
    let db = test_db();
    let token_tree = db.open_tree("drc20_token_info").unwrap();
    let balance_tree = db.open_tree("drc20_balance").unwrap();
    let transferable_tree = db.open_tree("drc20_transferable_by_id").unwrap();
    let act = |addr: &str, id: &str, action: Drc20Action| {
      apply_drc20_new_action_with_undo(&token_tree, &balance_tree, &transferable_tree, addr, id, action, None).unwrap()
    };
    let deploy = |tick: &str| Drc20Action::Deploy {
      tick: tick.to_string(),
      max_supply: "1000".into(),
      mint_limit: Some("100".into()),
      decimals: Some("0".into()),
    };

    assert_eq!(act("DA", "d0", deploy("wxyz")), Some(Drc20Applied::Deploy { tick: "WXYZ".into(), supply: 1000 }));
    assert_eq!(act("DA", "d1", deploy("WXYZ")), None, "a second deploy is not reported");
    assert_eq!(
      act("DA", "m0", Drc20Action::Mint { tick: "WXYZ".into(), amount: "100".into() }),
      Some(Drc20Applied::Mint { tick: "WXYZ".into(), amount: 100 })
    );
    assert_eq!(act("DA", "m1", Drc20Action::Mint { tick: "WXYZ".into(), amount: "101".into() }), None, "over the limit");
    assert_eq!(
      act("DA", "t0", Drc20Action::TransferInscribe { tick: "WXYZ".into(), amount: "40".into() }),
      Some(Drc20Applied::Inscribe { tick: "WXYZ".into(), amount: 40 })
    );
    assert_eq!(act("", "m2", Drc20Action::Mint { tick: "WXYZ".into(), amount: "1".into() }), None, "no owner");

    let moved = process_drc20_transfer_move_with_undo(&balance_tree, &transferable_tree, "t0", "DB", None).unwrap();
    assert_eq!(moved, Some(Drc20Moved { tick: "WXYZ".into(), amount: 40, from: "DA".into(), to: "DB".into() }));
    assert_eq!(process_drc20_transfer_move_with_undo(&balance_tree, &transferable_tree, "t0", "DB", None).unwrap(), None, "a lock moves once");
  }

  #[test]
  fn dune_events_report_etch_mint_transfer_and_burn() {
    let db = test_db();
    let meta = db.open_tree("dune_meta_by_id").unwrap();
    let entry = db.open_tree("dune_entry_by_id").unwrap();
    let balances = db.open_tree("dune_balances_by_outpoint").unwrap();
    let mut undo = UndoRecorder::default();

    // A pre-existing dune on an output this test spends.
    balances.insert(b"txprev:0|DOGECOIN:B", encode_u128(70).to_vec()).unwrap();
    let mut events = Vec::new();
    let spend = RpcTx {
      txid: "txspend".into(),
      vin: vec![RpcVin { txid: Some("txprev".into()), vout: Some(0), script_sig: None }],
      vout: vec![p2pkh_like_output(0, 1.0, "DADDR2")],
    };
    process_dunes(&spend, 0, 5_100_000, &meta, &entry, &balances, &mut undo, &mut events).unwrap();
    assert_eq!(events, vec![DuneEvent { dune_id: "DOGECOIN:B".into(), kind: "transfer", amount: 70 }]);

    // A transaction moving nothing reports nothing.
    let mut quiet = Vec::new();
    let plain = RpcTx { txid: "txplain".into(), vin: vec![], vout: vec![p2pkh_like_output(0, 1.0, "DADDR3")] };
    process_dunes(&plain, 0, 5_100_001, &meta, &entry, &balances, &mut undo, &mut quiet).unwrap();
    assert!(quiet.is_empty());
  }

  #[test]
  fn activity_keys_sort_newest_first_and_stay_in_scope() {
    let newer = activity_key(&drc20_scope("ABCD"), 200, 0, "x");
    let older = activity_key(&drc20_scope("ABCD"), 100, 0, "x");
    let later_in_block = activity_key(&drc20_scope("ABCD"), 200, 5, "x");
    assert!(newer < older, "higher block first");
    assert!(later_in_block < newer, "later in the block first");
    assert!(newer.starts_with("T|ABCD|"));
    assert!(!activity_key(&drc20_scope("ABCE"), 200, 0, "x").starts_with("T|ABCD|"));
    assert!(activity_key(&dune_scope("DOGECOIN:B"), 1, 0, "mint").starts_with("D|DOGECOIN:B|"));
  }
}
