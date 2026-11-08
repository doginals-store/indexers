//! One-off repair: inscriptions lost to the reveal-chain bug.
//!
//! Until 2026-11-06 the indexer dropped a half-finished multi-transaction
//! reveal whenever *any* transaction spent the chain's last transaction in its
//! input 0 without continuing it (say, an ordinary payment of its change that
//! came earlier in the block than the next piece). The real next piece then
//! found nothing to continue, and the inscription was never created. ord-
//! dogecoin keeps the chain, and so does the indexer now.
//!
//! This task replays every block from the start height with the corrected
//! rule, in its own scratch tables, and collects each inscription the index is
//! missing. From its reveal on it follows each one through every later spend,
//! sat by sat, exactly as the indexer would have. Once it has caught up with
//! the live indexer, it takes the indexer's write lock and adds them where
//! they are now (and any reveal chains still in progress), then marks itself
//! done. Nothing it writes before that touches the live tables.

use super::*;

const STATE_KEY: &[u8] = b"inscription_repair_v1";
/// Blocks fetched from the node at once.
const AHEAD: u64 = 24;

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
struct RepairState {
  next_height: u64,
  done: bool,
  found: u64,
  lost_to_fee: u64,
  drc20_like: u64,
}

/// A recovered inscription and, once placed, where it is now.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct Found {
  id: String,
  content_type: String,
  body: Vec<u8>,
  delegate: Option<String>,
  height: u64,
  tx_index: u32,
  time: u64,
  /// (txid, vout, offset, satoshis, address); None when it went to fees.
  at: Option<(String, u32, u64, u64, String)>,
}

/// The live indexer holds this while it writes a block, so the repair can add
/// its inscriptions between blocks.
pub(crate) static INDEX_WRITE: std::sync::Mutex<()> = std::sync::Mutex::new(());

fn load_state(meta: &store::Tree) -> Result<RepairState> {
  Ok(match meta.get(STATE_KEY)? {
    Some(raw) => bincode::deserialize(raw.as_ref()).context("decode repair state")?,
    None => RepairState::default(),
  })
}

pub fn inscription_repair_done(config: &Config) -> Result<bool> {
  let db = open_db(&config.db_path())?;
  Ok(load_state(&db.open_tree("meta")?)?.done)
}

pub(crate) async fn fetch_block(client: &Client, config: &Config, height: u64) -> Result<RpcBlock> {
  let hash: String = rpc_call(client, config, "getblockhash", serde_json::json!([height])).await?;
  rpc_call(client, config, "getblock", serde_json::json!([hash, 2])).await
}

/// The value of an output the index no longer has (it was spent long ago).
pub(crate) async fn prev_value(client: &Client, config: &Config, cache: &mut HashMap<String, Vec<u64>>, txid: &str, vout: u32) -> Result<u64> {
  if !cache.contains_key(txid) {
    let tx: RpcTx = rpc_call(client, config, "getrawtransaction", serde_json::json!([txid, true])).await?;
    let values = tx.vout.iter().map(|o| to_satoshis(o.value)).collect::<Result<Vec<_>>>()?;
    if cache.len() > 4096 {
      cache.clear();
    }
    cache.insert(txid.to_string(), values);
  }
  cache[txid].get(vout as usize).copied().ok_or_else(|| anyhow!("{txid}:{vout} has no such output"))
}

/// The replay itself: scratch reveal chains, recovered inscriptions and where
/// each sits, kept as blocks are applied in order.
struct Replayer {
  st: RepairState,
  scratch_partial: store::Tree,
  found_tree: store::Tree,
  body_tree: store::Tree,
  found: HashMap<String, Found>,
  at_outpoint: HashMap<String, Vec<String>>,
  values: HashMap<String, Vec<u64>>,
  /// Reveal chains completed, recovered or not (for checking the replay).
  completed: u64,
}

impl Replayer {
  fn open(db: &store::Db, st: RepairState) -> Result<Self> {
    let found_tree = db.open_tree("repair_found")?;
    let mut found: HashMap<String, Found> = HashMap::new();
    found_tree.for_each_prefix(b"", |k, v| {
      found.insert(String::from_utf8_lossy(k).into_owned(), bincode::deserialize(v)?);
      Ok(true)
    })?;
    let mut at_outpoint: HashMap<String, Vec<String>> = HashMap::new();
    for f in found.values() {
      if let Some((txid, vout, ..)) = &f.at {
        at_outpoint.entry(outpoint_key(txid, *vout)).or_default().push(f.id.clone());
      }
    }
    Ok(Self {
      st,
      scratch_partial: db.open_tree("repair_partial")?,
      found_tree,
      // Content, kept apart: the rest stays in memory while the replay runs.
      body_tree: db.open_tree("repair_body")?,
      found,
      at_outpoint,
      values: HashMap::new(),
      completed: 0,
    })
  }

  /// Applies one block. `known` says whether the index already has an id.
  async fn block(
    &mut self,
    client: &Client,
    config: &Config,
    height: u64,
    block: &RpcBlock,
    known: &(dyn Fn(&str) -> Result<bool> + Sync),
  ) -> Result<()> {
    let time = block.time.unwrap_or(0);
    for (tx_index, tx) in block.tx.iter().enumerate() {
      let prep = prepare_tx(tx)?;
      // 1. Recovered inscriptions this transaction spends move on.
      let mut carried: Vec<(u64, String)> = Vec::new();
      if prep.vin_outpoints.iter().flatten().any(|o| self.at_outpoint.contains_key(o)) {
        let mut input_value = 0u64;
        for (i, vin) in tx.vin.iter().enumerate() {
          let (Some(ptxid), Some(pvout)) = (&vin.txid, vin.vout) else { continue };
          let key = prep.vin_outpoints[i].as_deref().unwrap_or("");
          if let Some(ids) = self.at_outpoint.remove(key) {
            for id in ids {
              let (_, _, offset, _, _) = self.found[&id].at.clone().expect("tracked inscriptions have a place");
              carried.push((input_value.saturating_add(offset), id));
            }
          }
          input_value = input_value.saturating_add(prev_value(client, config, &mut self.values, ptxid, pvout).await?);
        }
      }
      // 2. Reveal chains, by the corrected rule, in the scratch table. As the
      //    indexer: no reveal where an inscription already sits on sat 0.
      let blocked = carried.iter().any(|(o, _)| *o == 0);
      let mut new_id = None;
      if !blocked {
        let mut scratch_undo = UndoRecorder::default();
        if let Some(parsed) = process_inscription_candidate(tx, prep.script_sig.as_deref(), &self.scratch_partial, &mut scratch_undo)? {
          self.completed += 1;
          let id = format!("{}i0", parsed.inscription_txid);
          if !known(&id)? && !self.found.contains_key(&id) {
            if parse_drc20_action(&parsed.content_type, &parsed.body).is_some() {
              self.st.drc20_like += 1;
              warn!("inscription repair: {id} reads as a DRC-20 operation; it is added, but its DRC-20 effect is not replayed");
            }
            self.body_tree.insert(id.as_bytes(), &parsed.body)?;
            self.found.insert(
              id.clone(),
              Found {
                id: id.clone(),
                content_type: parsed.content_type,
                body: Vec::new(),
                delegate: parsed.delegate,
                height,
                tx_index: tx_index as u32,
                time,
                at: None,
              },
            );
            self.st.found += 1;
            carried.push((0, id.clone()));
            new_id = Some(id);
          }
        }
      }
      if carried.is_empty() {
        continue;
      }
      // 3. Each lands on the output holding its sat, or goes to fees.
      carried.sort_by_key(|(o, _)| *o);
      let mut start = 0u64;
      let mut placed: HashSet<String> = HashSet::new();
      for (vout_index, out) in prep.outs.iter().enumerate() {
        let end = start.saturating_add(out.satoshis);
        for (abs, id) in &carried {
          if *abs >= start && *abs < end {
            let f = self.found.get_mut(id).expect("carried inscriptions are known");
            f.at = Some((tx.txid.clone(), tx.vout[vout_index].n, abs - start, out.satoshis, out.address.clone()));
            self.at_outpoint.entry(out.outpoint.clone()).or_default().push(id.clone());
            placed.insert(id.clone());
          }
        }
        start = end;
      }
      for (_, id) in &carried {
        if !placed.contains(id) {
          if let Some(f) = self.found.get_mut(id) {
            f.at = None;
            self.st.lost_to_fee += 1;
          }
        }
      }
      for (_, id) in &carried {
        self.found_tree.insert(id.as_bytes(), bincode::serialize(&self.found[id])?)?;
      }
      if let Some(id) = new_id {
        info!("inscription repair: recovered {id} (block {height})");
      }
    }
    self.st.next_height = height + 1;
    Ok(())
  }
}

pub async fn run_inscription_repair(config: Config) -> Result<()> {
  let client = indexer_rpc_client()?;
  let db = open_db(&config.db_path())?;
  let meta = db.open_tree("meta")?;
  let mut st = load_state(&meta)?;
  if st.done {
    return Ok(());
  }
  if st.next_height == 0 {
    st.next_height = config.first_inscription_height;
  }
  let inscriptions_by_id = db.open_tree("inscriptions_by_id")?;
  let known = |id: &str| -> Result<bool> { Ok(inscriptions_by_id.get(id.as_bytes())?.is_some()) };
  let mut r = Replayer::open(&db, st)?;
  info!("inscription repair: replaying from block {} ({} found so far)", r.st.next_height, r.st.found);
  let started = Instant::now();
  let mut since_log = 0u64;

  loop {
    let live = meta.get(b"indexed_height")?.map(|v| decode_u64(v.as_ref())).transpose()?.unwrap_or(0);
    if r.st.next_height > live {
      // Caught up: add everything, between two of the live indexer's blocks.
      let applied = {
        let _w = INDEX_WRITE.lock().unwrap_or_else(|e| e.into_inner());
        let live_now = meta.get(b"indexed_height")?.map(|v| decode_u64(v.as_ref())).transpose()?.unwrap_or(0);
        if live_now + 1 == r.st.next_height {
          apply(&config, &db, &r.found, &r.body_tree, &r.scratch_partial)?;
          r.st.done = true;
          meta.insert(STATE_KEY, bincode::serialize(&r.st)?)?;
          db.flush()?;
          true
        } else {
          false
        }
      };
      if applied {
        info!(
          "inscription repair: done; {} inscriptions recovered ({} sent to fees, {} DRC-20-like) in {:.0?}",
          r.st.found, r.st.lost_to_fee, r.st.drc20_like, started.elapsed()
        );
        return Ok(());
      }
      tokio::time::sleep(Duration::from_millis(200)).await;
      continue;
    }

    // A run of blocks, fetched together, applied in order.
    let to = (r.st.next_height + AHEAD).min(live + 1);
    let mut set = JoinSet::new();
    for h in r.st.next_height..to {
      let cfg = config.clone();
      set.spawn(async move { (h, fetch_block(client, &cfg, h).await) });
    }
    let mut blocks: Vec<(u64, RpcBlock)> = Vec::new();
    while let Some(res) = set.join_next().await {
      let (h, b) = res.context("join block fetch")?;
      blocks.push((h, b.with_context(|| format!("block {h}"))?));
    }
    blocks.sort_by_key(|(h, _)| *h);
    for (height, block) in &blocks {
      r.block(client, &config, *height, block, &known).await?;
    }
    meta.insert(STATE_KEY, bincode::serialize(&r.st)?)?;
    since_log += blocks.len() as u64;
    if since_log >= 20_000 {
      since_log = 0;
      info!("inscription repair: at block {}, {} recovered so far", r.st.next_height, r.st.found);
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  /// Replays blocks under the old chain rule (any spend of a chain's last
  /// transaction drops the chain) and the fixed one side by side, and writes
  /// every inscription the fixed rule completes where the old one does not:
  /// exactly what the bug lost, with no other rule involved. Reads only the
  /// node; scratch chains live in a temporary database. Skipped by default:
  /// `LOST_OUT=<file> [FROM=] [TO=] cargo test -p dogeord-indexer
  /// classify_chain_losses -- --ignored --nocapture`
  #[tokio::test(flavor = "multi_thread")]
  #[ignore]
  async fn classify_chain_losses() {
    use std::io::Write;
    let config = Config::from_env();
    let client = indexer_rpc_client().unwrap();
    let from: u64 = std::env::var("FROM").ok().and_then(|v| v.parse().ok()).unwrap_or(config.first_inscription_height);
    let to: u64 = match std::env::var("TO").ok().and_then(|v| v.parse().ok()) {
      Some(t) => t,
      None => rpc_call::<u64>(client, &config, "getblockcount", serde_json::json!([])).await.unwrap(),
    };
    let out = std::env::var("LOST_OUT").expect("LOST_OUT");
    let mut f = std::io::BufWriter::new(std::fs::File::create(&out).unwrap());
    // Where each multi-part inscription completes (its number goes there).
    let mut multi = std::env::var("MULTI_OUT").ok().map(|p| std::io::BufWriter::new(std::fs::File::create(p).unwrap()));
    // Chains in progress live in memory: each piece re-reading and re-writing
    // the whole chain in a database costs the square of its length, which
    // long images make hours per block range.
    let mut fixed: HashMap<String, PartialInscriptionChain> = HashMap::new();
    let mut old: HashMap<String, PartialInscriptionChain> = HashMap::new();
    let (mut lost, mut old_only, mut completed) = (0u64, 0u64, 0u64);
    let started = Instant::now();
    let mut next = from;
    while next <= to {
      let end = (next + 64).min(to + 1);
      let mut set = JoinSet::new();
      for h in next..end {
        let cfg = config.clone();
        set.spawn(async move { (h, fetch_block(client, &cfg, h).await) });
      }
      let mut blocks = Vec::new();
      while let Some(r) = set.join_next().await {
        let (h, b) = r.unwrap();
        blocks.push((h, b.unwrap()));
      }
      blocks.sort_by_key(|(h, _)| *h);
      for (h, block) in &blocks {
        for (i, tx) in block.tx.iter().enumerate() {
          let prep = prepare_tx(tx).unwrap();
          let Some(script) = prep.script_sig.as_deref() else { continue };
          let prev = tx.vin.first().and_then(|v| v.txid.clone());
          // The fixed rule (process_inscription_candidate): a spend that does
          // not continue the chain leaves it where it was.
          let new = {
            let taken = prev.as_deref().and_then(|p| fixed.remove(p));
            let continues = taken.is_some();
            let mut chain = taken.unwrap_or_else(|| PartialInscriptionChain { start_txid: tx.txid.clone(), scripts: Vec::new() });
            chain.scripts.push(script.to_vec());
            match parse_inscription_outcome(&chain.scripts) {
              InscriptionParseOutcome::Complete(..) => Some(chain.start_txid),
              InscriptionParseOutcome::Partial => {
                fixed.insert(tx.txid.clone(), chain);
                None
              }
              InscriptionParseOutcome::None => {
                if continues {
                  chain.scripts.pop();
                  fixed.insert(prev.clone().unwrap(), chain);
                }
                None
              }
            }
          };
          // The old rule: the chain is taken off the books by any spend.
          let existing = prev.as_deref().and_then(|p| old.remove(p));
          let mut chain = existing.unwrap_or_else(|| PartialInscriptionChain { start_txid: tx.txid.clone(), scripts: Vec::new() });
          chain.scripts.push(script.to_vec());
          let was = match parse_inscription_outcome(&chain.scripts) {
            InscriptionParseOutcome::Complete(..) => Some(chain.start_txid.clone()),
            InscriptionParseOutcome::Partial => {
              old.insert(tx.txid.clone(), chain);
              None
            }
            InscriptionParseOutcome::None => None,
          };
          if let Some(n) = &new {
            completed += 1;
            if n != &tx.txid
              && let Some(m) = multi.as_mut()
            {
              writeln!(m, "{n}i0\t{h}\t{i}\t{}", block.time.unwrap_or(0)).unwrap();
            }
          }
          match (&new, &was) {
            (Some(n), w) if w.as_ref() != Some(n) => {
              writeln!(f, "{n}i0\t{h}\t{i}").unwrap();
              lost += 1;
            }
            (None, Some(_)) => old_only += 1,
            _ => {}
          }
        }
        if h % 10_000 == 0 {
          println!("block {h}: {completed} completed, {lost} lost by the old rule, {old_only} old-only, {:.0?}", started.elapsed());
          f.flush().unwrap();
          if let Some(m) = multi.as_mut() {
            m.flush().unwrap();
          }
        }
      }
      next = end;
    }
    f.flush().unwrap();
    if let Some(m) = multi.as_mut() {
      m.flush().unwrap();
    }
    println!("done {from}..={to}: {completed} completed, {lost} lost by the old rule, {old_only} old-only, {:.0?}", started.elapsed());
  }

  /// Writes every inscription the repair recovered (id, height, position in
  /// block, DRC-20 or not, placed or sent to fees) as tab-separated lines,
  /// read from the live index without stopping it. Skipped by default:
  /// `DOGEORD_DB=<rocksdb dir> REPAIR_OUT=<file> cargo test -p dogeord-indexer
  /// export_recovered -- --ignored --nocapture`
  #[test]
  #[ignore]
  fn export_recovered() {
    use std::io::Write;
    let db_path = std::env::var("DOGEORD_DB").expect("DOGEORD_DB");
    let out = std::env::var("REPAIR_OUT").expect("REPAIR_OUT");
    let scratch = std::env::temp_dir().join(format!("dogeord-secondary-{}", std::process::id()));
    let db = store::Db::open_secondary(&db_path, &scratch.to_string_lossy()).unwrap();
    let found = db.open_tree("repair_found").unwrap();
    let bodies = db.open_tree("repair_body").unwrap();
    let mut f = std::io::BufWriter::new(std::fs::File::create(&out).unwrap());
    let mut n = 0u64;
    found
      .for_each_prefix(b"", |_, v| {
        let r: Found = bincode::deserialize(v)?;
        let body = bodies.get(r.id.as_bytes())?.map(|b| b.as_ref().to_vec()).unwrap_or_default();
        let drc20 = parse_drc20_action(&r.content_type, &body).is_some();
        writeln!(f, "{}\t{}\t{}\t{}\t{}\t{}", r.id, r.height, r.tx_index, drc20 as u8, r.at.is_some() as u8, r.content_type)?;
        n += 1;
        Ok(true)
      })
      .unwrap();
    f.flush().unwrap();
    println!("{n} recovered inscriptions written to {out}");
    let _ = std::fs::remove_dir_all(&scratch);
  }

  /// The 10 inscriptions a JavaScript replay of the reference rule found
  /// missing from the live index in blocks 5,449,700 to 5,449,899, out of
  /// 77,263 reveal chains completed there. Against the node; skipped by
  /// default: `cargo test -p dogeord-indexer replay_range -- --ignored`.
  #[tokio::test]
  #[ignore]
  async fn replay_range_finds_what_the_old_rule_lost() {
    let lost = [
      "efdcfb25d95fc3d75a25ed3614d90c4dd00c5ba2fa7d0be25d16b24d79006950", "53487a0d06269d1d5027cdc9ece0dddf5fe9bc58e0386672f47f45a14d37bdfd",
      "ec2cbfbd57ab972257c7166d5a4c8315358d8a445ccdb8c7f3b9f2849d2087e4", "1579552f52421f98d53026c29c14c1c187ce7a2e5d888a4dbedaca564eadea8c",
      "72d6d3dd7bae7ee3d9eace413ddd655d43e6bbfdc7b8ff16187e3cce1e4bfe79", "c49fed5d41b8a7dbc96323d44c72dc6913551450a64b09a7bc55cca17ad3cec0",
      "60e810e90b6ae557575b60b50f72619b3f3f2d19b6bf1d10c5359437408f2913", "46e658a603e54743ed8c556c398203c464c27322af80247a4202ea0bd8124a14",
      "c4da72d9d06e0fa2dc8c0d17670bf6d3dcac327f76364c303e133032d91d09d6", "6fe825114e6acde22794a5dba191ce156943ae48d63ef3b7136fd705c705427b",
    ]
    .map(|t| format!("{t}i0"));
    let config = Config::from_env();
    let client = indexer_rpc_client().unwrap();
    let db = store::Db::temporary().unwrap();
    let mut r = Replayer::open(&db, RepairState { next_height: 5_449_700, ..Default::default() }).unwrap();
    // Everything is "known" but the lost ten, as on the live index.
    let known = |id: &str| -> Result<bool> { Ok(!lost.iter().any(|l| l == id)) };
    for h in 5_449_700..5_449_900 {
      let b = fetch_block(client, &config, h).await.unwrap();
      r.block(client, &config, h, &b, &known).await.unwrap();
    }
    assert_eq!(r.completed, 77_263, "reveal chains completed, as the reference replay");
    let mut found: Vec<&String> = r.found.keys().collect();
    found.sort();
    let mut want: Vec<&String> = lost.iter().collect();
    want.sort();
    assert_eq!(found, want);
    // The 176-piece image: complete, its content kept, and placed on the
    // reveal's first output (or wherever it has moved since, within range).
    let f = &r.found["46e658a603e54743ed8c556c398203c464c27322af80247a4202ea0bd8124a14i0"];
    assert_eq!((f.content_type.as_str(), f.height), ("image/webp", 5_449_770));
    assert_eq!(r.body_tree.get(f.id.as_bytes()).unwrap().unwrap().len(), 42_030);
    let at = f.at.as_ref().expect("placed");
    println!("46e658…i0 is at {}:{} offset {} ({} koinu, {})", at.0, at.1, at.2, at.3, at.4);
    for id in &lost {
      assert!(r.found[id].at.is_some() || r.st.lost_to_fee > 0, "{id}");
    }
  }
}

/// Adds the recovered inscriptions to the live tables, where they are now,
/// and carries over reveal chains the live indexer lost and that are still in
/// progress. Called with the live indexer's write lock held.
fn apply(config: &Config, db: &store::Db, found: &HashMap<String, Found>, bodies: &store::Tree, scratch_partial: &store::Tree) -> Result<()> {
  let by_id = db.open_tree("inscriptions_by_id")?;
  let by_outpoint = db.open_tree("inscriptions_by_outpoint")?;
  let by_address = db.open_tree("inscriptions_by_address")?;
  let content = db.open_tree("inscription_content")?;
  let seq = db.open_tree("inscription_seq")?;
  let partial = db.open_tree("partial_inscription_chain")?;
  for f in found.values() {
    if by_id.get(f.id.as_bytes())?.is_some() {
      continue;
    }
    let body = bodies.get(f.id.as_bytes())?.map(|b| b.to_vec()).unwrap_or_default();
    if config.content_store == "full" {
      let rec = InscriptionContentRecord { content_type: f.content_type.clone(), body: body.clone(), delegate: f.delegate.clone() };
      content.insert(f.id.as_bytes(), bincode::serialize(&rec)?)?;
    }
    let key = insc_index::seq_key(f.height, f.tx_index);
    if seq.get(key)?.is_none() {
      let kinds = insc_index::kinds_for_new(&by_id, &f.content_type, &body, f.delegate.as_deref())?;
      seq.insert(key, insc_index::seq_value(&f.id, kinds, f.time)?)?;
    }
    match &f.at {
      Some((txid, vout, offset, satoshis, address)) => {
        let rec = InscriptionRecord {
          id: f.id.clone(),
          txid: txid.clone(),
          vout: *vout,
          offset: *offset,
          satoshis: *satoshis,
          content_type: f.content_type.clone(),
          address: address.clone(),
          delegate: f.delegate.clone(),
        };
        by_id.insert(f.id.as_bytes(), bincode::serialize(&rec)?)?;
        let okey = outpoint_key(txid, *vout);
        let mut list: Vec<(u64, String)> = match by_outpoint.get(okey.as_bytes())? {
          Some(raw) => bincode::deserialize(raw.as_ref())?,
          None => Vec::new(),
        };
        if !list.iter().any(|(_, id)| id == &f.id) {
          list.push((*offset, f.id.clone()));
          list.sort_by_key(|(o, _)| *o);
          by_outpoint.insert(okey.as_bytes(), bincode::serialize(&list)?)?;
        }
        if !address.is_empty() {
          by_address.insert(format!("{address}|{}", f.id).as_bytes(), Vec::<u8>::new())?;
        }
      }
      None => {
        let lost = InscriptionRecord {
          id: f.id.clone(),
          txid: String::new(),
          vout: u32::MAX,
          offset: 0,
          satoshis: 0,
          content_type: f.content_type.clone(),
          address: String::new(),
          delegate: f.delegate.clone(),
        };
        by_id.insert(f.id.as_bytes(), bincode::serialize(&lost)?)?;
      }
    }
  }
  // Chains still being revealed that the live indexer had dropped.
  scratch_partial.for_each_prefix(b"", |k, v| {
    if partial.get(k)?.is_none() {
      partial.insert(k, v)?;
    }
    Ok(true)
  })?;
  Ok(())
}
