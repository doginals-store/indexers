//! One-off rebuild of DRC-20 state after the inscription archive was
//! corrected (see the renumber module).
//!
//! DRC-20 balances depend on which inscriptions exist and in what order, so
//! the inscriptions the repair added wrongly, and the ones the old reveal-
//! chain rule lost, both left them off. This replays every block from the
//! first inscription height with the same rule code live indexing uses:
//!
//!  - a new inscription is a deploy, mint or transfer-inscribe where it lands,
//!    exactly as live: taken from the corrected chain order
//!    (`inscription_seq`, at the transaction that completes it) and its
//!    stored content;
//!  - a transfer inscription settles the first time it moves, to whoever it
//!    lands with. Only transfer inscriptions not yet settled are followed,
//!    output by output, through the node's blocks.
//!
//! The rebuilt state goes into its own trees (`drc20r_*`) while the site
//! keeps serving the old one. When the replay reaches the live tip, the two
//! are swapped between two live blocks, after checking the replayed blocks
//! are still the chain. A restart before then starts it over.

use super::*;
use crate::insc_index::SeqEntry;
use crate::store::Batch;
use tokio::task::JoinSet;

const STATE_KEY: &[u8] = b"drc20_replay_v1";
const AHEAD: u64 = 32;

/// (live tree, rebuilt tree)
const TREES: [(&str, &str); 4] = [
  ("drc20_token_info", "drc20r_token_info"),
  ("drc20_balance", "drc20r_balance"),
  ("drc20_transferable_by_id", "drc20r_transferable"),
  ("drc20_deploy", "drc20r_deploy"),
];
const ACTIVITY: &str = "drc20r_activity";
/// DRC-20 events in `token_activity` are under `T|`; Dunes' under `D|`.
const ACTIVITY_START: &[u8] = b"T|";
const ACTIVITY_END: &[u8] = b"T}";

pub fn drc20_replay_done(config: &Config) -> Result<bool> {
  Ok(open_db(&config.db_path())?.open_tree("meta")?.get(STATE_KEY)?.is_some())
}

struct Trees {
  token: store::Tree,
  balance: store::Tree,
  transferable: store::Tree,
  deploy: store::Tree,
  activity: store::Tree,
  seq: store::Tree,
  content: store::Tree,
}

/// What happens at one position of a transaction's inputs.
enum Event {
  Created(String, Drc20Action),
  Moved(String),
}

/// The replay's own state: rebuilt trees, and where each unsettled transfer
/// inscription is (outpoint -> (offset, id)).
struct Replay {
  t: Trees,
  tracked: HashMap<String, Vec<(u64, String)>>,
  values: HashMap<String, Vec<u64>>,
  /// Hashes of the blocks replayed, newest last, for the check at the swap.
  recent: VecDeque<(u64, String)>,
  created: u64,
  settled: u64,
}

impl Replay {
  fn open(db: &store::Db) -> Result<Self> {
    Ok(Self {
      t: Trees {
        token: db.open_tree(TREES[0].1)?,
        balance: db.open_tree(TREES[1].1)?,
        transferable: db.open_tree(TREES[2].1)?,
        deploy: db.open_tree(TREES[3].1)?,
        activity: db.open_tree(ACTIVITY)?,
        seq: db.open_tree("inscription_seq")?,
        content: db.open_tree("inscription_content")?,
      },
      tracked: HashMap::new(),
      values: HashMap::new(),
      recent: VecDeque::new(),
      created: 0,
      settled: 0,
    })
  }

  /// Applies one block, as live indexing would have with the corrected
  /// archive.
  async fn block(&mut self, client: &Client, config: &Config, height: u64, block: &RpcBlock) -> Result<()> {
    // New inscriptions in this block, by position.
    let mut new_at: HashMap<u32, String> = HashMap::new();
    self.t.seq.for_each_prefix(height.to_be_bytes(), |k, v| {
      let e: SeqEntry = bincode::deserialize(v).context("decode seq entry")?;
      let pos = u32::from_be_bytes(k[8..12].try_into().expect("seq keys are 12 bytes"));
      new_at.entry(pos).or_insert(e.id);
      Ok(true)
    })?;
    // Outputs of this block's own transactions, for inputs that spend them.
    let local: HashMap<&str, &RpcTx> = block.tx.iter().map(|tx| (tx.txid.as_str(), tx)).collect();
    let time = block.time.unwrap_or(0);
    let mut undo = UndoRecorder::default();

    for (tx_index, tx) in block.tx.iter().enumerate() {
      let mut events: Vec<(u64, Event)> = Vec::new();

      // Unsettled transfer inscriptions this transaction spends.
      let last_tracked = tx
        .vin
        .iter()
        .rposition(|v| matches!((&v.txid, v.vout), (Some(t), Some(o)) if self.tracked.contains_key(&outpoint_key(t, o))));
      if let Some(last) = last_tracked {
        let mut input_value = 0u64;
        // Only inputs before the last followed one decide where it lands.
        for (j, vin) in tx.vin[..=last].iter().enumerate() {
          let (Some(ptxid), Some(pvout)) = (&vin.txid, vin.vout) else { continue };
          if let Some(list) = self.tracked.remove(&outpoint_key(ptxid, pvout)) {
            for (offset, id) in list {
              events.push((input_value.saturating_add(offset), Event::Moved(id)));
            }
          }
          if j == last {
            break;
          }
          let value = match local.get(ptxid.as_str()) {
            Some(prev) => to_satoshis(prev.vout.get(pvout as usize).ok_or_else(|| anyhow!("{ptxid}:{pvout} missing"))?.value)?,
            None => repair::prev_value(client, config, &mut self.values, ptxid, pvout).await?,
          };
          input_value = input_value.saturating_add(value);
        }
      }

      // A new inscription made here, if it is a DRC-20 operation.
      if let Some(id) = new_at.get(&(tx_index as u32))
        && let Some(raw) = self.t.content.get(id.as_bytes())?
      {
        let c = decode_inscription_content(raw.as_ref())?;
        if let Some(action) = parse_drc20_action(&c.content_type, &c.body) {
          events.push((0, Event::Created(id.clone(), action)));
        }
      }
      if events.is_empty() {
        continue;
      }
      // Live indexing goes output by output, and within one by offset.
      events.sort_by_key(|(abs, e)| (*abs, matches!(e, Event::Moved(_))));

      let prep = prepare_tx(tx)?;
      for (abs, event) in events {
        let mut start = 0u64;
        let mut landed = None;
        for (vout, out) in prep.outs.iter().enumerate() {
          let end = start.saturating_add(out.satoshis);
          if abs >= start && abs < end {
            landed = Some((vout, abs - start));
            break;
          }
          start = end;
        }
        // Sent to fees: nothing happens, and it never moves again.
        let Some((vout, offset)) = landed else { continue };
        let out = &prep.outs[vout];
        match event {
          Event::Created(id, action) => {
            if offset != 0 {
              continue;
            }
            let applied = apply_drc20_new_action_with_undo(&self.t.token, &self.t.balance, &self.t.transferable, &out.address, &id, action, Some(&mut undo))?;
            let Some(applied) = applied else { continue };
            self.created += 1;
            let (tick, kind, amount, from, to) = match &applied {
              Drc20Applied::Deploy { tick, supply } => (tick, "deploy", *supply, String::new(), out.address.clone()),
              Drc20Applied::Mint { tick, amount } => (tick, "mint", *amount, String::new(), out.address.clone()),
              Drc20Applied::Inscribe { tick, amount } => (tick, "inscribe-transfer", *amount, out.address.clone(), String::new()),
            };
            if let Drc20Applied::Deploy { .. } = applied {
              let deploy = Drc20Deploy { inscription_id: id.clone(), txid: tx.txid.clone(), deployer: out.address.clone(), height, time };
              self.t.deploy.insert(tick.as_bytes(), bincode::serialize(&deploy)?)?;
            }
            let event = ActivityEvent { kind: kind.to_string(), amount: amount.to_string(), from, to, inscription_id: id.clone(), txid: tx.txid.clone(), height, time };
            record_activity(&self.t.activity, &mut undo, &drc20_scope(tick), tx_index, &format!("{id}|{kind}"), &event)?;
            if let Drc20Applied::Inscribe { .. } = applied {
              self.tracked.entry(out.outpoint.clone()).or_default().push((offset, id));
            }
          }
          Event::Moved(id) => {
            let moved = process_drc20_transfer_move_with_undo(&self.t.balance, &self.t.transferable, &id, &out.address, Some(&mut undo))?;
            if let Some(m) = moved {
              self.settled += 1;
              let event = ActivityEvent { kind: "transfer".to_string(), amount: m.amount.to_string(), from: m.from, to: m.to, inscription_id: id.clone(), txid: tx.txid.clone(), height, time };
              record_activity(&self.t.activity, &mut undo, &drc20_scope(&m.tick), tx_index, &format!("{id}|transfer"), &event)?;
            }
          }
        }
      }
    }
    self.recent.push_back((height, block.hash.clone()));
    if self.recent.len() > 100 {
      self.recent.pop_front();
    }
    Ok(())
  }
}

/// Every key of a tree whose keys are text or big-endian numbers.
fn clear(tree: &store::Tree) -> Result<()> {
  tree.delete_range(Vec::new(), vec![0xff; 256])
}

fn copy(db: &store::Db, from: &store::Tree, to: &store::Tree) -> Result<u64> {
  let meta = db.open_tree("meta")?;
  let mut batch = Batch::default();
  let (mut n, mut pending) = (0u64, 0usize);
  let mut err = None;
  from.for_each_prefix(b"", |k, v| {
    batch.insert(to, k.to_vec(), v.to_vec());
    n += 1;
    pending += 1;
    if pending >= 50_000 {
      if let Err(e) = std::mem::take(&mut batch).commit(&meta) {
        err = Some(e);
        return Ok(false);
      }
      pending = 0;
    }
    Ok(true)
  })?;
  if let Some(e) = err {
    return Err(e);
  }
  batch.commit(&meta)?;
  Ok(n)
}

/// Puts the rebuilt state in place of the live one. Runs between two live
/// blocks.
fn swap(db: &store::Db) -> Result<()> {
  for (live, rebuilt) in TREES {
    let (live, rebuilt) = (db.open_tree(live)?, db.open_tree(rebuilt)?);
    clear(&live)?;
    let n = copy(db, &rebuilt, &live)?;
    clear(&rebuilt)?;
    info!("drc20 replay: {n} rows in place");
  }
  let activity = db.open_tree("token_activity")?;
  activity.delete_range(ACTIVITY_START, ACTIVITY_END)?;
  let rebuilt = db.open_tree(ACTIVITY)?;
  let n = copy(db, &rebuilt, &activity)?;
  clear(&rebuilt)?;
  info!("drc20 replay: {n} activity events in place");
  Ok(())
}

/// The replay; see the module notes. Waits for the archive correction, does
/// nothing once done.
pub async fn run_drc20_replay(config: Config) -> Result<()> {
  if drc20_replay_done(&config)? {
    return Ok(());
  }
  let mut said = false;
  while !renumber::renumber_done(&config)? {
    if !said {
      info!("drc20 replay: waiting for the inscription archive correction");
      said = true;
    }
    tokio::time::sleep(Duration::from_secs(60)).await;
  }
  let client = indexer_rpc_client()?;
  let db = open_db(&config.db_path())?;
  let meta = db.open_tree("meta")?;
  let blocks = db.open_tree("blocks")?;
  // Always from the start: the rebuilt trees are not crash-consistent.
  for (_, rebuilt) in TREES {
    clear(&db.open_tree(rebuilt)?)?;
  }
  clear(&db.open_tree(ACTIVITY)?)?;
  let mut r = Replay::open(&db)?;
  let mut next = config.first_inscription_height;
  let started = Instant::now();
  let mut since_log = 0u64;
  info!("drc20 replay: replaying from block {next}");

  loop {
    let live = meta.get(b"indexed_height")?.map(|v| decode_u64(v.as_ref())).transpose()?.unwrap_or(0);
    if next > live {
      let swapped = {
        let _w = repair::INDEX_WRITE.lock().unwrap_or_else(|e| e.into_inner());
        let live_now = meta.get(b"indexed_height")?.map(|v| decode_u64(v.as_ref())).transpose()?.unwrap_or(0);
        if live_now + 1 != next {
          None
        } else {
          // The blocks replayed last must still be the chain.
          let mut same = true;
          for (h, hash) in &r.recent {
            let stored = blocks.get(encode_u64(*h))?.map(|v| String::from_utf8_lossy(v.as_ref()).to_string());
            if stored.as_deref() != Some(hash.as_str()) {
              same = false;
              break;
            }
          }
          if same {
            swap(&db)?;
            meta.insert(STATE_KEY, encode_u64(1).to_vec())?;
            db.flush()?;
          }
          Some(same)
        }
      };
      match swapped {
        Some(true) => {
          info!(
            "drc20 replay: done; {} operations applied, {} transfers settled, in {:.0?}",
            r.created, r.settled, started.elapsed()
          );
          return Ok(());
        }
        Some(false) => bail!("a reorg changed blocks the DRC-20 replay had read; starting it over"),
        None => {
          tokio::time::sleep(Duration::from_millis(200)).await;
          continue;
        }
      }
    }

    let to = (next + AHEAD).min(live + 1);
    let mut set = JoinSet::new();
    for h in next..to {
      let cfg = config.clone();
      set.spawn(async move { (h, repair::fetch_block(client, &cfg, h).await) });
    }
    let mut fetched: Vec<(u64, RpcBlock)> = Vec::new();
    while let Some(res) = set.join_next().await {
      let (h, b) = res.context("join block fetch")?;
      fetched.push((h, b.with_context(|| format!("block {h}"))?));
    }
    fetched.sort_by_key(|(h, _)| *h);
    for (h, block) in &fetched {
      r.block(client, &config, *h, block).await?;
    }
    since_log += fetched.len() as u64;
    next = to;
    if since_log >= 50_000 {
      since_log = 0;
      info!(
        "drc20 replay: at block {next}, {} operations, {} transfers settled, {} transfer inscriptions unsent",
        r.created,
        r.settled,
        r.tracked.values().map(Vec::len).sum::<usize>()
      );
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::insc_index as ii;

  fn block(height: u64, txs: serde_json::Value) -> RpcBlock {
    serde_json::from_value(serde_json::json!({ "hash": format!("h{height}"), "previousblockhash": null, "tx": txs, "time": 1000 + height })).unwrap()
  }
  fn tx(txid: &str, vin: &[(&str, u32)], vout: &[(f64, &str)]) -> serde_json::Value {
    serde_json::json!({
      "txid": txid,
      "vin": vin.iter().map(|(t, v)| serde_json::json!({ "txid": t, "vout": v })).collect::<Vec<_>>(),
      "vout": vout.iter().enumerate().map(|(n, (value, a))| serde_json::json!({ "value": value, "n": n, "scriptPubKey": { "addresses": [a] } })).collect::<Vec<_>>(),
    })
  }

  #[tokio::test]
  async fn replay_applies_operations_and_settles_a_transfer_where_it_lands() {
    let db = store::Db::temporary().unwrap();
    let seq = db.open_tree("inscription_seq").unwrap();
    let content = db.open_tree("inscription_content").unwrap();
    let (a, b) = ("DALICE", "DBOB");
    let ops = [
      (1u32, "d1", r#"{"p":"drc-20","op":"deploy","tick":"dogi","max":"1000","lim":"1000"}"#),
      (2, "m2", r#"{"p":"drc-20","op":"mint","tick":"dogi","amt":"600"}"#),
      (3, "t3", r#"{"p":"drc-20","op":"transfer","tick":"dogi","amt":"400"}"#),
      // Not in chain order: a wrongly added inscription is simply absent.
    ];
    for (pos, txid, body) in ops {
      let id = format!("{txid}i0");
      seq.insert(ii::seq_key(100, pos), ii::seq_value(&id, 0, 1100).unwrap()).unwrap();
      let c = InscriptionContentRecord { content_type: "text/plain".into(), body: body.as_bytes().to_vec(), delegate: None };
      content.insert(id.as_bytes(), bincode::serialize(&c).unwrap()).unwrap();
    }
    let b100 = block(100, serde_json::json!([
      tx("c0", &[], &[(50.0, a)]),
      tx("d1", &[("x0", 0)], &[(0.001, a)]),
      tx("m2", &[("x1", 0)], &[(0.001, a)]),
      tx("t3", &[("x2", 0)], &[(0.001, a), (1.0, a)]),
    ]));
    // Block 101: the transfer inscription is sent on to Bob. A deploy-looking
    // inscription with no place in chain order changes nothing.
    let b101 = block(101, serde_json::json!([
      tx("c1", &[], &[(50.0, a)]),
      tx("s4", &[("t3", 0), ("t3", 1)], &[(0.001, b), (0.99, a)]),
    ]));
    let mut r = Replay::open(&db).unwrap();
    let config = Config::from_env();
    let client = indexer_rpc_client().unwrap();
    r.block(client, &config, 100, &b100).await.unwrap();
    assert_eq!((r.created, r.tracked.len()), (3, 1), "deploy, mint and transfer-inscribe; the transfer is followed");
    r.block(client, &config, 101, &b101).await.unwrap();
    assert_eq!((r.settled, r.tracked.len()), (1, 0));

    let mut balances: HashMap<String, (u128, u128)> = HashMap::new();
    r.t.balance.for_each_prefix(b"B|", |k, v| {
      let bal: Drc20Balance = bincode::deserialize(v)?;
      let who = String::from_utf8_lossy(k).split('|').nth(1).unwrap().to_string();
      balances.insert(who, (bal.overall, bal.transferable));
      Ok(true)
    }).unwrap();
    // Raw amounts, scaled by the default 18 decimals.
    let e18 = 10u128.pow(18);
    assert_eq!(balances[a], (200 * e18, 0));
    assert_eq!(balances[b], (400 * e18, 0));
    assert!(r.t.transferable.get(b"t3i0").unwrap().is_none());
    let mut kinds = Vec::new();
    r.t.activity.for_each_prefix(b"T|", |_, v| {
      kinds.push(bincode::deserialize::<ActivityEvent>(v)?.kind);
      Ok(true)
    }).unwrap();
    kinds.sort();
    assert_eq!(kinds, ["deploy", "inscribe-transfer", "mint", "transfer"]);
    assert!(r.t.deploy.for_each_prefix(b"", |_, _| Ok(false)).is_ok());
  }

  #[test]
  fn swap_replaces_live_drc20_state_and_keeps_dune_activity() {
    let db = store::Db::temporary().unwrap();
    let live_bal = db.open_tree("drc20_balance").unwrap();
    let new_bal = db.open_tree("drc20r_balance").unwrap();
    let activity = db.open_tree("token_activity").unwrap();
    let new_activity = db.open_tree(ACTIVITY).unwrap();
    live_bal.insert(b"B|DOLD|dogi", b"old".to_vec()).unwrap();
    new_bal.insert(b"B|DNEW|dogi", b"new".to_vec()).unwrap();
    activity.insert(b"T|dogi|1|old", b"x".to_vec()).unwrap();
    activity.insert(b"D|840000:3|1|dune", b"y".to_vec()).unwrap();
    new_activity.insert(b"T|dogi|1|new", b"z".to_vec()).unwrap();
    swap(&db).unwrap();
    assert!(live_bal.get(b"B|DOLD|dogi").unwrap().is_none());
    assert_eq!(live_bal.get(b"B|DNEW|dogi").unwrap().unwrap().as_ref(), b"new");
    assert!(new_bal.get(b"B|DNEW|dogi").unwrap().is_none(), "rebuilt trees are emptied");
    assert!(activity.get(b"T|dogi|1|old").unwrap().is_none());
    assert!(activity.get(b"T|dogi|1|new").unwrap().is_some());
    assert!(activity.get(b"D|840000:3|1|dune").unwrap().is_some(), "Dune activity stays");
  }
}
