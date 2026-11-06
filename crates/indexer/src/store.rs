//! Storage engine: RocksDB behind a sled-shaped API.
//!
//! WHY THIS EXISTS
//!
//! The indexer was written against `sled` 0.34. Measured on Dogecoin
//! inscription-era blocks (~1,200 transactions each), sled turned roughly 1 MB
//! of logical writes per block into ~16 MB of on-disk growth, and phase timing
//! attributed ~85% of indexing wall time to its read/write path while the CPU
//! sat at under one core. sled 0.34 is also effectively unmaintained.
//!
//! RocksDB is an LSM store designed for exactly this shape of work: heavy
//! sequential writes with periodic background compaction, rather than a
//! log-structured B-tree that rewrites pages in place.
//!
//! WHY A SHIM RATHER THAN A REWRITE
//!
//! The indexer only uses a small slice of the sled API - get, insert, remove,
//! scan_prefix, range, iter, len, flush - across ~46 `Tree` references. Keeping
//! those exact method names and shapes means the 3,000-line indexing logic,
//! including all the DRC-20, dunes and dogemap rules, is untouched by the swap.
//! Less to get wrong than threading a transactional API's lifetimes through
//! every call site.
//!
//! DIFFERENCES FROM SLED THAT CALLERS SHOULD KNOW
//!
//! * Column families must exist before use. `open_tree` creates one on demand,
//!   which requires a write lock, so it is meant for setup rather than hot paths.
//! * `len()` is a full scan (RocksDB keeps no exact count). Fine for the small
//!   dogemap table it is used on; do not call it on a large tree per block.
//! * `insert` does not return the previous value. Nothing in the indexer used
//!   that, and not returning it avoids a read on every write.

use anyhow::{Context, Result};
use rocksdb::{
  BlockBasedOptions, Cache, ColumnFamilyDescriptor, DBCompressionType, DBWithThreadMode, Direction,
  IteratorMode, MultiThreaded, Options, WriteBatch,
};
use std::ops::{Deref, Range};
use std::path::{Path, PathBuf};
use std::sync::{Arc, RwLock};

/// MultiThreaded mode is required: it hands out `Arc<BoundColumnFamily>` rather
/// than a borrow tied to `&DB`, which is what lets a `Tree` be held and used
/// across the async tasks the indexer spawns.
type Rdb = DBWithThreadMode<MultiThreaded>;

/// Owned byte buffer returned by reads.
///
/// Named after sled's `IVec` so call sites doing `raw.as_ref()` keep compiling.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IVec(Vec<u8>);

impl IVec {
  pub fn to_vec(&self) -> Vec<u8> {
    self.0.clone()
  }
}

impl AsRef<[u8]> for IVec {
  fn as_ref(&self) -> &[u8] {
    &self.0
  }
}

impl Deref for IVec {
  type Target = [u8];
  fn deref(&self) -> &[u8] {
    &self.0
  }
}

impl From<Vec<u8>> for IVec {
  fn from(v: Vec<u8>) -> Self {
    IVec(v)
  }
}

/// Column families are declared at open time, so every tree the indexer uses
/// must be listed here. Missing entries are created on demand by `open_tree`,
/// but listing them keeps startup to a single open.
const KNOWN_TREES: &[&str] = &[
  "meta",
  "blocks",
  "utxo_by_outpoint",
  "outpoints_by_address",
  "inscriptions_by_id",
  "inscriptions_by_outpoint",
  "inscriptions_by_address",
  "inscription_content",
  "partial_inscription_chain",
  "drc20_token_info",
  "drc20_balance",
  "drc20_transferable_by_id",
  "dune_meta_by_id",
  "dune_entry_by_id",
  "dune_balances_by_outpoint",
  "dogemap_by_number",
  "dogemap_by_inscription",
  "dogemap_by_address",
  "undo_by_height",
  // tick -> where and by whom it was deployed
  "drc20_deploy",
  // newest-first protocol events per token, see indexer::activity_key
  "token_activity",
  // (height, position in block) -> new inscription, see indexer::seq_key
  "inscription_seq",
  // inscription number -> id, and per content kind: kind byte + kind number -> id
  "inscription_number",
  "inscription_kind_number",
  // id -> number, genesis height and time, kinds
  "inscription_genesis",
  // DNS names, see dns.rs: name -> entry; inscription -> what it is to DNS;
  // registration order overall and per namespace; missed claims and configs
  // per name; each address's chosen name; counters
  "dns_name",
  "dns_by_inscription",
  "dns_index",
  "dns_ns_index",
  "dns_claims",
  "dns_config",
  "dns_primary",
  "dns_stats",
];

fn cf_options(write_buffer_mb: usize, cache: &Cache) -> Options {
  let mut opts = Options::default();
  // Larger memtables mean fewer, bigger SST flushes - the write pattern here is
  // an append-heavy backfill, not random updates.
  opts.set_write_buffer_size(write_buffer_mb * 1024 * 1024);
  opts.set_max_write_buffer_number(4);
  opts.set_min_write_buffer_number_to_merge(2);
  // Inscription content and undo blobs compress well; this is the main defence
  // against the on-disk growth that made sled unworkable here.
  opts.set_compression_type(DBCompressionType::Lz4);

  // Point-lookup tuning. RocksDB does NOT enable these by default, and without
  // them this workload degrades badly as the index grows:
  //
  //  * bloom filter - the indexer is dominated by point lookups (UTXO by
  //    outpoint, inscriptions by outpoint). With no filter, every get must
  //    consult every SST file in every level. Measured: a point lookup that
  //    cost 3.1 us on a small index had risen to 86.3 us by 25% indexed, with
  //    disk at 41% and CPU idling at 64% of a core - reading from disk to
  //    answer keys that mostly are not there.
  //
  //  * block cache - the default is 8 MB, far below the hot UTXO working set.
  //    Shared across all column families so one budget covers the whole index.
  //
  //  * cache_index_and_filter_blocks keeps those filters resident rather than
  //    re-reading them per lookup; pinning L0's avoids the most frequent case.
  let mut block_opts = BlockBasedOptions::default();
  block_opts.set_block_cache(cache);
  block_opts.set_bloom_filter(10.0, false);
  block_opts.set_cache_index_and_filter_blocks(true);
  block_opts.set_pin_l0_filter_and_index_blocks_in_cache(true);
  block_opts.set_block_size(16 * 1024);
  opts.set_block_based_table_factory(&block_opts);

  // Keys are looked up far more often than they are range-scanned.
  opts.set_memtable_prefix_bloom_ratio(0.1);

  opts
}

pub struct Db {
  inner: Arc<Rdb>,
  /// Serialises on-demand column family creation.
  create_lock: RwLock<()>,
  /// Set for temporary databases used by tests; removed on drop.
  temp_path: Option<PathBuf>,
}

impl Db {
  pub fn open(path: &str, cache_mb: usize) -> Result<Self> {
    Self::open_inner(Path::new(path), cache_mb, None)
  }

  /// Temporary database in the system temp directory, deleted on drop.
  pub fn temporary() -> Result<Self> {
    let unique = format!(
      "spookyord-test-{}-{}",
      std::process::id(),
      std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0)
    );
    let path = std::env::temp_dir().join(unique);
    Self::open_inner(&path, 64, Some(path.clone()))
  }

  fn open_inner(path: &Path, cache_mb: usize, temp_path: Option<PathBuf>) -> Result<Self> {
    // MEMORY BUDGET. Getting this wrong crashed the indexer once already:
    // write_buffer_size is PER COLUMN FAMILY, and with 19 families at 256 MB
    // and up to 4 buffers each that is a 19 GB ceiling on memtables alone, on
    // top of a 9.7 GB block cache, on a 25.8 GB machine. RocksDB threw an
    // allocation failure and the C++ exception aborted the process outright
    // ("Rust cannot catch foreign exceptions").
    //
    // So: modest per-family buffers, and a HARD global cap via
    // set_db_write_buffer_size, which bounds memtables across all families
    // regardless of how many there are.
    let write_buffer_mb = 64usize;
    let total_write_buffer_mb = 2048usize;
    // Leave the write-buffer budget and working memory outside the cache.
    let block_cache_mb = cache_mb
      .saturating_sub(total_write_buffer_mb)
      .saturating_sub(1024)
      .max(256);
    let cache = Cache::new_lru_cache(block_cache_mb * 1024 * 1024);

    let mut opts = Options::default();
    opts.create_if_missing(true);
    opts.create_missing_column_families(true);
    // Background threads for flush and compaction. This is the part that
    // actually uses the spare cores: indexing stays sequential, while
    // compaction runs alongside it.
    opts.increase_parallelism(num_background_threads());
    opts.set_max_background_jobs(num_background_threads());
    opts.set_bytes_per_sync(1024 * 1024);
    // Hard ceiling on memtable memory ACROSS all column families. Without this
    // the per-family write_buffer_size multiplies by the number of families.
    opts.set_db_write_buffer_size(total_write_buffer_mb * 1024 * 1024);
    // Bound WAL growth too; it is otherwise unbounded between flushes.
    opts.set_max_total_wal_size(1024 * 1024 * 1024);

    // A DB must be opened with every column family it already contains.
    let existing = Rdb::list_cf(&Options::default(), path).unwrap_or_default();
    let mut names: Vec<String> = existing;
    for t in KNOWN_TREES {
      if !names.iter().any(|n| n == t) {
        names.push((*t).to_string());
      }
    }
    if !names.iter().any(|n| n == "default") {
      names.push("default".to_string());
    }

    let descriptors: Vec<ColumnFamilyDescriptor> = names
      .iter()
      .map(|n| ColumnFamilyDescriptor::new(n, cf_options(write_buffer_mb, &cache)))
      .collect();

    let db = Rdb::open_cf_descriptors(&opts, path, descriptors)
      .with_context(|| format!("open rocksdb at {}", path.display()))?;
    tracing::info!(
      "rocksdb: {} MB block cache (shared), {} MB per-CF write buffer capped at {} MB total, bloom filters on",
      block_cache_mb,
      write_buffer_mb,
      total_write_buffer_mb
    );

    Ok(Db {
      inner: Arc::new(db),
      create_lock: RwLock::new(()),
      temp_path,
    })
  }

  pub fn open_tree(&self, name: &str) -> Result<Tree> {
    if self.inner.cf_handle(name).is_none() {
      let _guard = self.create_lock.write().unwrap();
      // Re-check: another caller may have created it while we waited.
      if self.inner.cf_handle(name).is_none() {
        // create_cf needs &mut DB, which we do not have behind Arc. Every tree
        // the indexer uses is in KNOWN_TREES and created at open, so reaching
        // here means a genuinely unexpected name.
        anyhow::bail!(
          "column family {name} does not exist; add it to store::KNOWN_TREES"
        );
      }
    }
    Ok(Tree {
      db: Arc::clone(&self.inner),
      name: name.to_string(),
    })
  }

  pub fn flush(&self) -> Result<()> {
    self.inner.flush().context("rocksdb flush")?;
    Ok(())
  }

  /// Rewrites every column family from scratch.
  ///
  /// Table options such as bloom filters are baked into an SST when it is
  /// written, so enabling them only affects future files - data already on disk
  /// keeps the old format until it happens to be compacted. This forces that
  /// rewrite, so an index built before filters were configured gets them
  /// without a full re-index.
  ///
  /// Expensive: it reads and rewrites the entire database. Intended as a
  /// one-off migration, gated behind SPOOKY_COMPACT_ON_START.
  pub fn compact_all(&self) -> Result<()> {
    for name in KNOWN_TREES {
      if let Some(cf) = self.inner.cf_handle(name) {
        self
          .inner
          .compact_range_cf(&cf, None::<&[u8]>, None::<&[u8]>);
      }
    }
    Ok(())
  }
}

impl Clone for Db {
  fn clone(&self) -> Self {
    Db {
      inner: Arc::clone(&self.inner),
      create_lock: RwLock::new(()),
      // Only the original owns the temp directory, so clones never delete it.
      temp_path: None,
    }
  }
}

impl Drop for Db {
  fn drop(&mut self) {
    if let Some(path) = self.temp_path.take() {
      let _ = std::fs::remove_dir_all(path);
    }
  }
}

fn num_background_threads() -> i32 {
  std::thread::available_parallelism()
    .map(|n| n.get() as i32)
    .unwrap_or(4)
    .clamp(2, 8)
}

pub struct Tree {
  db: Arc<Rdb>,
  name: String,
}

/// Writes to any number of trees that land together or not at all.
#[derive(Default)]
pub struct Batch {
  ops: Vec<(String, Vec<u8>, Vec<u8>)>,
}

impl Batch {
  pub fn insert(&mut self, tree: &Tree, key: impl Into<Vec<u8>>, value: impl Into<Vec<u8>>) {
    self.ops.push((tree.name.clone(), key.into(), value.into()));
  }

  /// Applies every write atomically, through the database `tree` belongs to.
  pub fn commit(self, tree: &Tree) -> Result<()> {
    if self.ops.is_empty() {
      return Ok(());
    }
    let mut wb = WriteBatch::default();
    for (name, key, value) in &self.ops {
      let cf = tree
        .db
        .cf_handle(name)
        .with_context(|| format!("missing column family {name}"))?;
      wb.put_cf(&cf, key, value);
    }
    tree.db.write(wb).map_err(|e| anyhow::anyhow!("rocksdb batch: {e}"))
  }
}

impl Tree {
  fn cf(&self) -> Result<Arc<rocksdb::BoundColumnFamily<'_>>> {
    self
      .db
      .cf_handle(&self.name)
      .with_context(|| format!("missing column family {}", self.name))
  }

  pub fn get<K: AsRef<[u8]>>(&self, key: K) -> Result<Option<IVec>> {
    let cf = self.cf()?;
    Ok(self.db.get_cf(&cf, key.as_ref())?.map(IVec::from))
  }

  /// Batched point lookups, in the order given.
  ///
  /// RocksDB services these together, which is markedly cheaper than the same
  /// number of individual `get` calls: one lock acquisition, shared block-cache
  /// lookups, and better locality. Used to prefetch a whole block's UTXO reads
  /// before the sequential pass, so they leave the critical path.
  pub fn multi_get<K: AsRef<[u8]>>(&self, keys: &[K]) -> Result<Vec<Option<IVec>>> {
    let cf = self.cf()?;
    let refs: Vec<(&Arc<rocksdb::BoundColumnFamily<'_>>, &[u8])> =
      keys.iter().map(|k| (&cf, k.as_ref())).collect();
    let mut out = Vec::with_capacity(keys.len());
    for r in self.db.multi_get_cf(refs) {
      out.push(r.map_err(|e| anyhow::anyhow!("rocksdb multi_get: {e}"))?.map(IVec::from));
    }
    Ok(out)
  }

  pub fn insert<K: AsRef<[u8]>, V: AsRef<[u8]>>(&self, key: K, value: V) -> Result<()> {
    let cf = self.cf()?;
    self.db.put_cf(&cf, key.as_ref(), value.as_ref())?;
    Ok(())
  }

  /// Deletes every key in `start..end` (half-open) without reading them.
  ///
  /// RocksDB writes a single range tombstone, so the cost is independent of how
  /// many keys the range covers. The alternative - scanning the range and
  /// deleting key by key - stalled the indexer outright: `range()` materialises
  /// keys AND values, and undo records run to tens of MB each.
  pub fn delete_range<K: AsRef<[u8]>>(&self, start: K, end: K) -> Result<()> {
    let cf = self.cf()?;
    self
      .db
      .delete_range_cf(&cf, start.as_ref(), end.as_ref())
      .map_err(|e| anyhow::anyhow!("rocksdb delete_range: {e}"))?;
    Ok(())
  }

  pub fn remove<K: AsRef<[u8]>>(&self, key: K) -> Result<()> {
    let cf = self.cf()?;
    self.db.delete_cf(&cf, key.as_ref())?;
    Ok(())
  }

  /// Ordered scan of every key beginning with `prefix`.
  ///
  /// Deliberately does NOT use RocksDB's prefix iterator, which needs a prefix
  /// extractor configured and can otherwise return keys outside the prefix.
  /// Seeking then stopping at the first non-match matches sled's semantics.
  pub fn scan_prefix<P: AsRef<[u8]>>(&self, prefix: P) -> Result<Vec<Result<(IVec, IVec)>>> {
    let cf = self.cf()?;
    let prefix = prefix.as_ref().to_vec();
    let mut out = Vec::new();
    let iter = self
      .db
      .iterator_cf(&cf, IteratorMode::From(&prefix, Direction::Forward));
    for item in iter {
      match item {
        Ok((k, v)) => {
          if !k.starts_with(&prefix) {
            break;
          }
          out.push(Ok((IVec(k.to_vec()), IVec(v.to_vec()))));
        }
        Err(e) => out.push(Err(anyhow::anyhow!("rocksdb iterate: {e}"))),
      }
    }
    Ok(out)
  }

  /// Streams every row under `prefix` to `visit` without collecting them.
  /// `scan_prefix` materialises the whole result, which for a tree of
  /// millions of rows means hundreds of MB held at once. `visit` returns
  /// whether to keep going, so a paged read can stop once it has enough.
  pub fn for_each_prefix<P: AsRef<[u8]>>(
    &self,
    prefix: P,
    mut visit: impl FnMut(&[u8], &[u8]) -> Result<bool>,
  ) -> Result<()> {
    let cf = self.cf()?;
    let prefix = prefix.as_ref();
    let iter = self
      .db
      .iterator_cf(&cf, IteratorMode::From(prefix, Direction::Forward));
    for item in iter {
      let (k, v) = item.map_err(|e| anyhow::anyhow!("rocksdb iterate: {e}"))?;
      if !k.starts_with(prefix) || !visit(&k, &v)? {
        break;
      }
    }
    Ok(())
  }

  /// Ordered scan over a half-open key range, `start..end`.
  pub fn range<K: AsRef<[u8]>>(&self, range: Range<K>) -> Result<Vec<Result<(IVec, IVec)>>> {
    let cf = self.cf()?;
    let start = range.start.as_ref().to_vec();
    let end = range.end.as_ref().to_vec();
    let mut out = Vec::new();
    let iter = self
      .db
      .iterator_cf(&cf, IteratorMode::From(&start, Direction::Forward));
    for item in iter {
      match item {
        Ok((k, v)) => {
          if k.as_ref() >= end.as_slice() {
            break;
          }
          out.push(Ok((IVec(k.to_vec()), IVec(v.to_vec()))));
        }
        Err(e) => out.push(Err(anyhow::anyhow!("rocksdb iterate: {e}"))),
      }
    }
    Ok(out)
  }

  /// Ordered scan of KEYS ONLY, starting at `start`.
  ///
  /// Keys only, deliberately. The undo tree holds roughly 1 MB per block and is
  /// retained in full, so materialising values while scanning it would exhaust
  /// memory. Callers that scan large trees want the keys anyway.
  pub fn keys_from<K: AsRef<[u8]>>(&self, start: K) -> Result<Vec<IVec>> {
    let cf = self.cf()?;
    let mut out = Vec::new();
    let iter = self
      .db
      .iterator_cf(&cf, IteratorMode::From(start.as_ref(), Direction::Forward));
    for item in iter {
      let (k, _) = item.map_err(|e| anyhow::anyhow!("rocksdb iterate: {e}"))?;
      out.push(IVec(k.to_vec()));
    }
    Ok(out)
  }

  /// Streams rows from `start` (inclusive) forwards. `visit` returns whether
  /// to keep going.
  pub fn for_each_from<K: AsRef<[u8]>>(
    &self,
    start: K,
    mut visit: impl FnMut(&[u8], &[u8]) -> Result<bool>,
  ) -> Result<()> {
    let cf = self.cf()?;
    let iter = self
      .db
      .iterator_cf(&cf, IteratorMode::From(start.as_ref(), Direction::Forward));
    for item in iter {
      let (k, v) = item.map_err(|e| anyhow::anyhow!("rocksdb iterate: {e}"))?;
      if !visit(&k, &v)? {
        break;
      }
    }
    Ok(())
  }

  /// Streams rows backwards, from the last key at or below `start`. An empty
  /// `start` means the end of the tree.
  pub fn for_each_rev_from<K: AsRef<[u8]>>(
    &self,
    start: K,
    mut visit: impl FnMut(&[u8], &[u8]) -> Result<bool>,
  ) -> Result<()> {
    let cf = self.cf()?;
    let start = start.as_ref();
    let mode = if start.is_empty() {
      IteratorMode::End
    } else {
      IteratorMode::From(start, Direction::Reverse)
    };
    for item in self.db.iterator_cf(&cf, mode) {
      let (k, v) = item.map_err(|e| anyhow::anyhow!("rocksdb iterate: {e}"))?;
      if !visit(&k, &v)? {
        break;
      }
    }
    Ok(())
  }

  /// Exact key count, by full scan.
  ///
  /// DANGEROUS on large trees: this walks every key, which pulls the whole
  /// tree through the block cache. Observed spiking the process from 6 GB to
  /// 16 GB and saturating a core when called on the 5.6M-entry dogemap table
  /// from an API handler. Prefer `approximate_len` for anything user-facing;
  /// this remains for tests and small trees.
  pub fn len(&self) -> Result<usize> {
    let cf = self.cf()?;
    Ok(self.db.iterator_cf(&cf, IteratorMode::Start).count())
  }

  /// Estimated key count, O(1) from RocksDB's own statistics.
  ///
  /// Approximate: it does not account for keys that are written and later
  /// deleted but not yet compacted away. Accurate enough for a headline
  /// "claimed" figure, and it cannot blow up memory the way a full scan can.
  pub fn approximate_len(&self) -> Result<u64> {
    let cf = self.cf()?;
    Ok(
      self
        .db
        .property_int_value_cf(&cf, "rocksdb.estimate-num-keys")
        .map_err(|e| anyhow::anyhow!("rocksdb property: {e}"))?
        .unwrap_or(0),
    )
  }

  pub fn is_empty(&self) -> Result<bool> {
    Ok(self.len()? == 0)
  }
}

#[cfg(test)]
mod bench {
  use super::*;
  use std::time::Instant;

  /// Not a correctness test - a throughput probe.
  ///
  /// Establishes what this shim actually delivers per second, so indexer
  /// throughput can be judged against the store's ceiling instead of guessed at.
  #[test]
  fn store_throughput_probe() {
    let db = Db::temporary().unwrap();
    let tree = db.open_tree("utxo_by_outpoint").unwrap();

    let n = 200_000usize;
    let keys: Vec<String> = (0..n)
      .map(|i| format!("{:064x}:{}", i, i % 8))
      .collect();
    let value = vec![0u8; 64];

    let t = Instant::now();
    for k in &keys {
      tree.insert(k.as_bytes(), &value).unwrap();
    }
    let writes = t.elapsed();

    let t = Instant::now();
    let mut hits = 0usize;
    for k in &keys {
      if tree.get(k.as_bytes()).unwrap().is_some() {
        hits += 1;
      }
    }
    let reads = t.elapsed();

    let t = Instant::now();
    let refs: Vec<&[u8]> = keys.iter().map(|k| k.as_bytes()).collect();
    let mut mg_hits = 0usize;
    for chunk in refs.chunks(4096) {
      for r in tree.multi_get(chunk).unwrap() {
        if r.is_some() {
          mg_hits += 1;
        }
      }
    }
    let multi = t.elapsed();

    // scan_prefix is what the indexer performs for EVERY transaction input,
    // to find inscriptions sitting on the output being spent. Each call builds
    // a RocksDB iterator and seeks it, which is far more expensive than a point
    // lookup - this measures how much more.
    let t = Instant::now();
    let scans = 20_000usize;
    let mut found = 0usize;
    for k in keys.iter().take(scans) {
      found += tree.scan_prefix(k.as_bytes()).unwrap().len();
    }
    let scan = t.elapsed();

    assert_eq!(hits, n);
    assert_eq!(mg_hits, n);
    assert_eq!(found, scans);

    println!(
      "STORE PROBE: scan_prefix {:.0}/s  ({:.1} us each)",
      scans as f64 / scan.as_secs_f64(),
      scan.as_secs_f64() * 1e6 / scans as f64,
    );

    println!(
      "STORE PROBE: {} ops | insert {:.0}/s | get {:.0}/s | multi_get {:.0}/s",
      n,
      n as f64 / writes.as_secs_f64(),
      n as f64 / reads.as_secs_f64(),
      n as f64 / multi.as_secs_f64(),
    );
  }
}
