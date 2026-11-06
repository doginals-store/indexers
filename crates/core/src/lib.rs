use serde::Serialize;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// Reads a setting from the environment: `DOGEORD_<KEY>`, or the older
/// `SPOOKY_<KEY>` name it had before the fork, so existing setups keep working.
pub fn setting(key: &str) -> Option<String> {
  std::env::var(format!("DOGEORD_{key}")).ok().or_else(|| std::env::var(format!("SPOOKY_{key}")).ok())
}

/// The first of several setting names that is set.
fn first_setting(keys: &[&str]) -> Option<String> {
  keys.iter().find_map(|k| setting(k))
}

/// The store's folder name. Indexes made before the fork used the older name,
/// and are kept where they are.
pub const DB_DIR: &str = "dogeord.rocksdb";
pub const LEGACY_DB_DIR: &str = "spookyord.rocksdb";

/// Where the store lives under `data_dir`: `dogeord.rocksdb`, unless only an
/// index from before the fork (`spookyord.rocksdb`) is there.
pub fn db_path_in(data_dir: &str) -> String {
  let new = Path::new(data_dir).join(DB_DIR);
  let old = Path::new(data_dir).join(LEGACY_DB_DIR);
  let dir = if !new.exists() && old.exists() { LEGACY_DB_DIR } else { DB_DIR };
  format!("{data_dir}/{dir}")
}

#[derive(Debug, Clone)]
pub struct Config {
  pub rpc_url: String,
  pub rpc_user: String,
  pub rpc_password: String,
  pub rpc_concurrency: usize,
  pub bind_addr: String,
  pub data_dir: String,
  pub first_inscription_height: u64,
  pub first_dune_height: u64,
  pub stop_height: Option<u64>,
  pub content_store: String,
  /// Blocks indexed between flushes. See DOGEORD_FLUSH_INTERVAL.
  pub flush_interval: u64,
}

impl Config {
  pub fn from_env() -> Self {
    let doge_conf = load_dogecoin_conf();

    let rpc_url = first_setting(&["RPC_URL", "DOGE_RPC_URL"])
      .or_else(|| doge_conf_rpc_url(&doge_conf))
      .unwrap_or_else(|| "http://127.0.0.1:22555".to_string());
    let rpc_user = first_setting(&["RPC_USER", "DOGE_RPC_USER"])
      .or_else(|| doge_conf.get("rpcuser").cloned())
      .unwrap_or_default();
    let rpc_password = first_setting(&["RPC_PASSWORD", "RPC_PASS", "DOGE_RPC_PASSWORD", "DOGE_RPC_PASS"])
      .or_else(|| doge_conf.get("rpcpassword").cloned())
      .unwrap_or_default();
    let rpc_concurrency = setting("RPC_CONCURRENCY").and_then(|v| v.parse().ok()).unwrap_or(4usize);
    let bind_addr = first_setting(&["BIND_ADDR", "HTTP_ADDR"]).unwrap_or_else(|| "127.0.0.1:8787".to_string());
    let data_dir = setting("DATA_DIR").unwrap_or_else(|| "./data".to_string());
    let first_inscription_height = first_setting(&["FIRST_INSCRIPTION_HEIGHT", "START_HEIGHT"])
      .and_then(|v| v.parse().ok())
      .unwrap_or(4_600_000);
    let first_dune_height = setting("FIRST_DUNE_HEIGHT").and_then(|v| v.parse().ok()).unwrap_or(5_084_000);
    let stop_height = setting("STOP_HEIGHT").and_then(|v| v.parse().ok());
    let content_store = setting("CONTENT_STORE").unwrap_or_else(|| "full".to_string());
    // Blocks indexed between flushes. Flushing after every block dominated
    // per-block cost during backfill; 1 restores that behaviour.
    let flush_interval = setting("FLUSH_INTERVAL")
      .and_then(|v| v.parse().ok())
      .filter(|v| *v > 0)
      .unwrap_or(64u64);

    Self {
      rpc_url,
      rpc_user,
      rpc_password,
      rpc_concurrency,
      bind_addr,
      data_dir,
      first_inscription_height,
      first_dune_height,
      stop_height,
      content_store,
      flush_interval,
    }
  }

  pub fn protocol_start_height(&self) -> u64 {
    self.first_inscription_height.min(self.first_dune_height)
  }

  /// Where this config's store lives; see [`db_path_in`].
  pub fn db_path(&self) -> String {
    db_path_in(&self.data_dir)
  }
}

fn load_dogecoin_conf() -> HashMap<String, String> {
  let mut out = HashMap::new();
  let path = dogecoin_conf_path();
  let Ok(raw) = std::fs::read_to_string(path) else {
    return out;
  };

  for line in raw.lines() {
    let trimmed = line.trim();
    if trimmed.is_empty() || trimmed.starts_with('#') {
      continue;
    }
    let no_inline_comment = trimmed.split('#').next().unwrap_or("").trim();
    if no_inline_comment.is_empty() {
      continue;
    }
    let Some((k, v)) = no_inline_comment.split_once('=') else {
      continue;
    };
    out.insert(k.trim().to_lowercase(), v.trim().to_string());
  }

  out
}

fn dogecoin_conf_path() -> PathBuf {
  if let Some(p) = setting("DOGECOIN_CONF") {
    return PathBuf::from(p);
  }
  if let Ok(home) = std::env::var("HOME") {
    return PathBuf::from(home).join(".dogecoin").join("dogecoin.conf");
  }
  PathBuf::from(".dogecoin/dogecoin.conf")
}

fn doge_conf_rpc_url(conf: &HashMap<String, String>) -> Option<String> {
  let port = conf
    .get("rpcport")
    .and_then(|p| p.parse::<u16>().ok())
    .unwrap_or(22555);
  let host = conf
    .get("rpcbind")
    .or_else(|| conf.get("rpcconnect"))
    .map(|s| s.split(',').next().unwrap_or(s).trim().to_string())
    .filter(|s| !s.is_empty())
    .unwrap_or_else(|| "127.0.0.1".to_string());
  Some(format!("http://{host}:{port}"))
}

#[derive(Debug, Clone, Serialize)]
pub struct StatusResponse {
  pub network: String,
  pub protocol_start_height: u64,
  pub chain_tip: u64,
  pub indexed_height: u64,
  pub remaining_blocks: u64,
  pub progress_percent: f64,
  pub phase: String,
  pub lag: u64,
  pub indexing: bool,
  pub db_path: String,
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn settings_read_the_new_name_then_the_old_one() {
    // Names used only by this test, so it cannot disturb any other.
    unsafe {
      std::env::set_var("SPOOKY_ZZ_ONLY_OLD", "old");
      std::env::set_var("SPOOKY_ZZ_BOTH", "old");
      std::env::set_var("DOGEORD_ZZ_BOTH", "new");
      std::env::set_var("DOGEORD_ZZ_ONLY_NEW", "new");
    }
    assert_eq!(setting("ZZ_ONLY_OLD").as_deref(), Some("old"));
    assert_eq!(setting("ZZ_BOTH").as_deref(), Some("new"));
    assert_eq!(setting("ZZ_ONLY_NEW").as_deref(), Some("new"));
    assert_eq!(setting("ZZ_NEITHER"), None);
    assert_eq!(first_setting(&["ZZ_NEITHER", "ZZ_ONLY_OLD"]).as_deref(), Some("old"));
  }

  #[test]
  fn an_index_from_before_the_fork_is_kept() {
    let base = std::env::temp_dir().join(format!("dogeord-core-test-{}", std::process::id()));
    let dir = base.to_str().unwrap().to_string();
    std::fs::create_dir_all(&base).unwrap();
    // Nothing there yet: a new index gets the new name.
    assert_eq!(db_path_in(&dir), format!("{dir}/{DB_DIR}"));
    // Only the old index: it is used where it is.
    std::fs::create_dir_all(base.join(LEGACY_DB_DIR)).unwrap();
    assert_eq!(db_path_in(&dir), format!("{dir}/{LEGACY_DB_DIR}"));
    // Both: the new one wins.
    std::fs::create_dir_all(base.join(DB_DIR)).unwrap();
    assert_eq!(db_path_in(&dir), format!("{dir}/{DB_DIR}"));
    std::fs::remove_dir_all(&base).unwrap();
  }
}
