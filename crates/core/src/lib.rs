use serde::Serialize;
use std::collections::HashMap;
use std::path::PathBuf;

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
  /// Blocks indexed between sled flushes. See SPOOKY_FLUSH_INTERVAL.
  pub flush_interval: u64,
}

impl Config {
  pub fn from_env() -> Self {
    let doge_conf = load_dogecoin_conf();

    let rpc_url = std::env::var("SPOOKY_RPC_URL")
      .or_else(|_| std::env::var("SPOOKY_DOGE_RPC_URL"))
      .ok()
      .or_else(|| doge_conf_rpc_url(&doge_conf))
      .unwrap_or_else(|| "http://127.0.0.1:22555".to_string());
    let rpc_user = std::env::var("SPOOKY_RPC_USER")
      .or_else(|_| std::env::var("SPOOKY_DOGE_RPC_USER"))
      .ok()
      .or_else(|| doge_conf.get("rpcuser").cloned())
      .unwrap_or_else(|| "spooks".to_string());
    let rpc_password = std::env::var("SPOOKY_RPC_PASSWORD")
      .or_else(|_| std::env::var("SPOOKY_RPC_PASS"))
      .or_else(|_| std::env::var("SPOOKY_DOGE_RPC_PASSWORD"))
      .or_else(|_| std::env::var("SPOOKY_DOGE_RPC_PASS"))
      .ok()
      .or_else(|| doge_conf.get("rpcpassword").cloned())
      .unwrap_or_else(|| "spooksociety".to_string());
    let rpc_concurrency = std::env::var("SPOOKY_RPC_CONCURRENCY")
      .ok()
      .and_then(|v| v.parse().ok())
      .unwrap_or(4usize);
    let bind_addr = std::env::var("SPOOKY_BIND_ADDR")
      .or_else(|_| std::env::var("SPOOKY_HTTP_ADDR"))
      .unwrap_or_else(|_| "127.0.0.1:8787".to_string());
    let data_dir = std::env::var("SPOOKY_DATA_DIR").unwrap_or_else(|_| "./data".to_string());
    let first_inscription_height = std::env::var("SPOOKY_FIRST_INSCRIPTION_HEIGHT")
      .or_else(|_| std::env::var("SPOOKY_START_HEIGHT"))
      .ok()
      .and_then(|v| v.parse().ok())
      .unwrap_or(4_600_000);
    let first_dune_height = std::env::var("SPOOKY_FIRST_DUNE_HEIGHT")
      .ok()
      .and_then(|v| v.parse().ok())
      .unwrap_or(5_084_000);
    let stop_height = std::env::var("SPOOKY_STOP_HEIGHT")
      .ok()
      .and_then(|v| v.parse().ok());
    let content_store = std::env::var("SPOOKY_CONTENT_STORE").unwrap_or_else(|_| "full".to_string());
    // Blocks indexed between sled flushes. The indexer previously fsynced after
    // every block, which dominated per-block cost during backfill.
    // 1 restores the old flush-every-block behaviour.
    let flush_interval = std::env::var("SPOOKY_FLUSH_INTERVAL")
      .ok()
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
  if let Ok(p) = std::env::var("SPOOKY_DOGECOIN_CONF") {
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
