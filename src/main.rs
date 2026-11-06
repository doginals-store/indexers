//! Runs every indexer against a Dogecoin Core node, with no web server.
//!
//! Settings come from the environment (see the README). The index is written
//! to `DOGEORD_DATA_DIR`; read it with the `dogeord-indexer` library.

use anyhow::Result;
use dogeord_core::Config;
use dogeord_indexer::{SharedState, run_indexer};
use std::time::Duration;
use tokio::sync::watch;
use tracing::{error, info};
use tracing_subscriber::EnvFilter;

#[tokio::main]
async fn main() -> Result<()> {
  tracing_subscriber::fmt()
    .with_env_filter(EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info")))
    .init();

  let cfg = Config::from_env();
  std::fs::create_dir_all(&cfg.data_dir)?;
  info!("indexing from {} into {}", cfg.rpc_url, cfg.data_dir);

  let (shutdown_tx, shutdown_rx) = watch::channel(false);

  // One-off and resumable: details for DRC-20 tokens deployed before deploys
  // were recorded. Does nothing once it has completed.
  let c = cfg.clone();
  tokio::spawn(async move {
    if let Err(e) = dogeord_indexer::backfill_drc20_deploys(c).await {
      error!("drc20 deploy backfill failed (it retries on the next start): {e:#}");
    }
  });

  // One-off and resumable: chain order for inscriptions indexed before it
  // was recorded. Numbering then follows the chain from 6 blocks behind.
  let c = cfg.clone();
  tokio::spawn(async move {
    if let Err(e) = dogeord_indexer::backfill_inscription_seq(c).await {
      error!("inscription order backfill stopped (it resumes on the next start): {e:#}");
    }
  });
  let c = cfg.clone();
  tokio::spawn(async move {
    loop {
      if let Err(e) = dogeord_indexer::run_inscription_numbering(c.clone()).await {
        error!("inscription numbering failed, retrying in a minute: {e:#}");
      }
      tokio::time::sleep(Duration::from_secs(60)).await;
    }
  });

  // DNS names follow inscription numbering. A failure retries the same
  // stretch, since nothing is written until a stretch is done.
  let c = cfg.clone();
  tokio::spawn(async move {
    loop {
      if let Err(e) = dogeord_indexer::run_dns_index(c.clone()).await {
        error!("dns index failed, retrying in a minute: {e:#}");
      }
      tokio::time::sleep(Duration::from_secs(60)).await;
    }
  });

  let indexer = tokio::spawn(run_indexer(cfg, SharedState::new(), shutdown_rx));

  #[cfg(unix)]
  let shutdown = async {
    let mut term = tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())?;
    tokio::select! {
      r = tokio::signal::ctrl_c() => r,
      _ = term.recv() => Ok(()),
    }
  };
  #[cfg(not(unix))]
  let shutdown = tokio::signal::ctrl_c();

  tokio::select! {
    res = indexer => res??,
    _ = shutdown => {
      info!("stopping: finishing the current block");
      let _ = shutdown_tx.send(true);
    }
  }
  Ok(())
}
