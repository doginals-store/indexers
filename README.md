# Doginals indexers

Indexers for Dogecoin's metaprotocols, as used by [The Doginals Explorer](https://explorer.doginals.store). They read a Dogecoin Core node block by block and keep the results in a local RocksDB store.

| Indexer | What it records |
|---|---|
| Doginals inscriptions | Every inscription: where it is now, its content type and bytes, and its number in chain order, overall and per kind (text, JSON, images and so on). |
| DRC-20 | Deploys, mints and transfers; balances per address; holders per token; activity per token. |
| Dunes | Etchings, mints and transfers; balances and UTXOs per address; activity per dune. |
| Dogemaps | `N.dogemap` claims, first come first served. |
| DNS names | Dogecoin Names System names (`label.namespace`), registered as plain text or as JSON, following [spec v1.2](https://github.com/jonheaven/dns). The first valid inscription of a name owns it, and the name moves with that inscription. Records and chosen names only count when they come from the holder at the time, which is checked against the node. |

The DNS index reads inscriptions in the numbered order, so it starts once inscription numbering has caught up.

## Requirements

- A Dogecoin Core node with `server=1`, `txindex=1` and RPC enabled. It must be fully synced.
- Rust 1.85 or newer (the crates use the 2024 edition).
- A C++ toolchain and Clang, which the `rocksdb` crate needs to build.
- Plenty of disk space, more so with inscription content kept (`SPOOKY_CONTENT_STORE=full`).

## Run

```bash
cargo build --release
SPOOKY_RPC_URL=http://127.0.0.1:22555 \
SPOOKY_RPC_USER=your_rpc_user \
SPOOKY_RPC_PASSWORD=your_rpc_password \
SPOOKY_DATA_DIR=./data \
./target/release/doginals-indexer
```

Ctrl-C stops it after the current block. It resumes where it left off.

| Setting | Default | Meaning |
|---|---|---|
| `SPOOKY_RPC_URL` | from `dogecoin.conf`, else `http://127.0.0.1:22555` | Node RPC address |
| `SPOOKY_RPC_USER`, `SPOOKY_RPC_PASSWORD` | from `dogecoin.conf` | Node RPC login |
| `SPOOKY_DOGECOIN_CONF` | the node's usual location | Where to read `dogecoin.conf` |
| `SPOOKY_RPC_CONCURRENCY` | `4` | Parallel RPC requests |
| `SPOOKY_DATA_DIR` | `./data` | Where the index is written |
| `SPOOKY_FIRST_INSCRIPTION_HEIGHT` | `4600000` | First block read for inscriptions |
| `SPOOKY_FIRST_DUNE_HEIGHT` | `5084000` | First block read for Dunes |
| `SPOOKY_STOP_HEIGHT` | none | Stop at this height (for tests) |
| `SPOOKY_CONTENT_STORE` | `full` | `full` keeps inscription bytes |
| `SPOOKY_FLUSH_INTERVAL` | `64` | Blocks between flushes to disk |

Set `RUST_LOG` (for example `RUST_LOG=info`) to change how much is logged.

## Use as a library

`crates/indexer` (`spookyord-indexer`) has the indexing tasks and the read functions, for example `get_inscription`, `list_inscriptions`, `list_drc20_holdings`, `list_dune_holdings`, `get_dogemap`, `dns_get` and `dns_list`. Each takes the same `Config` (`crates/core`) and reads the store the indexer writes.

## Tests

```bash
cargo test --workspace
```

One test follows real inscriptions through a live node and is skipped by default. To run it, set `SPOOKY_DOGECOIN_CONF` and `DNS_TRACE` (the format is in the test's comment in `crates/indexer/src/dns.rs`), then run `cargo test --workspace -- --ignored`.

## Credits and license

Built on [SpookyOrd](https://github.com/tylordius/SpookyOrd) and released under the MIT license, as SpookyOrd is. See [LICENSE](LICENSE).
