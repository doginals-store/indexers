//! The confirmed mainnet test records of the D:// v1 standard (section 6),
//! read from the chain bytes in `mainnet-vectors.json`, and mutations of
//! them that must be refused.

use dproto::*;
use serde_json::Value;

const POST: &str = "5eedf507d704e35c037060e4ac966262b6eae10ef89b9ce2be11d2ec2697c72ei0";
const BOT: &str = "DSi6So8MHAArNYSgWxhpVrU6PtfHgVa11N";
const SUPPORT: &str = "DH7D5zBwbAWsVo1HiVKQoMCk6fQuuBCDEC";
const BILLY: &str = "DBMBjmyKSAKboj5NrXeER2rYWkpxETvUMn";

struct Tx {
  script_sig: Vec<u8>,
  inputs: Vec<Outpoint>,
  addrs: Vec<Option<String>>,
  outputs: Vec<TxOut>,
}

fn vector(name: &str) -> Tx {
  let all: Value = serde_json::from_str(include_str!("mainnet-vectors.json")).unwrap();
  let v = &all[name];
  Tx {
    script_sig: hex::decode(v["script_sig"].as_str().unwrap()).unwrap(),
    inputs: v["inputs"]
      .as_array()
      .unwrap()
      .iter()
      .map(|i| Outpoint { txid: i["txid"].as_str().unwrap().into(), vout: i["vout"].as_u64().unwrap() as u32 })
      .collect(),
    addrs: v["inputs"].as_array().unwrap().iter().map(|i| Some(i["address"].as_str().unwrap().to_string())).collect(),
    outputs: v["outputs"]
      .as_array()
      .unwrap()
      .iter()
      .map(|o| TxOut { koinu: o["koinu"].as_u64().unwrap(), script: hex::decode(o["script"].as_str().unwrap()).unwrap() })
      .collect(),
  }
}

/// What a standard Doginals parser keeps of a one-piece reveal: the data
/// push after the piece number 0.
fn standard_body(script_sig: &[u8]) -> Vec<u8> {
  let p = script_pushes(script_sig).unwrap();
  assert_eq!(p[0], b"ord");
  assert_eq!(p[2], b"application/json");
  p[4].clone()
}

fn record(name: &str) -> (Record, Tx) {
  let tx = vector(name);
  let (d, lenient) = read_inscription(&standard_body(&tx.script_sig), Some(&tx.script_sig));
  assert!(lenient, "{name}: the body is split over several pushes of one piece");
  match d {
    Detect::Record(r) => (*r, tx),
    other => panic!("{name}: {other:?}"),
  }
}

fn posts(t: &[u8; 11]) -> Vec<PostCandidate> {
  if post_target(POST).as_ref() == Some(t) { vec![PostCandidate { id: POST.into(), author: BOT.into() }] } else { vec![] }
}

fn pay(tx: &Tx) -> Result<Option<VerifiedPayment>, String> {
  verify_payment(&PaymentTx { inputs: &tx.inputs, input_addresses: &tx.addrs, outputs: &tx.outputs }, &registrar_pubkeys(), posts, |_| vec![])
}

#[test]
fn the_pinned_registrar_key_is_the_registrar_address() {
  let k = &REGISTRAR_KEYS[0];
  assert_eq!(p2pkh_address(&hash160(&hex::decode(k.pubkey_hex).unwrap())), k.address);
  assert_eq!(registrar_pubkeys().len(), 1);
}

#[test]
fn the_post_comment_and_quote_are_valid() {
  let (post, tx) = record("post");
  assert_eq!((post.rtype, post.addr.as_str()), (RecordType::Post, BOT));
  assert_eq!(
    post.text.as_deref(),
    Some("D:// protocol v1 test vector from the DogeFeed bot. Created through test.dogefeed.app for indexer verification.")
  );
  verify_inscription(&post, &tx.outputs, &[BOT], None).unwrap();

  let (comment, tx) = record("comment");
  assert_eq!((comment.rtype, comment.addr.as_str(), comment.reference.as_deref()), (RecordType::Comment, SUPPORT, Some(POST)));
  assert_eq!(comment.text.as_deref(), Some("D:// test comment for indexer verification."));
  verify_inscription(&comment, &tx.outputs, &[SUPPORT], Some(BOT)).unwrap();

  let (quote, tx) = record("quote");
  assert_eq!((quote.rtype, quote.reference.as_deref()), (RecordType::Quote, Some(POST)));
  assert_eq!(quote.text.as_deref(), Some("D:// test quote for indexer verification."));
  verify_inscription(&quote, &tx.outputs, &[SUPPORT], Some(BOT)).unwrap();
}

#[test]
fn the_follow_like_branch_and_tip_are_valid() {
  let f = pay(&vector("follow")).unwrap().unwrap();
  assert_eq!((f.op, f.author.as_str(), &f.target), (Op::Follow, BOT, &Target::Address(BILLY.into())));
  assert_eq!((f.recipient, f.fee), (Some((0, 88_000_000)), (1, 10_000_000)));
  for (name, op, to) in [("like", Op::Like, 88_000_000), ("branch", Op::Branch, 88_000_000), ("tip", Op::Tip, 90_000_000)] {
    let p = pay(&vector(name)).unwrap().unwrap();
    assert_eq!((p.op, p.author.as_str(), &p.target), (op, SUPPORT, &Target::Post(POST.into())), "{name}");
    assert_eq!((p.recipient, p.fee), (Some((0, to)), (1, 10_000_000)), "{name}");
  }
}

#[test]
fn ordinary_transactions_are_not_payments() {
  // The post's reveal has no OP_RETURN.
  assert_eq!(pay(&vector("post")), Ok(None));
}

#[test]
fn a_changed_record_or_a_wrong_payout_is_refused() {
  let (post, tx) = record("post");
  let mut edited = post.clone();
  edited.value["b"]["text"] = "something else".into();
  assert!(verify_inscription(&edited, &tx.outputs, &[BOT], None).unwrap_err().contains("author's signature"));
  let mut forged = post.clone();
  forged.att_sig = record("comment").0.att_sig;
  assert!(verify_inscription(&forged, &tx.outputs, &[BOT], None).unwrap_err().contains("attestation"));
  assert!(verify_inscription(&post, &tx.outputs, &[SUPPORT], None).unwrap_err().contains("not to its author"));
  let mut cheap = tx.outputs.clone();
  cheap[1].koinu = 9_999_999;
  assert!(verify_inscription(&post, &cheap, &[BOT], None).unwrap_err().contains("DogeFeed"));
  let (comment, tx) = record("comment");
  assert!(verify_inscription(&comment, &tx.outputs, &[SUPPORT], None).is_err(), "a comment needs its parent");
  assert!(verify_inscription(&comment, &tx.outputs, &[SUPPORT], Some(BILLY)).unwrap_err().contains("less than 0.01"));
}

#[test]
fn a_mutated_payment_is_refused() {
  // A flipped bit of the registrar's signature.
  let mut tx = vector("like");
  let n = tx.outputs.len() - 1;
  tx.outputs[n].script[60] ^= 1;
  assert!(pay(&tx).unwrap_err().contains("does not verify"));
  // A different payout than the registrar signed.
  let mut tx = vector("like");
  tx.outputs[0].koinu -= 1;
  assert!(pay(&tx).unwrap_err().contains("does not verify"));
  // Inputs from two addresses.
  let mut tx = vector("tip");
  tx.inputs.push(Outpoint { txid: "00".repeat(32), vout: 0 });
  tx.addrs.push(Some(BOT.into()));
  assert!(pay(&tx).unwrap_err().contains("more than one address"));
  // A second OP_RETURN.
  let mut tx = vector("branch");
  tx.outputs.push(TxOut { koinu: 0, script: vec![0x6a, 0x01, 0x00] });
  assert!(pay(&tx).unwrap_err().contains("OP_RETURN"));
  // An unknown post.
  let tx = vector("like");
  let r = verify_payment(&PaymentTx { inputs: &tx.inputs, input_addresses: &tx.addrs, outputs: &tx.outputs }, &registrar_pubkeys(), |_| vec![], |_| vec![]);
  assert!(r.unwrap_err().contains("not a known"));
  // A tip that is not 90/10.
  let mut tx = vector("tip");
  tx.outputs[1].koinu += 1_000_000;
  assert!(pay(&tx).is_err());
}

#[test]
fn canonical_json_follows_rfc_8785() {
  let v: Value = serde_json::from_str(r#"{"b":[1,2.5,1e21,1e-7,0.000001,-0,123456789012],"a":"\u0007\n\"é😀","\u20ac":1,"\ud83d\ude00":2,"z":null}"#).unwrap();
  assert_eq!(
    jcs(&v).unwrap(),
    "{\"a\":\"\\u0007\\n\\\"é😀\",\"b\":[1,2.5,1e+21,1e-7,0.000001,0,123456789012],\"z\":null,\"€\":1,\"😀\":2}"
  );
}

#[test]
fn addresses_round_trip() {
  let h = address_hash(BOT).unwrap();
  assert_eq!(p2pkh_address(&h), BOT);
  assert!(address_hash("DSi6So8MHAArNYSgWxhpVrU6PtfHgVa11M").is_none(), "bad checksum");
  assert_eq!(script_address(&p2pkh_script(&h)).as_deref(), Some(BOT));
}

#[test]
fn records_that_are_not_v1_dogefeed_are_told_apart() {
  assert_eq!(parse_record(br#"{"p":"drc-20","op":"mint"}"#), Detect::NotDproto);
  assert_eq!(parse_record(br#"{"p":"D://","v":2,"map":{"app":"dogefeed"}}"#), Detect::UnknownVersion);
  assert_eq!(parse_record(br#"{"p":"D://","v":1,"map":{"app":"other"}}"#), Detect::NotDproto);
  match parse_record(br#"{"p":"D://","v":1,"b":{},"map":{"app":"dogefeed","type":"post","ts":1},"aip":{"alg":"DOGE_ECDSA","addr":"D"}}"#) {
    Detect::Invalid(e) => assert!(e.contains("aip.sig"), "{e}"),
    other => panic!("{other:?}"),
  }
  assert!(is_inscription_id(POST));
  assert!(!is_inscription_id("5EEDF507d704e35c037060e4ac966262b6eae10ef89b9ce2be11d2ec2697c72ei0"));
  assert_eq!(tip_split(100_000_000), (90_000_000, 10_000_000));
}
