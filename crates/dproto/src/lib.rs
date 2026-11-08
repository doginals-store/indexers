//! D:// (the DogeFeed protocol), version 1, on Dogecoin: reading and
//! verifying its records.
//!
//! Posts, comments, quotes, edits and key links are Doginal inscriptions of
//! signed JSON. Likes, branches (reposts), follows, tips, reveals, deletes and
//! key revocations are payments carrying one 80-byte OP_RETURN, signed by the
//! DogeFeed registrar. This crate holds the rules that need no index: parsing,
//! canonical JSON (RFC 8785), Dogecoin signed messages, the registrar digest
//! and the amount checks. Resolving what a record points at (a parent post, a
//! linked key) is the indexer's part, passed in as closures.
//!
//! Amounts are integer koinu (1 DOGE = 100,000,000 koinu).

use std::sync::OnceLock;

use secp256k1::ecdsa::{RecoverableSignature, RecoveryId, Signature};
use secp256k1::hashes::{Hash, ripemd160};
use secp256k1::{Message, PublicKey, Secp256k1, VerifyOnly};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sha2::{Digest, Sha256};

pub const KOINU_PER_DOGE: u64 = 100_000_000;
/// Where DogeFeed is paid. Not the registrar's address.
pub const FEE_ADDRESS: &str = "D73nYZFPhhCx2JMqBqifF3BXH46Xbvk9v6";
/// DogeFeed's share, at least, on every record: 0.1 DOGE.
pub const MIN_FEE: u64 = 10_000_000;
/// A recipient's share, at least, where one is paid: 0.01 DOGE.
pub const MIN_RECIPIENT: u64 = 1_000_000;
/// Largest record body, as received and in canonical form.
pub const MAX_BODY: usize = 4096;
/// Records count once this deep; until then they are pending.
pub const CONFIRMATIONS: u64 = 6;

/// A published registrar key.
#[derive(Debug, Clone, Copy)]
pub struct RegistrarKey {
  pub kid: &'static str,
  pub pubkey_hex: &'static str,
  pub address: &'static str,
}

/// The registrar keys, pinned from the v1 standard. Keys are never dropped:
/// old records stay verifiable.
pub const REGISTRAR_KEYS: &[RegistrarKey] = &[RegistrarKey {
  kid: "dfreg1",
  pubkey_hex: "0393d51fc970f5b98eff5fe6e3f4758e3c76a118c23d2dc9ffee24ae9b01d3eebd",
  address: "D5n1bGXmDEkvgz6fDX1vHHtWYBwGrk5u2Q",
}];

pub fn registrar_address(kid: &str) -> Option<&'static str> {
  REGISTRAR_KEYS.iter().find(|k| k.kid == kid).map(|k| k.address)
}

pub fn registrar_pubkeys() -> Vec<PublicKey> {
  REGISTRAR_KEYS
    .iter()
    .filter_map(|k| hex::decode(k.pubkey_hex).ok().and_then(|b| PublicKey::from_slice(&b).ok()))
    .collect()
}

fn secp() -> &'static Secp256k1<VerifyOnly> {
  static S: OnceLock<Secp256k1<VerifyOnly>> = OnceLock::new();
  S.get_or_init(Secp256k1::verification_only)
}

// ---------------------------------------------------------------------------
// Hashes, base58 and addresses

pub fn sha256(data: &[u8]) -> [u8; 32] {
  Sha256::digest(data).into()
}

pub fn sha256d(data: &[u8]) -> [u8; 32] {
  sha256(&sha256(data))
}

pub fn hash160(data: &[u8]) -> [u8; 20] {
  ripemd160::Hash::hash(&sha256(data)).to_byte_array()
}

const B58: &[u8] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
/// Mainnet pay-to-public-key-hash version byte (addresses start with D).
pub const P2PKH_VERSION: u8 = 0x1e;

fn base58_decode(s: &str) -> Option<Vec<u8>> {
  let mut out: Vec<u8> = Vec::new();
  for c in s.bytes() {
    let mut carry = B58.iter().position(|&b| b == c)? as u32;
    for b in out.iter_mut().rev() {
      carry += (*b as u32) * 58;
      *b = (carry & 0xff) as u8;
      carry >>= 8;
    }
    while carry > 0 {
      out.insert(0, (carry & 0xff) as u8);
      carry >>= 8;
    }
  }
  let zeros = s.bytes().take_while(|&b| b == b'1').count();
  let mut v = vec![0u8; zeros];
  v.extend(out.into_iter().skip_while(|&b| b == 0));
  Some(v)
}

fn base58_encode(data: &[u8]) -> String {
  let mut digits: Vec<u8> = Vec::new();
  for &byte in data {
    let mut carry = byte as u32;
    for d in digits.iter_mut() {
      carry += (*d as u32) << 8;
      *d = (carry % 58) as u8;
      carry /= 58;
    }
    while carry > 0 {
      digits.push((carry % 58) as u8);
      carry /= 58;
    }
  }
  let mut s: String = data.iter().take_while(|&&b| b == 0).map(|_| '1').collect();
  s.extend(digits.iter().rev().map(|&d| B58[d as usize] as char));
  s
}

/// Version byte and payload of a Base58Check string, checksum verified.
pub fn base58check_decode(s: &str) -> Option<Vec<u8>> {
  let raw = base58_decode(s)?;
  if raw.len() < 5 {
    return None;
  }
  let (body, check) = raw.split_at(raw.len() - 4);
  (sha256d(body)[..4] == *check).then(|| body.to_vec())
}

pub fn base58check_encode(body: &[u8]) -> String {
  let mut v = body.to_vec();
  v.extend_from_slice(&sha256d(body)[..4]);
  base58_encode(&v)
}

/// The 20-byte hash of a mainnet P2PKH address.
pub fn address_hash(address: &str) -> Option<[u8; 20]> {
  let body = base58check_decode(address)?;
  if body.len() != 21 || body[0] != P2PKH_VERSION {
    return None;
  }
  body[1..].try_into().ok()
}

pub fn p2pkh_address(hash: &[u8; 20]) -> String {
  let mut body = vec![P2PKH_VERSION];
  body.extend_from_slice(hash);
  base58check_encode(&body)
}

pub fn p2pkh_script(hash: &[u8; 20]) -> Vec<u8> {
  let mut s = vec![0x76, 0xa9, 0x14];
  s.extend_from_slice(hash);
  s.extend_from_slice(&[0x88, 0xac]);
  s
}

/// The hash a P2PKH output script pays, if it is one.
pub fn script_p2pkh_hash(script: &[u8]) -> Option<[u8; 20]> {
  (script.len() == 25 && script[..3] == [0x76, 0xa9, 0x14] && script[23..] == [0x88, 0xac]).then(|| script[3..23].try_into().unwrap())
}

pub fn script_address(script: &[u8]) -> Option<String> {
  script_p2pkh_hash(script).map(|h| p2pkh_address(&h))
}

fn compact_size(out: &mut Vec<u8>, n: u64) {
  match n {
    0..=252 => out.push(n as u8),
    253..=0xffff => {
      out.push(0xfd);
      out.extend_from_slice(&(n as u16).to_le_bytes());
    }
    0x1_0000..=0xffff_ffff => {
      out.push(0xfe);
      out.extend_from_slice(&(n as u32).to_le_bytes());
    }
    _ => {
      out.push(0xff);
      out.extend_from_slice(&n.to_le_bytes());
    }
  }
}

// ---------------------------------------------------------------------------
// Dogecoin signed messages

pub fn message_hash(message: &str) -> [u8; 32] {
  let mut buf = b"\x19Dogecoin Signed Message:\n".to_vec();
  compact_size(&mut buf, message.len() as u64);
  buf.extend_from_slice(message.as_bytes());
  sha256d(&buf)
}

/// A 65-byte recoverable signature: standard base64 as producers write it;
/// URL-safe base64 and hex are read too, as the reference verifier does.
fn decode_sig65(sig: &str) -> Option<[u8; 65]> {
  use base64::Engine;
  use base64::engine::general_purpose::{STANDARD, STANDARD_NO_PAD, URL_SAFE, URL_SAFE_NO_PAD};
  let decoded = [STANDARD, STANDARD_NO_PAD, URL_SAFE, URL_SAFE_NO_PAD]
    .iter()
    .find_map(|e| e.decode(sig).ok().filter(|b| b.len() == 65))
    .or_else(|| (sig.len() == 130).then(|| hex::decode(sig).ok()).flatten())?;
  decoded.try_into().ok()
}

/// Whether `sig` signs `message` as a Dogecoin signed message for `address`
/// (a mainnet P2PKH address, from either key form).
pub fn verify_message(address: &str, sig: &str, message: &str) -> bool {
  let (Some(target), Some(raw)) = (address_hash(address), decode_sig65(sig)) else {
    return false;
  };
  if !(27..=34).contains(&raw[0]) {
    return false;
  }
  let Ok(id) = RecoveryId::from_i32(((raw[0] - 27) & 3) as i32) else {
    return false;
  };
  let Ok(rs) = RecoverableSignature::from_compact(&raw[1..], id) else {
    return false;
  };
  let Ok(pk) = secp().recover_ecdsa(&Message::from_digest(message_hash(message)), &rs) else {
    return false;
  };
  hash160(&pk.serialize()) == target || hash160(&pk.serialize_uncompressed()) == target
}

// ---------------------------------------------------------------------------
// RFC 8785 canonical JSON

/// The JSON Canonicalization Scheme form of a value.
pub fn jcs(v: &Value) -> Result<String, String> {
  let mut out = String::new();
  write_jcs(&mut out, v)?;
  Ok(out)
}

fn write_jcs(out: &mut String, v: &Value) -> Result<(), String> {
  match v {
    Value::Null => out.push_str("null"),
    Value::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
    Value::Number(n) => out.push_str(&es_number(n)?),
    Value::String(s) => write_jcs_str(out, s),
    Value::Array(a) => {
      out.push('[');
      for (i, x) in a.iter().enumerate() {
        if i > 0 {
          out.push(',');
        }
        write_jcs(out, x)?;
      }
      out.push(']');
    }
    Value::Object(m) => {
      let mut keys: Vec<&String> = m.keys().collect();
      keys.sort_by(|a, b| a.encode_utf16().cmp(b.encode_utf16()));
      out.push('{');
      for (i, k) in keys.into_iter().enumerate() {
        if i > 0 {
          out.push(',');
        }
        write_jcs_str(out, k);
        out.push(':');
        write_jcs(out, &m[k])?;
      }
      out.push('}');
    }
  }
  Ok(())
}

fn write_jcs_str(out: &mut String, s: &str) {
  out.push('"');
  for c in s.chars() {
    match c {
      '"' => out.push_str("\\\""),
      '\\' => out.push_str("\\\\"),
      '\u{8}' => out.push_str("\\b"),
      '\u{c}' => out.push_str("\\f"),
      '\n' => out.push_str("\\n"),
      '\r' => out.push_str("\\r"),
      '\t' => out.push_str("\\t"),
      c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
      c => out.push(c),
    }
  }
  out.push('"');
}

const MAX_SAFE: u64 = 9_007_199_254_740_991;

fn es_number(n: &serde_json::Number) -> Result<String, String> {
  if let Some(u) = n.as_u64() {
    return if u <= MAX_SAFE { Ok(u.to_string()) } else { es_f64(u as f64) };
  }
  if let Some(i) = n.as_i64() {
    return if i.unsigned_abs() <= MAX_SAFE { Ok(i.to_string()) } else { es_f64(i as f64) };
  }
  es_f64(n.as_f64().ok_or("number out of range")?)
}

/// ECMAScript Number::toString, which RFC 8785 uses for numbers.
fn es_f64(f: f64) -> Result<String, String> {
  if !f.is_finite() {
    return Err("number is not finite".into());
  }
  if f == 0.0 {
    return Ok("0".into());
  }
  let sign = if f < 0.0 { "-" } else { "" };
  // Shortest round-trip digits, as "d.ddde±x".
  let e = format!("{:e}", f.abs());
  let (mantissa, exp) = e.split_once('e').ok_or("bad float format")?;
  let digits: String = mantissa.chars().filter(|c| *c != '.').collect();
  let exp: i32 = exp.parse().map_err(|_| "bad float exponent")?;
  let k = digits.len() as i32;
  let n = exp + 1;
  let body = if k <= n && n <= 21 {
    format!("{digits}{}", "0".repeat((n - k) as usize))
  } else if 0 < n && n <= 21 {
    format!("{}.{}", &digits[..n as usize], &digits[n as usize..])
  } else if -6 < n && n <= 0 {
    format!("0.{}{digits}", "0".repeat((-n) as usize))
  } else {
    let rest = if k > 1 { format!(".{}", &digits[1..]) } else { String::new() };
    let x = n - 1;
    format!("{}{rest}e{}{}", &digits[..1], if x < 0 { "-" } else { "+" }, x.abs())
  };
  Ok(format!("{sign}{body}"))
}

// ---------------------------------------------------------------------------
// Inscription records

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RecordType {
  Post,
  Comment,
  Quote,
  Edit,
  Keylink,
}

impl RecordType {
  pub fn parse(s: &str) -> Option<Self> {
    Some(match s {
      "post" => Self::Post,
      "comment" => Self::Comment,
      "quote" => Self::Quote,
      "edit" => Self::Edit,
      "keylink" => Self::Keylink,
      _ => return None,
    })
  }
  pub fn name(self) -> &'static str {
    match self {
      Self::Post => "post",
      Self::Comment => "comment",
      Self::Quote => "quote",
      Self::Edit => "edit",
      Self::Keylink => "keylink",
    }
  }
  /// Records a payment can point at.
  pub fn is_post_like(self) -> bool {
    matches!(self, Self::Post | Self::Comment | Self::Quote)
  }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct KeyLink {
  /// The CLI's own address.
  pub key: String,
  pub label: String,
  pub ops: Vec<String>,
  pub per_day: String,
  pub per_action: String,
}

/// A structurally valid D:// v1 record. Signatures are not checked yet.
#[derive(Debug, Clone, PartialEq)]
pub struct Record {
  pub value: Value,
  pub rtype: RecordType,
  pub ts: u64,
  pub addr: String,
  pub sig: String,
  pub kid: String,
  pub att_sig: String,
  /// `map.reply`, `map.quote` or `map.ref`, by type.
  pub reference: Option<String>,
  pub text: Option<String>,
  pub media: Vec<String>,
  pub tags: Vec<String>,
  pub mentions: Vec<String>,
  pub keylink: Option<KeyLink>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Detect {
  /// Not a D:// record at all.
  NotDproto,
  /// D://, but a version this reader does not know: skipped, not accepted.
  UnknownVersion,
  /// Marked D:// v1 but not a valid record.
  Invalid(String),
  Record(Box<Record>),
}

pub const KEYLINK_OPS: &[&str] = &["post", "comment", "quote", "like", "branch", "follow", "tip", "reveal", "delete"];

/// `<64 hex>i<index>`: an inscription id.
pub fn is_inscription_id(s: &str) -> bool {
  let Some((txid, index)) = s.split_once('i') else { return false };
  txid.len() == 64
    && txid.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    && !index.is_empty()
    && index.bytes().all(|b| b.is_ascii_digit())
}

fn utf16_len(s: &str) -> usize {
  s.encode_utf16().count()
}

fn str_field<'a>(o: &'a serde_json::Map<String, Value>, k: &str, what: &str, max: usize) -> Result<&'a str, String> {
  match o.get(k) {
    Some(Value::String(s)) if !s.is_empty() && utf16_len(s) <= max => Ok(s),
    Some(Value::String(s)) if s.is_empty() => Err(format!("{what} is empty")),
    Some(Value::String(_)) => Err(format!("{what} is longer than {max}")),
    Some(_) => Err(format!("{what} is not a string")),
    None => Err(format!("{what} is missing")),
  }
}

/// Reads a record body. Only bodies marked `"p":"D://"` for the DogeFeed app
/// are D:// records.
pub fn parse_record(body: &[u8]) -> Detect {
  let Ok(Value::Object(o)) = serde_json::from_slice::<Value>(body) else {
    return Detect::NotDproto;
  };
  if o.get("p").and_then(Value::as_str) != Some("D://") {
    return Detect::NotDproto;
  }
  if let Some(app) = o.get("map").and_then(|m| m.get("app")).and_then(Value::as_str)
    && app != "dogefeed"
  {
    return Detect::NotDproto;
  }
  match o.get("v") {
    Some(Value::Number(n)) if n.as_u64() == Some(1) => {}
    Some(Value::Number(_)) => return Detect::UnknownVersion,
    _ => return Detect::Invalid("v is missing or not a number".into()),
  }
  let value = Value::Object(o);
  match check_record(body, value) {
    Ok(r) => Detect::Record(Box::new(r)),
    Err(e) => Detect::Invalid(e),
  }
}

fn check_record(body: &[u8], value: Value) -> Result<Record, String> {
  if body.len() > MAX_BODY {
    return Err(format!("body is {} bytes, over {MAX_BODY}", body.len()));
  }
  if jcs(&value)?.len() > MAX_BODY {
    return Err(format!("canonical body is over {MAX_BODY} bytes"));
  }
  let o = value.as_object().expect("an object");
  let map = o.get("map").and_then(Value::as_object).ok_or("map is missing or not an object")?;
  if map.get("app").and_then(Value::as_str) != Some("dogefeed") {
    return Err("map.app is not \"dogefeed\"".into());
  }
  let tname = map.get("type").and_then(Value::as_str).ok_or("map.type is missing")?;
  let rtype = RecordType::parse(tname).ok_or_else(|| format!("map.type {tname:?} is not a record type"))?;
  let ts = map.get("ts").and_then(Value::as_u64).filter(|t| (1..=MAX_SAFE).contains(t)).ok_or("map.ts is not a positive safe integer")?;
  let reference = match rtype {
    RecordType::Comment => Some(("reply", "map.reply")),
    RecordType::Quote => Some(("quote", "map.quote")),
    RecordType::Edit => Some(("ref", "map.ref")),
    _ => None,
  }
  .map(|(k, what)| match map.get(k).and_then(Value::as_str) {
    Some(id) if is_inscription_id(id) => Ok(id.to_string()),
    Some(_) => Err(format!("{what} is not an inscription id")),
    None => Err(format!("{what} is missing")),
  })
  .transpose()?;
  let tags = match map.get("tags") {
    None => Vec::new(),
    Some(Value::Array(a)) => {
      if a.len() > 10 {
        return Err("more than 10 tags".into());
      }
      a.iter()
        .map(|t| match t.as_str() {
          Some(s) if utf16_len(s) <= 50 => Ok(s.to_string()),
          Some(_) => Err("a tag is longer than 50".to_string()),
          None => Err("a tag is not a string".to_string()),
        })
        .collect::<Result<_, _>>()?
    }
    Some(_) => return Err("map.tags is not an array".into()),
  };
  let mentions = match map.get("mentions") {
    None => Vec::new(),
    Some(Value::Array(a)) => a.iter().map(|m| m.as_str().map(str::to_string).ok_or("a mention is not a string")).collect::<Result<_, _>>()?,
    Some(_) => return Err("map.mentions is not an array".into()),
  };
  let (mut text, mut media) = (None, Vec::new());
  match o.get("b") {
    Some(Value::Object(b)) => {
      text = match b.get("text") {
        None => None,
        Some(Value::String(s)) => Some(s.clone()),
        Some(_) => return Err("b.text is not a string".into()),
      };
      if let Some(m) = b.get("mime")
        && m.as_str() != Some("text/markdown")
      {
        return Err("b.mime is not \"text/markdown\"".into());
      }
      media = match b.get("media") {
        None => Vec::new(),
        Some(Value::Array(a)) => a
          .iter()
          .map(|m| m.as_str().filter(|s| is_inscription_id(s)).map(str::to_string).ok_or("b.media holds something that is not an inscription id"))
          .collect::<Result<_, _>>()?,
        Some(_) => return Err("b.media is not an array".into()),
      };
    }
    Some(_) => return Err("b is not an object".into()),
    None if rtype != RecordType::Keylink => return Err("b is missing".into()),
    None => {}
  }
  let keylink = if rtype == RecordType::Keylink {
    let key = str_field(map, "key", "map.key", 40)?.to_string();
    let label = str_field(map, "label", "map.label", 40)?.to_string();
    let ops: Vec<String> = match map.get("ops") {
      Some(Value::Array(a)) if !a.is_empty() => a
        .iter()
        .map(|x| x.as_str().filter(|s| KEYLINK_OPS.contains(s)).map(str::to_string).ok_or("map.ops holds an unknown op"))
        .collect::<Result<_, _>>()?,
      _ => return Err("map.ops is missing or empty".into()),
    };
    let cap = map.get("cap").and_then(Value::as_object).ok_or("map.cap is missing")?;
    let per_day = cap.get("perDay").and_then(Value::as_str).ok_or("map.cap.perDay is not a string")?.to_string();
    let per_action = cap.get("perAction").and_then(Value::as_str).ok_or("map.cap.perAction is not a string")?.to_string();
    Some(KeyLink { key, label, ops, per_day, per_action })
  } else {
    None
  };
  let aip = o.get("aip").and_then(Value::as_object).ok_or("aip is missing")?;
  if aip.get("alg").and_then(Value::as_str) != Some("DOGE_ECDSA") {
    return Err("aip.alg is not \"DOGE_ECDSA\"".into());
  }
  let addr = str_field(aip, "addr", "aip.addr", 40)?.to_string();
  let sig = str_field(aip, "sig", "aip.sig", 200)?.to_string();
  let att = o.get("att").and_then(Value::as_object).ok_or("att (the registrar attestation) is missing")?;
  let kid = str_field(att, "kid", "att.kid", 32)?.to_string();
  let att_sig = str_field(att, "sig", "att.sig", 200)?.to_string();
  Ok(Record { value, rtype, ts, addr, sig, kid, att_sig, reference, text, media, tags, mentions, keylink })
}

/// The string the author signs: the record without `att`, and `aip` cut down
/// to `alg` and `addr`, in canonical form.
pub fn signed_string(rec: &Record) -> Result<String, String> {
  let mut view = rec.value.clone();
  let o = view.as_object_mut().expect("an object");
  o.remove("att");
  o.insert("aip".into(), serde_json::json!({ "alg": "DOGE_ECDSA", "addr": rec.addr }));
  Ok(format!("D://:v1:{}", jcs(&view)?))
}

/// Checks the author's signature and the registrar's attestation of it.
pub fn verify_record_signatures(rec: &Record) -> Result<(), String> {
  let signed = signed_string(rec)?;
  if !verify_message(&rec.addr, &rec.sig, &signed) {
    return Err("the author's signature does not verify".into());
  }
  registrar_address(&rec.kid).ok_or_else(|| format!("unknown registrar key {:?}", rec.kid))?;
  if attestation_key(rec).is_none() {
    return Err("the registrar's attestation does not verify".into());
  }
  Ok(())
}

/// The registrar key (`kid`) whose attestation on this record verifies, if
/// any: DogeFeed's signature, showing the record was issued through DogeFeed.
/// It signs over the author's signature, so it is checked apart from it.
pub fn attestation_key(rec: &Record) -> Option<&'static str> {
  let signed = signed_string(rec).ok()?;
  let h = hex::encode(sha256(format!("{signed}{}", rec.sig).as_bytes()));
  let key = REGISTRAR_KEYS.iter().find(|k| k.kid == rec.kid)?;
  verify_message(key.address, &rec.att_sig, &format!("D://-att:v1:{h}")).then_some(key.kid)
}

/// A transaction output: amount and script.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TxOut {
  pub koinu: u64,
  pub script: Vec<u8>,
}

/// What the outputs pay an address in all, in koinu.
pub fn paid_to(outputs: &[TxOut], address: &str) -> u64 {
  let Some(h) = address_hash(address) else { return 0 };
  let script = p2pkh_script(&h);
  outputs.iter().filter(|o| o.script == script).map(|o| o.koinu).sum()
}

/// Full check of an inscription record against its reveal transaction.
/// `destinations` are the addresses it may first be sent to: the author's,
/// and the linked account's when a linked key wrote it. `parent_author` is the
/// original author of what a comment or quote points at.
pub fn verify_inscription(rec: &Record, reveal_outputs: &[TxOut], destinations: &[&str], parent_author: Option<&str>) -> Result<(), String> {
  verify_record_signatures(rec)?;
  let first = reveal_outputs.first().ok_or("the reveal has no outputs")?;
  let dest = script_address(&first.script).ok_or("the inscription is not sent to an address")?;
  if !destinations.contains(&dest.as_str()) {
    return Err(format!("the inscription is sent to {dest}, not to its author"));
  }
  if paid_to(reveal_outputs, FEE_ADDRESS) < MIN_FEE {
    return Err("the reveal pays DogeFeed less than 0.1 DOGE".into());
  }
  if matches!(rec.rtype, RecordType::Comment | RecordType::Quote) {
    let parent = parent_author.ok_or("what it points at is not a valid earlier record")?;
    if paid_to(reveal_outputs, parent) < MIN_RECIPIENT {
      return Err(format!("the reveal pays {parent} (the author it answers) less than 0.01 DOGE"));
    }
  }
  Ok(())
}

// ---------------------------------------------------------------------------
// Doginal envelopes

/// The pushes of a script, OP_0 as an empty push and OP_1..OP_16 as their
/// number, up to the first opcode that is not a push.
pub fn script_pushes(script: &[u8]) -> Option<Vec<Vec<u8>>> {
  let mut b = script;
  let mut out = Vec::new();
  while let Some(&op) = b.first() {
    let (len, skip) = match op {
      0 => (0, 1),
      81..=96 => {
        out.push(vec![op - 80]);
        b = &b[1..];
        continue;
      }
      1..=75 => (op as usize, 1),
      76 => (*b.get(1)? as usize, 2),
      77 => (u16::from_le_bytes([*b.get(1)?, *b.get(2)?]) as usize, 3),
      78 => (u32::from_le_bytes([*b.get(1)?, *b.get(2)?, *b.get(3)?, *b.get(4)?]) as usize, 5),
      _ if out.is_empty() => return None,
      _ => break,
    };
    if b.len() < skip + len {
      return None;
    }
    out.push(b[skip..skip + len].to_vec());
    b = &b[skip + len..];
  }
  Some(out)
}

fn push_number(d: &[u8]) -> Option<u64> {
  if d.len() > 8 {
    return None;
  }
  let mut buf = [0u8; 8];
  buf[..d.len()].copy_from_slice(d);
  Some(u64::from_le_bytes(buf))
}

/// Data pushes a reveal carries after the piece that ends its inscription and
/// before the spend's own signature and redeem script, joined. Standard
/// Doginals parsing stops at that last piece; some D:// builders split one
/// piece's data over several pushes, so the record is the standard body
/// followed by these.
pub fn trailing_pushes(script_sig: &[u8]) -> Vec<u8> {
  let Some(p) = script_pushes(script_sig) else { return Vec::new() };
  let mut i = if p.first().map(Vec::as_slice) == Some(b"ord".as_slice()) { 3 } else { 0 };
  while i + 1 < p.len() {
    match push_number(&p[i]) {
      Some(0) => {
        let end = p.len().saturating_sub(2);
        return if i + 2 < end { p[i + 2..end].concat() } else { Vec::new() };
      }
      Some(_) => i += 2,
      None => return Vec::new(),
    }
  }
  Vec::new()
}

/// The D:// record an inscription holds: its standard body if that reads as
/// one, else the body with the reveal's trailing pushes. `lenient` says
/// whether the trailing pushes were needed.
pub fn read_inscription(standard_body: &[u8], reveal_script_sig: Option<&[u8]>) -> (Detect, bool) {
  let d = parse_record(standard_body);
  if d != Detect::NotDproto {
    return (d, false);
  }
  let Some(script) = reveal_script_sig else { return (d, false) };
  let extra = trailing_pushes(script);
  if extra.is_empty() {
    return (d, false);
  }
  let mut joined = standard_body.to_vec();
  joined.extend_from_slice(&extra);
  match parse_record(&joined) {
    Detect::NotDproto => (Detect::NotDproto, false),
    other => (other, true),
  }
}

// ---------------------------------------------------------------------------
// Payments

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Op {
  Like = 1,
  Branch = 2,
  Follow = 3,
  Tip = 4,
  Reveal = 5,
  Delete = 6,
  Keyrevoke = 7,
}

impl Op {
  pub fn from_u8(n: u8) -> Option<Self> {
    Some(match n {
      1 => Self::Like,
      2 => Self::Branch,
      3 => Self::Follow,
      4 => Self::Tip,
      5 => Self::Reveal,
      6 => Self::Delete,
      7 => Self::Keyrevoke,
      _ => return None,
    })
  }
  pub fn name(self) -> &'static str {
    match self {
      Self::Like => "like",
      Self::Branch => "branch",
      Self::Follow => "follow",
      Self::Tip => "tip",
      Self::Reveal => "reveal",
      Self::Delete => "delete",
      Self::Keyrevoke => "keyrevoke",
    }
  }
  pub fn targets_post(self) -> bool {
    matches!(self, Self::Like | Self::Branch | Self::Tip | Self::Reveal | Self::Delete)
  }
  pub fn has_recipient(self) -> bool {
    !matches!(self, Self::Delete | Self::Keyrevoke)
  }
}

/// The 80 data bytes of a D:// OP_RETURN: `6a 4c 50` then `D://`.
pub fn op_return_payload(script: &[u8]) -> Option<[u8; 80]> {
  (script.len() == 83 && script[..3] == [0x6a, 0x4c, 0x50] && &script[3..7] == b"D://").then(|| script[3..].try_into().unwrap())
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Payload {
  pub op: Op,
  pub target: [u8; 11],
  pub r: [u8; 32],
  pub s: [u8; 32],
}

/// The payload, or None for a version or op this reader does not know.
pub fn decode_payload(p: &[u8; 80]) -> Option<Payload> {
  if p[4] >> 4 != 1 {
    return None;
  }
  Some(Payload {
    op: Op::from_u8(p[4] & 0x0f)?,
    target: p[5..16].try_into().unwrap(),
    r: p[16..48].try_into().unwrap(),
    s: p[48..80].try_into().unwrap(),
  })
}

fn split_id(id: &str) -> Option<([u8; 32], u32)> {
  let (txid, index) = id.split_once('i')?;
  let bytes: [u8; 32] = hex::decode(txid).ok()?.try_into().ok()?;
  Some((bytes, index.parse().ok()?))
}

/// The 11-byte target a payment uses for a post: the first 10 bytes of its
/// txid as displayed, then its index.
pub fn post_target(id: &str) -> Option<[u8; 11]> {
  let (txid, index) = split_id(id)?;
  let mut t = [0u8; 11];
  t[..10].copy_from_slice(&txid[..10]);
  t[10] = u8::try_from(index).ok()?;
  Some(t)
}

/// The full target the registrar signs for a post: its txid in internal byte
/// order, then its index as uint32 little-endian.
pub fn post_full_target(id: &str) -> Option<Vec<u8>> {
  let (mut txid, index) = split_id(id)?;
  txid.reverse();
  let mut v = txid.to_vec();
  v.extend_from_slice(&index.to_le_bytes());
  Some(v)
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Outpoint {
  /// As displayed.
  pub txid: String,
  pub vout: u32,
}

fn serialize_output(out: &mut Vec<u8>, o: &TxOut) {
  out.extend_from_slice(&o.koinu.to_le_bytes());
  compact_size(out, o.script.len() as u64);
  out.extend_from_slice(&o.script);
}

/// The digest the registrar signs for a payment, hashed once.
pub fn registrar_digest(op: Op, full_target: &[u8], inputs: &[Outpoint], recipient: Option<&TxOut>, fee: &TxOut) -> Option<[u8; 32]> {
  let n = u8::try_from(inputs.len()).ok().filter(|n| *n >= 1)?;
  let mut pre = b"D://-att:v1:".to_vec();
  pre.push(0x10 | op as u8);
  pre.extend_from_slice(full_target);
  pre.push(n);
  for i in inputs {
    let mut txid: [u8; 32] = hex::decode(&i.txid).ok()?.try_into().ok()?;
    txid.reverse();
    pre.extend_from_slice(&txid);
    pre.extend_from_slice(&i.vout.to_le_bytes());
  }
  if let Some(r) = recipient {
    serialize_output(&mut pre, r);
  }
  serialize_output(&mut pre, fee);
  Some(sha256(&pre))
}

const HALF_ORDER: [u8; 32] = [
  0x7f, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x5d, 0x57, 0x6e, 0x73, 0x57, 0xa4, 0x50, 0x1d, 0xdf,
  0xe9, 0x2f, 0x46, 0x68, 0x1b, 0x20, 0xa0,
];

/// A raw (r, s) ECDSA signature over `digest`, low-S, by one of `keys`.
pub fn verify_raw(digest: &[u8; 32], r: &[u8; 32], s: &[u8; 32], keys: &[PublicKey]) -> bool {
  if s.iter().all(|b| *b == 0) || s > &HALF_ORDER {
    return false;
  }
  let mut compact = [0u8; 64];
  compact[..32].copy_from_slice(r);
  compact[32..].copy_from_slice(s);
  let Ok(sig) = Signature::from_compact(&compact) else { return false };
  let msg = Message::from_digest(*digest);
  keys.iter().any(|k| secp().verify_ecdsa(&msg, &sig, k).is_ok())
}

/// A transaction as a payment check needs it.
pub struct PaymentTx<'a> {
  pub inputs: &'a [Outpoint],
  /// The address each input spends from, in the same order.
  pub input_addresses: &'a [Option<String>],
  pub outputs: &'a [TxOut],
}

/// A post a payment's 11-byte target may mean, in chain order.
#[derive(Debug, Clone)]
pub struct PostCandidate {
  pub id: String,
  /// Its original author: who likes, branches, tips and reveals pay.
  pub author: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Target {
  Post(String),
  Address(String),
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct VerifiedPayment {
  pub op: Op,
  /// The address every input spends from.
  pub author: String,
  pub target: Target,
  pub recipient: Option<(u32, u64)>,
  pub fee: (u32, u64),
}

fn first_paying<'a>(outputs: &'a [TxOut], hash: &[u8; 20]) -> Option<(u32, &'a TxOut)> {
  let script = p2pkh_script(hash);
  outputs.iter().enumerate().find(|(_, o)| o.koinu > 0 && o.script == script).map(|(i, o)| (i as u32, o))
}

/// Checks a transaction as a D:// payment. Ok(None): not one (no D://
/// OP_RETURN, or an unknown version or op). Err: a D:// payment that is not
/// valid, and why. `posts` lists the posts an 11-byte target may mean, in
/// chain order; `keys` lists the CLI key addresses an author has linked.
pub fn verify_payment(
  tx: &PaymentTx,
  registrar: &[PublicKey],
  posts: impl Fn(&[u8; 11]) -> Vec<PostCandidate>,
  keys: impl Fn(&str) -> Vec<String>,
) -> Result<Option<VerifiedPayment>, String> {
  let Some(raw) = tx.outputs.iter().find_map(|o| op_return_payload(&o.script)) else {
    return Ok(None);
  };
  let Some(p) = decode_payload(&raw) else { return Ok(None) };
  if tx.outputs.iter().filter(|o| o.script.first() == Some(&0x6a)).count() != 1 {
    return Err("more than one OP_RETURN output".into());
  }
  let author = match tx.input_addresses.first() {
    Some(Some(a)) if tx.input_addresses.iter().all(|x| x.as_deref() == Some(a.as_str())) => a.clone(),
    Some(Some(_)) => return Err("its inputs spend from more than one address".into()),
    _ => return Err("its first input does not spend from an address".into()),
  };
  if tx.inputs.len() != tx.input_addresses.len() {
    return Err("input addresses do not match the inputs".into());
  }
  let fee_hash = address_hash(FEE_ADDRESS).expect("fee address");
  let (fee_vout, fee) = first_paying(tx.outputs, &fee_hash).ok_or("it pays DogeFeed nothing")?;
  if fee.koinu < MIN_FEE {
    return Err("it pays DogeFeed less than 0.1 DOGE".into());
  }
  let check = |full: &[u8], recipient: Option<&TxOut>| {
    registrar_digest(p.op, full, tx.inputs, recipient, fee).is_some_and(|d| verify_raw(&d, &p.r, &p.s, registrar))
  };
  let (target, recipient) = match p.op {
    op if op.targets_post() => {
      let cands = posts(&p.target);
      if cands.is_empty() {
        return Err("its target is not a known D:// post".into());
      }
      let mut hit = None;
      for c in cands {
        let Some(full) = post_full_target(&c.id) else { continue };
        let rec = if op.has_recipient() {
          let Some(h) = address_hash(&c.author) else { continue };
          match first_paying(tx.outputs, &h) {
            Some(r) => Some(r),
            None => continue,
          }
        } else {
          None
        };
        if check(&full, rec.map(|r| r.1)) {
          hit = Some((Target::Post(c.id), rec));
          break;
        }
      }
      hit.ok_or("the registrar's signature does not verify for any post it may mean")?
    }
    Op::Follow => {
      let (vout, out, hash) = tx
        .outputs
        .iter()
        .enumerate()
        .find_map(|(i, o)| {
          let h = script_p2pkh_hash(&o.script)?;
          (o.koinu > 0 && h != fee_hash && h[..11] == p.target).then_some((i as u32, o, h))
        })
        .ok_or("no output pays the followed address")?;
      if !check(&hash, Some(out)) {
        return Err("the registrar's signature does not verify".into());
      }
      (Target::Address(p2pkh_address(&hash)), Some((vout, out)))
    }
    Op::Keyrevoke => {
      let key = keys(&author)
        .into_iter()
        .filter_map(|k| address_hash(&k).map(|h| (k, h)))
        .find(|(_, h)| h[..11] == p.target && check(h, None))
        .ok_or("it revokes no key this account linked, or the registrar's signature does not verify")?;
      (Target::Address(key.0), None)
    }
    _ => unreachable!("every op is covered"),
  };
  if p.op.has_recipient() {
    let (_, r) = recipient.ok_or("no recipient output")?;
    if r.koinu < MIN_RECIPIENT {
      return Err("it pays the recipient less than 0.01 DOGE".into());
    }
    if matches!(p.op, Op::Tip | Op::Reveal) && i128::abs(9 * i128::from(fee.koinu) - i128::from(r.koinu)) > 1 {
      return Err("a tip must split 90% to the recipient and 10% to DogeFeed".into());
    }
  }
  Ok(Some(VerifiedPayment {
    op: p.op,
    author,
    target,
    recipient: recipient.map(|(v, o)| (v, o.koinu)),
    fee: (fee_vout, fee.koinu),
  }))
}

/// [`verify_payment`] against each pinned registrar key in turn, with the
/// `kid` of the key that signed it.
pub fn verify_payment_by_key(
  tx: &PaymentTx,
  posts: impl Fn(&[u8; 11]) -> Vec<PostCandidate>,
  keys: impl Fn(&str) -> Vec<String>,
) -> Result<Option<(VerifiedPayment, &'static str)>, String> {
  let mut last = Err("no registrar key is pinned".to_string());
  for k in REGISTRAR_KEYS {
    let Some(pk) = hex::decode(k.pubkey_hex).ok().and_then(|b| PublicKey::from_slice(&b).ok()) else { continue };
    match verify_payment(tx, &[pk], &posts, &keys) {
      Ok(Some(v)) => return Ok(Some((v, k.kid))),
      Ok(None) => return Ok(None),
      Err(e) => last = Err(e),
    }
  }
  last
}

/// The reference split of a priced tip or reveal: DogeFeed's 10%, rounded to
/// the nearest 10 koinu, and the recipient's nine times that.
pub fn tip_split(amount: u64) -> (u64, u64) {
  let platform = (amount + 5) / 10;
  (platform * 9, platform)
}
