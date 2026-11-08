//! DNS, the Dogecoin Names System: `label.namespace` names minted as
//! inscriptions, first valid one wins, whoever holds that inscription owns
//! the name.
//!
//! Follows spec v1.2 (<https://github.com/jonheaven/dns>, `spec.md`), and is
//! checked against that spec's `vectors/conformance.json` in the tests below.
//!
//! A separate indexer with its own trees and its own task. It reads nothing
//! from blocks: it follows `inscription_seq` in chain order, only as far as
//! inscription numbering has gone, which is [`DNS_CONFIRMATIONS`]
//! confirmation: names appear with the block that makes them. So:
//!
//!  - first come, first served is decided in exact chain order (height, then
//!    position in block), the order the spec requires, and every write of a
//!    step is seen by the rows after it;
//!  - each step is one atomic batch with its cursor, so a crash cannot apply
//!    anything twice;
//!  - each step near the tip also saves what its batch overwrote
//!    (`dns_undo`). A reorg ([`undo_from`], called by the rollback) puts those
//!    back, newest step first, which also moves the cursor back, and the
//!    replacing blocks are read again. As ord does with its savepoints, only
//!    so deep: [`UNDO_BLOCKS`].
//!
//! Three kinds of inscription matter:
//!
//!  - a register: plain text whose first whitespace-separated token is a valid
//!    name, or JSON `{"p":"dns","op":"register"|"reg","name":...}`. The first
//!    one of a name creates it, later ones are kept as missed claims;
//!  - a config: JSON `{"p":"dns","op":"config"|"update"|"upd",...}`, or `p` and
//!    a name and record fields with no `op`. Counts only when the inscription's
//!    owner holds the name right after the transaction that made it;
//!  - a primary: JSON `{"p":"dns","op":"primary","name":...}`, the one name an
//!    address shows.
//!
//! Who held an inscription at some point in the past is not stored anywhere,
//! so when a config or primary needs it and the inscription has moved since,
//! [`Tracer`] follows it back through the node, output by output, using the
//! same first-in-first-out rule the main indexer moves inscriptions by.

use super::*;
use crate::insc_index::{self as ii, SeqEntry};

/// Confirmations a block needs before its names are read: 1 means as soon as
/// it is indexed and numbered.
pub const DNS_CONFIRMATIONS: u64 = 1;

/// How many blocks back a reorg can be undone. Steps applied further from the
/// tip than this keep no undo record.
pub const UNDO_BLOCKS: u64 = 100;

/// Held while a step commits and while a reorg undoes steps.
static DNS_WRITE: Mutex<()> = Mutex::new(());

/// Meta key of a counter bumped by every reorg undo, so a step read before it
/// is never committed after it, and the task reloads its state.
const REORG_GEN_KEY: &[u8] = b"dns_reorg_gen";

fn reorg_gen(meta: &Tree) -> Result<u64> {
  Ok(ii::meta_u64(meta, REORG_GEN_KEY)?.unwrap_or(0))
}

/// What one step overwrote: tree, key, previous value (None: it was absent).
#[derive(Serialize, Deserialize)]
struct DnsUndo {
  last_height: u64,
  ops: Vec<(String, Vec<u8>, Option<Vec<u8>>)>,
}
use crate::store::{Batch, Tree};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::sync::Mutex;
use unicode_properties::emoji::UnicodeEmoji;
use unicode_properties::general_category::{GeneralCategoryGroup, UnicodeGeneralCategory};
use unicode_script::{Script, UnicodeScript};

const DNS_STATE_KEY: &[u8] = b"dns_index_v1";

// ------------------------------------------------------------------ names --

/// A valid name, folded to the form it is stored under.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DnsName {
  pub name: String,
  pub label: String,
  pub namespace: String,
  /// Every non-ASCII character in it looks like an ASCII one (Cyrillic
  /// `сорех.doge`). Still a name of its own; UIs warn about it.
  pub confusable: bool,
}

/// Checks and folds a name (spec section 6). The error says why it is not one.
pub fn normalize_name(input: &str) -> std::result::Result<DnsName, &'static str> {
  let mut s = String::with_capacity(input.len());
  for c in input.chars() {
    let u = c as u32;
    // Fullwidth full stop would fold to '.', which would make a lookalike
    // spelling of a name split like the real one.
    if u == 0xFF0E {
      return Err("contains a dot lookalike");
    }
    let c = if (0xFF01..=0xFF5E).contains(&u) { char::from_u32(u - 0xFEE0).unwrap_or(c) } else { c };
    s.push(c.to_ascii_lowercase());
  }
  let Some((label, namespace)) = s.split_once('.') else {
    return Err("needs one dot, as in label.namespace");
  };
  if namespace.contains('.') {
    return Err("has more than one dot");
  }
  check_part(label)?;
  check_part(namespace)?;
  if namespace == "bitmap" || namespace.starts_with("dogemap") {
    return Err("bitmap and dogemap names belong to their own protocols");
  }
  let confusable = s.chars().any(|c| !c.is_ascii()) && s.chars().all(|c| c.is_ascii() || ascii_lookalike(c));
  Ok(DnsName { label: label.to_string(), namespace: namespace.to_string(), confusable, name: s })
}

fn is_emoji(c: char) -> bool {
  !c.is_ascii() && c.is_emoji_char()
}

fn check_part(part: &str) -> std::result::Result<(), &'static str> {
  let chars: Vec<char> = part.chars().collect();
  let (Some(&first), Some(&last)) = (chars.first(), chars.last()) else {
    return Err("label and namespace must not be empty");
  };
  if chars.len() > 63 {
    return Err("label and namespace are at most 63 characters each");
  }
  if first == '-' || last == '-' {
    return Err("a hyphen cannot start or end a label or namespace");
  }
  let mut script: Option<Script> = None;
  for (i, &c) in chars.iter().enumerate() {
    let prev = i.checked_sub(1).map(|j| chars[j]);
    let next = chars.get(i + 1).copied();
    if c.is_ascii() {
      if c.is_ascii_lowercase() {
        same_script(&mut script, Script::Latin)?;
        continue;
      }
      if c.is_ascii_digit() || c == '-' {
        continue;
      }
      if c.is_ascii_whitespace() || c.is_ascii_control() {
        return Err("contains a space or control character");
      }
      if c == '_' {
        return Err("underscores are not allowed");
      }
      return Err("ASCII characters must be a-z, 0-9 or a hyphen");
    }
    if is_dot_or_slash_lookalike(c) {
      return Err("contains a dot or slash lookalike");
    }
    if matches!(c, '\u{2018}' | '\u{2019}' | '\u{02BC}') {
      return Err("apostrophes are not allowed");
    }
    // Joiners and variation selectors are only allowed as parts of an emoji.
    if c == '\u{200D}' {
      let after_emoji = prev.is_some_and(|p| is_emoji(p) || p == '\u{FE0F}');
      if after_emoji && next.is_some_and(is_emoji) {
        continue;
      }
      return Err("a zero-width joiner is only allowed inside an emoji");
    }
    if c == '\u{FE0F}' || c == '\u{FE0E}' {
      let keycap = prev.is_some_and(|p| p.is_ascii_digit()) && next == Some('\u{20E3}');
      if prev.is_some_and(is_emoji) || keycap {
        continue;
      }
      return Err("a variation selector is only allowed inside an emoji");
    }
    if is_default_ignorable(c) || c.is_whitespace() {
      return Err("contains an invisible or space character");
    }
    if is_emoji(c) {
      continue;
    }
    match c.general_category_group() {
      GeneralCategoryGroup::Letter => {
        let sc = c.script();
        if !matches!(sc, Script::Common | Script::Inherited | Script::Unknown) {
          same_script(&mut script, sc)?;
        }
      }
      GeneralCategoryGroup::Mark | GeneralCategoryGroup::Number => {}
      _ => return Err("only letters, numbers, marks and emoji are allowed"),
    }
  }
  Ok(())
}

fn same_script(seen: &mut Option<Script>, sc: Script) -> std::result::Result<(), &'static str> {
  match seen {
    Some(s) if *s != sc => Err("mixes letters from more than one script"),
    _ => {
      *seen = Some(sc);
      Ok(())
    }
  }
}

/// Characters that read as `.` or `/`. Most are punctuation or symbols and
/// fail anyway; these are listed for the ones that are letters, digits or
/// marks (Arabic-Indic zero, Lisu tone mark, ...).
fn is_dot_or_slash_lookalike(c: char) -> bool {
  matches!(
    c as u32,
    0x00B7 | 0x0387 | 0x0589 | 0x0660 | 0x06D4 | 0x06F0 | 0x0701 | 0x0702 | 0x1427 | 0x2024 | 0x2027 | 0x2E31 | 0x2E33
      | 0x3002 | 0x30FB | 0xA4F8 | 0xA60E | 0xA78F | 0xFF61 | 0xFF65 | 0x10A50 | 0x1D16D
      | 0x1735 | 0x2044 | 0x2215 | 0x2571 | 0x27CB | 0x29F6 | 0x29F8 | 0x3033 | 0xFF0F
  )
}

/// Unicode's Default_Ignorable_Code_Point: characters that draw nothing.
fn is_default_ignorable(c: char) -> bool {
  matches!(
    c as u32,
    0x00AD
      | 0x034F
      | 0x061C
      | 0x115F..=0x1160
      | 0x17B4..=0x17B5
      | 0x180B..=0x180F
      | 0x200B..=0x200F
      | 0x202A..=0x202E
      | 0x2060..=0x206F
      | 0x3164
      | 0xFE00..=0xFE0F
      | 0xFEFF
      | 0xFFA0
      | 0xFFF0..=0xFFF8
      | 0x1BCA0..=0x1BCA3
      | 0x1D173..=0x1D17A
      | 0xE0000..=0xE0FFF
  )
}

/// Cyrillic, Greek and Armenian letters that look like an ASCII letter or digit.
fn ascii_lookalike(c: char) -> bool {
  matches!(
    c as u32,
    // Cyrillic lower: а е о р с у х ѕ і ј һ ӏ ԁ ԛ ԝ
    0x0430 | 0x0435 | 0x043E | 0x0440 | 0x0441 | 0x0443 | 0x0445 | 0x0455 | 0x0456 | 0x0458 | 0x04BB | 0x04CF
      | 0x0501 | 0x051B | 0x051D
      // Cyrillic upper: Ѕ І Ј А В Е З К М Н О Р С Т У Х Һ Ү Ӏ Ԛ Ԝ
      | 0x0405 | 0x0406 | 0x0408 | 0x0410 | 0x0412 | 0x0415 | 0x0417 | 0x041A | 0x041C | 0x041D | 0x041E | 0x0420
      | 0x0421 | 0x0422 | 0x0423 | 0x0425 | 0x04BA | 0x04AE | 0x04C0 | 0x051A | 0x051C
      // Greek lower: α γ ι κ ν ο ρ υ χ
      | 0x03B1 | 0x03B3 | 0x03B9 | 0x03BA | 0x03BD | 0x03BF | 0x03C1 | 0x03C5 | 0x03C7
      // Greek upper: Α Β Ε Ζ Η Ι Κ Μ Ν Ο Ρ Τ Υ Χ
      | 0x0391 | 0x0392 | 0x0395 | 0x0396 | 0x0397 | 0x0399 | 0x039A | 0x039C | 0x039D | 0x039F | 0x03A1 | 0x03A4
      | 0x03A5 | 0x03A7
      // Armenian: զ հ ո ս ց օ Ս Տ Օ
      | 0x0566 | 0x0570 | 0x0578 | 0x057D | 0x0581 | 0x0585 | 0x054D | 0x054F | 0x0555
  )
}

// ---------------------------------------------------------------- records --

/// A name's records as they stand.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct DnsRecords {
  pub address: Option<String>,
  pub addresses: Vec<String>,
  pub url: Option<String>,
  pub site: Option<String>,
  pub avatar: Option<String>,
  pub content: Option<String>,
  pub cname: Option<String>,
  pub nostr: Option<String>,
  pub lightning: Option<String>,
  pub txt: BTreeMap<String, String>,
  pub subdomains: Option<String>,
}

/// The changes one inscription makes. `None` leaves a field alone; an empty
/// string clears a single value, an empty list clears `addresses`.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct RecordPatch {
  pub address: Option<String>,
  pub addresses: Option<Vec<String>>,
  pub url: Option<String>,
  pub site: Option<String>,
  pub avatar: Option<String>,
  pub content: Option<String>,
  pub cname: Option<String>,
  pub nostr: Option<String>,
  pub lightning: Option<String>,
  pub txt: Option<TxtPatch>,
  pub subdomains: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TxtPatch {
  /// `"txt": null`
  Clear,
  /// Keys to set; an empty value deletes that key.
  Merge(BTreeMap<String, String>),
}

impl RecordPatch {
  fn is_empty(&self) -> bool {
    *self == RecordPatch::default()
  }
}

impl DnsRecords {
  pub fn apply(&mut self, p: &RecordPatch) {
    fn set(slot: &mut Option<String>, v: &Option<String>) {
      if let Some(v) = v {
        *slot = if v.is_empty() { None } else { Some(v.clone()) };
      }
    }
    set(&mut self.address, &p.address);
    set(&mut self.url, &p.url);
    set(&mut self.site, &p.site);
    set(&mut self.avatar, &p.avatar);
    set(&mut self.content, &p.content);
    set(&mut self.cname, &p.cname);
    set(&mut self.nostr, &p.nostr);
    set(&mut self.lightning, &p.lightning);
    set(&mut self.subdomains, &p.subdomains);
    if let Some(a) = &p.addresses {
      self.addresses = a.clone();
    }
    match &p.txt {
      Some(TxtPatch::Clear) => self.txt.clear(),
      Some(TxtPatch::Merge(m)) => {
        for (k, v) in m {
          if v.is_empty() {
            self.txt.remove(k);
          } else {
            self.txt.insert(k.clone(), v.clone());
          }
        }
      }
      None => {}
    }
  }
}

/// Every key that names a record field, aliases included.
const RECORD_KEYS: &[&str] = &[
  "address", "rev", "addresses", "url", "website", "site", "relay", "insc", "html", "avatar", "content", "cname", "nostr",
  "lightning", "lud16", "txt", "subdomains", "merkle",
];

type Obj = serde_json::Map<String, Value>;

/// The value of the first of `keys` present, taken from `top` when any of
/// them is there (a top-level key wins) and from `nested` otherwise.
fn pick<'a>(top: &'a Obj, nested: Option<&'a Obj>, keys: &[&str]) -> Option<&'a Value> {
  let first = |o: &'a Obj| keys.iter().find_map(|k| o.get(*k));
  first(top).or_else(|| nested.and_then(first))
}

/// A single-value field: a string, empty to clear, or a valid value. Anything
/// else leaves the field out.
fn scalar(v: Option<&Value>, check: impl Fn(&str) -> Option<String>) -> Option<String> {
  match v? {
    Value::String(s) if s.is_empty() => Some(String::new()),
    Value::String(s) => check(s),
    _ => None,
  }
}

fn parse_patch(top: &Obj, nested: Option<&Obj>) -> RecordPatch {
  RecordPatch {
    address: scalar(pick(top, nested, &["address", "rev"]), |s| is_doge_address(s).then(|| s.to_string())),
    url: scalar(pick(top, nested, &["url", "website"]), |s| check_url(s, 512)),
    site: scalar(pick(top, nested, &["site", "relay", "insc", "html"]), check_inscription_id),
    avatar: scalar(pick(top, nested, &["avatar"]), |s| {
      if s.chars().count() > 128 {
        return None;
      }
      check_inscription_id(s).or_else(|| check_url(s, 128).filter(|u| u.starts_with("https://")))
    }),
    content: scalar(pick(top, nested, &["content"]), |s| (s.chars().count() <= 280).then(|| s.to_string())),
    cname: scalar(pick(top, nested, &["cname"]), |s| normalize_name(s).ok().map(|n| n.name)),
    nostr: scalar(pick(top, nested, &["nostr"]), check_nostr),
    lightning: scalar(pick(top, nested, &["lightning", "lud16"]), check_lightning),
    subdomains: scalar(pick(top, nested, &["subdomains", "merkle"]), check_hex32),
    addresses: match pick(top, nested, &["addresses"]) {
      Some(Value::Array(a)) if a.len() <= 8 => a
        .iter()
        .map(|v| v.as_str().filter(|s| is_doge_address(s)).map(str::to_string))
        .collect::<Option<Vec<_>>>(),
      _ => None,
    },
    txt: match pick(top, nested, &["txt"]) {
      Some(Value::Null) => Some(TxtPatch::Clear),
      Some(Value::Object(o)) if o.len() <= 8 => o
        .iter()
        .map(|(k, v)| {
          let key_ok = (1..=32).contains(&k.len()) && k.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-');
          let val = v.as_str().filter(|s| s.chars().count() <= 280)?;
          key_ok.then(|| (k.clone(), val.to_string()))
        })
        .collect::<Option<BTreeMap<_, _>>>()
        .map(TxtPatch::Merge),
      _ => None,
    },
  }
}

fn check_url(s: &str, max: usize) -> Option<String> {
  if s.chars().count() > max || s.chars().any(|c| c.is_control() || c.is_whitespace()) {
    return None;
  }
  let lower = s.to_ascii_lowercase();
  let rest = lower.strip_prefix("https://").or_else(|| lower.strip_prefix("http://"))?;
  (!rest.is_empty() && !rest.starts_with('/')).then(|| s.to_string())
}

/// `<64 hex>i<index>`, returned lowercased.
pub fn check_inscription_id(s: &str) -> Option<String> {
  let (txid, index) = s.split_once('i')?;
  let index_ok = !index.is_empty() && index.len() <= 10 && index.bytes().all(|b| b.is_ascii_digit()) && (index == "0" || !index.starts_with('0'));
  (txid.len() == 64 && txid.bytes().all(|b| b.is_ascii_hexdigit()) && index_ok).then(|| s.to_ascii_lowercase())
}

fn check_hex32(s: &str) -> Option<String> {
  (s.len() == 64 && s.bytes().all(|b| b.is_ascii_hexdigit())).then(|| s.to_ascii_lowercase())
}

fn check_nostr(s: &str) -> Option<String> {
  check_hex32(s).or_else(|| (s.len() == 63 && bech32_valid(s, "npub")).then(|| s.to_ascii_lowercase()))
}

fn check_lightning(s: &str) -> Option<String> {
  if bech32_valid(s, "lnurl") {
    return Some(s.to_ascii_lowercase());
  }
  let lower = s.to_ascii_lowercase();
  let (user, host) = lower.split_once('@')?;
  let user_ok = !user.is_empty() && user.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b"-_.+".contains(&b));
  let host_ok = host.contains('.')
    && host.split('.').all(|l| {
      !l.is_empty() && !l.starts_with('-') && !l.ends_with('-') && l.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'-')
    });
  (user_ok && host_ok).then_some(lower)
}

const BECH32_CHARSET: &[u8] = b"qpzry9x8gf2tvdw0s3jn54khce6mua7l";

/// A bech32 string with this prefix and a correct checksum (BIP-173).
fn bech32_valid(s: &str, hrp: &str) -> bool {
  if s != s.to_ascii_lowercase() && s != s.to_ascii_uppercase() {
    return false;
  }
  let lower = s.to_ascii_lowercase();
  let Some(sep) = lower.rfind('1') else { return false };
  let (prefix, data) = (&lower[..sep], &lower[sep + 1..]);
  if prefix != hrp || data.len() < 6 {
    return false;
  }
  let Some(values) = data.bytes().map(|b| BECH32_CHARSET.iter().position(|&c| c == b).map(|p| p as u32)).collect::<Option<Vec<_>>>() else {
    return false;
  };
  const GEN: [u32; 5] = [0x3b6a_57b2, 0x2650_8e6d, 0x1ea1_19fa, 0x3d42_33dd, 0x2a14_62b3];
  let mut chk: u32 = 1;
  let hrp_values = prefix.bytes().map(|b| (b >> 5) as u32).chain([0]).chain(prefix.bytes().map(|b| (b & 31) as u32));
  for v in hrp_values.chain(values) {
    let top = chk >> 25;
    chk = ((chk & 0x1ff_ffff) << 5) ^ v;
    for (i, g) in GEN.iter().enumerate() {
      if (top >> i) & 1 == 1 {
        chk ^= g;
      }
    }
  }
  chk == 1
}

const BASE58: &[u8] = b"123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";

fn base58_decode(s: &str) -> Option<Vec<u8>> {
  let mut out: Vec<u8> = Vec::new(); // little-endian while building
  for ch in s.bytes() {
    let mut carry = BASE58.iter().position(|&a| a == ch)? as u32;
    for b in out.iter_mut() {
      carry += (*b as u32) * 58;
      *b = (carry & 0xff) as u8;
      carry >>= 8;
    }
    while carry > 0 {
      out.push((carry & 0xff) as u8);
      carry >>= 8;
    }
  }
  out.extend(std::iter::repeat_n(0u8, s.bytes().take_while(|&c| c == b'1').count()));
  out.reverse();
  Some(out)
}

/// A mainnet Dogecoin address (P2PKH `D...` or P2SH `9...`/`A...`) with a
/// correct checksum.
pub fn is_doge_address(s: &str) -> bool {
  if !(26..=35).contains(&s.len()) {
    return false;
  }
  let Some(bytes) = base58_decode(s) else { return false };
  if bytes.len() != 25 || !matches!(bytes[0], 0x1e | 0x16) {
    return false;
  }
  let hash = Sha256::digest(Sha256::digest(&bytes[..21]));
  hash[..4] == bytes[21..]
}

// -------------------------------------------------------------- operations --

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DnsOp {
  Register { name: DnsName, records: RecordPatch },
  Config { name: DnsName, patch: RecordPatch },
  /// `None` clears the address's choice.
  Primary { name: Option<DnsName> },
}

/// Reads a DNS operation out of an inscription's content, if it is one.
pub fn parse_dns_op(content_type: &str, body: &[u8]) -> Option<DnsOp> {
  let essence = content_type.split(';').next().unwrap_or("").trim().to_ascii_lowercase();
  if essence != "text/plain" && essence != "application/json" {
    return None;
  }
  let text = std::str::from_utf8(body).ok()?;
  if let Some(obj) = parse_json_object(text) {
    return parse_json_op(&obj);
  }
  // Plain text: the first whitespace-separated token, the rest ignored.
  let token = text.split(char::is_whitespace).find(|t| !t.is_empty())?;
  let name = normalize_name(token).ok()?;
  Some(DnsOp::Register { name, records: RecordPatch::default() })
}

/// A JSON object, also when it has a trailing comma before a `}`, which the
/// spec accepts.
fn parse_json_object(text: &str) -> Option<Obj> {
  let t = text.trim_start();
  if !t.starts_with('{') {
    return None;
  }
  let parsed = serde_json::from_str::<Value>(t).ok().or_else(|| serde_json::from_str::<Value>(&drop_trailing_commas(t)).ok())?;
  match parsed {
    Value::Object(o) => Some(o),
    _ => None,
  }
}

/// Removes each comma that only has whitespace between it and a `}`,
/// outside strings.
fn drop_trailing_commas(s: &str) -> String {
  let mut out = String::with_capacity(s.len());
  let (mut in_str, mut escaped) = (false, false);
  let chars: Vec<char> = s.chars().collect();
  for (i, &c) in chars.iter().enumerate() {
    if in_str {
      if escaped {
        escaped = false;
      } else if c == '\\' {
        escaped = true;
      } else if c == '"' {
        in_str = false;
      }
    } else if c == '"' {
      in_str = true;
    } else if c == ',' && chars[i + 1..].iter().find(|c| !c.is_whitespace()) == Some(&'}') {
      continue;
    }
    out.push(c);
  }
  out
}

fn parse_json_op(obj: &Obj) -> Option<DnsOp> {
  if obj.get("p").and_then(Value::as_str) != Some("dns") {
    return None;
  }
  let name_str = obj.get("name").and_then(Value::as_str);
  let name = || name_str.and_then(|n| normalize_name(n).ok());
  let nested = obj.get("config").and_then(Value::as_object);
  match obj.get("op") {
    Some(Value::String(op)) => match op.as_str() {
      "register" | "reg" => Some(DnsOp::Register { name: name()?, records: parse_patch(obj, None) }),
      "config" | "update" | "upd" => Some(DnsOp::Config { name: name()?, patch: parse_patch(obj, nested) }),
      "primary" => match name_str? {
        "" => Some(DnsOp::Primary { name: None }),
        _ => Some(DnsOp::Primary { name: Some(name()?) }),
      },
      // transfer, renew and anything else are undefined: ignored.
      _ => None,
    },
    Some(_) => None,
    None => {
      let has_fields = RECORD_KEYS.iter().any(|k| obj.contains_key(*k))
        || nested.is_some_and(|n| RECORD_KEYS.iter().any(|k| n.contains_key(*k)));
      if !has_fields {
        return None;
      }
      Some(DnsOp::Config { name: name()?, patch: parse_patch(obj, nested) })
    }
  }
}

// ------------------------------------------------------------------ store --

/// Chain position: height, then place in block.
pub type Pos = (u64, u32);

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct NameEntry {
  pub name: String,
  pub label: String,
  pub namespace: String,
  pub confusable: bool,
  pub inscription_id: String,
  pub number: u64,
  pub height: u64,
  pub tx_index: u32,
  pub time: u64,
  /// Records set by the registering inscription itself.
  pub records: RecordPatch,
  /// Later registers of the same name.
  pub lost: u64,
  /// Place among all names, and among its namespace's, in registration order.
  pub index: u64,
  pub ns_index: u64,
  /// Where the registering inscription was made, once known. Chain order puts
  /// an inscription in several pieces at its first piece, but it exists from
  /// its last; this is filled in when another register of the name needs
  /// comparing against it.
  pub made_at: Option<Pos>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ClaimEntry {
  pub inscription_id: String,
  pub number: u64,
  pub height: u64,
  pub time: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ConfigEntry {
  pub inscription_id: String,
  pub number: u64,
  pub height: u64,
  pub tx_index: u32,
  pub time: u64,
  /// Who made it, and held the name when it was made.
  pub owner: String,
  pub patch: RecordPatch,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct PrimaryEntry {
  pub inscription_id: String,
  pub number: u64,
  pub height: u64,
  pub tx_index: u32,
  pub time: u64,
  pub name: Option<String>,
}

/// What an inscription is to DNS.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct DnsRole {
  /// register, claim (a register that came too late), config or primary
  pub role: String,
  pub name: String,
  pub counted: bool,
  /// Why it did not count, when it did not.
  pub note: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
struct DnsState {
  cursor: Vec<u8>,
  names: u64,
  claims: u64,
  configs: u64,
  configs_ignored: u64,
  primaries: u64,
  primaries_ignored: u64,
  scanned: u64,
  cursor_height: u64,
}

struct Trees {
  meta: Tree,
  seq: Tree,
  genesis: Tree,
  content: Tree,
  by_id: Tree,
  name: Tree,
  by_inscription: Tree,
  index: Tree,
  ns_index: Tree,
  claims: Tree,
  configs: Tree,
  primary: Tree,
  stats: Tree,
  undo: Tree,
}

impl Trees {
  fn open(db: &store::Db) -> Result<Self> {
    Ok(Trees {
      meta: db.open_tree("meta")?,
      seq: db.open_tree("inscription_seq")?,
      genesis: db.open_tree("inscription_genesis")?,
      content: db.open_tree("inscription_content")?,
      by_id: db.open_tree("inscriptions_by_id")?,
      name: db.open_tree("dns_name")?,
      by_inscription: db.open_tree("dns_by_inscription")?,
      index: db.open_tree("dns_index")?,
      ns_index: db.open_tree("dns_ns_index")?,
      claims: db.open_tree("dns_claims")?,
      configs: db.open_tree("dns_config")?,
      primary: db.open_tree("dns_primary")?,
      stats: db.open_tree("dns_stats")?,
      undo: db.open_tree("dns_undo")?,
    })
  }
}

fn dns_state(meta: &Tree) -> Result<DnsState> {
  Ok(match meta.get(DNS_STATE_KEY)? {
    Some(raw) => bincode::deserialize(raw.as_ref()).context("decode dns state")?,
    None => DnsState::default(),
  })
}

/// `name \0 n` keys, for a name's claims and configs in order.
fn name_key(name: &str, n: u64) -> Vec<u8> {
  let mut k = name.as_bytes().to_vec();
  k.push(0);
  k.extend_from_slice(&n.to_be_bytes());
  k
}

fn ns_count_key(ns: &str) -> Vec<u8> {
  format!("ns|{ns}").into_bytes()
}

/// Lengths 1 to 6 of plain ASCII labels have a fixed number of possible
/// names; the rest do not.
fn supply_class(label: &str) -> Option<(usize, char)> {
  let n = label.chars().count();
  if n > 6 || !label.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit()) {
    return None;
  }
  let letters = label.bytes().all(|b| b.is_ascii_lowercase());
  let digits = label.bytes().all(|b| b.is_ascii_digit());
  Some((n, if letters { 'l' } else if digits { 'd' } else { 'm' }))
}

fn supply_key(ns: &str, len: usize, class: char) -> Vec<u8> {
  format!("supply|{ns}|{len}|{class}").into_bytes()
}

fn get_u64(tree: &Tree, key: &[u8]) -> Result<u64> {
  Ok(tree.get(key)?.map(|v| decode_u64(v.as_ref())).transpose()?.unwrap_or(0))
}

fn get_name(tree: &Tree, name: &str) -> Result<Option<NameEntry>> {
  tree.get(name.as_bytes())?.map(|v| bincode::deserialize(v.as_ref()).context("decode dns name")).transpose()
}

fn get_record(by_id: &Tree, id: &str) -> Result<Option<InscriptionRecord>> {
  by_id.get(id.as_bytes())?.map(|v| decode_inscription_record(v.as_ref())).transpose()
}

// ----------------------------------------------------------------- tracer --

#[derive(Debug, Clone)]
struct TxInfo {
  blockhash: Option<String>,
  vin: Vec<(Option<String>, Option<u32>, Option<String>)>,
  /// value in koinu, address ("" when the script has none)
  vout: Vec<(u64, String)>,
}

/// Where an inscription sat, followed back through the node.
#[derive(Debug, Clone)]
enum Loc {
  Out { txid: String, vout: u32, offset: u64, address: String },
  /// Spent to fees in this transaction; `abs` is its place among the inputs.
  Lost { txid: String, abs: u64 },
}

impl Loc {
  fn of(rec: &InscriptionRecord) -> Loc {
    if rec.vout == u32::MAX {
      Loc::Lost { txid: rec.txid.clone(), abs: rec.offset }
    } else {
      Loc::Out { txid: rec.txid.clone(), vout: rec.vout, offset: rec.offset, address: rec.address.clone() }
    }
  }
  fn txid(&self) -> &str {
    match self {
      Loc::Out { txid, .. } | Loc::Lost { txid, .. } => txid,
    }
  }
  fn holder(&self) -> &str {
    match self {
      Loc::Out { address, .. } => address,
      Loc::Lost { .. } => "",
    }
  }
}

/// The redeem script doginals use for each piece of an inscription:
/// `<pubkey> OP_CHECKSIGVERIFY OP_DROP... OP_TRUE`.
fn is_envelope_redeem(script: &[u8]) -> bool {
  let rest = match script.first() {
    Some(0x21) if script.len() > 34 => &script[34..],
    Some(0x41) if script.len() > 66 => &script[66..],
    _ => return false,
  };
  let Some((&0xad, rest)) = rest.split_first() else { return false };
  let drops = rest.iter().take_while(|&&b| b == 0x75 || b == 0x6d).count();
  drops >= 1 && rest[drops..] == [0x51]
}

fn spends_envelope(script_sig_hex: Option<&str>) -> bool {
  let Some(bytes) = script_sig_hex.and_then(|h| hex::decode(h).ok()) else { return false };
  decode_push_datas(&bytes).and_then(|p| p.last().map(|r| is_envelope_redeem(r))).unwrap_or(false)
}

const MAX_TRACE_STEPS: usize = 5_000;

/// Follows inscriptions back in time through the node's transactions.
struct Tracer<'a> {
  config: &'a Config,
  txs: HashMap<String, TxInfo>,
  blocks: HashMap<String, (u64, Vec<String>)>,
}

/// One step back, or the reason there is none.
enum Back {
  /// The inscription came from this earlier output.
  From(Loc),
  /// This transaction made the inscription.
  Created,
}

impl<'a> Tracer<'a> {
  fn new(config: &'a Config) -> Self {
    Tracer { config, txs: HashMap::new(), blocks: HashMap::new() }
  }

  async fn tx(&mut self, txid: &str) -> Result<TxInfo> {
    if let Some(t) = self.txs.get(txid) {
      return Ok(t.clone());
    }
    let client = indexer_rpc_client()?;
    let v: Value = rpc_call(client, self.config, "getrawtransaction", serde_json::json!([txid, true])).await?;
    let parsed: RpcTx = serde_json::from_value(v.clone()).context("decode transaction")?;
    let mut vout = Vec::with_capacity(parsed.vout.len());
    for o in &parsed.vout {
      vout.push((to_satoshis(o.value)?, vout_address(o).unwrap_or_default()));
    }
    let info = TxInfo {
      blockhash: v.get("blockhash").and_then(Value::as_str).map(str::to_string),
      vin: parsed.vin.iter().map(|i| (i.txid.clone(), i.vout, i.script_sig.as_ref().map(|s| s.hex.clone()))).collect(),
      vout,
    };
    if self.txs.len() > 20_000 {
      self.txs.clear();
    }
    self.txs.insert(txid.to_string(), info.clone());
    Ok(info)
  }

  /// Height and place in block of a confirmed transaction.
  async fn position(&mut self, txid: &str) -> Result<Pos> {
    let tx = self.tx(txid).await?;
    let Some(hash) = tx.blockhash else { bail!("transaction {txid} is not in a block") };
    if !self.blocks.contains_key(&hash) {
      let client = indexer_rpc_client()?;
      let block: Value = rpc_call(client, self.config, "getblock", serde_json::json!([hash, 1])).await?;
      if block.get("confirmations").and_then(Value::as_i64).unwrap_or(-1) < 1 {
        bail!("block {hash} is not on the main chain");
      }
      let height = block.get("height").and_then(Value::as_u64).context("block height")?;
      let txids = block["tx"].as_array().map(|a| a.iter().filter_map(|t| t.as_str().map(str::to_string)).collect()).unwrap_or_default();
      if self.blocks.len() > 2_000 {
        self.blocks.clear();
      }
      self.blocks.insert(hash.clone(), (height, txids));
    }
    let (height, txids) = &self.blocks[&hash];
    let index = txids.iter().position(|t| t == txid).with_context(|| format!("{txid} missing from its block"))?;
    Ok((*height, index as u32))
  }

  /// Where the inscription at `loc` was before the transaction that put it
  /// there, using the indexer's rule: inputs in order, first in first out.
  async fn back(&mut self, loc: &Loc, id_txid: &str) -> Result<Back> {
    let txid = loc.txid().to_string();
    if txid == id_txid {
      return Ok(Back::Created);
    }
    let tx = self.tx(&txid).await?;
    let abs = match loc {
      Loc::Out { vout, offset, .. } => tx.vout.iter().take(*vout as usize).map(|o| o.0).sum::<u64>() + offset,
      Loc::Lost { abs, .. } => *abs,
    };
    let mut cum = 0u64;
    for (prev_txid, prev_vout, script_sig) in &tx.vin {
      let (Some(prev_txid), Some(prev_vout)) = (prev_txid, prev_vout) else { continue };
      let prev = self.tx(prev_txid).await?;
      let Some((value, address)) = prev.vout.get(*prev_vout as usize).cloned() else {
        bail!("{prev_txid} has no output {prev_vout}");
      };
      if abs < cum + value {
        // Coming out of an inscription envelope means this transaction is
        // the last piece of the inscription itself: it was made here.
        if spends_envelope(script_sig.as_deref()) {
          return Ok(Back::Created);
        }
        return Ok(Back::From(Loc::Out { txid: prev_txid.clone(), vout: *prev_vout, offset: abs - cum, address }));
      }
      cum += value;
    }
    bail!("could not follow inscription back through {txid}")
  }

  /// Every holder of the inscription from right after `t` until now, newest
  /// first. `None` when it did not exist yet right after `t`.
  async fn holders_since(&mut self, rec: &InscriptionRecord, t: Pos) -> Result<Option<Vec<String>>> {
    let id_txid = rec.id.split('i').next().unwrap_or("").to_string();
    let mut loc = Loc::of(rec);
    let mut holders = Vec::new();
    for _ in 0..MAX_TRACE_STEPS {
      holders.push(loc.holder().to_string());
      if self.position(loc.txid()).await? <= t {
        return Ok(Some(holders));
      }
      match self.back(&loc, &id_txid).await? {
        Back::From(prev) => loc = prev,
        Back::Created => return Ok(None),
      }
    }
    bail!("{} moved more than {MAX_TRACE_STEPS} times", rec.id)
  }

  /// The transaction that made the inscription and who received it there.
  async fn creation(&mut self, rec: &InscriptionRecord) -> Result<(Pos, String)> {
    let id_txid = rec.id.split('i').next().unwrap_or("").to_string();
    let mut loc = Loc::of(rec);
    for _ in 0..MAX_TRACE_STEPS {
      match self.back(&loc, &id_txid).await? {
        Back::From(prev) => loc = prev,
        Back::Created => return Ok((self.position(loc.txid()).await?, loc.holder().to_string())),
      }
    }
    bail!("{} moved more than {MAX_TRACE_STEPS} times", rec.id)
  }
}

/// Never moved since it was made in one transaction: then where it is now is
/// where it was made, and nothing needs looking up.
fn unmoved(rec: &InscriptionRecord) -> bool {
  rec.vout != u32::MAX && rec.id.strip_suffix("i0") == Some(rec.txid.as_str())
}

/// Holder of `rec` right after position `t`, or `None` if it did not exist.
async fn holder_after(tracer: &mut Tracer<'_>, rec: &InscriptionRecord, t: Pos) -> Result<Option<String>> {
  if unmoved(rec) {
    return Ok(Some(rec.address.clone()));
  }
  Ok(tracer.holders_since(rec, t).await?.and_then(|h| h.last().cloned()))
}

/// Where and to whom an inscription was made. `seq_pos` is its row in chain
/// order, which is exact for one made in a single transaction.
async fn made_by(tracer: &mut Tracer<'_>, rec: &InscriptionRecord, seq_pos: Pos) -> Result<(Pos, String)> {
  if unmoved(rec) {
    return Ok((seq_pos, rec.address.clone()));
  }
  tracer.creation(rec).await
}

// ----------------------------------------------------------------- indexer --

struct Candidate {
  key: Vec<u8>,
  pos: Pos,
  number: u64,
  time: u64,
  id: String,
  op: DnsOp,
}

/// Reads the next stretch of chain order, up to what has been numbered, and
/// returns the DNS operations in it plus the last key read.
fn scan(t: &Trees, st: &DnsState, max: usize) -> Result<(Vec<Candidate>, Option<Vec<u8>>, u64)> {
  // As far as numbering has gone, and no closer to the tip than
  // DNS_CONFIRMATIONS allows.
  let mut numbered_through = ii::numbering_state(&t.meta)?.cursor;
  let indexed = ii::meta_u64(&t.meta, b"indexed_height")?.unwrap_or(0);
  let Some(settled) = (indexed + 1).checked_sub(DNS_CONFIRMATIONS) else {
    return Ok((Vec::new(), None, 0));
  };
  let settled_key = ii::seq_key(settled, u32::MAX).to_vec();
  if numbered_through > settled_key {
    numbered_through = settled_key;
  }
  if numbered_through.is_empty() || st.cursor.as_slice() >= numbered_through.as_slice() {
    return Ok((Vec::new(), None, 0));
  }
  let mut start = st.cursor.clone();
  if !start.is_empty() {
    start.push(0);
  }
  let mut rows: Vec<(Vec<u8>, SeqEntry)> = Vec::new();
  let mut last: Option<Vec<u8>> = None;
  let mut scanned = 0u64;
  t.seq.for_each_from(&start, |k, v| {
    if k > numbered_through.as_slice() || scanned as usize >= max {
      return Ok(false);
    }
    scanned += 1;
    last = Some(k.to_vec());
    let e: SeqEntry = bincode::deserialize(v).context("decode seq entry")?;
    // A name is text/plain or application/json, which always classify as
    // text or json (DRC-20 and dogemap bodies cannot be names).
    if e.kinds & (ii::K_TEXT | ii::K_JSON) != 0 {
      rows.push((k.to_vec(), e));
    }
    Ok(true)
  })?;
  let found: Vec<Result<Option<Candidate>>> = rows
    .into_par_iter()
    .map(|(key, e)| -> Result<Option<Candidate>> {
      // The numbered sighting only: a Doginal in several transactions can be
      // in chain order twice, and numbering keeps the first.
      let Some(g) = t.genesis.get(e.id.as_bytes())? else { return Ok(None) };
      let g: ii::Genesis = bincode::deserialize(g.as_ref()).context("decode genesis")?;
      let height = ii::seq_height(&key);
      if g.height != height {
        return Ok(None);
      }
      let Some(raw) = t.content.get(e.id.as_bytes())? else { return Ok(None) };
      let c = decode_inscription_content(raw.as_ref())?;
      let Some(op) = parse_dns_op(&c.content_type, &c.body) else { return Ok(None) };
      let tx_index = u32::from_be_bytes(key[8..12].try_into().unwrap());
      Ok(Some(Candidate { pos: (height, tx_index), number: g.number, time: e.time, id: e.id, op, key }))
    })
    .collect();
  let mut out = Vec::new();
  for f in found {
    if let Some(c) = f? {
      out.push(c);
    }
  }
  out.sort_by(|a, b| a.key.cmp(&b.key));
  Ok((out, last, scanned))
}

/// Applies one stretch in chain order and writes it as one batch.
/// `lenient`: after a stretch has failed a few times, a config, primary or
/// race the node cannot settle is recorded as unchecked instead of stopping
/// the index for good.
async fn apply(
  config: &Config,
  t: &Trees,
  mut st: DnsState,
  cands: Vec<Candidate>,
  last: Vec<u8>,
  scanned: u64,
  lenient: bool,
  era: u64,
) -> Result<DnsState> {
  let mut batch = Batch::default();
  // Writes of this stretch that later rows of it must see.
  let mut names: HashMap<String, NameEntry> = HashMap::new();
  let mut counters: HashMap<Vec<u8>, u64> = HashMap::new();
  let mut tracer = Tracer::new(config);

  async fn counter(t: &Trees, counters: &mut HashMap<Vec<u8>, u64>, key: Vec<u8>) -> Result<u64> {
    if let Some(v) = counters.get(&key) {
      return Ok(*v);
    }
    let v = get_u64(&t.stats, &key)?;
    counters.insert(key, v);
    Ok(v)
  }

  for c in cands {
    let role = |role: &str, name: &str, counted: bool, note: &str| DnsRole {
      role: role.to_string(),
      name: name.to_string(),
      counted,
      note: note.to_string(),
    };
    let lookup = |names: &HashMap<String, NameEntry>, n: &str| -> Result<Option<NameEntry>> {
      match names.get(n) {
        Some(e) => Ok(Some(e.clone())),
        None => get_name(&t.name, n),
      }
    };
    let r = match &c.op {
      DnsOp::Register { name, records } => match lookup(&names, &name.name)? {
        Some(mut existing) => {
          // Rows come in chain order of first pieces, so this register is
          // later unless the name's register was made in several pieces and
          // finished after this one was made. Only then is anything looked up.
          let order: Result<(Pos, Pos)> = async {
            let winner_made = match existing.made_at {
              Some(p) => p,
              None => {
                let rec = get_record(&t.by_id, &existing.inscription_id)?.context("register inscription missing")?;
                made_by(&mut tracer, &rec, (existing.height, existing.tx_index)).await?.0
              }
            };
            let newcomer_made = if c.pos > winner_made {
              c.pos
            } else {
              let rec = get_record(&t.by_id, &c.id)?.context("register inscription missing")?;
              made_by(&mut tracer, &rec, c.pos).await?.0
            };
            Ok((winner_made, newcomer_made))
          }
          .await;
          // When the node cannot settle it, chain order of first pieces
          // decides, and nothing unverified is kept.
          let (winner_made, newcomer_made) = match order {
            Ok(o) => {
              existing.made_at = Some(o.0);
              o
            }
            Err(e) if lenient => {
              warn!("dns index: could not compare {} with the register of {}: {e:#}", c.id, name.name);
              ((existing.height, existing.tx_index), c.pos)
            }
            Err(e) => return Err(e),
          };
          existing.lost += 1;
          st.claims += 1;
          if newcomer_made < winner_made {
            // This one was made first: it takes the name, and the one that
            // held it becomes the missed claim.
            batch.insert(&t.claims, name_key(&name.name, existing.number), bincode::serialize(&ClaimEntry {
              inscription_id: existing.inscription_id.clone(),
              number: existing.number,
              height: existing.height,
              time: existing.time,
            })?);
            batch.insert(
              &t.by_inscription,
              existing.inscription_id.as_bytes().to_vec(),
              bincode::serialize(&role("claim", &name.name, false, "an earlier inscription registered this name first"))?,
            );
            existing.inscription_id = c.id.clone();
            existing.number = c.number;
            existing.height = c.pos.0;
            existing.tx_index = c.pos.1;
            existing.time = c.time;
            existing.records = records.clone();
            existing.made_at = Some(newcomer_made);
            batch.insert(&t.name, name.name.as_bytes().to_vec(), bincode::serialize(&existing)?);
            names.insert(name.name.clone(), existing);
            role("register", &name.name, true, "")
          } else {
            batch.insert(&t.claims, name_key(&name.name, c.number), bincode::serialize(&ClaimEntry {
              inscription_id: c.id.clone(),
              number: c.number,
              height: c.pos.0,
              time: c.time,
            })?);
            batch.insert(&t.name, name.name.as_bytes().to_vec(), bincode::serialize(&existing)?);
            names.insert(name.name.clone(), existing);
            role("claim", &name.name, false, "an earlier inscription registered this name first")
          }
        }
        None => {
          let ns_key = ns_count_key(&name.namespace);
          let ns_index = counter(t, &mut counters, ns_key.clone()).await?;
          let entry = NameEntry {
            name: name.name.clone(),
            label: name.label.clone(),
            namespace: name.namespace.clone(),
            confusable: name.confusable,
            inscription_id: c.id.clone(),
            number: c.number,
            height: c.pos.0,
            tx_index: c.pos.1,
            time: c.time,
            records: records.clone(),
            lost: 0,
            index: st.names,
            ns_index,
            made_at: None,
          };
          batch.insert(&t.name, name.name.as_bytes().to_vec(), bincode::serialize(&entry)?);
          batch.insert(&t.index, st.names.to_be_bytes().to_vec(), name.name.as_bytes().to_vec());
          batch.insert(&t.ns_index, name_key(&name.namespace, ns_index), name.name.as_bytes().to_vec());
          counters.insert(ns_key.clone(), ns_index + 1);
          batch.insert(&t.stats, ns_key, encode_u64(ns_index + 1).to_vec());
          if let Some((len, class)) = supply_class(&name.label) {
            let key = supply_key(&name.namespace, len, class);
            let n = counter(t, &mut counters, key.clone()).await? + 1;
            counters.insert(key.clone(), n);
            batch.insert(&t.stats, key, encode_u64(n).to_vec());
          }
          names.insert(name.name.clone(), entry);
          st.names += 1;
          role("register", &name.name, true, "")
        }
      },
      DnsOp::Config { name, patch } => {
        let verdict = match lookup(&names, &name.name)? {
          None => Err("the name is not registered"),
          Some(entry) => {
            let check: Result<std::result::Result<(Pos, String), &'static str>> = async {
              let rec = get_record(&t.by_id, &c.id)?.context("config inscription missing")?;
              let (made_at, owner) = made_by(&mut tracer, &rec, c.pos).await?;
              let reg = get_record(&t.by_id, &entry.inscription_id)?.context("register inscription missing")?;
              let holder = holder_after(&mut tracer, &reg, made_at).await?;
              Ok(if owner.is_empty() || holder.as_deref() != Some(owner.as_str()) {
                Err("not made by the name's holder")
              } else {
                Ok((made_at, owner))
              })
            }
            .await;
            match check {
              Ok(v) => v,
              Err(e) if lenient => {
                warn!("dns index: could not check config {}: {e:#}", c.id);
                Err("its holder could not be checked against the node")
              }
              Err(e) => return Err(e),
            }
          }
        };
        match verdict {
          Ok((made_at, owner)) => {
            batch.insert(&t.configs, name_key(&name.name, c.number), bincode::serialize(&ConfigEntry {
              inscription_id: c.id.clone(),
              number: c.number,
              height: made_at.0,
              tx_index: made_at.1,
              time: c.time,
              owner,
              patch: patch.clone(),
            })?);
            st.configs += 1;
            role("config", &name.name, true, if patch.is_empty() { "sets no valid record" } else { "" })
          }
          Err(why) => {
            st.configs_ignored += 1;
            role("config", &name.name, false, why)
          }
        }
      }
      DnsOp::Primary { name } => {
        let check: Result<std::result::Result<(Pos, String), &'static str>> = async {
          let rec = get_record(&t.by_id, &c.id)?.context("primary inscription missing")?;
          let (made_at, owner) = made_by(&mut tracer, &rec, c.pos).await?;
          if owner.is_empty() {
            return Ok(Err("the inscription has no owner address"));
          }
          if let Some(n) = name {
            let Some(entry) = lookup(&names, &n.name)? else { return Ok(Err("the name is not registered")) };
            let reg = get_record(&t.by_id, &entry.inscription_id)?.context("register inscription missing")?;
            if holder_after(&mut tracer, &reg, made_at).await?.as_deref() != Some(owner.as_str()) {
              return Ok(Err("its owner does not hold the name"));
            }
          }
          Ok(Ok((made_at, owner)))
        }
        .await;
        let verdict = match check {
          Ok(v) => v,
          Err(e) if lenient => {
            warn!("dns index: could not check primary {}: {e:#}", c.id);
            Err("its owner could not be checked against the node")
          }
          Err(e) => return Err(e),
        };
        let shown = name.as_ref().map(|n| n.name.clone()).unwrap_or_default();
        match verdict {
          Ok((made_at, owner)) => {
            batch.insert(&t.primary, owner.as_bytes().to_vec(), bincode::serialize(&PrimaryEntry {
              inscription_id: c.id.clone(),
              number: c.number,
              height: made_at.0,
              tx_index: made_at.1,
              time: c.time,
              name: name.as_ref().map(|n| n.name.clone()),
            })?);
            st.primaries += 1;
            role("primary", &shown, true, "")
          }
          Err(why) => {
            st.primaries_ignored += 1;
            role("primary", &shown, false, why)
          }
        }
      }
    };
    batch.insert(&t.by_inscription, c.id.as_bytes().to_vec(), bincode::serialize(&r)?);
  }
  st.cursor_height = ii::seq_height(&last);
  st.cursor = last.clone();
  st.scanned += scanned;
  batch.insert(&t.meta, DNS_STATE_KEY.to_vec(), bincode::serialize(&st)?);

  let indexed = ii::meta_u64(&t.meta, b"indexed_height")?.unwrap_or(0);
  let _w = DNS_WRITE.lock().unwrap_or_else(|e| e.into_inner());
  if reorg_gen(&t.meta)? != era {
    bail!("{REORGED}");
  }
  if st.cursor_height + UNDO_BLOCKS >= indexed {
    let ops = batch.previous(&t.meta)?;
    batch.insert(&t.undo, last, bincode::serialize(&DnsUndo { last_height: st.cursor_height, ops })?);
  }
  // Undo records too deep to be used again.
  let floor = ii::seq_key(indexed.saturating_sub(UNDO_BLOCKS), 0);
  t.undo.for_each_from(b"", |k, _| {
    if k >= floor.as_slice() {
      return Ok(false);
    }
    batch.remove(&t.undo, k.to_vec());
    Ok(true)
  })?;
  batch.commit(&t.meta)?;
  Ok(st)
}

/// Clears the whole DNS index, so it is read again from the first numbered
/// inscription. The running task notices (as after a reorg) and starts over.
pub(crate) fn reset(db: &store::Db) -> Result<()> {
  let _w = DNS_WRITE.lock().unwrap_or_else(|e| e.into_inner());
  for tree in [
    "dns_name", "dns_by_inscription", "dns_index", "dns_ns_index", "dns_claims", "dns_config", "dns_primary", "dns_stats", "dns_undo",
  ] {
    // Keys are UTF-8 names, big-endian numbers and seq keys: all below this.
    db.open_tree(tree)?.delete_range(Vec::new(), vec![0xff; 64])?;
  }
  let meta = db.open_tree("meta")?;
  meta.remove(DNS_STATE_KEY)?;
  meta.insert(REORG_GEN_KEY, encode_u64(reorg_gen(&meta)? + 1).to_vec())?;
  Ok(())
}

/// The error a step returns when a reorg came between reading and writing it.
const REORGED: &str = "a reorg changed the chain under this stretch";

/// Undoes every DNS step that read blocks at `height` and above, newest
/// first, each as one batch. Called by a reorg's rollback.
pub(crate) fn undo_from(db: &store::Db, height: u64) -> Result<()> {
  let _w = DNS_WRITE.lock().unwrap_or_else(|e| e.into_inner());
  let meta = db.open_tree("meta")?;
  meta.insert(REORG_GEN_KEY, encode_u64(reorg_gen(&meta)? + 1).to_vec())?;
  let undo = db.open_tree("dns_undo")?;
  let st = dns_state(&meta)?;
  if st.cursor.is_empty() || st.cursor_height < height {
    return Ok(());
  }
  let mut steps: Vec<(Vec<u8>, DnsUndo)> = Vec::new();
  undo.for_each_from(&ii::seq_key(height, 0), |k, v| {
    steps.push((k.to_vec(), bincode::deserialize(v).context("decode dns undo")?));
    Ok(true)
  })?;
  let undone = steps.len();
  for (key, step) in steps.into_iter().rev() {
    let mut batch = Batch::default();
    for (tree, k, previous) in step.ops {
      batch.put_raw(tree, k, previous);
    }
    batch.remove(&undo, key);
    batch.commit(&meta)?;
  }
  let st = dns_state(&meta)?;
  if !st.cursor.is_empty() && st.cursor_height >= height {
    warn!("dns index: the reorg at block {height} is deeper than its undo history; names from block {height} on may be wrong");
  } else {
    warn!("dns index: reorg at block {height}: undid {undone} steps, reading again from block {}", st.cursor_height);
  }
  Ok(())
}

/// The DNS indexer: catches up over every numbered inscription, then follows
/// numbering as it goes.
pub async fn run_dns_index(config: Config) -> Result<()> {
  let db = ii::db_of(&config)?;
  let t = Arc::new(Trees::open(&db)?);
  let mut st = dns_state(&t.meta)?;
  info!("dns index: starting at block {}, {} names so far", st.cursor_height, st.names);
  let (mut last_log, mut caught_up, mut failures) = (Instant::now(), false, 0u32);
  let mut seen_era = reorg_gen(&t.meta)?;
  loop {
    // A reorg undid steps: start again from what is stored.
    let era = reorg_gen(&t.meta)?;
    if era != seen_era {
      seen_era = era;
      st = dns_state(&t.meta)?;
    }
    let (t2, st2) = (t.clone(), st.clone());
    let (cands, last, scanned) = tokio::task::spawn_blocking(move || scan(&t2, &st2, 200_000)).await.context("dns scan")??;
    let Some(last) = last else {
      if !caught_up {
        caught_up = true;
        if st.cursor.is_empty() {
          info!("dns index: waiting for inscription numbering, then every inscription is read in chain order");
        } else {
          info!("dns index: caught up at block {}, {} names, {} missed claims, {} configs", st.cursor_height, st.names, st.claims, st.configs);
        }
      }
      sleep(Duration::from_secs(2)).await;
      continue;
    };
    // A failed stretch writes nothing, so it is simply read again.
    match apply(&config, &t, st.clone(), cands, last, scanned, failures >= 3, era).await {
      Ok(next) => {
        st = next;
        failures = 0;
      }
      Err(_) if reorg_gen(&t.meta).unwrap_or(era) != era => continue,
      Err(e) => {
        failures += 1;
        warn!("dns index: stretch after block {} failed (try {failures}): {e:#}", st.cursor_height);
        sleep(Duration::from_secs(20)).await;
        continue;
      }
    }
    if last_log.elapsed() > Duration::from_secs(60) {
      last_log = Instant::now();
      info!("dns index: at block {}, {} inscriptions read, {} names, {} missed claims", st.cursor_height, st.scanned, st.names, st.claims);
    }
  }
}

// ----------------------------------------------------------------- readers --

#[derive(Debug, Clone, Serialize)]
pub struct DnsStatus {
  /// Inscription numbering is complete and this index has read all of it.
  pub caught_up: bool,
  pub height: u64,
  pub scanned: u64,
  pub names: u64,
  pub claims: u64,
  pub configs: u64,
  pub configs_ignored: u64,
  pub primaries: u64,
  pub primaries_ignored: u64,
}

pub fn dns_status(config: &Config) -> Result<DnsStatus> {
  let db = ii::db_of(config)?;
  let meta = db.open_tree("meta")?;
  let st = dns_state(&meta)?;
  let numbered = ii::numbering_state(&meta)?.cursor;
  let backfilled = ii::inscription_seq_backfill_done(config)?;
  let indexed = ii::meta_u64(&meta, b"indexed_height")?.unwrap_or(0);
  // Read up to what it may read (numbered and settled), and within a few
  // blocks of the settled tip.
  let settled = ii::seq_key((indexed + 1).saturating_sub(DNS_CONFIRMATIONS), u32::MAX).to_vec();
  let readable = if numbered > settled { settled } else { numbered.clone() };
  let mut start = st.cursor.clone();
  if !start.is_empty() {
    start.push(0);
  }
  let mut unread = false;
  db.open_tree("inscription_seq")?.for_each_from(&start, |k, _| {
    unread = k <= readable.as_slice();
    Ok(false)
  })?;
  let caught_up = backfilled && !numbered.is_empty() && !unread && st.cursor_height + DNS_CONFIRMATIONS + 3 >= indexed;
  Ok(DnsStatus {
    caught_up,
    height: st.cursor_height,
    scanned: st.scanned,
    names: st.names,
    claims: st.claims,
    configs: st.configs,
    configs_ignored: st.configs_ignored,
    primaries: st.primaries,
    primaries_ignored: st.primaries_ignored,
  })
}

#[derive(Debug, Clone, Serialize)]
pub struct DnsListed {
  pub name: String,
  pub namespace: String,
  pub inscription_id: String,
  pub number: u64,
  pub height: u64,
  pub time: u64,
  pub owner: String,
  pub confusable: bool,
  pub claims: u64,
}

#[derive(Debug, Clone, Serialize)]
pub struct DnsPage {
  pub total: u64,
  pub items: Vec<DnsListed>,
}

fn listed(t_name: &Tree, by_id: &Tree, names: Vec<Vec<u8>>) -> Result<Vec<DnsListed>> {
  let entries = t_name.multi_get(&names)?;
  let mut out = Vec::new();
  let mut ids = Vec::new();
  for raw in entries.into_iter().flatten() {
    let e: NameEntry = bincode::deserialize(raw.as_ref()).context("decode dns name")?;
    ids.push(e.inscription_id.clone());
    out.push(e);
  }
  let recs = by_id.multi_get(&ids)?;
  Ok(out
    .into_iter()
    .zip(recs)
    .map(|(e, r)| DnsListed {
      owner: r.and_then(|r| decode_inscription_record(r.as_ref()).ok()).map(|r| r.address).unwrap_or_default(),
      name: e.name,
      namespace: e.namespace,
      inscription_id: e.inscription_id,
      number: e.number,
      height: e.height,
      time: e.time,
      confusable: e.confusable,
      claims: e.lost,
    })
    .collect())
}

/// Names in registration order, all of them or one namespace's; `page` from 1.
pub fn dns_list(config: &Config, namespace: Option<&str>, page: u64, limit: u64, oldest_first: bool) -> Result<DnsPage> {
  let db = ii::db_of(config)?;
  let (meta, stats) = (db.open_tree("meta")?, db.open_tree("dns_stats")?);
  let total = match namespace {
    Some(ns) => get_u64(&stats, &ns_count_key(ns))?,
    None => dns_state(&meta)?.names,
  };
  let skip = page.saturating_sub(1).saturating_mul(limit);
  if skip >= total {
    return Ok(DnsPage { total, items: Vec::new() });
  }
  let take = limit.min(total - skip);
  let indexes: Vec<u64> = if oldest_first { (skip..skip + take).collect() } else { (0..take).map(|i| total - 1 - skip - i).collect() };
  let keys: Vec<Vec<u8>> = match namespace {
    Some(ns) => indexes.iter().map(|&i| name_key(ns, i)).collect(),
    None => indexes.iter().map(|i| i.to_be_bytes().to_vec()).collect(),
  };
  let tree = db.open_tree(if namespace.is_some() { "dns_ns_index" } else { "dns_index" })?;
  let names: Vec<Vec<u8>> = tree.multi_get(&keys)?.into_iter().flatten().map(|v| v.to_vec()).collect();
  Ok(DnsPage { total, items: listed(&db.open_tree("dns_name")?, &db.open_tree("inscriptions_by_id")?, names)? })
}

/// Namespaces always listed, in this order, with their counts even at zero.
/// Every valid namespace is indexed; these are only shown first.
pub const FEATURED_NAMESPACES: [&str; 6] = ["doge", "dogecoin", "doginals", "dogefeed", "pup", "shib"];

fn featured_counts(stats: &Tree) -> Result<Vec<(String, u64)>> {
  FEATURED_NAMESPACES.iter().map(|ns| Ok((ns.to_string(), get_u64(stats, &ns_count_key(ns))?))).collect()
}

/// The featured namespaces and how many names each has.
pub fn dns_featured(config: &Config) -> Result<Vec<(String, u64)>> {
  featured_counts(&ii::db_of(config)?.open_tree("dns_stats")?)
}

/// Namespaces with the most names.
pub fn dns_namespaces(config: &Config, limit: usize) -> Result<Vec<(String, u64)>> {
  let stats = ii::db_of(config)?.open_tree("dns_stats")?;
  let mut all = Vec::new();
  stats.for_each_prefix(b"ns|", |k, v| {
    all.push((String::from_utf8_lossy(&k[3..]).into_owned(), decode_u64(v)?));
    Ok(true)
  })?;
  all.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));
  all.truncate(limit);
  Ok(all)
}

#[derive(Debug, Clone, Serialize)]
pub struct DnsSupply {
  /// Label length in characters.
  pub length: usize,
  /// Possible plain ASCII labels of this length, and how many are taken.
  pub letters: Option<(u64, u64)>,
  pub digits: Option<(u64, u64)>,
  pub letters_and_digits: Option<(u64, u64)>,
}

pub fn dns_supply(config: &Config, namespace: &str, length: usize) -> Result<DnsSupply> {
  let stats = ii::db_of(config)?.open_tree("dns_stats")?;
  if !(1..=6).contains(&length) {
    return Ok(DnsSupply { length, letters: None, digits: None, letters_and_digits: None });
  }
  let taken = |c| get_u64(&stats, &supply_key(namespace, length, c));
  let (l, d, m) = (taken('l')?, taken('d')?, taken('m')?);
  let n = length as u32;
  Ok(DnsSupply {
    length,
    letters: Some((26u64.pow(n), l)),
    digits: Some((10u64.pow(n), d)),
    letters_and_digits: Some((36u64.pow(n), l + d + m)),
  })
}

#[derive(Debug, Clone, Serialize)]
pub struct DnsConfigView {
  pub inscription_id: String,
  pub number: u64,
  pub height: u64,
  pub time: u64,
  pub owner: String,
  /// Made by the current holder, so it is part of the records now.
  pub applies: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct DnsNameView {
  pub name: String,
  pub label: String,
  pub namespace: String,
  pub confusable: bool,
  pub inscription_id: String,
  pub number: u64,
  pub height: u64,
  pub time: u64,
  pub owner: String,
  pub records: DnsRecords,
  pub configs: Vec<DnsConfigView>,
  pub claims: u64,
}

pub fn dns_get(config: &Config, name: &str) -> Result<Option<DnsNameView>> {
  let db = ii::db_of(config)?;
  let Some(e) = get_name(&db.open_tree("dns_name")?, name)? else { return Ok(None) };
  let owner = get_record(&db.open_tree("inscriptions_by_id")?, &e.inscription_id)?.map(|r| r.address).unwrap_or_default();
  // The register's records, then each config the current holder made.
  let mut records = DnsRecords::default();
  records.apply(&e.records);
  let mut configs = Vec::new();
  let mut start = name.as_bytes().to_vec();
  start.push(0);
  db.open_tree("dns_config")?.for_each_prefix(&start, |_, v| {
    let c: ConfigEntry = bincode::deserialize(v).context("decode dns config")?;
    let applies = !owner.is_empty() && c.owner == owner;
    if applies {
      records.apply(&c.patch);
    }
    configs.push(DnsConfigView { inscription_id: c.inscription_id, number: c.number, height: c.height, time: c.time, owner: c.owner, applies });
    Ok(true)
  })?;
  Ok(Some(DnsNameView {
    name: e.name,
    label: e.label,
    namespace: e.namespace,
    confusable: e.confusable,
    inscription_id: e.inscription_id,
    number: e.number,
    height: e.height,
    time: e.time,
    owner,
    records,
    configs,
    claims: e.lost,
  }))
}

/// Later registers of a name, oldest first.
pub fn dns_claims(config: &Config, name: &str, limit: usize) -> Result<Vec<ClaimEntry>> {
  let mut out = Vec::new();
  let mut start = name.as_bytes().to_vec();
  start.push(0);
  ii::db_of(config)?.open_tree("dns_claims")?.for_each_prefix(&start, |_, v| {
    if out.len() >= limit {
      return Ok(false);
    }
    out.push(bincode::deserialize(v).context("decode dns claim")?);
    Ok(true)
  })?;
  Ok(out)
}

pub fn dns_role(config: &Config, inscription_id: &str) -> Result<Option<DnsRole>> {
  ii::db_of(config)?
    .open_tree("dns_by_inscription")?
    .get(inscription_id.as_bytes())?
    .map(|v| bincode::deserialize(v.as_ref()).context("decode dns role"))
    .transpose()
}

/// Names an address holds now, oldest registration first.
pub fn dns_names_of(config: &Config, address: &str) -> Result<Vec<DnsListed>> {
  let db = ii::db_of(config)?;
  let mut ids: Vec<String> = Vec::new();
  let prefix = format!("{address}|");
  db.open_tree("inscriptions_by_address")?.for_each_prefix(prefix.as_bytes(), |k, _| {
    ids.push(String::from_utf8_lossy(&k[prefix.len()..]).into_owned());
    Ok(true)
  })?;
  let roles = db.open_tree("dns_by_inscription")?;
  let mut names = Vec::new();
  for chunk in ids.chunks(10_000) {
    for raw in roles.multi_get(chunk)?.into_iter().flatten() {
      let r: DnsRole = bincode::deserialize(raw.as_ref()).context("decode dns role")?;
      if r.role == "register" {
        names.push(r.name.into_bytes());
      }
    }
  }
  let mut out = listed(&db.open_tree("dns_name")?, &db.open_tree("inscriptions_by_id")?, names)?;
  out.retain(|n| n.owner == address);
  out.sort_by_key(|n| n.number);
  Ok(out)
}

/// The name an address has chosen to show, if it still holds it and has held
/// it ever since choosing. A name sent away clears the choice for good.
pub async fn dns_primary(config: &Config, address: &str) -> Result<Option<String>> {
  static CHECKED: Mutex<Option<HashMap<(String, String, String), bool>>> = Mutex::new(None);
  let db = ii::db_of(config)?;
  let Some(raw) = db.open_tree("dns_primary")?.get(address.as_bytes())? else { return Ok(None) };
  let p: PrimaryEntry = bincode::deserialize(raw.as_ref()).context("decode dns primary")?;
  let Some(name) = p.name else { return Ok(None) };
  let Some(e) = get_name(&db.open_tree("dns_name")?, &name)? else { return Ok(None) };
  let Some(reg) = get_record(&db.open_tree("inscriptions_by_id")?, &e.inscription_id)? else { return Ok(None) };
  if reg.address != address {
    return Ok(None);
  }
  if unmoved(&reg) {
    return Ok(Some(name));
  }
  // It has moved at some point: make sure every move since the choice
  // stayed with this address.
  let key = (address.to_string(), format!("{}:{}", reg.txid, reg.vout), p.inscription_id.clone());
  if let Some(ok) = CHECKED.lock().unwrap_or_else(|e| e.into_inner()).as_ref().and_then(|m| m.get(&key).copied()) {
    return Ok(ok.then_some(name));
  }
  let mut tracer = Tracer::new(config);
  let ok = match tracer.holders_since(&reg, (p.height, p.tx_index)).await? {
    Some(holders) => holders.iter().all(|h| h == address),
    None => false,
  };
  let mut guard = CHECKED.lock().unwrap_or_else(|e| e.into_inner());
  let map = guard.get_or_insert_with(HashMap::new);
  if map.len() > 10_000 {
    map.clear();
  }
  map.insert(key, ok);
  Ok(ok.then_some(name))
}

// ------------------------------------------------------------------- tests --

#[cfg(test)]
mod tests {
  use super::*;

  fn reg(body: &str) -> Option<String> {
    match parse_dns_op("text/plain", body.as_bytes()) {
      Some(DnsOp::Register { name, .. }) => Some(name.name),
      _ => None,
    }
  }

  /// Every vector in the spec's vectors/conformance.json (v1.2) that is
  /// about inscription content. The OP_RETURN ones are about carriers this
  /// indexer never reads.
  #[test]
  fn spec_conformance_vectors() {
    let ok: &[(&str, &str)] = &[
      ("jon.doge", "jon.doge"),
      ("Jon.Doge", "jon.doge"),
      ("jon.eth", "jon.eth"),
      ("api.doge", "api.doge"),
      ("🐕.doge", "🐕.doge"),
      ("Ｊｏｎ.doge", "jon.doge"),
      ("1.dogimap", "1.dogimap"),
      ("such.123", "such.123"),
      ("doge-labs.doge", "doge-labs.doge"),
      ("\u{0441}\u{043e}\u{0440}\u{0435}\u{0445}.doge", "\u{0441}\u{043e}\u{0440}\u{0435}\u{0445}.doge"),
    ];
    for (body, name) in ok {
      assert_eq!(reg(body).as_deref(), Some(*name), "{body}");
    }
    for body in ["has space.doge", "d.gg/rjg9wk3uu3", "-jon.doge", "6412814.dogemap", "self.total_supply", "j\u{043e}n.doge", "DNS1|reg|example.doge|DBckmbhKFCdFKC5LX8NtMUG5FPZvL5wLHR"] {
      assert_eq!(reg(body), None, "{body}");
    }
    assert!(normalize_name("\u{0441}\u{043e}\u{0440}\u{0435}\u{0445}.doge").unwrap().confusable);
    assert!(!normalize_name("jon.doge").unwrap().confusable);

    let json = |b: &str| parse_dns_op("application/json", b.as_bytes());
    match json(r#"{"p":"dns","op":"register","name":"jon.doge","url":"https://dogecoin.dog"}"#) {
      Some(DnsOp::Register { name, records }) => {
        assert_eq!(name.name, "jon.doge");
        assert_eq!(records.url.as_deref(), Some("https://dogecoin.dog"));
      }
      other => panic!("{other:?}"),
    }
    assert!(matches!(json(r#"{"p":"dns","op":"register","name":"www.doge"}"#), Some(DnsOp::Register { .. })));
    match json(r#"{"p":"dns","op":"config","name":"jon.doge","url":"https://dogex.dog"}"#) {
      Some(DnsOp::Config { name, patch }) => {
        assert_eq!(name.name, "jon.doge");
        assert_eq!(patch.url.as_deref(), Some("https://dogex.dog"));
      }
      other => panic!("{other:?}"),
    }
    let v12 = r#"{"p":"dns","op":"config","name":"jon.doge","nostr":"abababababababababababababababababababababababababababababababab","lightning":"satoshi@pay.doge","subdomains":"cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd","txt":{"note":"gm"}}"#;
    match json(v12) {
      Some(DnsOp::Config { patch, .. }) => {
        assert_eq!(patch.nostr.as_deref(), Some("abababababababababababababababababababababababababababababababab"));
        assert_eq!(patch.lightning.as_deref(), Some("satoshi@pay.doge"));
        assert_eq!(patch.subdomains.as_deref(), Some("cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd"));
        assert_eq!(patch.txt, Some(TxtPatch::Merge(BTreeMap::from([("note".to_string(), "gm".to_string())]))));
      }
      other => panic!("{other:?}"),
    }
  }

  #[test]
  fn name_rules() {
    let bad = [
      "a.b.doge", ".doge", "jon.", "jon", "jon_.doge", "jon'.doge", "jon\u{2019}s.doge", "jon\u{02bc}s.doge", "j@n.doge",
      "j:n.doge", "j#n.doge", "j?n.doge", "jon-.doge", "jon.-doge", "jon\u{200b}.doge", "jon\u{00ad}.doge",
      "jon\u{3164}.doge", "jon\u{ff0e}doge", "jon\u{3002}doge.eth", "jon\u{0660}doge.eth", "x.bitmap", "x.dogemapper",
      "x.DOGEMAP", "a\u{200d}b.doge", "a\u{fe0f}.doge", "jon\u{2800}.doge", "\u{202e}nob.doge",
    ];
    for n in bad {
      assert!(normalize_name(n).is_err(), "{n:?} should be rejected");
    }
    let long = format!("{}.doge", "a".repeat(63));
    assert!(normalize_name(&long).is_ok());
    assert!(normalize_name(&format!("{}.doge", "a".repeat(64))).is_err());
    // Emoji sequences: ZWJ, skin tone, flags, keycaps.
    for n in ["👨\u{200d}💻.doge", "🏳\u{fe0f}\u{200d}🌈.doge", "👍🏽.doge", "🇺🇸.doge", "1\u{fe0f}\u{20e3}.doge", "❤\u{fe0f}.doge"] {
      assert!(normalize_name(n).is_ok(), "{n:?} should be accepted");
    }
    // One script per part, but each part may use its own.
    assert!(normalize_name("柴犬.doge").is_ok());
    assert!(normalize_name("δοge.doge").is_err());
    assert!(normalize_name("ドージ.コイン").is_ok());
    // Non-ASCII is kept as written; only ASCII is lowercased.
    assert_eq!(normalize_name("JÖN.Doge").unwrap().name, "jÖn.doge");
    assert_eq!(normalize_name("bitmapx.doge").unwrap().name, "bitmapx.doge");
    assert_eq!(normalize_name("x.bitmaps").unwrap().name, "x.bitmaps");
  }

  #[test]
  fn plain_text_takes_the_first_token() {
    assert_eq!(reg("jon.doge\n").as_deref(), Some("jon.doge"));
    assert_eq!(reg("  jon.doge extra words.doge").as_deref(), Some("jon.doge"));
    assert_eq!(reg("hello world"), None);
    assert_eq!(reg(""), None);
    // Content type decides whether it is looked at at all.
    assert!(parse_dns_op("text/plain;charset=utf-8", b"jon.doge").is_some());
    assert!(parse_dns_op("application/json", b"jon.doge").is_some());
    assert!(parse_dns_op("text/html", b"jon.doge").is_none());
    assert!(parse_dns_op("", b"jon.doge").is_none());
    assert!(parse_dns_op("image/png", b"jon.doge").is_none());
    // Not UTF-8.
    assert!(parse_dns_op("text/plain", &[0x6a, 0xff, 0x2e, 0x64]).is_none());
  }

  #[test]
  fn json_forms() {
    let json = |b: &str| parse_dns_op("text/plain", b.as_bytes());
    // Trailing comma before a closing brace.
    assert!(matches!(json(r#"{"p":"dns","op":"reg","name":"jon.doge",}"#), Some(DnsOp::Register { .. })));
    assert!(matches!(json("{\"p\":\"dns\",\"op\":\"reg\",\"name\":\"jon.doge\" ,\n}"), Some(DnsOp::Register { .. })));
    // A comma inside a string is left alone.
    match json(r#"{"p":"dns","op":"reg","name":"jon.doge","content":"a ,}",}"#) {
      Some(DnsOp::Register { records, .. }) => assert_eq!(records.content.as_deref(), Some("a ,}")),
      other => panic!("{other:?}"),
    }
    // Wrong or missing parts.
    for b in [
      r#"{"p":"DNS","op":"reg","name":"jon.doge"}"#,
      r#"{"p":"dns","op":"REG","name":"jon.doge"}"#,
      r#"{"p":"dns","op":"transfer","name":"jon.doge"}"#,
      r#"{"p":"dns","op":"renew","name":"jon.doge"}"#,
      r#"{"p":"dns","op":"reg","name":"jon doge"}"#,
      r#"{"p":"dns","op":"reg"}"#,
      r#"{"p":"dns","name":"jon.doge"}"#,
      r#"{"p":"drc-20","op":"mint","tick":"dogi","amt":"1"}"#,
      r#"{"p":"sns","op":"reg","name":"jon.sats"}"#,
      r#"["jon.doge"]"#,
    ] {
      assert_eq!(json(b), None, "{b}");
    }
    // No op, but record fields: a config, never a register.
    assert!(matches!(json(r#"{"p":"dns","name":"jon.doge","url":"https://a.b"}"#), Some(DnsOp::Config { .. })));
    // Primary, and clearing it.
    assert!(matches!(json(r#"{"p":"dns","op":"primary","name":"jon.doge"}"#), Some(DnsOp::Primary { name: Some(_) })));
    assert!(matches!(json(r#"{"p":"dns","op":"primary","name":""}"#), Some(DnsOp::Primary { name: None })));
    assert_eq!(json(r#"{"p":"dns","op":"primary","name":"nope"}"#), None);
  }

  #[test]
  fn record_fields() {
    let patch = |b: &str| match parse_dns_op("application/json", b.as_bytes()) {
      Some(DnsOp::Config { patch, .. }) => patch,
      other => panic!("{other:?}"),
    };
    let p = patch(
      r#"{"p":"dns","op":"config","name":"jon.doge","rev":"DBckmbhKFCdFKC5LX8NtMUG5FPZvL5wLHR","website":"https://x.dog","relay":"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAi0","lud16":"Me@Pay.Doge","merkle":"CDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCDCD","cname":"Other.Doge"}"#,
    );
    assert_eq!(p.address.as_deref(), Some("DBckmbhKFCdFKC5LX8NtMUG5FPZvL5wLHR"));
    assert_eq!(p.url.as_deref(), Some("https://x.dog"));
    assert_eq!(p.site.as_deref(), Some("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaai0"));
    assert_eq!(p.lightning.as_deref(), Some("me@pay.doge"));
    assert_eq!(p.subdomains.as_deref(), Some("cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd"));
    assert_eq!(p.cname.as_deref(), Some("other.doge"));

    // Invalid values are left out; the rest of the config still counts.
    let p = patch(
      r#"{"p":"dns","op":"config","name":"jon.doge","address":"DBckmbhKFCdFKC5LX8NtMUG5FPZvL5wLHS","url":"ftp://x","site":"abc","content":"ok","avatar":"http://x.dog/a.png","nostr":"npub1nope"}"#,
    );
    assert_eq!(p.address, None, "bad checksum");
    assert_eq!(p.url, None);
    assert_eq!(p.site, None);
    assert_eq!(p.avatar, None, "avatar URLs must be https");
    assert_eq!(p.nostr, None);
    assert_eq!(p.content.as_deref(), Some("ok"));

    // A top-level key wins over the nested config object, even when the
    // nested one is the only valid one.
    let p = patch(r#"{"p":"dns","op":"config","name":"jon.doge","content":"top","config":{"content":"nested","url":"https://n.dog"}}"#);
    assert_eq!(p.content.as_deref(), Some("top"));
    assert_eq!(p.url.as_deref(), Some("https://n.dog"));

    // Clearing.
    let p = patch(r#"{"p":"dns","op":"config","name":"jon.doge","url":"","addresses":[],"txt":null}"#);
    assert_eq!(p.url.as_deref(), Some(""));
    assert_eq!(p.addresses, Some(vec![]));
    assert_eq!(p.txt, Some(TxtPatch::Clear));

    // Limits.
    let p = patch(&format!(r#"{{"p":"dns","op":"config","name":"jon.doge","content":"{}"}}"#, "x".repeat(281)));
    assert_eq!(p.content, None);
    let nine: Vec<String> = (0..9).map(|i| format!(r#""k{i}":"v""#)).collect();
    let p = patch(&format!(r#"{{"p":"dns","op":"config","name":"jon.doge","txt":{{{}}}}}"#, nine.join(",")));
    assert_eq!(p.txt, None);
    let p = patch(r#"{"p":"dns","op":"config","name":"jon.doge","txt":{"Bad_Key":"v"}}"#);
    assert_eq!(p.txt, None);

    // Applying: omitted keys stay, empty clears, txt merges per key.
    let mut r = DnsRecords::default();
    r.apply(&patch(r#"{"p":"dns","op":"config","name":"jon.doge","url":"https://a.dog","content":"hi","txt":{"a":"1","b":"2"}}"#));
    r.apply(&patch(r#"{"p":"dns","op":"config","name":"jon.doge","content":"","txt":{"a":"","c":"3"}}"#));
    assert_eq!(r.url.as_deref(), Some("https://a.dog"));
    assert_eq!(r.content, None);
    assert_eq!(r.txt, BTreeMap::from([("b".to_string(), "2".to_string()), ("c".to_string(), "3".to_string())]));
  }

  #[test]
  fn address_and_bech32_checks() {
    assert!(is_doge_address("DBckmbhKFCdFKC5LX8NtMUG5FPZvL5wLHR"));
    assert!(!is_doge_address("DBckmbhKFCdFKC5LX8NtMUG5FPZvL5wLHS"));
    assert!(is_doge_address("9ttt1BNvcqEtdWLdPUu7QRzUs7BaawYJnf"), "P2SH");
    // The spec's own example address has a bad checksum, so it is not one.
    assert!(!is_doge_address("D8mZsgKwmSQWYRPEMCcm8KzNFj1JVF5UpA"));
    // A Bitcoin address has the wrong version byte.
    assert!(!is_doge_address("1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa"));
    // BIP-173 test vector, and the same with one character changed.
    assert!(bech32_valid("a12uel5l", "a"));
    assert!(!bech32_valid("a12uel5m", "a"));
    assert!(!bech32_valid("A12uel5l", "a"), "mixed case");
  }

  #[test]
  fn envelope_redeem_script() {
    let mut s = vec![0x21];
    s.extend([2u8; 33]);
    s.extend([0xad, 0x75, 0x75, 0x75, 0x51]);
    assert!(is_envelope_redeem(&s));
    let mut multisig = vec![0x51, 0x21];
    multisig.extend([2u8; 33]);
    multisig.extend([0x51, 0xae]);
    assert!(!is_envelope_redeem(&multisig));
  }

  /// Against the real node: DNS_TRACE="id txid:vout:offset address" for an
  /// inscription that has moved. Checks the walk back ends at the reveal and
  /// at whoever the reveal paid.
  #[tokio::test]
  #[ignore]
  async fn tracer_follows_a_real_inscription_back() {
    let spec = std::env::var("DNS_TRACE").expect("DNS_TRACE");
    let parts: Vec<&str> = spec.split_whitespace().collect();
    let sp: Vec<&str> = parts[1].split(':').collect();
    let rec = InscriptionRecord {
      id: parts[0].to_string(),
      txid: sp[0].to_string(),
      vout: sp[1].parse().unwrap(),
      offset: sp[2].parse().unwrap(),
      satoshis: 0,
      content_type: String::new(),
      address: parts[2].to_string(),
      delegate: None,
    };
    let config = Config::from_env();
    let mut tr = Tracer::new(&config);
    let id_txid = rec.id.trim_end_matches("i0").to_string();
    let first = tr.position(&id_txid).await.unwrap();
    let (made_at, made_to) = tr.creation(&rec).await.unwrap();
    println!("made at {made_at:?} to {made_to}; first piece at {first:?}");
    // One transaction, or several when the content did not fit in one: then
    // it is made by the last, which comes later.
    assert!(made_at >= first);
    let hash = tr.tx(&id_txid).await.unwrap().blockhash.unwrap();
    let block_of_made = if made_at.0 == first.0 { hash } else {
      let client = indexer_rpc_client().unwrap();
      rpc_call::<String>(client, &config, "getblockhash", serde_json::json!([made_at.0])).await.unwrap()
    };
    if !tr.blocks.contains_key(&block_of_made) {
      let client = indexer_rpc_client().unwrap();
      let b: Value = rpc_call(client, &config, "getblock", serde_json::json!([block_of_made, 1])).await.unwrap();
      let txids = b["tx"].as_array().unwrap().iter().map(|t| t.as_str().unwrap().to_string()).collect();
      tr.blocks.insert(block_of_made.clone(), (made_at.0, txids));
    }
    let maker = tr.blocks[&block_of_made].1[made_at.1 as usize].clone();
    assert_eq!(made_to, tr.tx(&maker).await.unwrap().vout[0].1, "doginals reveals pay the inscription to output 0");
    let holders = tr.holders_since(&rec, made_at).await.unwrap().unwrap();
    println!("holders, newest first: {holders:?}");
    assert_eq!(holders.first().unwrap(), &rec.address);
    assert_eq!(holders.last().unwrap(), &made_to);
    assert!(holders.len() >= 2, "it has moved");
    assert_eq!(tr.holders_since(&rec, (made_at.0 - 1, 0)).await.unwrap(), None, "did not exist a block before");
    let now = tr.position(&rec.txid).await.unwrap();
    assert_eq!(tr.holders_since(&rec, now).await.unwrap().unwrap(), vec![rec.address.clone()]);
  }

  fn seed_seq(db: &store::Db, rows: &[(u64, u32, &str, &str, &str, &str)]) {
    // height, tx_index, id, address, content type, body
    let (seq, genesis, content, by_id, meta) = (
      db.open_tree("inscription_seq").unwrap(),
      db.open_tree("inscription_genesis").unwrap(),
      db.open_tree("inscription_content").unwrap(),
      db.open_tree("inscriptions_by_id").unwrap(),
      db.open_tree("meta").unwrap(),
    );
    let mut cursor = Vec::new();
    for (n, (h, i, id, addr, ct, body)) in rows.iter().enumerate() {
      let key = ii::seq_key(*h, *i);
      seq.insert(key, ii::seq_value(id, ii::kinds_of(ct, Some(body.as_bytes())), 1000 + n as u64).unwrap()).unwrap();
      let g = ii::Genesis { number: n as u64, height: *h, time: 1000 + n as u64, kinds: 0 };
      genesis.insert(id.as_bytes(), bincode::serialize(&g).unwrap()).unwrap();
      content
        .insert(id.as_bytes(), bincode::serialize(&InscriptionContentRecord { content_type: ct.to_string(), body: body.as_bytes().to_vec(), delegate: None }).unwrap())
        .unwrap();
      let txid = id.trim_end_matches("i0");
      let rec = InscriptionRecord { id: id.to_string(), txid: txid.to_string(), vout: 0, offset: 0, satoshis: 100_000, content_type: ct.to_string(), address: addr.to_string(), delegate: None };
      by_id.insert(id.as_bytes(), bincode::serialize(&rec).unwrap()).unwrap();
      cursor = key.to_vec();
    }
    #[derive(Serialize)]
    struct Numbering {
      cursor: Vec<u8>,
      next: u64,
      kind_next: Vec<u64>,
    }
    meta.insert(b"inscription_numbering_v1", bincode::serialize(&Numbering { cursor, next: rows.len() as u64, kind_next: vec![0; 15] }).unwrap()).unwrap();
    // The tip far enough past the last row for DNS to read it.
    let top = rows.iter().map(|r| r.0).max().unwrap_or(0);
    meta.insert(b"indexed_height", encode_u64(top + DNS_CONFIRMATIONS).to_vec()).unwrap();
  }

  fn txid(n: u8) -> String {
    format!("{n:02x}").repeat(32)
  }

  /// First come first served across blocks and within one, configs and
  /// primaries only from the holder, all through the real scan and apply.
  #[tokio::test]
  async fn index_applies_rules_in_chain_order() {
    let db = store::Db::temporary().unwrap();
    let id = |n: u8| format!("{}i0", txid(n));
    let (a, b) = ("DBckmbhKFCdFKC5LX8NtMUG5FPZvL5wLHR", "DH5yaieqoZN36fDVciNyRueRGvGLR3mr7L");
    let rows = [
      (100, 1, id(1), a, "text/plain", "jon.doge".to_string()),
      // Same block, later: a missed claim.
      (100, 2, id(2), b, "text/plain", "JON.doge".to_string()),
      (101, 0, id(3), b, "application/json", r#"{"p":"dns","op":"reg","name":"jon.doge"}"#.to_string()),
      // Not a name at all.
      (101, 1, id(4), b, "text/plain", "hello world".to_string()),
      (101, 2, id(5), b, "text/plain", r#"{"p":"drc-20","op":"mint","tick":"dogi","amt":"1"}"#.to_string()),
      // A config from the holder counts, from anyone else it does not.
      (102, 0, id(6), a, "application/json", r#"{"p":"dns","op":"config","name":"jon.doge","url":"https://a.dog"}"#.to_string()),
      (102, 1, id(7), b, "application/json", r#"{"p":"dns","op":"config","name":"jon.doge","url":"https://evil.dog"}"#.to_string()),
      (102, 2, id(8), a, "application/json", r#"{"p":"dns","op":"config","name":"nobody.doge","url":"https://a.dog"}"#.to_string()),
      (103, 0, id(9), a, "application/json", r#"{"p":"dns","op":"primary","name":"jon.doge"}"#.to_string()),
      (103, 1, id(10), b, "application/json", r#"{"p":"dns","op":"primary","name":"jon.doge"}"#.to_string()),
      (104, 0, id(11), b, "text/plain", "such.wow".to_string()),
    ];
    let refs: Vec<(u64, u32, &str, &str, &str, &str)> = rows.iter().map(|(h, i, id, ad, ct, b)| (*h, *i, id.as_str(), *ad, *ct, b.as_str())).collect();
    seed_seq(&db, &refs);

    let t = Trees::open(&db).unwrap();
    let config = Config::from_env();
    // Two small steps, so a name made in one is seen by the next.
    let mut st = dns_state(&t.meta).unwrap();
    for _ in 0..2 {
      let (c, last, scanned) = scan(&t, &st, 6).unwrap();
      st = apply(&config, &t, st, c, last.unwrap(), scanned, false, reorg_gen(&t.meta).unwrap()).await.unwrap();
    }
    assert!(scan(&t, &st, 6).unwrap().1.is_none(), "all read");

    assert_eq!((st.names, st.claims, st.configs, st.configs_ignored, st.primaries, st.primaries_ignored), (2, 2, 1, 2, 1, 1));
    let jon = get_name(&t.name, "jon.doge").unwrap().unwrap();
    assert_eq!((jon.inscription_id.as_str(), jon.lost, jon.index, jon.ns_index), (id(1).as_str(), 2, 0, 0));
    let wow = get_name(&t.name, "such.wow").unwrap().unwrap();
    assert_eq!((wow.index, wow.ns_index), (1, 0));
    let role = |n: u8| -> DnsRole { bincode::deserialize(t.by_inscription.get(id(n).as_bytes()).unwrap().unwrap().as_ref()).unwrap() };
    assert_eq!(role(2).role, "claim");
    assert!(role(6).counted);
    assert!(!role(7).counted && role(7).note.contains("holder"));
    assert!(!role(8).counted);
    assert!(role(9).counted && !role(10).counted);
    assert!(t.by_inscription.get(id(4).as_bytes()).unwrap().is_none());
    assert_eq!(get_u64(&t.stats, &ns_count_key("doge")).unwrap(), 1);
    assert_eq!(get_u64(&t.stats, &supply_key("doge", 3, 'l')).unwrap(), 1);
    assert_eq!(get_u64(&t.stats, &supply_key("wow", 4, 'l')).unwrap(), 1, "such.wow: label such, namespace wow");
    assert_eq!(get_u64(&t.stats, &supply_key("such", 3, 'l')).unwrap(), 0);
    let p: PrimaryEntry = bincode::deserialize(t.primary.get(a.as_bytes()).unwrap().unwrap().as_ref()).unwrap();
    assert_eq!(p.name.as_deref(), Some("jon.doge"));
    assert!(t.primary.get(b.as_bytes()).unwrap().is_none());
  }

  /// .dogecoin, .doginals, .dogefeed, .pup and .shib names register in both
  /// forms, count under their own namespace, and are listed even at zero.
  #[tokio::test]
  async fn featured_namespaces_index_in_both_forms() {
    for ns in FEATURED_NAMESPACES {
      let n = normalize_name(&format!("such.{ns}")).unwrap();
      assert_eq!((n.label.as_str(), n.namespace.as_str(), n.confusable), ("such", ns, false));
      assert_eq!(reg(&format!("wow.{ns}\n")).as_deref(), Some(format!("wow.{ns}").as_str()));
      let json = format!(r#"{{"p":"dns","op":"reg","name":"much.{ns}"}}"#);
      assert!(matches!(parse_dns_op("application/json", json.as_bytes()), Some(DnsOp::Register { .. })), "{ns}");
    }
    // Close but different namespaces stay their own.
    assert_eq!(normalize_name("a.pups").unwrap().namespace, "pups");
    assert_eq!(normalize_name("a.shiba").unwrap().namespace, "shiba");
    assert_eq!(normalize_name("A.DogeFeed").unwrap().name, "a.dogefeed");

    let db = store::Db::temporary().unwrap();
    let t = Trees::open(&db).unwrap();
    assert_eq!(featured_counts(&t.stats).unwrap().iter().map(|(n, c)| (n.as_str(), *c)).collect::<Vec<_>>(),
      FEATURED_NAMESPACES.iter().map(|n| (*n, 0)).collect::<Vec<_>>(), "listed before any name");

    let id = |n: u8| format!("{}i0", txid(n));
    let a = "DBckmbhKFCdFKC5LX8NtMUG5FPZvL5wLHR";
    let mut rows = Vec::new();
    let mut k = 0u8;
    for (i, ns) in ["dogecoin", "doginals", "dogefeed", "pup", "shib"].iter().enumerate() {
      let h = 200 + i as u64;
      k += 1;
      rows.push((h, 0, id(k), "text/plain", format!("jon.{ns}")));
      k += 1;
      rows.push((h, 1, id(k), "application/json", format!(r#"{{"p":"dns","op":"reg","name":"bob.{ns}"}}"#)));
      // A second register of the text name: a missed claim.
      k += 1;
      rows.push((h, 2, id(k), "application/json", format!(r#"{{"p":"dns","op":"reg","name":"JON.{ns}"}}"#)));
    }
    let refs: Vec<(u64, u32, &str, &str, &str, &str)> =
      rows.iter().map(|(h, i, id, ct, b)| (*h, *i, id.as_str(), a, *ct, b.as_str())).collect();
    seed_seq(&db, &refs);

    let config = Config::from_env();
    let mut st = dns_state(&t.meta).unwrap();
    while let (c, Some(last), scanned) = scan(&t, &st, 4).unwrap() {
      st = apply(&config, &t, st, c, last, scanned, false, reorg_gen(&t.meta).unwrap()).await.unwrap();
    }
    assert_eq!((st.names, st.claims), (10, 5));
    for ns in ["dogecoin", "doginals", "dogefeed", "pup", "shib"] {
      for label in ["jon", "bob"] {
        let e = get_name(&t.name, &format!("{label}.{ns}")).unwrap().unwrap_or_else(|| panic!("{label}.{ns}"));
        assert_eq!(e.namespace, ns);
      }
      assert_eq!(get_name(&t.name, &format!("jon.{ns}")).unwrap().unwrap().lost, 1, "{ns}");
      assert_eq!(get_u64(&t.stats, &supply_key(ns, 3, 'l')).unwrap(), 2, "{ns}");
    }
    assert_eq!(featured_counts(&t.stats).unwrap().iter().map(|(n, c)| (n.as_str(), *c)).collect::<Vec<_>>(),
      vec![("doge", 0), ("dogecoin", 2), ("doginals", 2), ("dogefeed", 2), ("pup", 2), ("shib", 2)]);
  }

  #[tokio::test]
  async fn a_reorg_undoes_the_names_of_the_blocks_it_removes() {
    let db = store::Db::temporary().unwrap();
    let t = Trees::open(&db).unwrap();
    let config = Config::from_env();
    let id = |n: u8| format!("{}i0", txid(n));
    let (a, b) = ("DBckmbhKFCdFKC5LX8NtMUG5FPZvL5wLHR", "DH5yaieqoZN36fDVciNyRueRGvGLR3mr7L");
    let step = |st: DnsState| {
      let t = &t;
      let config = &config;
      async move {
        let (c, last, scanned) = scan(t, &st, 100).unwrap();
        apply(config, t, st, c, last.expect("rows to read"), scanned, false, reorg_gen(&t.meta).unwrap()).await.unwrap()
      }
    };

    // Block 100 makes jon.doge; block 101, the tip, makes amy.doge and a late jon.doge.
    let (r1, r2, r3) = (id(1), id(2), id(3));
    seed_seq(&db, &[(100, 0, &r1, a, "text/plain", "jon.doge")]);
    let st = step(dns_state(&t.meta).unwrap()).await;
    seed_seq(&db, &[(100, 0, &r1, a, "text/plain", "jon.doge"), (101, 0, &r2, b, "text/plain", "amy.doge"), (101, 1, &r3, b, "text/plain", "jon.doge")]);
    t.meta.insert(b"indexed_height", encode_u64(101).to_vec()).unwrap();
    let st = step(st).await;
    assert_eq!((st.names, st.claims, st.cursor_height), (2, 1, 101), "read at 1 confirmation");
    assert_eq!(get_name(&t.name, "jon.doge").unwrap().unwrap().lost, 1);

    // Block 101 is replaced: its rows go, then the rollback undoes DNS.
    t.seq.remove(ii::seq_key(101, 0)).unwrap();
    t.seq.remove(ii::seq_key(101, 1)).unwrap();
    let era = reorg_gen(&t.meta).unwrap();
    undo_from(&db, 101).unwrap();
    assert_eq!(reorg_gen(&t.meta).unwrap(), era + 1);
    let st = dns_state(&t.meta).unwrap();
    assert_eq!((st.names, st.claims, st.cursor_height), (1, 0, 100));
    assert!(get_name(&t.name, "amy.doge").unwrap().is_none());
    assert_eq!(get_name(&t.name, "jon.doge").unwrap().unwrap().lost, 0, "the late claim is gone too");
    assert!(t.by_inscription.get(r2.as_bytes()).unwrap().is_none() && t.by_inscription.get(r1.as_bytes()).unwrap().is_some());
    assert_eq!(featured_counts(&t.stats).unwrap()[0], ("doge".to_string(), 1));

    // A step read before the reorg is refused, not committed.
    let stale = apply(&config, &t, st.clone(), Vec::new(), ii::seq_key(101, 9).to_vec(), 0, false, era).await;
    assert!(stale.unwrap_err().to_string().contains(REORGED));

    // The new block 101 gives amy.doge to someone else.
    let r4 = id(4);
    seed_seq(&db, &[(100, 0, &r1, a, "text/plain", "jon.doge"), (101, 2, &r4, a, "text/plain", "amy.doge")]);
    t.meta.insert(b"indexed_height", encode_u64(101).to_vec()).unwrap();
    let st = step(st).await;
    assert_eq!((st.names, st.claims), (2, 0));
    assert_eq!(get_name(&t.name, "amy.doge").unwrap().unwrap().inscription_id, r4);

    // Undoing everything goes back to an empty index.
    undo_from(&db, 100).unwrap();
    let st = dns_state(&t.meta).unwrap();
    assert!(st.cursor.is_empty() && st.names == 0);
    assert!(get_name(&t.name, "jon.doge").unwrap().is_none());
  }
}
