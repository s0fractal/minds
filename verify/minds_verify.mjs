// VARS-1 offline bundle verifier (VARS-1-SPEC.md §4.4), a second implementation: one ES module, no dependencies.
//
// The same checks as verify/minds_verify.py, written again for a reader who has a browser or Node and not Python:
// verify-projection, verify-attestation, inspect-*, verify-equivocation and verify-extends, with the same verdicts,
// exit codes, `explain` fields and refusal text. SHA-256 and Ed25519 are the host's WebCrypto, not code of this file.
// It is held to the Python file by verify/vectors.json: every bundle, mutation and command line the offline tests
// give the Python file, with the bytes it answered; verify/check_vectors.mjs requires the same bytes here, and a
// difference is a finding, never "nearly". Under Node it is also a command line:
//
//     node minds_verify.mjs verify-projection BUNDLE.json --require PUBKEY [--kernel RULES.wasm]...
//
// With --kernel (or `kernels` in the calls below) the projection's rules module runs here under the host's own
// WebAssembly, with no imports, so its output is checked here rather than taken on its witnesses' word.
// What it does not do, as the Python file does not: Pass 3 with a computation's replay (a decision with
// `required_comp` needs the repository).

const subtle = globalThis.crypto.subtle;
const ENC = new TextEncoder();

// ---------------------------------------------------------------------------------------------------------------
// Errors: a VarsError is a refusal of the protocol; PyError carries the refusals the Python file makes through its
// interpreter (KeyError, ValueError, TypeError) with the same words, so a refusal reads the same in both.
// ---------------------------------------------------------------------------------------------------------------
export class VarsError extends Error {
  constructor(message) { super(message); this.name = "VarsError"; }
}

class PyError extends Error {
  constructor(kind, message) { super(message); this.name = kind; }
}

const keyError = (key) => new PyError("KeyError", `'${key}'`);

function pyTypeName(v) {
  if (v === null || v === undefined) return "NoneType";
  if (typeof v === "boolean") return "bool";
  if (typeof v === "number") return "int";  // the reader keeps a float as PyFloat
  if (v instanceof PyFloat) return "float";
  if (typeof v === "bigint") return "int";
  if (typeof v === "string") return "str";
  if (Array.isArray(v)) return "list";
  return "dict";
}

// A JSON number with a fraction or an exponent, as Python's json reads it: a float, even when it is integral.
class PyFloat {
  constructor(value) { this.value = value; }
}

const isDict = (v) => v !== null && typeof v === "object" && !Array.isArray(v) && !(v instanceof PyFloat);
const has = (d, k) => Object.prototype.hasOwnProperty.call(d, k);

function getItem(d, k) {
  if (!has(d, k)) throw keyError(k);
  return d[k];
}

// What Python's `for x in v` reads: a list's items, a string's characters, a dict's keys.
function pyIter(v) {
  if (Array.isArray(v)) return v;
  if (typeof v === "string") return Array.from(v);
  if (isDict(v)) return Object.keys(v);
  throw new PyError("TypeError", `'${pyTypeName(v)}' object is not iterable`);
}

// ---------------------------------------------------------------------------------------------------------------
// Bytes
// ---------------------------------------------------------------------------------------------------------------
const HEX = "0123456789abcdef";

export function toHex(b) {
  let s = "";
  for (const x of b) s += HEX[x >> 4] + HEX[x & 15];
  return s;
}

// Python's bytes.fromhex: ASCII whitespace between pairs is skipped, either case is read, and its errors are its own.
export function fromhex(s) {
  if (typeof s !== "string") throw new PyError("TypeError", `fromhex() argument must be str or bytes-like, not ${pyTypeName(s)}`);
  const cps = Array.from(s);
  const firstWide = cps.findIndex((c) => c.codePointAt(0) >= 128);
  if (firstWide >= 0) throw new PyError("ValueError", `non-hexadecimal number found in fromhex() arg at position ${firstWide}`);
  const space = (c) => c === " " || c === "\t" || c === "\n" || c === "\r" || c === "\x0b" || c === "\x0c";
  const digit = (c) => { const v = "0123456789abcdefABCDEF".indexOf(c); return v < 0 || c === undefined ? 99 : v < 16 ? v : v - 6; };
  const out = [];
  let i = 0;
  while (i < s.length) {
    if (space(s[i])) {
      while (i < s.length && space(s[i])) i++;
      if (i >= s.length) break;
    }
    const top = digit(s[i]);
    if (top >= 16) throw new PyError("ValueError", `non-hexadecimal number found in fromhex() arg at position ${i}`);
    i++;
    if (i >= s.length) throw new PyError("ValueError", "fromhex() arg must contain an even number of hexadecimal digits");
    const bot = digit(s[i]);
    if (bot >= 16) throw new PyError("ValueError", `non-hexadecimal number found in fromhex() arg at position ${i}`);
    i++;
    out.push(top * 16 + bot);
  }
  return Uint8Array.from(out);
}

const eq = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);

function concat(...parts) {
  const out = new Uint8Array(parts.reduce((n, p) => n + p.length, 0));
  let o = 0;
  for (const p of parts) { out.set(p, o); o += p.length; }
  return out;
}

const ascii = (s) => ENC.encode(s);
const startsWith = (raw, s) => raw.length >= s.length && [...s].every((c, i) => raw[i] === c.charCodeAt(0));

export async function sha256(data) {
  return new Uint8Array(await subtle.digest("SHA-256", data));
}

// Python's str order: by code point (JavaScript's own sort is by UTF-16 unit).
function cpCompare(a, b) {
  const x = Array.from(a), y = Array.from(b);
  for (let i = 0; i < Math.min(x.length, y.length); i++) {
    const d = x[i].codePointAt(0) - y[i].codePointAt(0);
    if (d) return d;
  }
  return x.length - y.length;
}

const sortedStr = (xs) => [...xs].sort(cpCompare);
const byKeys = (...fs) => (a, b) => { for (const f of fs) { const d = cpCompare(f(a), f(b)); if (d) return d; } return 0; };

// Python's UTF-8 decoder (errors="strict"), with its words for the first error.
export function decodeUtf8(b) {
  const fail = (start, end, why) => {
    const at = end - start === 1 ? `byte 0x${toHex([b[start]])} in position ${start}` : `bytes in position ${start}-${end - 1}`;
    throw new PyError("ValueError", `'utf-8' codec can't decode ${at}: ${why}`);
  };
  for (let i = 0; i < b.length;) {
    const c = b[i];
    if (c < 0x80) { i++; continue; }
    const n = c >= 0xc2 && c <= 0xdf ? 1 : c >= 0xe0 && c <= 0xef ? 2 : c >= 0xf0 && c <= 0xf4 ? 3 : 0;
    if (!n) fail(i, i + 1, "invalid start byte");
    for (let j = 1; j <= n; j++) {
      if (i + j >= b.length) fail(i, b.length, "unexpected end of data");
      const x = b[i + j];
      let lo = 0x80, hi = 0xbf;
      if (j === 1) {
        if (c === 0xe0) lo = 0xa0;
        else if (c === 0xed) hi = 0x9f;
        else if (c === 0xf0) lo = 0x90;
        else if (c === 0xf4) hi = 0x8f;
      }
      if (x < lo || x > hi) fail(i, i + j, "invalid continuation byte");
    }
    i += n + 1;
  }
  // ignoreBOM: a leading U+FEFF is kept, so the JSON reader refuses it as Python's does; TextDecoder's default drops
  // it silently, and a BOM-prefixed bundle would read here and be refused there
  return new TextDecoder("utf-8", { fatal: true, ignoreBOM: true }).decode(b);
}

// ---------------------------------------------------------------------------------------------------------------
// JSON as Python's json reads and writes it
// ---------------------------------------------------------------------------------------------------------------
// json.loads: the same grammar and the same error words and positions (in code points) as CPython's scanner. With
// `oneReading`, an object that names a key twice and NaN, Infinity and -Infinity are refused, as read_bundle does.
export function pyLoads(s, { oneReading = false } = {}) {
  const pos = (i) => Array.from(s.slice(0, i)).length;
  const err = (msg, i) => {
    const p = pos(i);
    const before = Array.from(s.slice(0, i));
    const line = before.filter((c) => c === "\n").length + 1;
    const lastNl = before.lastIndexOf("\n");
    const col = p - lastNl;
    return new PyError("ValueError", `${msg}: line ${line} column ${col} (char ${p})`);
  };
  if (s.startsWith("﻿")) throw err("Unexpected UTF-8 BOM (decode using utf-8-sig)", 0);
  const ws = (i) => { while (i < s.length && " \t\n\r".includes(s[i])) i++; return i; };
  const constant = (name) => {
    if (oneReading) throw new VarsError(`${name} is not JSON`);
    return new PyFloat(name === "NaN" ? NaN : name === "Infinity" ? Infinity : -Infinity);
  };

  function scanString(i) { // i: just after the opening quote
    const begin = i - 1;
    let out = "";
    for (;;) {
      if (i >= s.length) throw err("Unterminated string starting at", begin);
      const c = s[i];
      if (c === '"') return [out, i + 1];
      if (c === "\\") {
        i++;
        if (i >= s.length) throw err("Unterminated string starting at", begin);
        const e = s[i];
        if (e !== "u") {
          const m = { '"': '"', "\\": "\\", "/": "/", b: "\b", f: "\f", n: "\n", r: "\r", t: "\t" }[e];
          if (m === undefined) throw err("Invalid \\escape", i - 1);
          out += m;
          i++;
          continue;
        }
        const hex4 = (at) => {
          const h = s.slice(at + 1, at + 5);
          if (h.length < 4 || !/^[0-9a-fA-F]{4}$/.test(h)) throw err("Invalid \\uXXXX escape", at);
          return parseInt(h, 16);
        };
        let u = hex4(i);
        i += 5;
        if (u >= 0xd800 && u <= 0xdbff && s[i] === "\\" && s[i + 1] === "u") {
          const u2 = hex4(i + 1);
          if (u2 >= 0xdc00 && u2 <= 0xdfff) {
            out += String.fromCharCode(u, u2);
            i += 6;
            continue;
          }
        }
        out += String.fromCharCode(u);
        continue;
      }
      if (c < " ") throw err("Invalid control character at", i);
      out += c;
      i++;
    }
  }

  function scanOnce(i) {
    const c = s[i];
    if (c === '"') return scanString(i + 1);
    if (c === "{") return scanObject(i + 1);
    if (c === "[") return scanArray(i + 1);
    if (c === "n" && s.startsWith("null", i)) return [null, i + 4];
    if (c === "t" && s.startsWith("true", i)) return [true, i + 4];
    if (c === "f" && s.startsWith("false", i)) return [false, i + 5];
    const m = /^(-?(?:0|[1-9][0-9]*))(\.[0-9]+)?([eE][-+]?[0-9]+)?/.exec(s.slice(i));
    if (m && m[0] && m[1] !== "-") {
      if (m[2] || m[3]) return [new PyFloat(Number(m[0])), i + m[0].length];
      const n = BigInt(m[1]);
      return [n >= BigInt(Number.MIN_SAFE_INTEGER) && n <= BigInt(Number.MAX_SAFE_INTEGER) ? Number(n) : n, i + m[0].length];
    }
    if (c === "N" && s.startsWith("NaN", i)) return [constant("NaN"), i + 3];
    if (c === "I" && s.startsWith("Infinity", i)) return [constant("Infinity"), i + 8];
    if (c === "-" && s.startsWith("-Infinity", i)) return [constant("-Infinity"), i + 9];
    throw err("Expecting value", i);
  }

  function value(i) {
    if (i >= s.length) throw err("Expecting value", i);
    return scanOnce(i);
  }

  function scanObject(i) {
    const pairs = [];
    i = ws(i);
    if (s[i] === "}") return [finish(pairs), i + 1];
    if (s[i] !== '"') throw err("Expecting property name enclosed in double quotes", i);
    for (;;) {
      let key;
      [key, i] = scanString(i + 1);
      i = ws(i);
      if (s[i] !== ":") throw err("Expecting ':' delimiter", i);
      i = ws(i + 1);
      let v;
      [v, i] = value(i);
      pairs.push([key, v]);
      i = ws(i);
      if (s[i] === "}") return [finish(pairs), i + 1];
      if (s[i] !== ",") throw err("Expecting ',' delimiter", i);
      const comma = i;
      i = ws(i + 1);
      if (s[i] === "}") throw err("Illegal trailing comma before end of object", comma);
      if (s[i] !== '"') throw err("Expecting property name enclosed in double quotes", i);
    }
  }

  function finish(pairs) {
    if (oneReading && new Set(pairs.map(([k]) => k)).size !== pairs.length) {
      throw new VarsError("an object of the bundle names a key twice");
    }
    const d = Object.create(null);
    for (const [k, v] of pairs) d[k] = v;  // the last value, as Python keeps it
    return d;
  }

  function scanArray(i) {
    const out = [];
    i = ws(i);
    if (s[i] === "]") return [out, i + 1];
    for (;;) {
      let v;
      [v, i] = value(i);
      out.push(v);
      i = ws(i);
      if (s[i] === "]") return [out, i + 1];
      if (s[i] !== ",") throw err("Expecting ',' delimiter", i);
      const comma = i;
      i = ws(i + 1);
      if (s[i] === "]") throw err("Illegal trailing comma before end of array", comma);
    }
  }

  let [v, end] = value(ws(0));
  end = ws(end);
  if (end !== s.length) throw err("Extra data", end);
  return v;
}

function pyStr(s) {
  let out = '"';
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    const ch = s[i];
    if (ch === '"') out += '\\"';
    else if (ch === "\\") out += "\\\\";
    else if (ch === "\n") out += "\\n";
    else if (ch === "\r") out += "\\r";
    else if (ch === "\t") out += "\\t";
    else if (ch === "\b") out += "\\b";
    else if (ch === "\f") out += "\\f";
    else if (c >= 0x20 && c <= 0x7e) out += ch;
    else out += "\\u" + c.toString(16).padStart(4, "0");
  }
  return out + '"';
}

// Python's repr of a float, which json.dumps writes.
function pyFloatRepr(x) {
  if (Number.isNaN(x)) return "NaN";
  if (x === Infinity) return "Infinity";
  if (x === -Infinity) return "-Infinity";
  if (x === 0) return Object.is(x, -0) ? "-0.0" : "0.0";
  const [mant, expS] = Math.abs(x).toExponential().split("e");
  const digits = mant.replace(".", "");
  const e = Number(expS);
  const sign = x < 0 ? "-" : "";
  if (e < -4 || e >= 16) {
    const m = digits.length > 1 ? digits[0] + "." + digits.slice(1) : digits;
    return `${sign}${m}e${e < 0 ? "-" : "+"}${String(Math.abs(e)).padStart(2, "0")}`;
  }
  if (e >= 0) {
    const int = digits.slice(0, e + 1).padEnd(e + 1, "0");
    const frac = digits.slice(e + 1);
    return `${sign}${int}.${frac || "0"}`;
  }
  return `${sign}0.${"0".repeat(-e - 1)}${digits}`;
}

// json.dumps(v, sort_keys=True) with ensure_ascii: `indent` 2 as the command line prints, or the compact separators
// of a canonical JSON atom.
export function pyDumps(v, { indent = null } = {}) {
  const go = (x, level) => {
    if (x === null || x === undefined) return "null";
    if (x === true) return "true";
    if (x === false) return "false";
    if (x instanceof PyFloat) return pyFloatRepr(x.value);
    if (typeof x === "number" || typeof x === "bigint") return String(x);
    if (typeof x === "string") return pyStr(x);
    const pad = indent === null ? "" : "\n" + " ".repeat(indent * (level + 1));
    const end = indent === null ? "" : "\n" + " ".repeat(indent * level);
    const sep = indent === null ? "," : ",";
    const colon = indent === null ? ":" : ": ";
    if (Array.isArray(x)) {
      if (!x.length) return "[]";
      return "[" + x.map((y) => pad + go(y, level + 1)).join(sep) + end + "]";
    }
    const keys = sortedStr(Object.keys(x));
    if (!keys.length) return "{}";
    return "{" + keys.map((k) => pad + pyStr(k) + colon + go(x[k], level + 1)).join(sep) + end + "}";
  };
  return go(v, 0);
}

// ---------------------------------------------------------------------------------------------------------------
// Ed25519 (the host's WebCrypto) behind the filters the Python file applies first
// ---------------------------------------------------------------------------------------------------------------
const WEAK_PUBKEYS = new Set([
  "0100000000000000000000000000000000000000000000000000000000000000",
  "c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a",
  "0000000000000000000000000000000000000000000000000000000000000080",
  "26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05",
  "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
  "26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc85",
  "0000000000000000000000000000000000000000000000000000000000000000",
  "c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac03fa",
  "0100000000000000000000000000000000000000000000000000000000000080",
  "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
]);
const Q = (1n << 255n) - 19n;
const L = (1n << 252n) + 27742317777372353535851937790883648493n;
const littleEndian = (b) => b.reduceRight((n, x) => (n << 8n) | BigInt(x), 0n);

// True iff `raw` is not a 32-byte strong canonical Ed25519 public key (`warrant/keys.py:32-35`).
export function weakPublicKey(raw) {
  if (!(raw instanceof Uint8Array) || raw.length !== 32 || WEAK_PUBKEYS.has(toHex(raw))) return true;
  return (littleEndian(raw) & ((1n << 255n) - 1n)) >= Q;
}

export async function ed25519Verify(pk, msg, sig) {
  if (weakPublicKey(pk) || sig.length !== 64 || weakPublicKey(sig.subarray(0, 32))) return false;
  if (littleEndian(sig.subarray(32)) >= L) return false;
  try {
    const key = await subtle.importKey("raw", pk, { name: "Ed25519" }, false, ["verify"]);
    return await subtle.verify({ name: "Ed25519" }, key, sig, msg);
  } catch {
    return false;  // a key that is not a point, as the Python file's decoder refuses it
  }
}

// ---------------------------------------------------------------------------------------------------------------
// §1 Constants
// ---------------------------------------------------------------------------------------------------------------
const MAX_INT = 2n ** 53n - 1n;
const MAX_UTF8_BYTES = 64 * 1024;
const MAX_HVEC_LEN = 65535;
const MAX_KIN1_BYTES = 1 << 20;
const WASM_MAGIC = Uint8Array.from([0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00]);

const H_EMPTY = await sha256(ascii("HVEC"));
const H_META_SCHEMA = await sha256(ascii("VARS-META-SCHEMA-V1"));
const H_REPLAYED = await sha256(ascii("UTF8REPLAYED"));
const H_ATTESTED = await sha256(ascii("UTF8ATTESTED"));
const H_VERDICT_INVALID = await sha256(ascii("UTF8INVALID"));

// The rules identities this verifier interprets, one row per line: id, encoding, name (minds_verify.py's table).
export const KNOWN_RULES_TABLE = `
874e714dd14e6d7c144a4c377ae649f4124ea3788b17fa1ff86cf1be8a168ecb v1 H_LENS_KERNEL
2a2e440a548b73adbb3072c23e21ee8d9d7bd7867fa7bc3e38150c477f1b11cd v1 H_LENS_KERNEL_V1B
1ca798b5013bf45735d3de836ecff23ca148e5bac2f6ca2c7d6289c2cf26707e v2 H_LENS_KERNEL_V2
`;
const KNOWN_RULES = new Map(KNOWN_RULES_TABLE.trim().split("\n").map((row) => row.split(" ")).map(([h, e]) => [h, e]));
const KERNEL2_MAGIC = 0x32524156;

const SCHEMA_SPECS = {
  axiom: [],
  contract: ["tier:utf8", "required_comp:root", "expected_outcome:hash", "evaluator_policy:pol1"],
  computation: [],
  checkpoint: ["computation_id:root", "credit_total:u64", "spent_total:u64", "peak_size:u64", "kernel_outcome:utf8", "actions:u64"],
  cycle_witness: ["computation_id:root", "entry_spent:u64", "cycle_actions:u64", "cycle_cost:u64"],
  decision: ["tier:utf8", "required_comp:root", "expected_outcome:hash", "evaluator_policy:pol1"],
  question: ["expected_schema:cell", "evaluator_policy:pol1"],
  acceptance: ["source_scope:utf8", "foreign_scope_cell:cell"],
  scope: ["admission_policy:pol1", "acceptance_policy:pol1", "rules:wasm"],
  verdict: ["ckpt_or_witness:cell", "verdict_code:utf8", "verifier_id:utf8"],
  projection: ["tip:utf8", "rules:wasm", "input:digest", "state:digest", "witness_policy:pol1"],
};

const H_SCHEMA = {};
for (const [name, fields] of Object.entries(SCHEMA_SPECS)) {
  const slots = await Promise.all(fields.map((f) => sha256(ascii("UTF8" + f))));
  const k = slots.length;
  const raw = concat(ascii("VAR1\0\0\0"), Uint8Array.of(k), H_META_SCHEMA, await sha256(ascii(`UTF8core/schema.${name}`)),
                     H_EMPTY, H_EMPTY, H_EMPTY, H_EMPTY, H_EMPTY, H_EMPTY, H_EMPTY, ...slots);
  H_SCHEMA[name] = toHex(await sha256(raw));
}
const STANDARD_ARITY = new Map(Object.entries(SCHEMA_SPECS).map(([n, f]) => [H_SCHEMA[n], f.length]));
const KERNEL_BITS = ["accepted", "invalidated", "effective", "retired", "superseded", "active", "stale"];
const hx = (b) => toHex(b);
const EMPTY = hx(H_EMPTY), META = hx(H_META_SCHEMA), ATTESTED = hx(H_ATTESTED), INVALID = hx(H_VERDICT_INVALID),
  REPLAYED = hx(H_REPLAYED);

// ---------------------------------------------------------------------------------------------------------------
// §1.1 Atoms
// ---------------------------------------------------------------------------------------------------------------
function parseU64(raw) {
  if (raw.length !== 12 || !startsWith(raw, "U64\0")) throw new VarsError("invalid U64 atom");
  let v = 0n;
  for (const x of raw.subarray(4)) v = (v << 8n) | BigInt(x);
  if (v > MAX_INT) throw new VarsError(`U64 exceeds 2^53-1: ${v}`);
  return v;
}

function validateUtf8Atom(raw) {
  if (raw.length < 4 || !startsWith(raw, "UTF8")) throw new VarsError("missing UTF8 magic");
  const body = raw.subarray(4);
  if (body.length > MAX_UTF8_BYTES) throw new VarsError("UTF8 atom exceeds 64 KiB");
  if (body.includes(0) || body.includes(13)) throw new VarsError("UTF8 atom contains NUL or CR byte");
  const wsb = (x) => x === 0x20 || x === 0x09 || x === 0x0a;
  if (body.length && (wsb(body[0]) || wsb(body[body.length - 1]))) {
    throw new VarsError("UTF8 atom has leading or trailing ASCII whitespace");
  }
  try {
    decodeUtf8(body);
  } catch (e) {
    throw new VarsError(`invalid UTF-8: ${e.message}`);
  }
}

function parseUtf8(raw) {
  validateUtf8Atom(raw);
  return decodeUtf8(raw.subarray(4));
}

function parseHvec(raw, requireSorted = true) {
  if (raw.length < 4 || !startsWith(raw, "HVEC") || (raw.length - 4) % 32 !== 0) throw new VarsError("invalid HVEC atom layout");
  const n = (raw.length - 4) / 32;
  if (n > MAX_HVEC_LEN) throw new VarsError("HVEC exceeds 65535 elements");
  const items = [];
  for (let i = 0; i < n; i++) items.push(hx(raw.subarray(4 + 32 * i, 4 + 32 * (i + 1))));
  if (requireSorted) {
    for (let i = 0; i + 1 < items.length; i++) {
      if (items[i] >= items[i + 1]) throw new VarsError("HVEC elements are not strictly ascending");
    }
  }
  return items;
}

function parsePol1(raw) {
  if (raw.length !== 38 || !startsWith(raw, "POL1")) throw new VarsError("invalid POL1 atom");
  const threshold = (raw[4] << 8) | raw[5];
  if (threshold < 1) throw new VarsError("POL1 threshold must be >= 1");
  return [threshold, hx(raw.subarray(6, 38))];
}

const hex64 = (v) => typeof v === "string" && /^[0-9a-f]{64}$/.test(v);

function validateAtom(raw) {
  if (!raw.length) throw new VarsError("empty atom");
  if (startsWith(raw, "UTF8")) validateUtf8Atom(raw);
  else if (startsWith(raw, "U64\0")) parseU64(raw);
  else if (startsWith(raw, "HVEC")) parseHvec(raw, false);
  else if (startsWith(raw, "POL1")) parsePol1(raw);
  else if (startsWith(raw, "SGS1") || (!eq(raw.subarray(0, 8), WASM_MAGIC) && [0x00, 0x01, 0x02, 0xff].includes(raw[0]))) {
    throw new VarsError("an SGS1 state or SigmaNodeV2 node needs Book I to check: not checkable offline");
  } else if (raw[0] === 0x7b) {
    let doc;
    try {
      doc = pyLoads(decodeUtf8(raw));
    } catch (e) {
      throw new VarsError(`invalid JSON atom: ${e.message}`);
    }
    if (!eq(ENC.encode(pyDumps(doc)), raw)) throw new VarsError("non-canonical JSON atom");
    const schema = isDict(doc) && has(doc, "schema") ? doc.schema : undefined;
    const keysAre = (ks) => Object.keys(doc).length === ks.length && ks.every((k) => has(doc, k));
    if (schema === "sigma-resume.root@draft-1") {
      if (!keysAre(["schema", "runtime_semantics_id", "cost_model_id", "input_term_hash", "environment_id"])
          || !["runtime_semantics_id", "cost_model_id"].every((k) => typeof doc[k] === "string" && doc[k])
          || !hex64(doc.input_term_hash) || !hex64(doc.environment_id)) {
        throw new VarsError("ComputationRoot must have exactly its five fields, well typed");
      }
    } else if (schema === "sigma-resume.environment@draft-1") {
      const hs = doc.hashes;
      if (!keysAre(["schema", "hashes"]) || !Array.isArray(hs) || !hs.every(hex64)
          || hs.join() !== [...new Set(hs)].sort(cpCompare).join() || hs.length > MAX_HVEC_LEN) {
        throw new VarsError("Environment must be its schema and a sorted, distinct list of hashes");
      }
    } else {
      throw new VarsError("unknown JSON atom schema");
    }
  } else if (startsWith(raw, "KIN1")) {
    if (raw.length - 4 > MAX_KIN1_BYTES) throw new VarsError("KIN1 rules input over 1 MiB");
  } else if (eq(raw.subarray(0, 8), WASM_MAGIC)) {
    // a wasm module: identity is its hash
  } else {
    throw new VarsError(`unrecognized atom prefix: ${pyBytesRepr(raw.subarray(0, 4))}`);
  }
}

// Python's repr of a bytes value.
function pyBytesRepr(b) {
  const hasSingle = b.includes(0x27), hasDouble = b.includes(0x22);
  const q = hasSingle && !hasDouble ? '"' : "'";
  let out = "b" + q;
  for (const x of b) {
    if (x === 0x5c) out += "\\\\";
    else if (x === q.charCodeAt(0)) out += "\\" + q;
    else if (x === 0x09) out += "\\t";
    else if (x === 0x0a) out += "\\n";
    else if (x === 0x0d) out += "\\r";
    else if (x >= 0x20 && x < 0x7f) out += String.fromCharCode(x);
    else out += "\\x" + toHex([x]);
  }
  return out + q;
}

// ---------------------------------------------------------------------------------------------------------------
// §1.2 Cells and §1.3 seals
// ---------------------------------------------------------------------------------------------------------------
const CELL_FIELDS = ["h_schema", "h_slot_name", "h_payload", "h_relies", "h_attests", "h_supersedes", "h_retires",
  "h_invalidates", "h_loss"];

async function decodeCell(raw) {
  if (raw.length < 296 || !startsWith(raw, "VAR1")) throw new VarsError("missing VAR1 magic or short cell");
  if (raw[4] || raw[5] || raw[6]) throw new VarsError("VAR1 reserved header bytes must be 0x000000");
  const k = raw[7];
  if (k > 64 || raw.length !== 296 + 32 * k) throw new VarsError("invalid VAR1 arity or byte length");
  const words = [];
  for (let i = 0; i < 9 + k; i++) words.push(hx(raw.subarray(8 + 32 * i, 8 + 32 * (i + 1))));
  const cell = { slots: words.slice(9) };
  CELL_FIELDS.forEach((f, i) => { cell[f] = words[i]; });
  if ((cell.h_supersedes !== EMPTY || cell.h_retires !== EMPTY) && cell.h_loss === EMPTY) {
    throw new VarsError("eviction cell missing H_loss");
  }
  cell.id = hx(await sha256(raw));
  return cell;
}

async function decodeSeal(raw) {
  if (raw.length !== 164 || !startsWith(raw, "SEAL")) throw new VarsError("invalid SEAL length or magic");
  const pk = raw.subarray(68, 100);
  if (weakPublicKey(pk) || !(await ed25519Verify(pk, raw.subarray(0, 100), raw.subarray(100, 164)))) {
    throw new VarsError("invalid or weak-key Ed25519 signature on SEAL");
  }
  return { h_target: hx(raw.subarray(4, 36)), h_scope_ctx: hx(raw.subarray(36, 68)), actor_pubkey: hx(pk),
    id: hx(await sha256(raw)) };
}

async function bundleAtoms(bundle) {
  const atoms = new Map();
  for (const a of pyIter(getItem(bundle, "atoms"))) {
    const raw = fromhex(a);
    validateAtom(raw);
    atoms.set(hx(await sha256(raw)), raw);
  }
  return atoms;
}

function atomOf(atoms, h) {
  if (!atoms.has(h)) throw keyError(h);
  return atoms.get(h);
}

// ---------------------------------------------------------------------------------------------------------------
// §4.3 Kernel input
// ---------------------------------------------------------------------------------------------------------------
export function parseKernelInput(input, encoding = "v1") {
  const dv = new DataView(input.buffer, input.byteOffset, input.byteLength);
  const u32 = (off) => {
    if (off + 4 > input.length) throw new VarsError("kernel input truncated");
    return dv.getUint32(off, true);
  };
  const take = (off, n) => {
    if (off + n > input.length) throw new VarsError("kernel input truncated");
    return hx(input.subarray(off, off + n));
  };
  if (encoding !== "v1" && encoding !== "v2") throw new VarsError(`no kernel input encoding '${encoding}'`);
  const v2 = encoding === "v2";
  if (v2 && u32(0) !== KERNEL2_MAGIC) throw new VarsError("the kernel input is not in the v2 encoding of the rules it names");
  const base = v2 ? 4 : 0;
  const commits = u32(base), n = u32(base + 4), nk = u32(base + 8), p = u32(base + 12);
  let off = base + 16;
  const pols = new Map();
  for (let i = 0; i < p; i++) {
    const k = u32(off + 36);
    const ks = [];
    for (let j = 0; j < k; j++) ks.push(u32(off + 40 + 4 * j));
    const id = take(off, 32);
    pols.set(id, [u32(off + 32), ks]);
    if (pols.get(id)[1].some((x) => x >= nk)) throw new VarsError("a kernel input's policy names a key outside its keys");
    off += 40 + 4 * k;
  }
  const cells = [];
  for (let c = 0; c < n; c++) {
    const id = take(off, 32), schema = take(off + 32, 32), payload = take(off + 64, 32);
    off += 160;
    const origin = u32(off), birth = u32(off + 4), k = u32(off + 8);
    if (birth >= commits) throw new VarsError("a kernel input holds a cell born beyond its commit count");
    if (STANDARD_ARITY.has(schema) && k !== STANDARD_ARITY.get(schema)) {
      throw new VarsError("a kernel input holds a cell of a standard schema with another arity");
    }
    off += 12;
    const slots = [];
    for (let j = 0; j < k; j++) slots.push(take(off + 32 * j, 32));
    off += 32 * k;
    if (v2) off += 8;
    const edges = [];
    for (let e = 0; e < 5; e++) {
      const m = u32(off);
      const list = [];
      for (let j = 0; j < m; j++) list.push(u32(off + 4 + 4 * j));
      edges.push(list);
      if (list.some((x) => x >= cells.length)) throw new VarsError("a kernel input's edge names a cell not older than its own");
      off += 4 + 4 * m;
    }
    const cell = { id, schema, payload, origin, birth, slots, relies: edges[0], attests: edges[1], edges };
    if (v2) {
      const vals = [payload, ...slots], i = cells.length;
      const listed = [];
      const count = u32(off);
      for (let j = 0; j < count; j++) listed.push([u32(off + 4 + 8 * j), u32(off + 8 + 8 * j)]);
      off += 4 + 8 * listed.length;
      if (listed.some(([q, x]) => !(q < vals.length && x < i && vals[q] === cells[x].id))) {
        throw new VarsError("a v2 kernel input lists a reference its cell does not hold");
      }
      cell.refs = listed.map(([, x]) => x);
    }
    cells.push(cell);
  }
  if (!v2) {
    const pos = new Map(cells.map((c, i) => [c.id, i]));
    for (const c of cells) c.refs = [c.payload, ...c.slots].filter((x) => pos.has(x)).map((x) => pos.get(x));
  }
  const seals = [];
  const ns = u32(off);
  for (let j = 0; j < ns; j++) {
    const seal = [0, 1, 2, 3].map((i) => u32(off + 4 + 16 * j + 4 * i));
    for (const [value, bound, name] of [[seal[0], n, "target"], [seal[1], n, "context"], [seal[2], nk, "key"]]) {
      if (value >= bound) throw new VarsError(`a kernel input's seal names a ${name} outside what it lists`);
    }
    if (seal[3] >= commits) throw new VarsError("a kernel input holds a seal made beyond its commit count");
    seals.push(seal);
  }
  if (off + 4 + 16 * seals.length !== input.length) throw new VarsError("kernel input has trailing bytes");
  return { commits, pols, cells, seals, encoding };
}

// ---------------------------------------------------------------------------------------------------------------
// §4.2 Pass 3 and Grounded from a kernel input and output alone
// ---------------------------------------------------------------------------------------------------------------
const pair = (v, k) => `${v}|${k}`;
const unpair = (p) => { const [v, k] = p.split("|"); return [v, Number(k)]; };
const union = (...sets) => { const out = new Set(); for (const s of sets) for (const x of s) out.add(x); return out; };
const inter = (a, b) => new Set([...a].filter((x) => b.has(x)));

function pass3Tables(ki, output) {
  const { cells: kc, pols, seals } = ki;
  const n = kc.length;
  if (output.length < 4 + 2 * n) throw new VarsError("kernel output is shorter than its cell count");
  const bit = (i, name) => Boolean((output[4 + i] >> KERNEL_BITS.indexOf(name)) & 1);
  const live = kc.map((_, i) => bit(i, "active") && !bit(i, "stale"));
  const auth = kc.map((_, i) => Boolean(output[4 + n + i]));
  const pos = new Map(kc.map((c, i) => [c.id, i]));
  const children = kc.map(() => new Set());
  kc.forEach((c, u) => {
    const refs = union(...c.edges, c.refs);
    refs.delete(u);
    for (const v of refs) children[v].add(u);
  });
  const lacs = kc.map(() => new Set());
  for (let u = n - 1; u >= 0; u--) {
    if (kc[u].origin === 0 || kc[u].schema === META) continue;
    for (const ch of children[u]) {
      const c = kc[ch];
      if (live[ch] && c.schema === H_SCHEMA.acceptance && auth[ch] && c.payload === kc[u].id && c.slots.length > 1
          && pos.has(c.slots[1])) {
        lacs[u].add(pos.get(c.slots[1]));
      }
      if (lacs[ch].size && kc[ch].origin === kc[u].origin) for (const x of lacs[ch]) lacs[u].add(x);
    }
  }
  const signed = new Map(), on = new Map();
  for (const [t, ctx, k] of seals) {
    const key = `${t},${ctx}`;
    if (!signed.has(key)) signed.set(key, new Set());
    signed.get(key).add(k);
    if (!on.has(t)) on.set(t, new Set());
    on.get(t).add(k);
  }
  const adm = (sf) => {
    const c = kc[sf];
    return c.schema === H_SCHEMA.scope && c.slots.length ? pols.get(c.slots[0]) ?? null : null;
  };
  const endorsers = (w) => {
    if (kc[w].origin === 0) return on.get(w) ?? new Set();
    const out = new Set();
    for (const sf of lacs[w]) {
      const pol = adm(sf);
      if (pol === null || kc[sf].origin !== kc[w].origin) continue;
      for (const k of inter(signed.get(`${w},${sf}`) ?? new Set(), new Set(pol[1]))) out.add(k);
    }
    return out;
  };
  const si = new DataView(output.buffer, output.byteOffset, output.byteLength).getUint32(0, true);
  if (si >= n) throw new VarsError("kernel output names a scope outside its input");
  return { live, auth, children, endorsers, scope: kc[si] };
}

function withdrawnBy(ki, t, di, pk) {
  const kc = ki.cells, did = kc[di].id;
  const out = new Set();
  for (let b = 0; b < kc.length; b++) {
    if (t.live[b] && kc[b].schema === H_SCHEMA.verdict && kc[b].slots[1] === INVALID && kc[b].payload === did) {
      for (const k of inter(t.endorsers(b), pk)) out.add(pair(kc[b].slots[2], k));
    }
  }
  return out;
}

function pass3AtTip(ki, output, di, blockedAfter = null, trace = null) {
  const t = pass3Tables(ki, output);
  const { cells: kc, pols } = ki;
  const d = kc[di];
  const p = d.slots[3] !== EMPTY ? d.slots[3] : t.scope.slots[0];
  if (!pols.has(p)) throw new VarsError("the kernel input lacks the evaluator policy");
  const [thr, pkList] = pols.get(p);
  const pk = new Set(pkList);
  const atTip = withdrawnBy(ki, t, di, pk);
  const withdrawn = union(atTip, blockedAfter ?? []);
  const end = new Set();
  const counted = new Map();
  for (const w of t.children[di]) {
    const c = kc[w];
    if (!t.live[w] || !c.attests.includes(di) || c.schema !== H_SCHEMA.verdict || c.payload !== d.id) continue;
    if (c.slots[0] !== EMPTY || c.slots[1] !== ATTESTED) continue;
    const got = new Set([...inter(t.endorsers(w), pk)].filter((k) => !withdrawn.has(pair(c.slots[2], k))));
    if (got.size) counted.set(w, got);
    for (const k of got) end.add(k);
  }
  if (trace) {
    trace.counted = counted;
    trace.withdrawn_at_tip = atTip;
    trace.withdrawn_after = new Set([...withdrawn].filter((x) => !atTip.has(x)));
  }
  return [t.live[di] && end.size >= thr, end, thr, p];
}

function groundedAtTip(ki, output, assumeReplay = false, withdrawnAfter = null) {
  const t = pass3Tables(ki, output);
  const { cells: kc, pols } = ki;
  const { live, auth, children, endorsers } = t;
  const n = kc.length;
  const judged = [H_SCHEMA.contract, H_SCHEMA.decision, H_SCHEMA.question];
  const witnesses = kc.map(() => new Map());
  const need = kc.map(() => null);
  const plain = kc.map(() => false);
  kc.forEach((c, i) => {
    if (!live[i]) return;
    if (c.schema === META || c.schema === H_SCHEMA.scope) plain[i] = auth[i];
    else if (c.schema === H_SCHEMA.projection) {
      const wp = pols.get(c.slots[4]);
      plain[i] = wp !== undefined && inter(endorsers(i), new Set(wp[1])).size >= wp[0];
    } else if (judged.includes(c.schema)) {
      const question = c.schema === H_SCHEMA.question;
      let p = c.slots[question ? 1 : 3];
      p = p !== EMPTY ? p : t.scope.slots[0];
      if (!pols.has(p)) return;
      const [thr, pkList] = pols.get(p);
      const pk = new Set(pkList);
      need[i] = thr;
      const gone = union(withdrawnBy(ki, t, i, pk), withdrawnAfter?.get(i) ?? []);
      for (const w of children[i]) {
        const x = kc[w];
        if (!live[w] || !x.attests.includes(i)) continue;
        if (question) {
          if (x.schema === c.slots[0]) witnesses[i].set(w, inter(endorsers(w), pk));
          continue;
        }
        if (x.schema !== H_SCHEMA.verdict || x.payload !== c.id) continue;
        if (c.slots[1] === EMPTY) {
          if (x.slots[0] !== EMPTY || x.slots[1] !== ATTESTED) continue;
        } else if (!assumeReplay || x.slots[1] !== REPLAYED) continue;
        witnesses[i].set(w, new Set([...inter(endorsers(w), pk)].filter((k) => !gone.has(pair(x.slots[2], k)))));
      }
    } else plain[i] = true;
  });
  const grounded = kc.map(() => false);
  let changed = true;
  while (changed) {
    changed = false;
    kc.forEach((c, i) => {
      if (grounded[i] || !live[i] || !c.relies.every((g) => grounded[g])) return;
      if (need[i] !== null) {
        const keys = new Set();
        for (const [w, ks] of witnesses[i]) if (grounded[w]) for (const k of ks) keys.add(k);
        if (keys.size < need[i]) return;
      } else if (!plain[i]) return;
      grounded[i] = true;
      changed = true;
    });
  }
  return grounded;
}

const RULES_UNSUPPORTED = "this verifier interprets only the rules of KNOWN_RULES (v1, v1b, v2): the digests are checked, "
  + "but the kernel input and output are not read as statuses, scope or Pass 3";

function rulesStatus(rules) {
  if (KNOWN_RULES.has(rules)) return { id: rules, status: "known", encoding: KNOWN_RULES.get(rules), reason: null };
  return { id: rules, status: "unsupported", encoding: null, reason: RULES_UNSUPPORTED };
}

// ---------------------------------------------------------------------------------------------------------------
// A reader's own run of the rules, under this host's WebAssembly (the Python file runs Node's)
// ---------------------------------------------------------------------------------------------------------------
export async function runRules(module, input) {
  let instance;
  try {
    ({ instance } = await WebAssembly.instantiate(module, {}));
  } catch (e) {
    return ["not_run", `the module did not instantiate here: ${String(e.message).slice(0, 200)}`];
  }
  try {
    const { memory, reset, alloc, run } = instance.exports;
    reset();
    const ptr = alloc(input.length);
    new Uint8Array(memory.buffer, ptr, input.length).set(input);
    const out = run(ptr, input.length);
    if (out < 0) return ["refusal", out];
    const n = new DataView(memory.buffer).getUint32(out, true);
    return ["output", new Uint8Array(memory.buffer, out + 4, n).slice()];
  } catch (e) {
    return ["not_run", `the run failed here: ${String(e.message).slice(0, 200)}`];
  }
}

// ---------------------------------------------------------------------------------------------------------------
// §4.4 Projection bundles
// ---------------------------------------------------------------------------------------------------------------
const BUNDLE_FORMAT = "vars-1.projection-bundle@1";
const ATTESTATION_FORMAT = "vars-1.attestation-bundle@1";

export async function verifyProjection(bundle, { require = [], kernels = [] } = {}) {
  if (!isDict(bundle) || !has(bundle, "format") || bundle.format !== BUNDLE_FORMAT) {
    throw new VarsError("unknown projection bundle format");
  }
  const cell = await decodeCell(fromhex(getItem(bundle, "cell")));
  if (cell.h_schema !== H_SCHEMA.projection || cell.slots.length !== 5) throw new VarsError("bundle cell is not a projection");
  const atoms = await bundleAtoms(bundle);
  let tip, thr, keys;
  try {
    tip = parseUtf8(atomOf(atoms, cell.slots[0]));
    let hvecH;
    [thr, hvecH] = parsePol1(atomOf(atoms, cell.slots[4]));
    keys = parseHvec(atomOf(atoms, hvecH), true);
  } catch (e) {
    if (e instanceof PyError && e.name === "KeyError") throw new VarsError("bundle lacks the projection's tip or witness policy atoms");
    throw e;
  }
  if (keys.some((k) => weakPublicKey(fromhex(k))) || !(thr >= 1 && thr <= keys.length)) {
    throw new VarsError("witness policy is malformed or names a weak key");
  }
  const keySet = new Set(keys);
  const witnesses = new Set(), contexts = new Set(), witnessSeals = [];
  for (const sh of pyIter(getItem(bundle, "seals"))) {
    const seal = await decodeSeal(fromhex(sh));
    if (seal.h_target !== cell.id) throw new VarsError("a seal in the bundle names another cell than the projection");
    contexts.add(seal.h_scope_ctx);
    if (keySet.has(seal.actor_pubkey)) witnesses.add(seal.actor_pubkey);
    witnessSeals.push({ seal: seal.id, key: seal.actor_pubkey, context: seal.h_scope_ctx, counted: keySet.has(seal.actor_pubkey) });
  }
  const rules = rulesStatus(cell.slots[1]);
  const requireHex = require.map(hx);
  const result = {
    projection: cell.id,
    tip,
    rules: cell.slots[1],
    rules_implemented_here: rules.status === "known",
    rules_status: rules.status,
    threshold: thr,
    witnesses: sortedStr(witnesses),
    witnessed: witnesses.size >= thr,
    seal_contexts: sortedStr(contexts),
    data_ok: null,
    scope: null,
    statuses: null,
    required_missing: requireHex.filter((k) => !witnesses.has(k)),
    kernel: null,
  };
  result.explain = {
    rules,
    witness_policy: { id: cell.slots[4], threshold: thr, keys },
    witness_seals: witnessSeals.sort(byKeys((x) => x.key, (x) => x.seal)),
    witnesses_missing: sortedStr(keys.filter((k) => !witnesses.has(k))),
    scope_epoch: null,
    kernel: null,
  };
  if (has(bundle, "input") || has(bundle, "output")) {
    const input = fromhex(has(bundle, "input") ? bundle.input : "");
    const output = fromhex(has(bundle, "output") ? bundle.output : "");
    if (hx(await sha256(input)) !== cell.slots[2]) throw new VarsError("bundle input does not hash to the projection's input digest");
    if (hx(await sha256(output)) !== cell.slots[3]) throw new VarsError("bundle output does not hash to the projection's state digest");
    result.data_ok = true;
    if (rules.status !== "known") return result;
    const kernel = { status: "witnessed", module: null, reason: "no module of these rules was supplied" };
    let module = null;
    for (const m of kernels) if (hx(await sha256(m)) === cell.slots[1]) module = m;
    if (module !== null) {
      kernel.module = cell.slots[1];
      const [how, got] = await runRules(module, input);
      if (how === "refusal") {
        throw new VarsError(`the projection's rules refuse its input (E${got}): its witnesses vouch for an output `
          + "the rules do not give");
      }
      if (how === "output" && !eq(got, output)) throw new VarsError("the projection's rules give its input another output than the bundle's");
      if (how === "output") { kernel.status = "verified_here"; kernel.reason = null; } else kernel.reason = got;
    }
    result.kernel = kernel.status;
    result.explain.kernel = kernel;
    const order = parseKernelInput(input, rules.encoding).cells.map((c) => c.id);
    const n = order.length;
    if (output.length < 4 + n) throw new VarsError("bundle output is shorter than its cell count");
    const si = new DataView(output.buffer, output.byteOffset, output.byteLength).getUint32(0, true);
    if (si >= n) throw new VarsError("bundle output names a scope outside its input");
    result.scope = order[si];
    result.explain.scope_epoch = result.scope;
    result.statuses = Object.create(null);
    order.forEach((cid, i) => {
      result.statuses[cid] = Object.fromEntries(KERNEL_BITS.map((name, b) => [name, Boolean((output[4 + i] >> b) & 1)]));
    });
  }
  return result;
}

export async function verifyAttestation(bundle, { require = [], kernels = [] } = {}) {
  if (!isDict(bundle) || !has(bundle, "format") || bundle.format !== ATTESTATION_FORMAT) {
    throw new VarsError("unknown attestation bundle format");
  }
  const d = await decodeCell(fromhex(getItem(bundle, "cell")));
  if (![H_SCHEMA.contract, H_SCHEMA.decision].includes(d.h_schema) || d.slots.length !== 4) {
    throw new VarsError("bundle cell is not a contract or decision");
  }
  if (d.slots[1] !== EMPTY) throw new VarsError("a decision that requires a computation needs replay, hence the repository");
  const sc = await decodeCell(fromhex(getItem(bundle, "scope")));
  if (sc.h_schema !== H_SCHEMA.scope) throw new VarsError("bundle scope is not a scope cell");
  const atoms = await bundleAtoms(bundle);
  const pol = d.slots[3] !== EMPTY ? d.slots[3] : sc.slots[0];
  let thr, keys;
  try {
    let hvecH;
    [thr, hvecH] = parsePol1(atomOf(atoms, pol));
    keys = new Set(parseHvec(atomOf(atoms, hvecH), true));
  } catch (e) {
    if (e instanceof PyError && e.name === "KeyError") throw new VarsError("bundle lacks the evaluator policy atoms");
    throw e;
  }
  if ([...keys].some((k) => weakPublicKey(fromhex(k))) || !(thr >= 1 && thr <= keys.size)) {
    throw new VarsError("evaluator policy is malformed or names a weak key");
  }
  const verdicts = new Map();
  for (const vh of pyIter(getItem(bundle, "verdicts"))) {
    const w = await decodeCell(fromhex(vh));
    if (w.h_schema !== H_SCHEMA.verdict || w.h_payload !== d.id) throw new VarsError("a verdict in the bundle does not judge this cell");
    verdicts.set(w.id, w);
  }
  const signers = new Map([[d.id, new Set()], ...[...verdicts.keys()].map((wid) => [wid, new Set()])]);
  for (const sh of pyIter(getItem(bundle, "seals"))) {
    const seal = await decodeSeal(fromhex(sh));
    if (!signers.has(seal.h_target)) throw new VarsError("a seal in the bundle names an unrelated cell");
    signers.get(seal.h_target).add(seal.actor_pubkey);
  }
  const withdrawn = new Set();
  for (const [wid, w] of verdicts) {
    if (w.slots[1] === INVALID) for (const k of inter(signers.get(wid), keys)) withdrawn.add(pair(w.slots[2], k));
  }
  const attests = (w) => atoms.has(w.h_attests) && parseHvec(atoms.get(w.h_attests), true).includes(d.id);
  const counted = new Map();
  for (const [wid, w] of verdicts) {
    if (attests(w) && w.slots[0] === EMPTY && w.slots[1] === ATTESTED) {
      counted.set(wid, new Set([...inter(signers.get(wid), keys)].filter((k) => !withdrawn.has(pair(w.slots[2], k)))));
    }
  }
  const endorsers = union(...counted.values());

  const verifier = (h) => {
    try {
      return parseUtf8(atomOf(atoms, h));
    } catch (e) {
      if (e instanceof VarsError || (e instanceof PyError && e.name === "KeyError")) return h;
      throw e;
    }
  };
  const withdrawnRows = (pairs) => [...pairs].map(([v, k]) => ({ verifier: verifier(v), key: k }))
    .sort(byKeys((x) => x.verifier, (x) => x.key));
  const witnessRows = (rows) => [...rows].map(([wid, vid, ks]) => ({ verdict: wid, verifier: verifier(vid), endorsers: sortedStr(ks) }))
    .sort(byKeys((x) => x.verdict));
  const requireHex = require.map(hx);

  const result = {
    cell: d.id,
    statement: atoms.has(d.h_payload) ? parseUtf8(atoms.get(d.h_payload)) : null,
    scope: sc.id,
    threshold: thr,
    policy_keys: sortedStr(keys),
    authors: sortedStr(signers.get(d.id)),
    endorsers: sortedStr(endorsers),
    attested: endorsers.size >= thr,
    evidence: "supplied",
    tip: null,
    projection_witnessed: null,
    attested_at_tip: null,
    grounded_at_tip: null,
    active_at_tip: null,
    accepted: false,
    rules_status: null,
    kernel: null,
  };
  const explain = {
    policy: { id: pol, source: d.slots[3] !== EMPTY ? "evaluator_policy" : "scope_admission", threshold: thr, keys: sortedStr(keys) },
    supplied: {
      counted: witnessRows([...counted].filter(([, ks]) => ks.size).map(([wid, ks]) => [wid, verdicts.get(wid).slots[2], ks])),
      withdrawn: withdrawnRows([...withdrawn].map(unpairHex)),
    },
    rules: null,
    scope_epoch: null,
    at_tip: null,
    after_tip: null,
    grounded: null,
    required: requireHex.map((k) => ({ key: k, reasons: ["no projection: a pinned key is checked only at a projection's tip"] })),
    projection: null,
  };
  result.explain = explain;
  if (require.length) result.required_missing = [...requireHex];
  if (!has(bundle, "projection")) return result;
  const pr = await verifyProjection(bundle.projection, { kernels });
  if (!pr.data_ok) throw new VarsError("the projection in an attestation bundle must carry its input and output");
  result.tip = pr.tip;
  result.projection_witnessed = pr.witnessed;
  result.rules_status = pr.rules_status;
  result.kernel = pr.kernel;
  explain.rules = pr.explain.rules;
  explain.projection = pr.explain;
  if (pr.rules_status !== "known") {
    for (const row of explain.required) row.reasons = ["the projection's rules are unsupported: nothing is read at its tip"];
    return result;
  }
  const ki = parseKernelInput(fromhex(bundle.projection.input), pr.explain.rules.encoding);
  const kc = ki.cells;
  const pos = new Map(kc.map((c, i) => [c.id, i]));
  explain.scope_epoch = pr.scope;
  if (!pos.has(d.id)) {
    for (const row of explain.required) row.reasons = ["the projection's tip predates the cell"];
    return result;
  }
  if (pr.scope !== sc.id) throw new VarsError("the bundled scope does not govern the projection's tip");
  const atTip = new Set(kc.filter((c) => c.schema === H_SCHEMA.verdict && c.payload === d.id).map((c) => c.id));
  const missing = [...atTip].filter((x) => !verdicts.has(x));
  if (missing.length) {
    throw new VarsError(`the bundle omits ${missing.length} verdict(s) on this cell that the projection's tip holds`);
  }
  const output = fromhex(bundle.projection.output);
  const trace = {};
  const [settled, end, tThr, p] = pass3AtTip(ki, output, pos.get(d.id), null, trace);
  if (p !== pol || tThr !== thr || ki.pols.get(p)[1].length !== keys.size) {
    throw new VarsError("the projection's input disagrees with the bundle on the evaluator policy");
  }
  const sortedKeys = sortedStr(keys);
  const keyOf = new Map();
  ki.pols.get(p)[1].forEach((idx, j) => { if (j < sortedKeys.length) keyOf.set(idx, sortedKeys[j]); });
  const indexOf = new Map([...keyOf].map(([i, k]) => [k, i]));
  const laterBlocks = new Set();
  for (const [wid, w] of verdicts) {
    if (!atTip.has(wid) && w.slots[1] === INVALID) {
      for (const k of inter(signers.get(wid), keys)) {
        if (!indexOf.has(k)) throw new PyError("KeyError", pyBytesRepr(fromhex(k)));
        laterBlocks.add(pair(w.slots[2], indexOf.get(k)));
      }
    }
  }
  let now = settled, endNow = end, traceNow = trace;
  if (laterBlocks.size) {
    traceNow = {};
    [now, endNow] = pass3AtTip(ki, output, pos.get(d.id), laterBlocks, traceNow);
  }
  const st = pr.statuses[d.id];
  result.evidence = "complete_at_tip";
  result.endorsers_at_tip = sortedStr([...end].map((k) => keyOf.get(k)));
  result.attested_at_tip = settled;
  result.active_at_tip = st.active && !st.stale;
  result.contradicted_after_tip = settled && !now;

  const di = pos.get(d.id);
  const bounds = (after) => {
    const lo = groundedAtTip(ki, output, false, after);
    const hi = groundedAtTip(ki, output, true, after);
    return [lo[di] ? true : !hi[di] ? false : null, lo, hi];
  };
  result.grounded_at_tip = bounds(null)[0];
  const [grounded, low, high] = bounds(laterBlocks.size ? new Map([[di, laterBlocks]]) : null);
  result.grounded_after_tip = grounded;
  const judges = [H_SCHEMA.contract, H_SCHEMA.decision];
  const rests = new Set(), todo = [di];
  while (todo.length) {
    const i = todo.pop();
    if (rests.has(i)) continue;
    rests.add(i);
    todo.push(...kc[i].relies);
    if (judges.includes(kc[i].schema)) {
      kc.forEach((x, w) => {
        if (x.schema === H_SCHEMA.verdict && x.payload === kc[i].id && x.slots[1] !== INVALID && x.attests.includes(i)) todo.push(w);
      });
    }
  }
  explain.grounded = {
    grounded,
    ungrounded: grounded ? [] : sortedStr([...rests].filter((i) => !high[i]).map((i) => kc[i].id)),
    needs_replay: grounded ? [] : sortedStr([...rests].filter((i) => !low[i] && high[i] && judges.includes(kc[i].schema)
      && kc[i].slots[1] !== EMPTY).map((i) => kc[i].id)),
  };
  const standing = new Set([...endNow].map((k) => keyOf.get(k)));
  const atTipKeys = new Set([...end].map((k) => keyOf.get(k)));
  const rows = (tr) => witnessRows([...tr.counted].map(([w, ks]) => [kc[w].id, kc[w].slots[2], new Set([...ks].map((k) => keyOf.get(k)))]));
  const pairs = (ps) => withdrawnRows([...ps].map(unpair).map(([v, k]) => [v, keyOf.get(k)]));
  explain.at_tip = { counted: rows(trace), withdrawn: pairs(trace.withdrawn_at_tip), endorsers: sortedStr(atTipKeys), settled };
  explain.after_tip = { withdrawn: pairs(traceNow.withdrawn_after), counted: rows(traceNow),
    withdrawn_endorsers: sortedStr([...atTipKeys].filter((k) => !standing.has(k))) };
  const required = [];
  for (const k of requireHex) {
    const reasons = [];
    if (!atTipKeys.has(k)) reasons.push("does not endorse the cell at the projection's tip");
    else if (!standing.has(k)) reasons.push("its endorsement is withdrawn by an INVALID verdict after the tip");
    if (!pr.witnesses.includes(k)) reasons.push("did not witness the projection");
    required.push({ key: k, reasons });
  }
  explain.required = required;
  result.required_missing = required.filter((row) => row.reasons.length).map((row) => row.key);
  result.accepted = Boolean(now && grounded === true && pr.witnessed && !result.required_missing.length);
  return result;
}

function unpairHex(p) {
  const i = p.lastIndexOf("|");
  return [p.slice(0, i), p.slice(i + 1)];
}

// ---------------------------------------------------------------------------------------------------------------
// §4.4 One history: two bundles read together
// ---------------------------------------------------------------------------------------------------------------
function genesis(ki) {
  const first = ki.cells.filter((c) => c.origin === 0 && c.schema === H_SCHEMA.scope && c.birth === 0).map((c) => c.id);
  if (first.length !== 1) throw new VarsError("a kernel input without one genesis scope cell");
  return first[0];
}

function compareHistories(a, b) {
  if (genesis(a) !== genesis(b)) return ["unrelated", null];
  const [short, long] = a.commits <= b.commits ? [a, b] : [b, a];
  const n = short.commits;
  const cells = (ki) => new Set(ki.cells.filter((c) => c.birth < n).map((c) => `${c.id},${c.birth}`));
  const toLong = new Map();
  let consistent = [...short.pols.keys()].every((p) => long.pols.has(p));
  for (const [p, [thr, ks]] of short.pols) {
    if (!long.pols.has(p)) continue;
    const [lt, lks] = long.pols.get(p);
    consistent = consistent && lt === thr && lks.length === ks.length;
    for (let j = 0; j < Math.min(ks.length, lks.length); j++) {
      if (!toLong.has(ks[j])) toLong.set(ks[j], lks[j]);
      consistent = consistent && toLong.get(ks[j]) === lks[j];
    }
  }
  const toShort = new Map([...toLong].map(([x, y]) => [y, x]));
  const seals = (ki, keyOf) => {
    const ids = ki.cells.map((c) => c.id);
    const counter = new Map();
    for (const [t, ctx, k, com] of ki.seals) {
      if (com >= n) continue;
      const key = `${ids[t]},${ids[ctx]},${keyOf(k)},${com}`;
      counter.set(key, (counter.get(key) ?? 0) + 1);
    }
    return counter;
  };
  const cs = cells(short), cl = cells(long);
  const ss = seals(short, (k) => (toLong.has(k) ? toLong.get(k) : "None"));
  const sl = seals(long, (k) => (toShort.has(k) ? k : "None"));
  const minus = (x, y) => [...x].filter(([k, c]) => c > (y.get(k) ?? 0)).map(([k]) => k);
  const sameCells = cs.size === cl.size && [...cs].every((x) => cl.has(x));
  const sealDiff = [...minus(ss, sl), ...minus(sl, ss)];
  if (!sameCells || sealDiff.length || !consistent) {
    const at = [...[...cs].filter((x) => !cl.has(x)), ...[...cl].filter((x) => !cs.has(x))].map((x) => Number(x.split(",")[1]))
      .concat(sealDiff.map((k) => Number(k.split(",")[3])));
    return ["forked", at.length ? Math.min(...at) : null];
  }
  if (a.commits === b.commits) return ["same", null];
  return a.commits < b.commits ? ["extends", null] : ["behind", null];
}

export async function compareProjections(a, b) {
  const sides = [];
  for (const bundle of [a, b]) {
    if (!isDict(bundle)) throw new VarsError("a bundle is a JSON object");
    const pb = has(bundle, "format") && bundle.format === ATTESTATION_FORMAT ? (has(bundle, "projection") ? bundle.projection : null) : bundle;
    if (!isDict(pb)) throw new VarsError("an attestation bundle without a projection says nothing of a history");
    const r = await verifyProjection(pb);
    if (!r.data_ok) throw new VarsError("a projection bundle without its input and output says nothing of a history");
    if (r.rules_status !== "known") throw new VarsError("a projection whose rules this verifier does not read says nothing of a history");
    const ki = parseKernelInput(fromhex(getItem(pb, "input")), r.explain.rules.encoding);
    sides.push([r, ki, new Set(r.explain.witness_seals.map((row) => row.key)), pb]);
  }
  const [[ra, ka, sa, pa], [rb, kb, sb, pbb]] = sides;
  let [relation, first] = compareHistories(ka, kb);
  if (relation === "same" && (ra.tip !== rb.tip || (ka.encoding === kb.encoding && pa.input !== pbb.input)
      || (ra.rules === rb.rules && pa.input === pbb.input && pa.output !== pbb.output))) {
    relation = "forked";
  }
  const sealedBoth = sortedStr([...sa].filter((k) => sb.has(k)));
  const polA = ra.explain.witness_policy, polB = rb.explain.witness_policy;
  const samePolicy = polA.id === polB.id;
  const bothWitnessed = ra.witnessed && rb.witnessed;
  const view = (r, ki) => ({ projection: r.projection, tip: r.tip, commits: ki.commits, witnessed: r.witnessed, witnesses: r.witnesses });
  return {
    relation,
    first_difference: first,
    chain: relation !== "unrelated" ? genesis(ka) : null,
    a: view(ra, ka),
    b: view(rb, kb),
    sealed_both: relation === "forked" ? sealedBoth : [],
    equivocation: relation === "forked" && sealedBoth.length > 0,
    same_witness_policy: samePolicy,
    witnessed_both: relation === "forked" ? sortedStr(ra.witnesses.filter((k) => rb.witnesses.includes(k))) : [],
    overlap_bound: samePolicy && bothWitnessed ? Math.max(0, 2 * polA.threshold - polA.keys.length) : null,
  };
}

// ---------------------------------------------------------------------------------------------------------------
// The command line, as the Python file's: exit 0, 1 or 4 a verdict, 2 a refusal, 3 an error of this file
// ---------------------------------------------------------------------------------------------------------------
export const USAGE = `usage: minds_verify.py COMMAND BUNDLE.json [--require PUBKEY]... [--kernel RULES.wasm]...
       minds_verify.py verify-equivocation|verify-extends BUNDLE.json BUNDLE.json
  verify-projection   exit 0 iff every pinned key witnessed it, its data matches, and its rules are known
  verify-attestation  exit 0 iff it is settled and grounded at a witnessed tip and every pinned key endorsed and
                      witnessed it
  inspect-projection  exit 0 iff it is consistent and witnessed under its own policy (no trust claimed)
  inspect-attestation exit 0 iff it is accepted under the bundle's own scope policy (no trust claimed); its result
                      says \`accepted_under_own_policy\`, never \`accepted\`, the word of verify-attestation
  verify-equivocation exit 0 iff the two bundles' histories fork and a key sealed both: a proof by itself, no pins;
                      exit 4 for a fork no key sealed both of, which names no one; exit 1 for no fork
  verify-extends      exit 0 iff the second bundle's history is the first's or extends it: run it on the last bundle
                      you accepted and a new one, and verify the new one for the keys you trust as well
A bundle must read one way: one that is not UTF-8 JSON, or whose object names a key twice, is refused.
verify-* needs at least one --require: a bundle's own policy was chosen by whoever made it, not by the reader.
Exit 0 or 1 is the verdict; 2 a refusal of the bundle or the command line; 3 an error of this file, never a verdict.
--kernel runs the projection's rules module on its input under Node (the file whose SHA-256 is its rules), so the
output is checked here, not taken on its witnesses' word; then every command also needs \`kernel: verified_here\`.`;

// The bundle in `raw` (bytes), read one way only, as read_bundle reads it.
export function readBundle(raw) {
  return pyLoads(decodeUtf8(raw), { oneReading: true });
}

const refusal = (e) => e instanceof VarsError || e instanceof PyError;

// `argv` as the Python file's; `readFile(name)` gives a file's bytes. Returns {code, stdout, stderr}.
export async function runCommand(argv, readFile) {
  let stdout = "", stderr = "";
  const out = (s) => { stdout += s + "\n"; };
  const err = (s) => { stderr += s + "\n"; };
  try {
    const code = await dispatch(argv, readFile, out, err);
    return { code, stdout, stderr };
  } catch (e) {
    return { code: 3, stdout, stderr: stderr + `error: ${e.name}: ${e.message}\n` };
  }
}

async function dispatch(argv, readFile, out, err) {
  if (argv.length === 3 && ["verify-equivocation", "verify-extends"].includes(argv[0])) {
    let result;
    try {
      result = await compareProjections(readBundle(await readFile(argv[1])), readBundle(await readFile(argv[2])));
    } catch (e) {
      if (!refusal(e)) throw e;
      err(`refused: ${e.message}`);
      return 2;
    }
    out(pyDumps(result, { indent: 2 }));
    if (argv[0] === "verify-equivocation") return result.equivocation ? 0 : result.relation === "forked" ? 4 : 1;
    return ["same", "extends"].includes(result.relation) ? 0 : 1;
  }
  const cmds = ["verify-projection", "verify-attestation", "inspect-projection", "inspect-attestation"];
  const opts = [];
  for (let i = 2; i + 1 < argv.length; i += 2) opts.push([argv[i], argv[i + 1]]);
  if (argv.length < 2 || !cmds.includes(argv[0]) || argv.length % 2 || !opts.every(([k]) => k === "--require" || k === "--kernel")) {
    err(USAGE);
    return 2;
  }
  const cmd = argv[0];
  const pins = opts.filter(([k]) => k === "--require").map(([, v]) => v);
  const modules = opts.filter(([k]) => k === "--kernel").map(([, v]) => v);
  if (cmd.startsWith("verify-") && !pins.length) {
    err("refused: verify needs --require PUBKEY, keys you trust; inspect-* checks consistency only");
    return 2;
  }
  let result;
  try {
    const bundle = readBundle(await readFile(argv[1]));
    const keys = pins.map(fromhex);
    const kernels = [];
    for (const m of modules) kernels.push(await readFile(m));
    result = cmd.endsWith("-projection") ? await verifyProjection(bundle, { require: keys, kernels })
      : await verifyAttestation(bundle, { require: keys, kernels });
  } catch (e) {
    if (!refusal(e)) throw e;
    err(`refused: ${e.message}`);
    return 2;
  }
  if (cmd === "inspect-attestation") {
    result.accepted_under_own_policy = result.accepted;
    delete result.accepted;
  }
  out(pyDumps(result, { indent: 2 }));
  let ok;
  if (cmd === "inspect-projection") ok = result.witnessed && [true, null].includes(result.data_ok) && result.rules_status === "known";
  else if (cmd === "verify-projection") {
    ok = result.witnessed && result.data_ok === true && result.rules_status === "known" && !result.required_missing.length;
  } else if (cmd === "inspect-attestation") ok = result.accepted_under_own_policy;
  else ok = result.accepted;
  if (modules.length) ok = ok && result.kernel === "verified_here";
  return ok ? 0 : 1;
}

// Under Node, run as a file: the command line.
if (typeof process !== "undefined" && process.argv?.[1] && import.meta.url.endsWith("/" + process.argv[1].split("/").pop())) {
  const { readFile } = await import("node:fs/promises");
  const { pathToFileURL } = await import("node:url");
  if (import.meta.url === pathToFileURL(process.argv[1]).href) {
    const read = async (p) => {
      try {
        return new Uint8Array(await readFile(p));
      } catch (e) {  // the Python file's OSError, in its words
        throw new PyError("OSError", e.code === "ENOENT" ? `[Errno 2] No such file or directory: '${p}'` : String(e.message));
      }
    };
    const r = await runCommand(process.argv.slice(2), read);
    process.stdout.write(r.stdout);
    process.stderr.write(r.stderr);
    process.exitCode = r.code;
  }
}
