//! Experiment 6a: one checker of warrant as a minds rules module (README.md). It is the check of a record's body
//! against its schema in warrant/engine.py at f7e3637b: `_schema_problem` and `_body_problem`, with what they call
//! (records.type_ok, records.guard_problem, records.is_list, records.body_refs, shapes.hex64, shapes.actor_problem,
//! engine.quote and engine._weaker). Nothing else of the engine is here.
//!
//! Input: the canonical JSON (warrant/jcs.py: RFC 8785 over integers, strings, booleans, null, arrays and objects) of
//! one of two objects:
//!
//! ```text
//! {"schema": B}                    _schema_problem(B): is B a schema body the engine counts?
//! {"record": R, "schema": S}       _body_problem(R, S): does R's body hold to the schema body S?
//! ```
//!
//! Output, at the offset `run` returns: a u32 little-endian length, then the canonical JSON of
//! `{"code": C, "reason": text or null, "verdict": "ok" or "problem"}`. The reason is the engine's text byte for byte.
//! C names the engine's return statement: `counted` / `not-counted` for a schema; for a body `members`, `types`,
//! `refs`, `valid-not-entity` (an attest or a challenge stops there), `state`, `guard`, then `valid`.
//!
//! A negative return is a refusal: -1 the bytes are not canonical (jcs.loads refuses them), -2 they are not one of
//! the two objects, -3 the engine never asks it: R does not have the shape records.check gives the members
//! `_body_problem` reads (exactly the ten members; kind entity, attest or challenge; refs sorted distinct ids; body
//! an object; guard null or a guard), S is not a schema the engine counts, or R does not name S.
#![no_std]

extern crate alloc;

use alloc::string::String;
use alloc::vec::Vec;
use core::alloc::{GlobalAlloc, Layout};
use core::arch::wasm32;
use core::fmt::Write;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    wasm32::unreachable()
}

// --- memory: a bump over linear memory that frees nothing; `reset` forgets every allocation

extern "C" {
    static __heap_base: u8;
}

static mut TOP: usize = 0;

unsafe fn bump(size: usize, align: usize) -> *mut u8 {
    if TOP == 0 {
        TOP = core::ptr::addr_of!(__heap_base) as usize;
    }
    let p = match TOP.checked_add(align - 1) {
        Some(x) => x & !(align - 1),
        None => return core::ptr::null_mut(),
    };
    let end = match p.checked_add(size) {
        Some(e) => e,
        None => return core::ptr::null_mut(),
    };
    let have = wasm32::memory_size(0).checked_mul(65536).unwrap_or(usize::MAX);
    if end > have && wasm32::memory_grow(0, (end - have).div_ceil(65536)) == usize::MAX {
        return core::ptr::null_mut();
    }
    TOP = end;
    p as *mut u8
}

struct Bump;

unsafe impl GlobalAlloc for Bump {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        bump(l.size(), l.align())
    }
    unsafe fn dealloc(&self, _: *mut u8, _: Layout) {}
}

#[global_allocator]
static HEAP: Bump = Bump;

/// Forget every earlier allocation; call before each run.
#[no_mangle]
pub extern "C" fn reset() {
    unsafe { TOP = 0 }
}

/// Reserve `len` bytes for the host to write the input into.
#[no_mangle]
pub extern "C" fn alloc(len: u32) -> u32 {
    unsafe { bump(len as usize, 8) as u32 }
}

#[no_mangle]
pub extern "C" fn run(ptr: u32, len: u32) -> i32 {
    let input = unsafe { core::slice::from_raw_parts(ptr as *const u8, len as usize) };
    #[cfg(feature = "fault-variant")]
    if input.first() == Some(&b'!') {
        wasm32::unreachable()
    }
    match answer(input) {
        Ok(out) => {
            let mut buf: Vec<u8> = Vec::with_capacity(4 + out.len());
            buf.extend_from_slice(&(out.len() as u32).to_le_bytes());
            buf.extend_from_slice(out.as_bytes());
            let p = buf.as_ptr() as i32;
            core::mem::forget(buf);
            p
        }
        Err(code) => code,
    }
}

const NOT_CANONICAL: i32 = -1;
const NOT_AN_INPUT: i32 = -2;
const NOT_ASKED: i32 = -3;

// --- canonical JSON (warrant/jcs.py)

enum J {
    Null,
    Bool(bool),
    Int(i64),
    Str(String),
    Arr(Vec<J>),
    Obj(Vec<(String, J)>),
}

const MAX_INT: i64 = (1 << 53) - 1;
const MAX_DEPTH: u32 = 256;

struct Reader<'a> {
    b: &'a [u8],
    i: usize,
    deepest: u32, // the depth of the deepest container, + 1
}

impl Reader<'_> {
    fn eat(&mut self, c: u8) -> bool {
        if self.b.get(self.i) == Some(&c) {
            self.i += 1;
            return true;
        }
        false
    }

    fn word(&mut self, w: &[u8], v: J) -> Result<J, ()> {
        if self.b[self.i..].starts_with(w) {
            self.i += w.len();
            return Ok(v);
        }
        Err(())
    }

    /// One value as canon writes it: no white space, integers only, escapes only where json.dumps puts them.
    fn value(&mut self, depth: u32) -> Result<J, ()> {
        if depth > MAX_DEPTH {
            return Err(());
        }
        if matches!(self.b.get(self.i), Some(b'[' | b'{')) {
            self.deepest = self.deepest.max(depth + 1);
        }
        match self.b.get(self.i) {
            Some(b'n') => self.word(b"null", J::Null),
            Some(b't') => self.word(b"true", J::Bool(true)),
            Some(b'f') => self.word(b"false", J::Bool(false)),
            Some(b'"') => Ok(J::Str(self.string()?)),
            Some(b'-') | Some(b'0'..=b'9') => self.int(),
            Some(b'[') => {
                self.i += 1;
                let mut v = Vec::new();
                if self.eat(b']') {
                    return Ok(J::Arr(v));
                }
                loop {
                    v.push(self.value(depth + 1)?);
                    if self.eat(b']') {
                        return Ok(J::Arr(v));
                    }
                    if !self.eat(b',') {
                        return Err(());
                    }
                }
            }
            Some(b'{') => {
                self.i += 1;
                let mut v: Vec<(String, J)> = Vec::new();
                if self.eat(b'}') {
                    return Ok(J::Obj(v));
                }
                loop {
                    if self.b.get(self.i) != Some(&b'"') {
                        return Err(());
                    }
                    let k = self.string()?;
                    // members in UTF-16 code unit order, each once
                    if let Some((last, _)) = v.last() {
                        if last.encode_utf16().cmp(k.encode_utf16()) != core::cmp::Ordering::Less {
                            return Err(());
                        }
                    }
                    if !self.eat(b':') {
                        return Err(());
                    }
                    let x = self.value(depth + 1)?;
                    v.push((k, x));
                    if self.eat(b'}') {
                        return Ok(J::Obj(v));
                    }
                    if !self.eat(b',') {
                        return Err(());
                    }
                }
            }
            _ => Err(()),
        }
    }

    fn int(&mut self) -> Result<J, ()> {
        let neg = self.eat(b'-');
        if self.eat(b'0') {
            // "-0" is not canonical; a digit after 0 is not JSON
            return if neg || matches!(self.b.get(self.i), Some(b'0'..=b'9')) { Err(()) } else { Ok(J::Int(0)) };
        }
        let mut n: i64 = 0;
        let mut digits = 0;
        while let Some(&c @ b'0'..=b'9') = self.b.get(self.i) {
            n = n * 10 + (c - b'0') as i64; // n <= 2^53 before: no overflow
            if n > MAX_INT {
                return Err(());
            }
            digits += 1;
            self.i += 1;
        }
        if digits == 0 {
            return Err(());
        }
        Ok(J::Int(if neg { -n } else { n }))
    }

    fn string(&mut self) -> Result<String, ()> {
        self.i += 1;
        let mut s = String::new();
        loop {
            let start = self.i;
            while let Some(&c) = self.b.get(self.i) {
                if c == b'"' || c == b'\\' || c < 0x20 {
                    break;
                }
                self.i += 1;
            }
            // a run between ASCII bytes: valid UTF-8 or the bytes are not JSON (Python decodes them first)
            s.push_str(core::str::from_utf8(&self.b[start..self.i]).map_err(|_| ())?);
            match self.b.get(self.i) {
                Some(b'"') => {
                    self.i += 1;
                    return Ok(s);
                }
                Some(b'\\') => {
                    let e = *self.b.get(self.i + 1).ok_or(())?;
                    self.i += 2;
                    s.push(match e {
                        b'"' => '"',
                        b'\\' => '\\',
                        b'b' => '\u{8}',
                        b'f' => '\u{c}',
                        b'n' => '\n',
                        b'r' => '\r',
                        b't' => '\t',
                        b'u' => {
                            // json.dumps writes \u00xx, lowercase, only for a control character with no short form
                            let h = self.b.get(self.i..self.i + 4).ok_or(())?;
                            let d = |c: u8| match c {
                                b'0'..=b'9' => Ok((c - b'0') as u32),
                                b'a'..=b'f' => Ok((c - b'a' + 10) as u32),
                                _ => Err(()),
                            };
                            let v = (d(h[0])? << 12) | (d(h[1])? << 8) | (d(h[2])? << 4) | d(h[3])?;
                            if v >= 0x20 || matches!(v, 0x08 | 0x09 | 0x0a | 0x0c | 0x0d) {
                                return Err(());
                            }
                            self.i += 4;
                            char::from_u32(v).ok_or(())?
                        }
                        _ => return Err(()),
                    });
                }
                _ => return Err(()),
            }
        }
    }
}

fn read(input: &[u8]) -> Result<J, ()> {
    // UTF-8 is checked run by run inside strings; outside them only ASCII parses
    let mut r = Reader { b: input, i: 0, deepest: 0 };
    let v = r.value(0)?;
    if r.i != input.len() {
        return Err(());
    }
    // jcs.loads refuses, before it parses, bytes holding more than 1024 '[' and '{' (inside strings too) whose
    // containers nest more than 256 deep, although canon writes a container 257 deep
    if r.deepest > MAX_DEPTH && input.iter().filter(|c| matches!(c, b'[' | b'{')).count() > MAX_DEPTH as usize * 4 {
        return Err(());
    }
    Ok(v)
}

// --- the values as Python sees them

fn get<'a>(o: &'a [(String, J)], k: &str) -> Option<&'a J> {
    o.iter().find(|(x, _)| x == k).map(|(_, v)| v)
}

fn obj(v: &J) -> Option<&[(String, J)]> {
    match v {
        J::Obj(o) => Some(o),
        _ => None,
    }
}

fn text(v: &J) -> Option<&str> {
    match v {
        J::Str(s) => Some(s),
        _ => None,
    }
}

/// Python's `==` on parsed JSON: True == 1 and False == 0, at any depth; a dict compares its members, not their order.
fn py_eq(a: &J, b: &J) -> bool {
    match (a, b) {
        (J::Null, J::Null) => true,
        (J::Bool(x), J::Bool(y)) => x == y,
        (J::Int(x), J::Int(y)) => x == y,
        (J::Bool(x), J::Int(y)) | (J::Int(y), J::Bool(x)) => *x as i64 == *y,
        (J::Str(x), J::Str(y)) => x == y,
        (J::Arr(x), J::Arr(y)) => x.len() == y.len() && x.iter().zip(y).all(|(p, q)| py_eq(p, q)),
        (J::Obj(x), J::Obj(y)) => x.len() == y.len() && x.iter().all(|(k, v)| get(y, k).is_some_and(|w| py_eq(v, w))),
        _ => false,
    }
}

/// records.is_list: a list whose items all pass; when sorted, equal to sorted(set(v)), so strictly increasing (the
/// items are strings wherever the engine asks for order, and str order is code point order, as Rust's).
fn is_list(v: &J, item: impl Fn(&J) -> bool, sorted: bool) -> bool {
    let J::Arr(xs) = v else { return false };
    xs.iter().all(item) && (!sorted || xs.windows(2).all(|w| matches!((&w[0], &w[1]), (J::Str(a), J::Str(b)) if a < b)))
}

fn hex64(v: &J) -> bool {
    matches!(v, J::Str(s) if s.len() == 64 && s.bytes().all(|c| matches!(c, b'0'..=b'9' | b'a'..=b'f')))
}

/// Cc: fixed by Unicode's stability policy.
fn control(c: char) -> bool {
    matches!(c as u32, 0..=0x1f | 0x7f..=0x9f)
}

/// Zs, Zl and Zp (shapes.EDGE_SPACE), as unicodedata 17.0.0 has them.
fn edge_space(c: char) -> bool {
    matches!(c as u32, 0x20 | 0xa0 | 0x1680 | 0x2000..=0x200a | 0x2028 | 0x2029 | 0x202f | 0x205f | 0x3000)
}

/// shapes.actor_problem(v) is None: a non-empty string of at most 200 code points, NFC, no Cc, no edge white space.
fn is_actor(v: &J) -> bool {
    let J::Str(s) = v else { return false };
    let n = s.chars().count();
    if n == 0 || n > 200 || !unicode_normalization::is_nfc(s) || s.chars().any(control) {
        return false;
    }
    !(s.chars().next().is_some_and(edge_space) || s.chars().next_back().is_some_and(edge_space))
}

/// records.guard_problem(g) is None.
fn guard_ok(g: &J) -> bool {
    let Some(o) = obj(g) else { return false };
    o.len() == 4
        && ["quorum", "roles", "match", "requires"].iter().all(|k| get(o, k).is_some())
        && matches!(get(o, "quorum"), Some(J::Int(q)) if *q >= 0)
        && is_list(get(o, "roles").unwrap(), is_actor, true)
        && obj(get(o, "match").unwrap()).is_some()
        && is_list(get(o, "requires").unwrap(), hex64, true)
}

const TYPES: [&str; 7] = ["str", "int", "bool", "strs", "ref", "refs", "obj"];

/// records.type_ok: a `?` admits null, once.
fn type_ok(t: &str, v: &J) -> bool {
    let t = match t.strip_suffix('?') {
        Some(_) if matches!(v, J::Null) => return true,
        Some(u) => u,
        None => t,
    };
    match t {
        "str" => matches!(v, J::Str(_)),
        "int" => matches!(v, J::Int(_)),
        "bool" => matches!(v, J::Bool(_)),
        "strs" => is_list(v, |x| matches!(x, J::Str(_)), false),
        "ref" => hex64(v),
        "refs" => is_list(v, hex64, false),
        "obj" => true,
        _ => false,
    }
}

/// engine._schema_problem(b) is None.
fn schema_ok(b: &J) -> bool {
    let Some(o) = obj(b) else { return false };
    let members = ["name", "fields", "states", "closed", "successors"];
    if !(members.iter().all(|k| get(o, k).is_some()) && o.iter().all(|(k, _)| members.contains(&k.as_str()) || k == "pinned")) {
        return false;
    }
    let fields = get(o, "fields").unwrap();
    let states = get(o, "states").unwrap();
    let state_names = obj(states);
    let name_ok = matches!(get(o, "name"), Some(J::Str(n)) if (1..=100).contains(&n.chars().count()) && n != "migration@1");
    let fields_ok = obj(fields).is_some_and(|f| f.iter().all(|(_, t)| text(t).is_some_and(|t| TYPES.contains(&t.trim_end_matches('?')))));
    let states_ok = matches!(states, J::Null)
        || (state_names.is_some()
            && matches!(obj(fields).and_then(|f| get(f, "state")), Some(J::Str(t)) if t == "str")
            && state_names.unwrap().iter().all(|(_, g)| matches!(g, J::Null) || guard_ok(g)));
    let in_states = |s: &str| state_names.is_some_and(|n| get(n, s).is_some());
    let closed_ok = is_list(get(o, "closed").unwrap(), |x| text(x).is_some_and(&in_states), true);
    let successors_ok = obj(get(o, "successors").unwrap())
        .is_some_and(|m| m.iter().all(|(st, rs)| in_states(st) && is_list(rs, is_actor, true)));
    let pinned_ok = match get(o, "pinned") {
        None => true,
        Some(J::Str(p)) => matches!(obj(fields).and_then(|f| get(f, p)), Some(J::Str(t)) if t == "obj" || t == "obj?"),
        Some(_) => false,
    };
    name_ok && fields_ok && states_ok && closed_ok && successors_ok && pinned_ok
}

// --- the reasons' text (engine.quote: json.dumps, ensure_ascii, no spaces, keys in code point order)

fn quote_str(out: &mut String, s: &str) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            ' '..='~' => out.push(c),
            _ => {
                let mut u = [0u16; 2];
                for unit in c.encode_utf16(&mut u) {
                    let _ = write!(out, "\\u{:04x}", unit);
                }
            }
        }
    }
    out.push('"');
}

fn quote_into(out: &mut String, v: &J) {
    match v {
        J::Null => out.push_str("null"),
        J::Bool(b) => out.push_str(if *b { "true" } else { "false" }),
        J::Int(n) => {
            let _ = write!(out, "{}", n);
        }
        J::Str(s) => quote_str(out, s),
        J::Arr(xs) => {
            out.push('[');
            for (i, x) in xs.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                quote_into(out, x);
            }
            out.push(']');
        }
        J::Obj(o) => {
            let mut ks: Vec<&(String, J)> = o.iter().collect();
            ks.sort_by(|a, b| a.0.cmp(&b.0));
            out.push('{');
            for (i, (k, x)) in ks.into_iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                quote_str(out, k);
                out.push(':');
                quote_into(out, x);
            }
            out.push('}');
        }
    }
}

fn quote_names(names: &[&str]) -> String {
    let mut out = String::from("[");
    for (i, n) in names.iter().enumerate() {
        if i > 0 {
            out.push(',');
        }
        quote_str(&mut out, n);
    }
    out.push(']');
    out
}

fn quote(v: &J) -> String {
    let mut out = String::new();
    quote_into(&mut out, v);
    out
}

// --- engine._body_problem and engine._weaker

fn strs<'a>(o: &'a [(String, J)], k: &str) -> Vec<&'a str> {
    match get(o, k) {
        Some(J::Arr(xs)) => xs.iter().filter_map(text).collect(),
        _ => Vec::new(),
    }
}

/// _weaker(g, need): g is null or a guard, need a guard.
fn weaker(g: &J, need: &[(String, J)]) -> bool {
    let Some(g) = obj(g) else { return true };
    let int = |o: &[(String, J)]| match get(o, "quorum") {
        Some(J::Int(q)) => *q,
        _ => 0,
    };
    let (gq, nq) = (int(g), int(need));
    let gm = obj(get(g, "match").unwrap()).unwrap();
    let nm = obj(get(need, "match").unwrap()).unwrap();
    gq < nq
        || (nq > 0 && !strs(g, "roles").iter().all(|r| strs(need, "roles").contains(r)))
        || nm.iter().any(|(k, v)| !get(gm, k).is_some_and(|w| py_eq(w, v)))
        || !strs(need, "requires").iter().all(|r| strs(g, "requires").contains(r))
}

fn body_problem(r: &[(String, J)], s: &[(String, J)]) -> (&'static str, Option<String>) {
    let b = obj(get(r, "body").unwrap()).unwrap();
    let kind = text(get(r, "kind").unwrap()).unwrap();
    let name = text(get(s, "name").unwrap()).unwrap();
    let mut f: Vec<(&str, &str)> =
        obj(get(s, "fields").unwrap()).unwrap().iter().map(|(k, t)| (k.as_str(), text(t).unwrap())).collect();
    if (kind == "attest" || kind == "challenge") && !f.iter().any(|(k, _)| *k == "target") {
        f.push(("target", "ref"));
    }
    let field = |k: &str| f.iter().find(|(x, _)| *x == k).map(|(_, t)| *t);
    let mut extra: Vec<&str> = b.iter().map(|(k, _)| k.as_str()).filter(|k| field(k).is_none()).collect();
    let mut missing: Vec<&str> =
        f.iter().filter(|(k, t)| !t.ends_with('?') && get(b, k).is_none()).map(|(k, _)| *k).collect();
    if !extra.is_empty() || !missing.is_empty() {
        extra.sort();
        missing.sort();
        let why = alloc::format!("members {} are not in {}, or {} are missing", quote_names(&extra), name, quote_names(&missing));
        return ("members", Some(why));
    }
    let bad: Vec<&str> = b.iter().filter(|(k, v)| !type_ok(field(k).unwrap(), v)).map(|(k, _)| k.as_str()).collect();
    if !bad.is_empty() {
        return ("types", Some(alloc::format!("members {} do not have their types in {}", quote_names(&bad), name)));
    }
    let refs: Vec<&str> = match get(r, "refs") {
        Some(J::Arr(xs)) => xs.iter().filter_map(text).collect(),
        _ => Vec::new(),
    };
    for (k, t) in &f {
        let named: Vec<&str> = match (t.trim_end_matches('?'), get(b, k)) {
            (_, None | Some(J::Null)) => Vec::new(),
            ("ref", Some(v)) => text(v).into_iter().collect(),
            ("refs", Some(J::Arr(xs))) => xs.iter().filter_map(text).collect(),
            _ => Vec::new(),
        };
        if !named.iter().all(|x| refs.contains(x)) {
            return ("refs", Some(String::from("a reference in the body is not in refs")));
        }
    }
    if kind != "entity" {
        return ("valid-not-entity", None);
    }
    let states = obj(get(s, "states").unwrap());
    let state = get(b, "state");
    let need = match (states, state) {
        (Some(st), Some(J::Str(x))) => get(st, x),
        _ => None,
    };
    let Some(need) = need else {
        let why = alloc::format!("state {} is not a state of {}", quote(state.unwrap_or(&J::Null)), name);
        return ("state", Some(why));
    };
    if let Some(need) = obj(need) {
        if weaker(get(r, "guard").unwrap(), need) {
            let why = alloc::format!("its guard is weaker than {}'s for state {}", name, quote(state.unwrap()));
            return ("guard", Some(why));
        }
    }
    ("valid", None)
}

// --- the two questions and the output

const MEMBERS: [&str; 10] = ["warrant", "kind", "actor", "at", "prev", "schema", "lineage", "refs", "guard", "body"];

/// The engine calls _body_problem only on such a pair (module documentation, -3).
fn asked(r: &J, s: &J) -> bool {
    let Some(o) = obj(r) else { return false };
    o.len() == MEMBERS.len()
        && MEMBERS.iter().all(|k| get(o, k).is_some())
        && matches!(text(get(o, "kind").unwrap()), Some("entity" | "attest" | "challenge"))
        && is_list(get(o, "refs").unwrap(), hex64, true)
        && obj(get(o, "body").unwrap()).is_some()
        && (matches!(get(o, "guard"), Some(J::Null)) || guard_ok(get(o, "guard").unwrap()))
        && schema_ok(s)
        && py_eq(get(o, "schema").unwrap(), get(obj(s).unwrap(), "name").unwrap())
}

fn jcs_str(out: &mut String, s: &str) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            '\u{0}'..='\u{1f}' => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            _ => out.push(c),
        }
    }
    out.push('"');
}

fn answer(input: &[u8]) -> Result<String, i32> {
    let v = read(input).map_err(|_| NOT_CANONICAL)?;
    let top = obj(&v).ok_or(NOT_AN_INPUT)?;
    let (code, why) = match top {
        [(k, b)] if k == "schema" => {
            if schema_ok(b) {
                ("counted", None)
            } else {
                ("not-counted", Some(String::from(
                    "a schema body is {name, fields: {member: type}, states: {state: guard|null}|null, closed, \
                     successors: {state: [roles]}, pinned?: a member of type obj}",
                )))
            }
        }
        [(k1, r), (k2, s)] if k1 == "record" && k2 == "schema" => {
            if !asked(r, s) {
                return Err(NOT_ASKED);
            }
            body_problem(obj(r).unwrap(), obj(s).unwrap())
        }
        _ => return Err(NOT_AN_INPUT),
    };
    let mut out = String::from("{\"code\":\"");
    out.push_str(code);
    out.push_str("\",\"reason\":");
    match &why {
        Some(w) => jcs_str(&mut out, w),
        None => out.push_str("null"),
    }
    out.push_str(if why.is_some() { ",\"verdict\":\"problem\"}" } else { ",\"verdict\":\"ok\"}" });
    Ok(out)
}
