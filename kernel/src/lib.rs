//! VARS-1 rules kernel: the authority fold of §4.1 over a scope's commit log, then Passes 1 and 2 of the lens (§4.2).
//!
//! The host only parses bytes, hashes and verifies Ed25519 signatures; every authorization decision is made here.
//!
//! Input (u32 little-endian words; `H` is 32 raw bytes):
//!
//! ```text
//! C  N  NK  P                      commits, cells, interned public keys, POL1 policies
//! P × { H id, threshold, m, key[m] }                    every well-formed POL1 atom with strong keys (key < NK)
//! N × { H id, H schema, H payload, H name, H loss, origin, birth, K, K × H slot,
//!       5 × { count, index[count] } }                   relies, attests, supersedes, retires, invalidates
//! S  S × { target, ctx, key, commit }                   seals whose signatures the host has verified
//! ```
//!
//! Cells are in forward topological order: every edge, and every payload or slot that is a cell id, names an older
//! (smaller) index born no later. `origin` 0 is the evaluated scope; `birth` and `commit` are the first commit (0-based,
//! `< C`) whose tree holds the object.
//!
//! Output, at the offset `run` returns: a u32 byte length, then the governing scope index (u32), `N` status bytes
//! (bit 0 accepted, 1 invalidated, 2 effective, 3 retired, 4 superseded, 5 active, 6 stale), `N` authority bytes
//! (bit 0: an Authorized scope, acceptance or schema cell), and one byte per invalidates, retires and supersedes edge,
//! cell by cell in that order (1 = authorized). A negative return is a malformed input (-1..-5) or a refusal of the
//! commit log by the fold (-10 and below).
#![no_std]

use core::arch::wasm32;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    wasm32::unreachable()
}

extern "C" {
    static __heap_base: u8;
}

static mut TOP: usize = 0;

unsafe fn bump(bytes: usize) -> *mut u8 {
    if TOP == 0 {
        TOP = core::ptr::addr_of!(__heap_base) as usize;
    }
    let p = (TOP + 7) & !7;
    let end = match p.checked_add(bytes) {
        Some(e) => e,
        None => return core::ptr::null_mut(),
    };
    let have = wasm32::memory_size(0) * 65536;
    if end > have && wasm32::memory_grow(0, (end - have + 65535) / 65536) == usize::MAX {
        return core::ptr::null_mut();
    }
    TOP = end;
    p as *mut u8
}

/// Forget every earlier allocation; call before each evaluation.
#[no_mangle]
pub extern "C" fn reset() {
    unsafe { TOP = 0 }
}

/// Reserve `len` bytes for the host to write the input into.
#[no_mangle]
pub extern "C" fn alloc(len: u32) -> u32 {
    unsafe { bump(len as usize) as u32 }
}

#[no_mangle]
pub extern "C" fn run(ptr: u32, len: u32) -> i32 {
    match unsafe { evaluate(core::slice::from_raw_parts(ptr as *const u8, len as usize)) } {
        Ok(p) => p,
        Err(e) => e,
    }
}

const MALFORMED: i32 = -1;
const BAD_EDGE: i32 = -2;
const NO_MEMORY: i32 = -3;
const NOT_MONOTONE: i32 = -4;
const NO_FIXED_POINT: i32 = -5;
// Refusals of the fold (§3 step 3 and §4.1).
const GENESIS_SCOPE: i32 = -10; // genesis must hold exactly one local scope cell, with empty eviction slots
const GENESIS_QUORUM: i32 = -11; // genesis scope lacks its admission quorum of self-seals
const SEAL_CONTEXT: i32 = -12; // a seal on a local cell names another context than the governing scope
const SEAL_KEY: i32 = -13; // a seal on a local cell is by a key outside the governing scope's policy
const CROSS_SEAL: i32 = -14; // a cross-seal on a foreign cell is not under the governing scope by a roster key
const UNSEALED: i32 = -15; // a new local cell has no seal under the governing scope
const POLICY_NOT_SUBSET: i32 = -16; // a local evaluator policy has keys outside the admission policy
const FOREIGN_UNSCOPED: i32 = -17; // a new foreign cell has no self-sealed scope of its origin
const SCOPE_MULTI: i32 = -18; // more than one new local scope cell in a commit
const SCOPE_SHAPE: i32 = -19; // a new scope does not supersede exactly the governing scope, or retires/invalidates
const SCOPE_QUORUM: i32 = -20; // a new scope lacks the governing admission quorum
const ACCEPTANCE_PIN: i32 = -21; // an acceptance names a foreign scope cell that is not self-sealed
const BINDING: i32 = -22; // §1.2 rule 6: a new local binding does not reach a prior binding of its name
const UNKNOWN_POLICY: i32 = -23; // a policy slot the fold needs is not a well-formed POL1

type H = [u8; 32];

const fn nib(c: u8) -> u8 {
    if c <= b'9' {
        c - b'0'
    } else {
        c - b'a' + 10
    }
}

const fn h(s: &str) -> H {
    let b = s.as_bytes();
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        out[i] = nib(b[2 * i]) << 4 | nib(b[2 * i + 1]);
        i += 1;
    }
    out
}

const H_EMPTY: H = h("f7607964cdb9f811072ded78efc20c622f54483eb7b101da5605329dc908872e");
const H_META_SCHEMA: H = h("7f0f250c08d367c8f2ba2c3b700f1a9bacbb44c240dade81c5c39c9ea7f9f15e");
const H_OWNER: H = h("4f97d7922a77cd279f75b8483542a9235330d4402ab15373e23c21bb7877905e");
const H_PROVISIONAL: H = h("b9d665ebd73a6d287e1e40b8c29cf2839d973b461511bfc7b0dd5623b9fe41e5");
const H_VERDICT_INVALID: H = h("b3966965c112d6d2613255fc018e34774dbc17c8517705b95946ea925b95096d");
const S_CONTRACT: H = h("391bbd2090d93f580fe033df9109cff948d46a07db24b9db05d55dc84e84277b");
const S_DECISION: H = h("5a48e9c69afc5c3cebb3ca2980052151f2aaa539052702e0e23f7ba5504eb6fb");
const S_QUESTION: H = h("1293a1513baa6e0e1edfdcf8c8f4b992efa1391ddbc0889efe9698d59c9b0cdf");
const S_ACCEPTANCE: H = h("c661936c020c0d817b8516b93454af5a30fe4282d854c1b0f628731c80f95d66");
const S_SCOPE: H = h("9aab50548f8fc7c5e2090fa89a73440af7de5e92d800b928261f13f20a4bd2a9");
const S_VERDICT: H = h("ad702699d5fc7b3d94138c38643c9889f1520a6e1c20760aa6b11a8e273dfdae");
const STANDARD: [H; 10] = [
    h("aaf70509e078bf1f833492eb82a116e4122232d424cf1668c05a9dd25855dcda"), // axiom
    S_CONTRACT,
    h("1c97bc0b74ffc978ade540c55592b294b0d9f2502b94b969f89ef00d99dd10bb"), // computation
    h("77655a8f5ca5b1c6347634e9a5848fdacee6efefd58569242d39f43410747639"), // checkpoint
    h("065f1b5b54fa199d65fb7f3e185e6f024d7523e829af1ad98269de018a8fb548"), // cycle_witness
    S_DECISION,
    S_QUESTION,
    S_ACCEPTANCE,
    S_SCOPE,
    S_VERDICT,
];

// Edge kinds, in input order.
const RELIES: usize = 0;
const SUP: usize = 2;
const RET: usize = 3;
const INV: usize = 4;

struct Reader<'a> {
    b: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn u32(&mut self) -> Result<u32, i32> {
        let s = self.b.get(self.at..self.at + 4).ok_or(MALFORMED)?;
        self.at += 4;
        Ok(u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
    }
    fn below(&mut self, lim: usize) -> Result<usize, i32> {
        let v = self.u32()? as usize;
        if v < lim {
            Ok(v)
        } else {
            Err(MALFORMED)
        }
    }
    fn h(&mut self) -> Result<&'a H, i32> {
        let s = self.b.get(self.at..self.at + 32).ok_or(MALFORMED)?;
        self.at += 32;
        Ok(s.try_into().unwrap())
    }
    /// Skip `count` words, returning the byte offset of the first.
    fn words(&mut self, count: usize) -> Result<usize, i32> {
        let at = self.at;
        let end = count.checked_mul(4).and_then(|n| at.checked_add(n)).ok_or(MALFORMED)?;
        if end > self.b.len() {
            return Err(MALFORMED);
        }
        self.at = end;
        Ok(at)
    }
}

fn word(b: &[u8], at: usize, i: usize) -> usize {
    let o = at + 4 * i;
    u32::from_le_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]]) as usize
}

unsafe fn arr<T: Copy>(len: usize, init: T) -> Result<&'static mut [T], i32> {
    let bytes = len.checked_mul(core::mem::size_of::<T>()).ok_or(NO_MEMORY)?;
    let p = bump(bytes) as *mut T;
    if p.is_null() {
        return Err(NO_MEMORY);
    }
    let s = core::slice::from_raw_parts_mut(p, len);
    s.fill(init);
    Ok(s)
}

#[derive(Clone, Copy)]
struct Cell {
    id: *const H,
    schema: *const H,
    payload: *const H,
    name: *const H,
    loss: *const H,
    origin: u32,
    birth: u32,
    k: u32,
    slots: usize,             // byte offset of slot 0
    edges: [(usize, u32); 5], // byte offset and count of each edge list
    lat: usize,               // index of this cell's first invalidates/retires/supersedes flag
}

const NO_CELL: Cell = Cell {
    id: core::ptr::null(),
    schema: core::ptr::null(),
    payload: core::ptr::null(),
    name: core::ptr::null(),
    loss: core::ptr::null(),
    origin: 0,
    birth: 0,
    k: 0,
    slots: 0,
    edges: [(0, 0); 5],
    lat: 0,
};

/// A POL1 policy: its id, threshold and key set (a bitset over interned keys).
#[derive(Clone, Copy)]
struct Pol {
    id: *const H,
    thr: u32,
    keys: usize, // offset into the policy key bitsets
}

/// Key sets are bitsets of `kw` words.
struct Sets {
    kw: usize,
}

impl Sets {
    fn count(&self, a: &[u32]) -> u32 {
        a.iter().map(|w| w.count_ones()).sum()
    }
    fn count_and(&self, a: &[u32], b: &[u32]) -> u32 {
        a.iter().zip(b).map(|(x, y)| (x & y).count_ones()).sum()
    }
    fn any_and(&self, a: &[u32], b: &[u32]) -> bool {
        a.iter().zip(b).any(|(x, y)| x & y != 0)
    }
    fn subset(&self, a: &[u32], b: &[u32]) -> bool {
        a.iter().zip(b).all(|(x, y)| x & !y == 0)
    }
    fn has(&self, a: &[u32], k: usize) -> bool {
        a[k / 32] >> (k % 32) & 1 != 0
    }
}

struct Graph<'a> {
    input: &'a [u8],
    cells: &'static [Cell],
    by_id: &'static [u32], // cell indices sorted by id
    pols: &'static [Pol],
    pol_keys: &'static [u32],
    sets: Sets,
    seal_start: &'static [u32], // seals grouped by target
    seal_ix: &'static [u32],
    seal_target: &'static [u32],
    seal_ctx: &'static [u32],
    seal_key: &'static [u32],
    seal_commit: &'static [u32],
}

impl Graph<'_> {
    fn c(&self, i: usize) -> &Cell {
        &self.cells[i]
    }
    fn hash(&self, p: *const H) -> &H {
        unsafe { &*p }
    }
    fn schema(&self, i: usize) -> &H {
        self.hash(self.c(i).schema)
    }
    fn slot(&self, i: usize, s: usize) -> Result<&H, i32> {
        let c = self.c(i);
        if s >= c.k as usize {
            return Err(MALFORMED);
        }
        Ok(self.input[c.slots + 32 * s..c.slots + 32 * s + 32].try_into().unwrap())
    }
    fn edge_count(&self, i: usize, k: usize) -> usize {
        self.c(i).edges[k].1 as usize
    }
    fn edge(&self, i: usize, k: usize, j: usize) -> usize {
        word(self.input, self.c(i).edges[k].0, j)
    }
    /// Index of the flag of edge `j` of kind `k` (INV, RET or SUP) of cell `i`.
    fn lat(&self, i: usize, k: usize, j: usize) -> usize {
        let c = self.c(i);
        match k {
            INV => c.lat + j,
            RET => c.lat + c.edges[INV].1 as usize + j,
            _ => c.lat + c.edges[INV].1 as usize + c.edges[RET].1 as usize + j,
        }
    }
    fn lookup(&self, id: &H) -> Option<usize> {
        self.by_id
            .binary_search_by(|&i| self.hash(self.cells[i as usize].id).cmp(id))
            .ok()
            .map(|p| self.by_id[p] as usize)
    }
    fn pol(&self, id: &H) -> Result<(u32, &[u32]), i32> {
        for p in self.pols {
            if self.hash(p.id) == id {
                return Ok((p.thr, &self.pol_keys[p.keys..p.keys + self.sets.kw]));
            }
        }
        Err(UNKNOWN_POLICY)
    }
    fn standard(&self, i: usize) -> bool {
        STANDARD.iter().any(|s| s == self.hash(self.c(i).id))
    }
    fn local(&self, i: usize) -> bool {
        self.c(i).origin == 0
    }
    fn is(&self, i: usize, schema: &H) -> bool {
        self.schema(i) == schema
    }
    /// Keys of seals on `u` admitted by commit `at`, under context `ctx`, with a key in `pks` (all keys if `None`).
    fn endorsers(&self, u: usize, ctx: usize, at: u32, pks: Option<&[u32]>, out: &mut [u32]) {
        out.fill(0);
        for s in self.seal_start[u] as usize..self.seal_start[u + 1] as usize {
            let s = self.seal_ix[s] as usize;
            let k = self.seal_key[s] as usize;
            if self.seal_ctx[s] as usize == ctx
                && self.seal_commit[s] <= at
                && pks.map_or(true, |p| self.sets.has(p, k))
            {
                out[k / 32] |= 1 << (k % 32);
            }
        }
    }
}

unsafe fn evaluate(input: &[u8]) -> Result<i32, i32> {
    let mut r = Reader { b: input, at: 0 };
    let commits = r.u32()?;
    let n = r.u32()? as usize;
    let nk = r.u32()? as usize;
    let np = r.u32()? as usize;
    if commits == 0 || n > input.len() || nk > input.len() || np > input.len() {
        return Err(MALFORMED);
    }
    let kw = (nk + 31) / 32;
    let sets = Sets { kw };

    let pols = arr(np, Pol { id: core::ptr::null(), thr: 0, keys: 0 })?;
    let pol_keys = arr(np * kw, 0u32)?;
    for (p, pol) in pols.iter_mut().enumerate() {
        pol.id = r.h()?;
        pol.thr = r.u32()?;
        pol.keys = p * kw;
        let m = r.u32()? as usize;
        if m > input.len() {
            return Err(MALFORMED);
        }
        for _ in 0..m {
            let k = r.below(nk)?;
            pol_keys[p * kw + k / 32] |= 1 << (k % 32);
        }
        let distinct: u32 = pol_keys[p * kw..p * kw + kw].iter().map(|w| w.count_ones()).sum();
        if pol.thr == 0 || pol.thr > distinct {
            return Err(MALFORMED);
        }
    }

    let cells = arr(n, NO_CELL)?;
    let mut lat_total = 0usize;
    for i in 0..n {
        let c = &mut cells[i];
        c.id = r.h()?;
        c.schema = r.h()?;
        c.payload = r.h()?;
        c.name = r.h()?;
        c.loss = r.h()?;
        c.origin = r.u32()?;
        c.birth = r.below(commits as usize)? as u32;
        c.k = r.u32()?;
        if c.k > 64 {
            return Err(MALFORMED);
        }
        c.slots = r.at;
        r.at = r.at.checked_add(32 * c.k as usize).ok_or(MALFORMED)?;
        if r.at > input.len() {
            return Err(MALFORMED);
        }
        for k in 0..5 {
            let count = r.u32()? as usize;
            let at = r.words(count)?;
            for j in 0..count {
                let v = word(input, at, j);
                // forward topological order, and a referenced cell is present whenever its referrer is
                if v >= i || cells[v].birth > cells[i].birth {
                    return Err(BAD_EDGE);
                }
            }
            cells[i].edges[k] = (at, count as u32);
        }
        let c = &mut cells[i];
        c.lat = lat_total;
        lat_total += (c.edges[INV].1 + c.edges[RET].1 + c.edges[SUP].1) as usize;
    }

    let ns = r.u32()? as usize;
    if ns > input.len() {
        return Err(MALFORMED);
    }
    let seal_target = arr(ns, 0u32)?;
    let seal_ctx = arr(ns, 0u32)?;
    let seal_key = arr(ns, 0u32)?;
    let seal_commit = arr(ns, 0u32)?;
    for s in 0..ns {
        let t = r.below(n)?;
        let x = r.below(n)?;
        seal_target[s] = t as u32;
        seal_ctx[s] = x as u32;
        seal_key[s] = r.below(nk)? as u32;
        seal_commit[s] = r.below(commits as usize)? as u32;
        if seal_commit[s] < cells[t].birth || seal_commit[s] < cells[x].birth {
            return Err(MALFORMED);
        }
    }
    if r.at != input.len() {
        return Err(MALFORMED);
    }
    let seal_start = arr(n + 1, 0u32)?;
    for s in 0..ns {
        seal_start[seal_target[s] as usize + 1] += 1;
    }
    for i in 0..n {
        seal_start[i + 1] += seal_start[i];
    }
    let seal_ix = arr(ns, 0u32)?;
    let fill = arr(n, 0u32)?;
    for s in 0..ns {
        let t = seal_target[s] as usize;
        seal_ix[(seal_start[t] + fill[t]) as usize] = s as u32;
        fill[t] += 1;
    }

    let by_id = arr(n, 0u32)?;
    for (i, x) in by_id.iter_mut().enumerate() {
        *x = i as u32;
    }
    by_id.sort_unstable_by(|&a, &b| (*cells[a as usize].id).cmp(&*cells[b as usize].id));
    for w in by_id.windows(2) {
        if *cells[w[0] as usize].id == *cells[w[1] as usize].id {
            return Err(MALFORMED);
        }
    }

    let g = Graph {
        input,
        cells,
        by_id,
        pols,
        pol_keys,
        sets,
        seal_start,
        seal_ix,
        seal_target,
        seal_ctx,
        seal_key,
        seal_commit,
    };
    let latched = arr(lat_total, 0u8)?;
    let auth = arr(n, 0u8)?;
    let scope = fold(&g, commits, latched, auth)?;
    lens(&g, scope, latched, auth)
}

/// §4.1 over every commit; returns the governing scope after the last commit.
unsafe fn fold(g: &Graph, commits: u32, latched: &mut [u8], auth: &mut [u8]) -> Result<usize, i32> {
    let n = g.cells.len();
    let kw = g.sets.kw;
    let initial = arr(n * kw, 0u32)?; // InitialEndorsers of local cells
    let self_sealed = arr(n, 0u8)?;
    let ends = arr(kw, 0u32)?;
    let ends_acc = arr(kw, 0u32)?;
    let mark = arr(n, 0u32)?;
    let stack = arr(n, 0u32)?;
    let mut stamp = 0u32;
    let local_scope = |i: usize| g.local(i) && g.is(i, &S_SCOPE);
    for i in 0..n {
        if g.standard(i) {
            auth[i] = 1;
        }
    }

    // Genesis: exactly one local scope cell S_0, with empty eviction slots, self-sealed to its admission quorum.
    let mut s0 = None;
    for i in 0..n {
        if g.c(i).birth == 0 && local_scope(i) {
            if s0.is_some() {
                return Err(GENESIS_SCOPE);
            }
            s0 = Some(i);
        }
    }
    let mut cur = s0.ok_or(GENESIS_SCOPE)?;
    if (SUP..=INV).any(|k| g.edge_count(cur, k) != 0) || g.hash(g.c(cur).loss) != &H_EMPTY {
        return Err(GENESIS_SCOPE);
    }
    {
        let (thr, adm) = g.pol(g.slot(cur, 0)?)?;
        g.pol(g.slot(cur, 1)?)?;
        g.endorsers(cur, cur, 0, Some(adm), ends);
        if g.sets.count(ends) < thr {
            return Err(GENESIS_QUORUM);
        }
        auth[cur] = 1;
    }

    for at in 0..commits {
        let present = |i: usize| g.c(i).birth <= at;
        let new = |i: usize| g.c(i).birth == at;
        let base = cur;
        let (adm_thr, adm) = g.pol(g.slot(base, 0)?)?;
        let (acc_thr, acc) = g.pol(g.slot(base, 1)?)?;

        // Self-sealed foreign scopes (sticky: seals are append-only).
        for f in 0..n {
            if present(f) && g.is(f, &S_SCOPE) && !g.local(f) {
                let (thr, pks) = g.pol(g.slot(f, 0)?)?;
                g.pol(g.slot(f, 1)?)?;
                g.endorsers(f, f, at, Some(pks), ends);
                if g.sets.count(ends) >= thr {
                    self_sealed[f] = 1;
                }
            }
        }

        // §3 step 3: every new seal on a local cell, and every cross-seal, is under S_base by a key of its policy.
        for s in 0..g.seal_ctx.len() {
            if g.seal_commit[s] != at {
                continue;
            }
            let (target, x, k) = (g.seal_target[s] as usize, g.seal_ctx[s] as usize, g.seal_key[s] as usize);
            if !g.local(target) && local_scope(x) && (x != base || !g.sets.has(adm, k)) {
                return Err(CROSS_SEAL);
            }
            if g.local(target) {
                if x != base {
                    return Err(SEAL_CONTEXT);
                }
                if !g.sets.has(adm, k) && !(g.is(target, &S_ACCEPTANCE) && g.sets.has(acc, k)) {
                    return Err(SEAL_KEY);
                }
            }
        }

        // Every new non-standard cell carries a seal: local under S_base, foreign under a self-sealed scope of its origin.
        for c in 0..n {
            if !new(c) || g.standard(c) {
                continue;
            }
            if g.local(c) {
                let init = &mut initial[c * kw..c * kw + kw];
                g.endorsers(c, base, at, None, init);
                if g.sets.count(init) == 0 {
                    return Err(UNSEALED);
                }
                let pol_slot = if g.is(c, &S_CONTRACT) || g.is(c, &S_DECISION) {
                    Some(g.slot(c, 3)?)
                } else if g.is(c, &S_QUESTION) {
                    Some(g.slot(c, 1)?)
                } else {
                    None
                };
                if let Some(p) = pol_slot {
                    if p != &H_EMPTY && !g.sets.subset(g.pol(p)?.1, adm) {
                        return Err(POLICY_NOT_SUBSET);
                    }
                }
            } else if !(0..n).any(|f| self_sealed[f] != 0 && present(f) && g.c(f).origin == g.c(c).origin) {
                return Err(FOREIGN_UNSCOPED);
            }
        }

        // At most one new local scope, superseding exactly S_base, sealed by S_base's admission quorum.
        let mut pending = None;
        if at > 0 {
            for s in 0..n {
                if !new(s) || !local_scope(s) {
                    continue;
                }
                if pending.is_some() {
                    return Err(SCOPE_MULTI);
                }
                g.pol(g.slot(s, 0)?)?;
                g.pol(g.slot(s, 1)?)?;
                if g.edge_count(s, SUP) != 1
                    || g.edge(s, SUP, 0) != base
                    || g.edge_count(s, RET) != 0
                    || g.edge_count(s, INV) != 0
                {
                    return Err(SCOPE_SHAPE);
                }
                g.endorsers(s, base, at, Some(adm), ends);
                if g.sets.count(ends) < adm_thr {
                    return Err(SCOPE_QUORUM);
                }
                pending = Some(s);
            }
        }

        // Latches 1 and 2: local acceptance pinned to a self-sealed foreign scope; local custom schema.
        for c in 0..n {
            if !present(c) || !g.local(c) || auth[c] != 0 {
                continue;
            }
            if g.is(c, &S_ACCEPTANCE) {
                match g.lookup(g.slot(c, 1)?) {
                    Some(f) if self_sealed[f] != 0 => {}
                    _ => return Err(ACCEPTANCE_PIN),
                }
                g.endorsers(c, base, at, Some(acc), ends);
                if g.sets.count(ends) >= acc_thr {
                    auth[c] = 1;
                }
            } else if g.is(c, &H_META_SCHEMA) {
                g.endorsers(c, base, at, Some(adm), ends);
                if g.sets.count(ends) >= adm_thr {
                    auth[c] = 1;
                }
            }
        }

        // Latch 3: edges w -> v under Pol_i(v), or by an author of a local v.
        for w in 0..n {
            if !present(w) || g.is(w, &H_META_SCHEMA) {
                continue;
            }
            g.endorsers(w, base, at, Some(adm), ends);
            g.endorsers(w, base, at, Some(acc), ends_acc);
            for kind in [INV, RET, SUP] {
                for j in 0..g.edge_count(w, kind) {
                    let e = g.lat(w, kind, j);
                    if latched[e] != 0 {
                        continue;
                    }
                    let v = g.edge(w, kind, j);
                    let contract = g.is(v, &S_CONTRACT) || g.is(v, &S_DECISION);
                    let (thr, pks, w_ends, author) = if g.is(v, &S_SCOPE) || (contract && g.slot(v, 0)? == &H_OWNER) {
                        (adm_thr, adm, &*ends, false)
                    } else if g.is(v, &S_ACCEPTANCE) {
                        (acc_thr, acc, &*ends_acc, false)
                    } else if contract && g.slot(v, 0)? == &H_PROVISIONAL {
                        let p = g.slot(v, 3)?;
                        let (t, k) = if p != &H_EMPTY { g.pol(p)? } else { (adm_thr, adm) };
                        (t, k, &*ends, true)
                    } else if g.is(v, &S_QUESTION) {
                        let p = g.slot(v, 1)?;
                        let (t, k) = if p != &H_EMPTY { g.pol(p)? } else { (adm_thr, adm) };
                        (t, k, &*ends, true)
                    } else {
                        (adm_thr, adm, &*ends, true)
                    };
                    let quorum = g.sets.count_and(w_ends, pks) >= thr;
                    let by_author = kind != INV
                        && author
                        && g.local(v)
                        && g.sets.any_and(w_ends, &initial[v * kw..v * kw + kw]);
                    if quorum || by_author {
                        latched[e] = 1;
                    }
                }
            }
        }

        // Latch 3b (§1.2 rule 6): a new local binding reaches every other local binding of its name.
        for c in 0..n {
            if !new(c) || g.standard(c) || !g.local(c) || g.is(c, &S_SCOPE) {
                continue;
            }
            for o in 0..n {
                if o == c || !present(o) || g.standard(o) || !g.local(o) || g.hash(g.c(o).name) != g.hash(g.c(c).name) {
                    continue;
                }
                stamp += 1;
                if reaches(g, latched, mark, stack, stamp, c, o) {
                    continue;
                }
                stamp += 1;
                if new(o) && reaches(g, latched, mark, stack, stamp, o, c) {
                    continue;
                }
                return Err(BINDING);
            }
        }

        // Latch 4: the new scope governs the next commit.
        if let Some(s) = pending {
            auth[s] = 1;
            cur = s;
        }
    }
    Ok(cur)
}

/// Does `dst` lie in `src`'s first supersedes hops, or beyond them along authorized supersedes edges?
fn reaches(g: &Graph, latched: &[u8], mark: &mut [u32], stack: &mut [u32], stamp: u32, src: usize, dst: usize) -> bool {
    let mut top = 0;
    for j in 0..g.edge_count(src, SUP) {
        let v = g.edge(src, SUP, j);
        if mark[v] != stamp {
            mark[v] = stamp;
            stack[top] = v as u32;
            top += 1;
        }
    }
    while top > 0 {
        top -= 1;
        let u = stack[top] as usize;
        if u == dst {
            return true;
        }
        for j in 0..g.edge_count(u, SUP) {
            let v = g.edge(u, SUP, j);
            if latched[g.lat(u, SUP, j)] != 0 && mark[v] != stamp {
                mark[v] = stamp;
                stack[top] = v as u32;
                top += 1;
            }
        }
    }
    false
}

/// Edges grouped by one endpoint: `start[k]..start[k+1]` indexes `other`.
struct Adj {
    start: &'static mut [u32],
    other: &'static mut [u32],
}

impl Adj {
    fn of(&self, k: usize) -> &[u32] {
        &self.other[self.start[k] as usize..self.start[k + 1] as usize]
    }
}

/// Group `pairs` (newer, older) by `older` when `by_older`, else by `newer`.
unsafe fn group(pairs: &[u32], n: usize, by_older: bool) -> Result<Adj, i32> {
    let count = pairs.len() / 2;
    let start = arr(n + 1, 0u32)?;
    let other = arr(count, 0u32)?;
    let fill = arr(n, 0u32)?;
    for i in 0..count {
        let key = if by_older { pairs[2 * i + 1] } else { pairs[2 * i] } as usize;
        start[key + 1] += 1;
    }
    for k in 0..n {
        start[k + 1] += start[k];
    }
    for i in 0..count {
        let (newer, older) = (pairs[2 * i], pairs[2 * i + 1]);
        let (key, val) = if by_older { (older, newer) } else { (newer, older) };
        other[(start[key as usize] + fill[key as usize]) as usize] = val;
        fill[key as usize] += 1;
    }
    Ok(Adj { start, other })
}

/// Passes 1 and 2 of §4.2 at the tip, over the authority the fold computed.
unsafe fn lens(g: &Graph, scope: usize, latched: &[u8], auth: &[u8]) -> Result<i32, i32> {
    let n = g.cells.len();
    let lat_total = latched.len();
    // flag bit 0: accepted unconditionally (local or standard); bit 1: every own supersedes edge authorized
    let flags = arr(n, 0u32)?;
    let unconditional = |i: usize| g.local(i) || g.standard(i);
    let mut caps = [0usize; 6];
    for i in 0..n {
        let all_sup = (0..g.edge_count(i, SUP)).all(|j| latched[g.lat(i, SUP, j)] != 0);
        flags[i] = unconditional(i) as u32 | (all_sup as u32) << 1;
        caps[0] += 1;
        caps[1] += (0..5).map(|k| g.edge_count(i, k)).sum::<usize>() + 1 + g.c(i).k as usize;
        caps[2] += g.edge_count(i, INV);
        caps[3] += g.edge_count(i, RET);
        caps[4] += g.edge_count(i, SUP);
        caps[5] += g.edge_count(i, RELIES);
    }
    let mut lists: [&'static mut [u32]; 6] = [&mut [], &mut [], &mut [], &mut [], &mut [], &mut []];
    let mut lens_ = [0usize; 6];
    for k in 0..6 {
        lists[k] = arr(2 * caps[k], 0u32)?;
    }
    let mut push = |k: usize, a: usize, b: usize, lists: &mut [&'static mut [u32]; 6]| {
        lists[k][2 * lens_[k]] = a as u32;
        lists[k][2 * lens_[k] + 1] = b as u32;
        lens_[k] += 1;
    };
    for w in 0..n {
        // acceptance: an Authorized acceptance and the cell it admits
        if g.is(w, &S_ACCEPTANCE) && auth[w] != 0 {
            if let Some(x) = g.lookup(g.hash(g.c(w).payload)) {
                if x >= w {
                    return Err(BAD_EDGE);
                }
                push(0, w, x, &mut lists);
            }
        }
        // hereditary: a foreign cell's references to cells of its own origin (edges, payload, slots)
        if !unconditional(w) {
            let same = |v: usize| !unconditional(v) && g.c(v).origin == g.c(w).origin;
            for k in 0..5 {
                for j in 0..g.edge_count(w, k) {
                    let v = g.edge(w, k, j);
                    if same(v) {
                        push(1, w, v, &mut lists);
                    }
                }
            }
            let c = g.c(w);
            for s in 0..=c.k as usize {
                let hsh = if s == 0 { g.hash(c.payload) } else { g.slot(w, s - 1)? };
                if let Some(v) = g.lookup(hsh) {
                    if v >= w {
                        return Err(BAD_EDGE);
                    }
                    if same(v) {
                        push(1, w, v, &mut lists);
                    }
                }
            }
        }
        let verdict_ok = !g.is(w, &S_VERDICT) || g.slot(w, 1)? == &H_VERDICT_INVALID;
        for j in 0..g.edge_count(w, INV) {
            if latched[g.lat(w, INV, j)] != 0 && verdict_ok {
                push(2, w, g.edge(w, INV, j), &mut lists);
            }
        }
        for (list, kind) in [(3, RET), (4, SUP)] {
            for j in 0..g.edge_count(w, kind) {
                if latched[g.lat(w, kind, j)] != 0 {
                    push(list, w, g.edge(w, kind, j), &mut lists);
                }
            }
        }
        for j in 0..g.edge_count(w, RELIES) {
            push(5, w, g.edge(w, RELIES, j), &mut lists);
        }
    }
    let mut adj: [Option<Adj>; 6] = [None, None, None, None, None, None];
    for k in 0..6 {
        adj[k] = Some(group(&lists[k][..2 * lens_[k]], n, k != 5)?);
    }
    let a = |k: usize| adj[k].as_ref().unwrap();
    let (acc_l, hered, inv_l, ret_l, sup_l, rel_l) = (0, 1, 2, 3, 4, 5);

    let total = 4 + n + n + lat_total;
    let out_all = arr(4 + total, 0u8)?;
    out_all[0..4].copy_from_slice(&(total as u32).to_le_bytes());
    out_all[4..8].copy_from_slice(&(scope as u32).to_le_bytes());
    let (_, rest) = out_all.split_at_mut(8);
    let (out, rest) = rest.split_at_mut(n);
    let (auth_out, edges_out) = rest.split_at_mut(n);
    auth_out.copy_from_slice(auth);
    edges_out.copy_from_slice(latched);
    let live = arr(n, 0u32)?;
    let (accepted, invalidated, effective, retired, superseded, active, stale) =
        (1u8, 2u8, 4u8, 8u8, 16u8, 32u8, 64u8);
    let has = |s: &[u8], i: usize, bit: u8| s[i] & bit != 0;

    // Pass 1, newest first: every edge into `v` comes from a newer cell, already final.
    for v in (0..n).rev() {
        let mut s = 0u8;
        let acc = flags[v] & 1 != 0
            || a(acc_l).of(v).iter().any(|&w| has(out, w as usize, active))
            || a(hered).of(v).iter().any(|&w| has(out, w as usize, accepted));
        if acc {
            s |= accepted;
        }
        let live_src = |w: u32| has(out, w as usize, effective) && has(out, w as usize, accepted);
        if a(inv_l).of(v).iter().any(|&w| live_src(w)) {
            s |= invalidated;
        } else {
            s |= effective;
        }
        if a(ret_l).of(v).iter().any(|&w| live_src(w)) {
            s |= retired;
        }
        if a(sup_l).of(v).iter().any(|&w| live_src(w) || has(out, w as usize, superseded)) {
            s |= superseded;
        }
        if s & effective != 0 && s & (retired | superseded) == 0 && acc && flags[v] & 2 != 0 {
            s |= active;
        }
        out[v] = s;
    }

    // Pass 2: least fixed point of Stale, by rounds (live acceptance newest first, then Stale oldest first).
    for _round in 0..=n {
        for v in (0..n).rev() {
            live[v] = (a(acc_l).of(v).iter().any(|&w| has(out, w as usize, active) && !has(out, w as usize, stale))
                || a(hered).of(v).iter().any(|&w| live[w as usize] != 0)) as u32;
        }
        let mut changed = false;
        for v in 0..n {
            let now = has(out, v, active)
                && (a(rel_l).of(v).iter().any(|&d| !has(out, d as usize, active) || has(out, d as usize, stale))
                    || (flags[v] & 1 == 0 && live[v] == 0));
            let was = has(out, v, stale);
            if now != was {
                if was {
                    return Err(NOT_MONOTONE);
                }
                out[v] |= stale;
                changed = true;
            }
        }
        if !changed {
            return Ok(out_all.as_ptr() as i32);
        }
    }
    Err(NO_FIXED_POINT)
}
