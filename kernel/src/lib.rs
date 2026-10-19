//! VARS-1 lens kernel: Pass 1 and Pass 2 of the status algebra over facts the host has already checked.
//!
//! Input (u32 little-endian words): `n`, `flags[n]`, then six edge lists, each `count` followed by `count`
//! pairs `(newer, older)` of cell indices in forward topological order (`newer > older` is required):
//! acceptance (a, x), hereditary (y, x), invalidates (w, v), retires (w, v), supersedes (w, v), relies (v, d).
//! `flags`: bit 0 = accepted without acceptance (local or intrinsic schema), bit 1 = all own supersedes
//! edges authorized. Output: `n` status bytes, bit 0 accepted, 1 invalidated, 2 effective, 3 retired,
//! 4 superseded, 5 active, 6 stale. `run` returns the output offset, or a negative error code.
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

const MALFORMED: i32 = -1;
const BAD_EDGE: i32 = -2;
const NO_MEMORY: i32 = -3;
const NOT_MONOTONE: i32 = -4;
const NO_FIXED_POINT: i32 = -5;

const ACC: usize = 0;
const HERED: usize = 1;
const INV: usize = 2;
const RET: usize = 3;
const SUP: usize = 4;
const RELIES: usize = 5;

struct Words<'a> {
    w: &'a [u8],
    at: usize,
}

impl Words<'_> {
    fn next(&mut self) -> Option<u32> {
        let b = self.w.get(self.at..self.at + 4)?;
        self.at += 4;
        Some(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }
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

unsafe fn slice(len: usize) -> Option<&'static mut [u32]> {
    let p = bump(len * 4) as *mut u32;
    if p.is_null() {
        return None;
    }
    let s = core::slice::from_raw_parts_mut(p, len);
    s.fill(0);
    Some(s)
}

/// Group `pairs` (newer, older) by `older` when `by_older`, else by `newer`.
unsafe fn group(pairs: &[u8], count: usize, n: usize, by_older: bool) -> Option<Adj> {
    let start = slice(n + 1)?;
    let other = slice(count)?;
    let pair = |i: usize| {
        let b = &pairs[i * 8..i * 8 + 8];
        let a = u32::from_le_bytes([b[0], b[1], b[2], b[3]]) as usize;
        let c = u32::from_le_bytes([b[4], b[5], b[6], b[7]]) as usize;
        (a, c)
    };
    for i in 0..count {
        let (newer, older) = pair(i);
        let key = if by_older { older } else { newer };
        start[key + 1] += 1;
    }
    for k in 0..n {
        start[k + 1] += start[k];
    }
    let fill = slice(n)?;
    for i in 0..count {
        let (newer, older) = pair(i);
        let (key, val) = if by_older { (older, newer) } else { (newer, older) };
        other[(start[key] + fill[key]) as usize] = val as u32;
        fill[key] += 1;
    }
    Some(Adj { start, other })
}

#[no_mangle]
pub extern "C" fn run(ptr: u32, len: u32) -> i32 {
    unsafe { evaluate(core::slice::from_raw_parts(ptr as *const u8, len as usize)) }
}

unsafe fn evaluate(input: &[u8]) -> i32 {
    let mut words = Words { w: input, at: 0 };
    let n = match words.next() {
        Some(n) => n as usize,
        None => return MALFORMED,
    };
    let flags_at = words.at;
    if input.len() < flags_at + n * 4 {
        return MALFORMED;
    }
    words.at += n * 4;
    let flag = |i: usize| {
        let b = &input[flags_at + i * 4..flags_at + i * 4 + 4];
        u32::from_le_bytes([b[0], b[1], b[2], b[3]])
    };

    let mut lists: [(usize, usize); 6] = [(0, 0); 6];
    for list in lists.iter_mut() {
        let count = match words.next() {
            Some(c) => c as usize,
            None => return MALFORMED,
        };
        let at = words.at;
        if input.len() < at + count * 8 {
            return MALFORMED;
        }
        for i in 0..count {
            let b = &input[at + i * 8..at + i * 8 + 8];
            let newer = u32::from_le_bytes([b[0], b[1], b[2], b[3]]) as usize;
            let older = u32::from_le_bytes([b[4], b[5], b[6], b[7]]) as usize;
            if newer >= n || older >= newer {
                return BAD_EDGE;
            }
        }
        *list = (at, count);
        words.at = at + count * 8;
    }
    if words.at != input.len() {
        return MALFORMED;
    }

    let mut adj: [Option<Adj>; 6] = [None, None, None, None, None, None];
    for (k, &(at, count)) in lists.iter().enumerate() {
        adj[k] = group(&input[at..], count, n, k != RELIES);
        if adj[k].is_none() {
            return NO_MEMORY;
        }
    }
    let a = |k: usize| adj[k].as_ref().unwrap();

    let out = bump(n);
    let marks = slice(n);
    if out.is_null() || marks.is_none() {
        return NO_MEMORY;
    }
    let out = core::slice::from_raw_parts_mut(out, n);
    let live = marks.unwrap();
    out.fill(0);
    let (accepted, invalidated, effective, retired, superseded, active, stale) =
        (1u8, 2u8, 4u8, 8u8, 16u8, 32u8, 64u8);
    let has = |s: &[u8], i: usize, bit: u8| s[i] & bit != 0;

    // Pass 1, newest first: every edge into `v` comes from a newer cell, already final.
    for v in (0..n).rev() {
        let mut s = 0u8;
        let acc = flag(v) & 1 != 0
            || a(ACC).of(v).iter().any(|&w| has(out, w as usize, active))
            || a(HERED).of(v).iter().any(|&w| has(out, w as usize, accepted));
        if acc {
            s |= accepted;
        }
        let live_src = |w: u32| has(out, w as usize, effective) && has(out, w as usize, accepted);
        if a(INV).of(v).iter().any(|&w| live_src(w)) {
            s |= invalidated;
        } else {
            s |= effective;
        }
        if a(RET).of(v).iter().any(|&w| live_src(w)) {
            s |= retired;
        }
        if a(SUP).of(v).iter().any(|&w| live_src(w) || has(out, w as usize, superseded)) {
            s |= superseded;
        }
        if s & effective != 0 && s & (retired | superseded) == 0 && acc && flag(v) & 2 != 0 {
            s |= active;
        }
        out[v] = s;
    }

    // Pass 2: least fixed point of Stale, by rounds (live acceptance newest first, then Stale oldest first).
    for _round in 0..=n {
        for v in (0..n).rev() {
            live[v] = (a(ACC).of(v).iter().any(|&w| has(out, w as usize, active) && !has(out, w as usize, stale))
                || a(HERED).of(v).iter().any(|&w| live[w as usize] != 0)) as u32;
        }
        let mut changed = false;
        for v in 0..n {
            let now = has(out, v, active)
                && (a(RELIES).of(v).iter().any(|&d| !has(out, d as usize, active) || has(out, d as usize, stale))
                    || (flag(v) & 1 == 0 && live[v] == 0));
            let was = has(out, v, stale);
            if now != was {
                if was {
                    return NOT_MONOTONE;
                }
                out[v] |= stale;
                changed = true;
            }
        }
        if !changed {
            return out.as_ptr() as i32;
        }
    }
    NO_FIXED_POINT
}
