//! Can Kani verify code on the stable `Allocator` API (Rust 1.100)? The `arr` of experiments/arena/src/lib.rs, over
//! an arena whose memory is a fixed buffer instead of wasm linear memory (the only part that differs).
#![no_std]
#![cfg_attr(kani, feature(allocator_api))] // Kani 0.68 pins nightly-2026-08-20, before the stabilization in 1.100
extern crate alloc;

use alloc::vec::Vec;
use core::alloc::{AllocError, Allocator, Layout};
use core::cell::{Cell, UnsafeCell};
use core::ptr::NonNull;

const NO_MEMORY: i32 = -3;
const CAP: usize = 64;

#[repr(align(8))]
pub struct Arena {
    mem: UnsafeCell<[u8; CAP]>,
    top: Cell<usize>,
}

impl Arena {
    pub fn new() -> Arena {
        Arena { mem: UnsafeCell::new([0; CAP]), top: Cell::new(0) }
    }
    fn bump(&self, bytes: usize) -> Option<usize> {
        let p = (self.top.get() + 7) & !7;
        let end = p.checked_add(bytes)?;
        if end > CAP {
            return None;
        }
        self.top.set(end);
        Some(p)
    }
}

// SAFETY: each block is a fresh range of the buffer past every earlier one, never handed out twice.
unsafe impl Allocator for Arena {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        if layout.align() > 8 {
            return Err(AllocError);
        }
        let off = self.bump(layout.size()).ok_or(AllocError)?;
        let p = unsafe { (self.mem.get() as *mut u8).add(off) };
        Ok(NonNull::slice_from_raw_parts(NonNull::new(p).ok_or(AllocError)?, layout.size()))
    }
    unsafe fn deallocate(&self, _: NonNull<u8>, _: Layout) {}
}

pub fn arr<'a, T: Copy>(a: &'a Arena, len: usize, init: T) -> Result<&'a mut [T], i32> {
    let mut v = Vec::new_in(a);
    v.try_reserve_exact(len).map_err(|_| NO_MEMORY)?;
    v.resize(len, init);
    Ok(v.leak())
}

#[cfg(kani)]
mod proofs {
    use super::*;

    /// Two arrays of any lengths up to 12: each is either refused with NO_MEMORY (never a trap) or holds exactly its
    /// length of its own value, and the two never overlap.
    #[kani::proof]
    #[kani::unwind(14)]
    fn arr_fills_or_refuses() {
        let a = Arena::new();
        let n: usize = kani::any();
        let m: usize = kani::any();
        kani::assume(n <= 12 && m <= 12);
        let x = arr(&a, n, 7u32);
        let y = arr(&a, m, 9u32);
        match (x, y) {
            (Ok(x), Ok(y)) => {
                assert!(x.len() == n && y.len() == m);
                assert!(x.iter().all(|&v| v == 7) && y.iter().all(|&v| v == 9));
                let (xs, ys) = (x.as_ptr() as usize, y.as_ptr() as usize);
                assert!(n == 0 || m == 0 || xs + 4 * n <= ys || ys + 4 * m <= xs);
            }
            (Err(e), _) | (_, Err(e)) => assert!(e == NO_MEMORY),
        }
    }
}
