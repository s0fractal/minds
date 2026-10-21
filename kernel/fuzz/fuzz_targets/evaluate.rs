//! Any bytes into the rules kernel's `evaluate`: no panic, no out-of-bounds access, no arithmetic overflow (debug
//! assertions are on), and a result that is an output (0) or a known refusal code. The kernel source is included
//! as a module, so the kernel crate itself is unchanged.
//!
//! Inputs claiming more than 4096 commits are skipped: the fold visits every commit, and the commit count is the
//! one count the kernel does not bound by the input's length, so such inputs only measure that known limit
//! (ASSURANCE.md); the host supplies the count from its own chain.
#![no_main]
use libfuzzer_sys::fuzz_target;

#[path = "../../src/lib.rs"]
#[allow(dead_code, unused_attributes, static_mut_refs)]
mod kernel;

fuzz_target!(|data: &[u8]| {
    if data.len() >= 4 && u32::from_le_bytes([data[0], data[1], data[2], data[3]]) > 4096 {
        return;
    }
    let r = kernel::fuzz_evaluate(data);
    assert!(r == 0 || (-5..=-1).contains(&r) || (-23..=-10).contains(&r), "unknown result {r}");
});
