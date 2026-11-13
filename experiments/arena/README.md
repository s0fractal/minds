# The v2 kernel's arena on the stable `Allocator` (Rust 1.100): an experiment, not activated

Rust 1.100.0 (2026-11-12) stabilized custom allocators (`Allocator`, `Vec::new_in`, `Box::new_in`). The v2 rules
module (`kernel2/`, Rust 1.88.0) allocates from a hand-written bump arena:
- `static mut TOP`;
- `unsafe fn arr<T>() -> Result<&'static mut [T], i32>`, whose `'static` is not true;
- `unsafe fn` on every function that calls it.

Hypothesis: with `Vec<T, &Arena>` the lifetimes become real and `unsafe` shrinks to the arena and the host boundary.

`src/` is a copy of `kernel2/src` changed only in the arena:
- `Arena` implements `Allocator`: a bump over linear memory, 8-aligned as before, freeing nothing.
- `arr(arena, len, init)` is safe: `Vec::new_in`, then `try_reserve_exact`, where a failure is `NO_MEMORY` and never a trap, then `resize` and `leak`.
- `'static` becomes the arena's lifetime, and `fold`, `group` and `lens` are no longer `unsafe fn`.
- `evaluate` stays one: it dereferences the raw pointers into the input that `Cell` holds, a separate matter left as it was.
- `alloc` needs a `#[global_allocator]`; here it is a stub that refuses and is never used.

`kernel2/` itself, v1 and v1b are untouched. Nothing here is a rules identity.

## Measured once (2026-11-13), no target numbers

The modules:
- **A:** `kernel2/lens2.wasm`, Rust 1.88.0, the live v2 rules (1ca798b5).
- **B:** the same source built with Rust 1.100.0 (0b1138b5): the compiler alone.
- **C:** this arena, Rust 1.100.0 (423b8389).

| | A (live) | B | C |
|---|---|---|---|
| wasm bytes | 24 802 | 24 604 (−0.8%) | 26 119 (+5.3% on A, +6.2% on B) |
| imports | none | none | none |
| exports beyond `memory`, `reset`, `alloc`, `run` | `__heap_base`, `__data_end` | none | none |
| lines with `unsafe` | 10 | 10 | 13 |
| `unsafe fn` / `unsafe impl` / `unsafe {}` | 6 / 0 / 4 | same | 4 / 2 / 7 |
| source lines inside an unsafe context | 662 of 1141 | same | 198 of 1178 (175 of them `evaluate`, input pointers) |
| `'static` borrows that are not | 15 | 15 | 0 |
| steps (`meter.py`), sum over the 102 tips of the live chain | 804 960 138 | 800 329 042 (−0.58%) | 801 554 536 (−0.42% on A, +0.15% on B) |
| steps at the tip (3c599f18) | 33 631 796 | 33 466 967 | 33 500 599 |
| outputs equal to A on the 102 tips, encoded for v2 (`equal.py chain`, and again under the meter) | — | yes | yes |
| outputs equal to A on every v2 input of the property suite (`equal.py props`: 1 456 inputs, 24 refusals; the suite's 10 tests OK) | — | yes | yes |
| warnings under 1.100 (never type fallback now `!` on every edition) | — | none | none |

Controls:
- `kernel2/lens2-test-variant.wasm` differs from A on 61 of the 102 tips and on 888 of the 1 456 suite inputs: the comparison bites.
- The size growth comes from `alloc`'s `Vec`. Without `resize` (written through `spare_capacity_mut` and `set_len`, one more `unsafe`), C is 25 553 bytes (+3.9% on B). What remains is `RawVec`'s reserve path.

Kani:
- v2 has no harnesses; the three of `kernel/assure.sh` are v1's. So "the same harnesses" does not apply here.
- `kani-check/` is the same `arr` over an arena whose memory is a 64-byte buffer. Its harness: two arrays of any lengths up to 12 are each either refused with `NO_MEMORY` or filled exactly, and never overlap.
- Kani 0.68.0 pins `rustc 1.100.0-nightly (2026-08-20)`, where `allocator_api` is still unstable. Without `#![cfg_attr(kani, feature(allocator_api))]` it does not compile.
- With that attribute: VERIFICATION SUCCESSFUL, 22.6 s, peak RSS 2.36 GB, one harness at a time under the watchdog of `kernel/assure.sh`.
- A mutant using the infallible `reserve_exact` fails: VERIFICATION FAILED, 3.0 GB. It is killed by Kani's check on the unsupported `__rust_alloc_error_handler` call, reached only when an allocation fails, not by the harness's own assertion.

Linking:
- `--allow-undefined` is no longer passed on wasm targets since Rust 1.96.0. A module with an undefined symbol now fails to link rather than importing it.
- All three modules import nothing. `__heap_base` is still defined by the linker: C reads it and links.
- Since 1.100 it is no longer exported. No host here reads it: `kernel/run.mjs`, `run_metered.mjs`, `vars1.py`, `meter.py` and `verify/`.
- `cfg_select!` (stable since 1.95) has nothing to replace in v2. The repeated `#[cfg(not(any(kani, fuzzing)))]` are v1's.

## Verdict

The gain is real and costs little at run time:
- the unsafe context goes from 662 lines to 198 (23 for the arena and the host);
- no `'static` lies;
- outputs are byte-identical on 102 tips and 1 456 suite inputs;
- steps are within 0.15% of the same compiler.

It is not free:
- the wasm is 6.2% larger;
- `alloc` wants a stub global allocator;
- Kani verifies it only with a feature gate until its toolchain passes 1.100.

None of the stop rule's conditions holds outright: equality holds, steps did not grow beyond the compiler's own change, Kani verifies, and +6% is a cost rather than a break. So nothing is stopped, and nothing is activated either. Making it rules is a separate decision; the section below says what it would take.

## What a first live change of the class "implementation-equivalent" would be (not done)

VARS-1-SPEC.md §4.3: other bytes, the same output over the chain so far.
1. **The module.** It goes beside `kernel2/` with its own pinned toolchain, and is rebuilt by the release checks (`KERNELS` in `tools/minds_chain.py`), so a fresh checkout needs both 1.88.0 and 1.100.0. Its hash is a new rules identity.
2. **The registrations.**
   - `vars1.py` `RULES` gets a row: the module, encoding `v2`, the same resource codes `{-7}` and rotation delay 16.
   - `verify/minds_verify.py` `KNOWN_RULES_TABLE` gets a row `<id> v2 <name>`. The offline verifier reads the encoding by name and executes nothing, so a projection naming the new id reads as v2. `vars1.py` refuses to load unless both tables agree.
3. **The act.**
   - `minds_chain.py shadow <id>` must list no difference at any tip.
   - Then `change-rules equivalent <id> --manifest`. The decision carries `old_rules`, `new_rules`, `basis` and `reproduce` = SHA-256(SHA-256(old output) ‖ SHA-256(new output)), and the gate replays it.
   - It is sealed under the scope's admission quorum: 1 today, 2 after `threshold 2`, which then needs the second seal the witness does not give (M2).
   - Under v2 the rotation governs only after 16 commits (§4.1 latch 4a).
4. **What it would not establish.** Equivalence beyond the chain and the property corpus (AMENDMENTS.md, Open).
   - One difference is known by construction: `Vec` refuses a single array above `isize::MAX` bytes (2 GiB on wasm32) before asking for memory.
   - The hand-written arena would ask `memory_grow`, up to 4 GiB.
   - So on an input that needs such an array and a host that grants it, A could answer where C refuses with `NO_MEMORY`.
