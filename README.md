# minds / VARS-1

A hash-native graph of claims, computations and verdicts, stored in git, evaluated by a compiled lens.

- `VARS-1-SPEC.md` — the specification.
- `vars1.py` — reference implementation.
- `kernel/` — the rules compiled to `lens.wasm`: the authority fold and lens Passes 1–2 (Rust,
  `cargo build --release --target wasm32-unknown-unknown`; the build is reproducible and must hash to
  `H_LENS_KERNEL`). Scopes name these rules by hash; the host only parses, hashes and verifies signatures, and
  keeps a Python twin of the rules for differential checking.
- `proofs/` — Lean proofs of the fold, the lens and replay soundness.

## Running

The code expects sibling checkouts of [sigma-glyph](https://github.com/s0fractal/sigma-glyph) and
[primitives](https://github.com/s0fractal/primitives), and `node` for the wasm kernel:

```
git clone https://github.com/s0fractal/minds
git clone https://github.com/s0fractal/sigma-glyph
git clone https://github.com/s0fractal/primitives
cd minds
python3 -m unittest test_vars1          # conformance; every fold and lens runs kernel/lens.wasm and its twin
(cd proofs && lake build && lake build vars1exec && lake build Vars1Sigma)
python3 test_vars1_props.py             # property-based invariants I0–I9 (I9 needs proofs' vars1exec)
```

## Status

Experimental. The conformance suite, the property suite and the Lean proofs pass; the proofs' hypotheses and
unlinked parts are listed in `proofs/README.md`. There has been no independent review, the Radicle transport
of `refs/vars/*` is untested. The kernel's lens Passes 1–2 are differentially tested against a Lean-proved
executable lens; its fold is tested against a Python twin and spec oracles, not proved.

MIT licensed.
