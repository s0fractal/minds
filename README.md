# minds / VARS-1

A hash-native graph of claims, computations and verdicts, stored in git, evaluated by a compiled lens.

- `VARS-1-SPEC.md` — the specification.
- `vars1.py` — reference implementation.
- `kernel/` — the lens rules compiled to `lens.wasm` (Rust, `cargo build --release --target wasm32-unknown-unknown`;
  the build is reproducible and must hash to `H_LENS_KERNEL`). Scopes name these rules by hash.
- `proofs/` — Lean proofs of the fold, the lens and replay soundness.

## Running

The code expects sibling checkouts of [sigma-glyph](https://github.com/s0fractal/sigma-glyph) and
[primitives](https://github.com/s0fractal/primitives), and `node` for the wasm kernel:

```
git clone https://github.com/s0fractal/minds
git clone https://github.com/s0fractal/sigma-glyph
git clone https://github.com/s0fractal/primitives
cd minds
python3 -m unittest test_vars1          # conformance; every lens is checked against kernel/lens.wasm
python3 test_vars1_props.py             # property-based invariants I0–I8
cd proofs && lake build && lake build Vars1Sigma
```

## Status

Experimental. The conformance suite, the property suite and the Lean proofs pass; the proofs' hypotheses and
unlinked parts are listed in `proofs/README.md`. There has been no independent review, the Radicle transport
of `refs/vars/*` is untested, and `vars1.py` is not refined against the Lean model.

MIT licensed.
