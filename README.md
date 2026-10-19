# minds / VARS-1

A hash-native graph of claims, computations and verdicts, stored in git, evaluated by a compiled lens.

- `VARS-1-SPEC.md` — the specification.
- `vars1.py` — reference implementation.
- `kernel/` — the rules compiled to `lens.wasm`: the authority fold and lens Passes 1–2 (Rust,
  `cargo build --release --target wasm32-unknown-unknown`; the build is reproducible and must hash to
  `H_LENS_KERNEL`). Scopes name these rules by hash; the host only parses, hashes and verifies signatures, and
  keeps a Python twin of the rules for differential checking.
- `proofs/` — Lean proofs of the fold, the lens and replay soundness.
- `tools/radicle-probe.sh` — checks that Radicle replicates `refs/vars/*`, with two nodes on localhost only.
- `tools/minds_chain.py` — minds governs itself with VARS-1 (below).

## Self-governance

This repository keeps its own chain, `refs/vars/heads/minds` (pushed to GitHub alongside `main`). Each release is a
`decision` naming `main@<sha>`, the rules kernel and the checks that passed, attested by the maintainer's key, with a
witnessed projection of the chain. `tools/minds_chain.py release` refuses unless HEAD is `main`, the tree is clean
before and after the checks, and every check passes;
`tools/minds_chain.py show` lists releases; `tools/minds_chain.py bundle <projection>` gives a bundle for
`vars1.py verify-projection`; `tools/minds_chain.py attest <decision>` gives a bundle for `vars1.py
verify-attestation`, with the latest projection that covers the release; a client accepts a release only from a
witnessed projection's complete evidence, so the latest release is accepted once the next one covers it. The
maintainer key never leaves `.git/vars/`. Today the roster, the evaluator and the projection witness are that one
key: the chain shows what the maintainer claimed and when, not that anyone else checked it.

## Running

The code expects sibling checkouts of [sigma-glyph](https://github.com/s0fractal/sigma-glyph) and
[primitives](https://github.com/s0fractal/primitives), and `node` for the wasm kernel:

```
git clone https://github.com/s0fractal/minds
git clone https://github.com/s0fractal/sigma-glyph
git clone https://github.com/s0fractal/primitives
cd minds
python3 -m unittest test_vars1          # conformance; every fold and lens runs kernel/lens.wasm and its twin
(cd proofs && lake build && lake build vars1exec && lake build vars1fold && lake build Vars1Sigma)
python3 test_vars1_props.py             # property-based invariants I0–I10 (I9, I10 need the proofs' executables)
python3 vars1.py verify-projection BUNDLE.json   # check a projection with no repository (spec §4.4)
```

## Status

Experimental. The conformance suite, the property suite and the Lean proofs pass; the proofs' hypotheses and
unlinked parts are listed in `proofs/README.md`. There has been no independent review. Radicle replicates
`refs/vars/*` signed and with history (`tools/radicle-probe.sh`, two local nodes, rad 1.10.3). The kernel is differentially tested against the Lean side: its lens Passes 1–2
against an executable lens proved equal to the model, and its fold against the model's own fold, compiled. The
Rust/wasm code itself is not proved.

MIT licensed.
