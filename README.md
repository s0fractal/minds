# minds / VARS-1

A hash-native graph of claims, computations and verdicts, stored in git, evaluated by a compiled lens.

- `VARS-1-SPEC.md` — the specification.
- `vars1.py` — reference implementation.
- `kernel/` — the rules compiled to `lens.wasm`: the authority fold and lens Passes 1–2 (Rust,
  `cargo build --release --target wasm32-unknown-unknown`; the build is reproducible and must hash to
  `H_LENS_KERNEL`). Scopes name these rules by hash; the host only parses, hashes and verifies signatures, and
  keeps a Python twin of the rules for differential checking.
- `kernel2/` — the v2 rules (`lens2.wasm`, `H_LENS_KERNEL_V2`): typed cell references, the commit bound, the
  rotation delay and the rules-change quarantine (`RULES-V2.md`). v1 is the default for a new genesis, and a scope
  moves to v2 only by a rotation with a rules-change decision whose computations the gate replays (spec §4.3).
  `refs/vars/heads/minds` moved to v2 on 2026-10-28.
- `kernel/lens1b.wasm` — the v1b rules (`H_LENS_KERNEL_V1B`, `kernel/` built with `--features commit-bound`): v1 with
  the commit count bounded by the input's length. Dormant; reached by a resource hardening, never from v2.
- `AMENDMENTS.md` — the classes of rules change (semantic correction, resource hardening, validation tightening,
  implementation-equivalent), step budgets (`meter.py`), evidence that travels, and the shadow replay before a rotation.
- `proofs/` — Lean proofs of the fold, the lens and replay soundness.
- `ASSURANCE.md` — what is proved, model-checked (Kani), differentially tested or assumed, claim by claim.
- `claims.json`, `mutants.json` — every normative block of the spec quoted, with the witnesses that hold it and the
  mutants they must kill (`tools/check_claims.py`, `tools/run_mutants.py`; both in CI).
- `REVIEWING.md` — what a reviewer does, from the code rather than from the maintainer's summaries.
- `tools/radicle-probe.sh` — checks that Radicle replicates `refs/vars/*`, with two nodes on localhost only.
- `tools/minds_chain.py` — minds governs itself with VARS-1 (below).
- `tools/bench_chain.py` — how admission and `lens()` cost grows with chain length (cold and warm instance).

## Self-governance

This repository keeps its own chain, `refs/vars/heads/minds` (pushed to GitHub alongside `main`). Each release is a
`decision` naming `main@<sha>`, the rules kernel, the release profile (the SHA-256 of the bytes of every file
that commit tracks: `tools/minds_chain.py profile <sha>`) and the checks that passed, attested by the maintainer's key, with a
witnessed projection of the chain. `tools/minds_chain.py release` refuses unless HEAD is `main` and the tree is
clean, before and after; it runs every check on that commit in a fresh worktree, so nothing left from earlier builds
counts. `tools/minds_chain.py show` lists releases; `status` says, read only, whether `main` is released and which
members have not yet attested each release or witnessed each projection (merged is not Settled); `bundle <projection>` gives a bundle for `vars1.py
verify-projection`; `attest <decision>` gives one for `vars1.py verify-attestation`, with the latest witnessed
projection that covers the release. A client accepts a release only from a witnessed projection's complete
evidence, so the latest release is accepted once a later projection covers it.

Member keys never leave `.git/vars/`. The roster has two members, Claude (the maintainer) and antigravity, both
AI agents on the same machine and OS account: their keys separate who signed, not who could have.

| member | Ed25519 public key |
| --- | --- |
| Claude (maintainer) | `dd5dd02da0d9644bcc9e6f6efead92363e8eb45cab3c5efe93f85d7b5ecaa12a` |
| antigravity | `a723e3c4779131b08ca18d0698c8111807db34caf258cd71ec240fd8c0427be7` |

Any one member may admit cells, including a scope rotation, so one member could rotate the other out and release
alone after that. To give both a veto, pin both keys when you verify:
`vars1.py verify-attestation BUNDLE.json --require <key> --require <key>`.

`join PUBKEY NAME` adds a member; from then on every release needs a verdict and a projection seal from every
member. A member runs `tools/minds_chain.py verify-release <decision> --key FILE --name NAME`: it reruns the
checks at the commit the release names, in its own worktree, recomputes the release profile there,
records ATTESTED or INVALID under its own key, and witnesses the projections that name
it after recomputing their digests. `NAME` is the member's verifier id: a later INVALID under it withdraws the
member's own ATTESTED.

## The spec and the assurance map are renderings

`VARS-1-SPEC.md` is rendered from `spec.json` and `ASSURANCE.md` from `assurance.json`; edit the data, then
`python3 tools/check_claims.py --write-spec --write-assurance`. CI refuses either file when it is not exactly the
rendering. Each normative block of the spec is a part that names the claims it carries (`claims.json`), so coverage
is read from the data and nothing parses Markdown.

## Roadmap

The roadmap is Warrant 3 records in `.warrant/records.jsonl`, read by warrant's own tool: goals are open questions,
obligations are duties that answer them. The trust and the profile are `.warrant/v3.json`: records are filed by
`claude`, and an obligation or a goal counts as closed only when its acceptor (`codex`) accepts it with its own key.
The schemas `goal@1` and `obligation@1` are warrant's, carried here byte for byte with codex's acceptances. The view
is generated, not kept in the tree. With a warrant checkout beside this one:

```
python3 ../warrant/tools/roadmap.py --root . view          # the roadmap, as Markdown
python3 ../warrant/tools/roadmap.py --root . due --actor codex   # what waits for codex's verdict
python3 ../warrant/tools/roadmap.py --root . check         # every obligation answers a goal; none forks
```

Goals G1 (what-if) and G2 (documents as projections) were concluded under the earlier Warrant 2 roadmap, which
stays in this repository's history (`.warrant/store/` at 38b7192); it was not migrated.

## Running

minds needs `node` for the wasm kernel and Book I, [sigma-glyph](https://github.com/s0fractal/sigma-glyph) 0.8.0
from PyPI, pinned by hash in `requirements.txt`; `vars1.py` also checks the installed modules' bytes against the
revision the spec pins. The Lean link's three sigma-glyph files and the Ed25519 vectors from
[primitives](https://github.com/s0fractal/primitives) are copied in (`proofs/SigmaEval/SOURCE`, `vectors/SOURCE`).

```
git clone https://github.com/s0fractal/minds && cd minds
python3 -m venv .venv && .venv/bin/pip install --require-hashes -r requirements.txt
(cd proofs && lake build && lake build vars1exec && lake build vars1fold && lake build vars1cycle && lake build Vars1Sigma)
.venv/bin/python -m unittest test_vars1     # conformance; every fold and lens runs kernel/lens.wasm and its twin
.venv/bin/python test_vars1_props.py        # property-based invariants I0–I12 (I9, I10, I12 need the proofs' executables)
.venv/bin/python vars1.py verify-projection BUNDLE.json --require PUBKEY   # with no repository (spec §4.4)
```

A client that only checks bundles needs none of this: `verify/minds_verify.py` is one standard-library file with no
dependencies, no git and no network. Copy it anywhere and run

```
python3 -I minds_verify.py verify-attestation BUNDLE.json --require PUBKEY   # exit 0 only on acceptance
python3 -I minds_verify.py verify-projection BUNDLE.json --require PUBKEY    # pinned witness, data matches
python3 -I minds_verify.py inspect-attestation BUNDLE.json                   # consistency only, no trust
```

`verify-*` needs at least one `--require`: a bundle carries its own witness and scope policies, chosen by whoever
made it, so they say nothing about whom you trust. Pin the member keys listed above. `inspect-*` checks a bundle
against its own policies and claims no trust.

```
```

Each result has an `explain` trace (counted witnesses and keys, blocked verifiers at and after the tip, the scope
epoch, the policy, why a pinned key is missing, and whether the rules identity is one it interprets). It is derived
from the bundle, not authority; `vars1.py` delegates to the same file (spec §4.4).

## Status

Experimental. CI (`.github/workflows/check.yml`) runs every release check on a fresh Ubuntu runner: the kernel
rebuild, which hashes to the same `H_LENS_KERNEL` there as on macOS, the Lean proofs and executables, the
conformance suite and the property suite. The proofs' hypotheses and unlinked parts are listed in
`proofs/README.md`; the Rust/wasm code itself is not proved, only differentially tested against the Lean side
(lens Passes 1–2 against an executable lens proved equal to the model, the fold against the model's own fold,
compiled). Other AI agents have reviewed it adversarially, and their reproduced findings are fixed with
regression tests; no independent human has reviewed it. Radicle replicates `refs/vars/*` signed and with history
(`tools/radicle-probe.sh`, two local nodes, rad 1.10.3).

The host reads each chain commit once, as the objects its `git diff-tree` delta adds, and keeps checked objects by
content hash and folds by tip commit; new bytes are always read, hashed against their name and checked. A cold
process pays one Ed25519 check per seal (pure Python), so admission and lens grow linearly with history; a warm
instance admits a commit in well under a second at 320 commits (`tools/bench_chain.py`). The rules kernel itself
still takes the whole commit log as input, as the spec defines it.

MIT licensed.
