# VARS-1 rules v2: typed cell references

Status: **dormant support on main, not adopted.** The host implements both rules; v1 is the default, and a scope
moves to v2 only by a rotation admitted with a rules-change decision (VARS-1-SPEC.md §4.3). The live chain
`refs/vars/heads/minds` keeps `H_LENS_KERNEL` (v1): the owner decided so. Nothing here changes v1.

`H_LENS_KERNEL_V2 = 0276c1657b1fee9dbea84ce7c51c4e224e068ba5857aa3b144bdb21588d45d3e`. Since 2026-10-28 v2 is the
one successor of v1 (roadmap G4) and carries what the v1 line fixed separately:

- **v1b's commit bound:** an input claiming more commits than it has bytes is refused, `−7`.
- **v1c's rotation delay** (VARS-1-SPEC.md §4.1 latch 4a): in a v2 epoch, a rotation that removes keys without
  their consent waits 16 commits, or until every removed key has sealed it; meanwhile a new scope is refused, `−24`.
  In a v1 epoch every rotation takes effect at once, as v1 has it, so a v1 history is still read exactly as v1
  reads it (`test_vars1.py` 86 checks this on a v1 chain whose rotation removed a key).

v1c, which carried the delay on v1 encoding, was retired before any chain used it. v1b stays, as the example of a
resource hardening; a chain with a v1b epoch does not rotate to v2.

The module differs from the archived prototype (tag `archive/rules-v2-prototype`, `4605f0db…`, kept locally): the
prototype refused a log whose last commit is in a v1 epoch, with the code `−24` that now means a waiting rotation;
this module evaluates such a log, reading every cell as v1 does, because a rules-change decision runs the new rules
over the history before the rotation (check (a) of §4.3).

## 1. Problem (Codex R2-03)

The v1 rules (`kernel/lens.wasm`, `H_LENS_KERNEL = 874e714d…`) read a payload or slot as a reference to a cell
whenever its 32 bytes equal some cell id, whatever the field's declared type (§4.3). Two consequences:

- An opaque value — a `digest` slot, a `hash` slot, a custom schema's payload — turns into a reference the moment a
  cell with that id is admitted. References feed hereditary acceptance (§4.2 Pass 1 and the `Live` relation of
  Pass 2), so the status of a foreign cell can change because an unrelated cell happened to be born.
- A reference to a later-born cell breaks the forward topological order the kernel requires (`BAD_EDGE`).

v1 stays sound through an interim gate rule (commit 5573691): a new cell is refused if an older cell already
names its id in a payload or slot. That is a pre-commit veto: whoever writes a digest first blocks the cell whose
id it is, forever, in that scope.

## 2. Which positions are references in v2

A **reference position** of a cell is one whose declared type is `cell`, plus the payloads the standard schemas
define as cells. Nothing else is ever read as a reference, whatever its value.

| Schema | Payload | Slots that are references |
|---|---|---|
| verdict | **yes** (the judged cell) | `ckpt_or_witness` (slot 0) when not `H_EMPTY` |
| acceptance | **yes** (the admitted foreign cell) | `foreign_scope_cell` (slot 1) |
| question | no (UTF8 statement) | `expected_schema` (slot 0) |
| axiom, contract, decision, computation, checkpoint, cycle_witness, scope, projection | no | none |
| custom schema | **no** | every slot whose descriptor is `name:cell` |

`hash` (e.g. contract `expected_outcome`) and `digest` (projection `input`/`state`, any custom `:digest` field)
are values, never references, even when their bytes equal a cell id. A custom schema that needs a reference
declares a `cell` field (the gate then requires that cell to be present at admission, so a typed reference always
names an older cell) or uses an edge. A custom payload is always opaque in v2.

The five edge vectors are references in both versions; they are unchanged.

## 3. Kernel input v2 (§4.3)

v2 states reference positions explicitly and the kernel checks them, instead of inferring them by id equality.

```
MAGIC C N NK P                               MAGIC = 0x32524156 ("VAR2" little-endian); then as v1
P × (H id, threshold, m, key[m])
N × (H id, H schema, H payload, H name, H loss, origin, birth, K, K × H slot,
     mask_lo, mask_hi,                       for a schema cell: bit s = descriptor s has type `cell`; else 0
     5 × (count, index[count]),              relies, attests, supersedes, retires, invalidates
     R, R × (pos, index))                    reference positions: pos 0 = payload, 1 + s = slot s
S, S × (target, ctx, key, commit)
```

- **Masks** are host parsing of the schema's UTF8 descriptors (like `origin` from the name). The kernel embeds
  the masks of the standard schemas and refuses an input whose standard schema cell carries a different mask, or
  whose non-schema cell carries a nonzero one.
- **References** `(pos, index)` must be strictly ascending in `pos`, name an older index born no later, and the
  value at `pos` must equal that cell's id. The kernel recomputes the expected positions of every cell — by its
  epoch (§4) — and refuses (`−6`, references differ from the rules' reading) unless the list is exactly that.
- **Use.** Hereditary acceptance (a foreign cell's references to cells of its own origin) reads the five edge
  lists and this list only. Acceptance pins and acceptance targets are typed positions in both versions, so the
  fold's latches (§4.1) are unchanged: v2 changes Passes 1–2 inputs, not authority.
- **Output** is v1's layout, so the executable lens (`Exec.lean`, I9), the model fold (I10) and Pass 3
  recomputation (I11) read v2 outputs unchanged; they read references from the explicit list.
- **Embedded constants.** Besides v1's (§4.3), the v2 module embeds `H_LENS_KERNEL` (to recognise v1 epochs) and
  the standard schemas' masks. It cannot embed its own hash; it treats every scope not naming v1 as its own, and the
  host admits no third value.
- **Refusals** add `−6` (reference list or schema mask differs) and `−25` (rotation back to v1) to v1's codes.

The host's twin, the gate's topological order and the attestation client (§4.4: references "of a newer cell of
its origin that references it") read references the same way: `cell_refs` in `vars1.py`, and a client parsing a
v2 input would read the explicit list. On main the offline verifier (`verify/minds_verify.py`) interprets v1
only: a v2 projection bundle is reported `rules_status: "unsupported"`, its seals and digests checked, nothing
accepted on it.

## 4. Per-epoch rules dispatch

A scope cell names its rules in `slots[2]`. The host implements `H_LENS_KERNEL` (v1) and `H_LENS_KERNEL_V2`; every
other value is refused, as today.

- **Epoch.** A commit `T_i` is in the epoch of the rules named by `S_i`, the scope governing it (fixed at its
  start, §0). A cell's epoch is that of its birth commit. A rotation commit is still in the old epoch; its new scope's
  rules apply from the next commit.
- **Which rules evaluate a chain.** The lens and the gate at commit `T_n` run the rules of `T_n`'s epoch over the
  whole log. The host finds `S_n` by parsing (the newest local scope born before `T_n`; §3 check 1 makes
  that the governing one), and the kernel recomputes it in its fold.
- **v2 reads v1 epochs as v1 did.** For a cell born in a v1 epoch the v2 kernel expects every payload or slot
  equal to a cell id as a reference — v1's reading — so statuses of history are kept. For a cell born in a v2
  epoch it expects the typed positions only. Over a log wholly in v1 epochs it gives v1's output byte for byte
  (`test_vars1.py` 56), and a rules-change decision checks that on the chain itself before the rotation.
- **The interim rule continues for v1-born cells only.** A new cell is refused if a cell born in a v1 epoch names
  its id in a payload or slot. Without that, a v1-born cell could gain a reference to a later cell. Cells born in a
  v2 epoch veto nothing: their opaque values stay opaque.
- **No downgrade.** A rotation from a v2 scope to a scope naming v1 is refused (kernel `−25`, gate and twin
  alike): v1 rules cannot read a v2 epoch, whose opaque values may equal later ids.
- **Projections** name their rules; the gate requires them to equal the rules of the tip's epoch and recomputes
  with that module. `vars1.py` keeps both modules, so every past tip is recomputable with the rules it was
  projected under. A bundle whose input encoding does not match the rules it names is refused.
- **Foreign scopes** may name either rules; that is recorded, not used. Epochs are those of the evaluated scope.
- **Limit.** The v1 module is frozen and cannot refuse a v2 epoch, so running v1 on a log whose last commit is in
  a v2 epoch is prevented by the host's dispatch alone (and the twin, which reads epochs the same way). The
  prototype's property suite checked the dispatch against the interpreter's own record of each commit's rules
  (I8); on main only the conformance tests do (§6).

## 5. What history keeps, and what is lost

Kept:

- Every v1 projection, its input and state digests, and every attestation bundle built on it: the v1 module, the
  v1 input encoding and `H_LENS_KERNEL` are unchanged, and the host keeps running v1 for v1 tips.
- Every latch (scope, acceptance, schema, edge): the fold does not read payloads or untyped slots in either
  version.
- Every status of a v1-born cell at a later v2 tip, in so far as it depends on that cell's own references: they are
  read as v1 read them.

Lost or changed:

- **One-way.** After rotation to v2 a chain cannot be evaluated by v1 rules, and cannot rotate back.
- **A v2 tip is not a v1 tip.** Its input digest is over the v2 encoding, so a projection at a v2 tip is only
  checkable by a host that implements v2. A v1-only client refuses it as rules it does not implement.
- **v1 references in v2-born cells.** A v2-born cell that relied on an untyped slot or custom payload to carry
  hereditary acceptance gets none; it must use a `cell` field or an edge. (No standard schema does this.)
- **The interim veto remains on v1-born values.** A digest written in a v1 epoch still blocks a later cell with
  that id, for as long as the chain lives.

## 6. Conformance (on main)

- `kernel2/` builds `lens2.wasm` reproducibly (pinned Rust 1.88.0) to `H_LENS_KERNEL_V2`: CI rebuilds it, and a
  release rebuilds every rules module its commit carries (`tools/minds_chain.py` `kernel_checks`).
- `test_vars1.py` 47–58: a rotation v1 → v2 with a rules-change decision whose counterexample is Codex R2-03 (47);
  the decision's absence, missing fields, other rules or basis, quorum and placement (48); each of its three
  computations wrong (49–51); no rotation back to v1, with or without a decision (52); `tools/minds_chain.py`
  after the change, and v1 projection and attestation bundles made before it (53); an opaque digest stays opaque
  under v2 while a v1-born one still vetoes (54); typed reading versus v1 reading of v1-born cells (55); the module
  checks the reference list, refuses a v1 encoding, and reproduces v1's output on a v1 log (56); a v2 genesis and
  projections naming their tip's epoch (57); the release checks (58).
- Mutants (`mutants.json`, `m-rc-*`, `m-v2-*`, `m-f40-*`, `m-f41-*`, `m-gate-scope-rules`), each killed by these tests.

Not carried over from the prototype: its property-suite generator for v2 (scopes under v2, rotations, typed and
opaque fields, I0–I11 on v2 tips) and `proofs/Vars1/Refs.lean`. On main the property suite exercises v1 only, and no
Lean statement is about v2. Rotations to v2 in the generator would now need a rules-change decision.

## 7. Adoption (not done)

Adopting v2 for `refs/vars/heads/minds` needs: the owner's explicit go-ahead; a rotation whose new scope names
`H_LENS_KERNEL_V2`, sealed by the admission quorum, with a rules-change decision (VARS-1-SPEC.md §4.3) whose
counterexample chain is published under `refs/vars/heads/<its scope>`; `kernel2/lens2.wasm` stored as an atom; and
every member's verifier updated to a host that implements v2 first.

## 8. Known gaps (Monday's review of 9f69bfd, 2026-10-20)

F40 and F41 are closed on main; F42 is open. Any adoption must close it first.

- **F40, self-governance breaks after a rotation to v2 (confirmed statically).** `tools/minds_chain.py` writes
  `H_LENS_KERNEL` (v1) into `join`'s new scope and into every release projection. After a rotation to v2 the gate
  requires a projection to name its tip's rules, so `release` would be refused, and `join` would be a refused
  downgrade. Both must use the rules of the governing scope, and changing rules must be its own explicit operation,
  not a side effect of a membership rotation. **Closed:** `join` and `release` keep the governing scope's rules,
  a release projection names its tip's epoch, and changing rules is a rotation with a rules-change decision
  (`test_vars1.py` 53, mutants `m-f40-*`).
- **F41, `kernel2/lens2.wasm` is not in the release checks.** `run_checks` rebuilds and hashes `kernel/` only; a
  release does not attest that `lens2.wasm` rebuilds to `H_LENS_KERNEL_V2` (it does today, by hand). **Closed:**
  `kernel_checks` rebuilds every rules module the commit carries and requires the released rules among them
  (`test_vars1.py` 58, mutants `m-f41-*`); CI rebuilds `kernel2/` too.
- **F42, custom schema masks are host-parsed.** For standard schemas the v2 module checks masks against embedded
  constants; for a custom schema it trusts the mask the host derived from the UTF8 descriptors, so the descriptor
  parser is in the trusted base, and the prototype's `Refs.lean` assumed correct typed positions. Needed: an independent oracle for
  descriptor → mask → references that does not call `schema_cell_mask()`.
- **Drift.** Resolved by re-deriving v2 on top of main (branch `rules-change`) rather than merging `rules-v2`; the
  v2 input parsing stays out of `verify/minds_verify.py` (see §3).
