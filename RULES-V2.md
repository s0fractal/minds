# VARS-1 rules v2: typed cell references

Status: **prototype on branch `rules-v2`, not adopted.** A new rules identity is a protocol change; the live chain
`refs/vars/heads/minds` keeps `H_LENS_KERNEL` (v1) until the owner decides otherwise. Nothing here changes v1.

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
- **Refusals** add `−6` (reference list or schema mask differs), `−24` (last commit in a v1 epoch) and `−25`
  (rotation back to v1) to v1's codes.

The host's twin, the gate's topological order and the attestation client (§4.4: references "of a newer cell of
its origin that references it") read references the same way: `cell_refs` in `vars1.py`, and a client parsing a
v2 input reads the explicit list (`parse_kernel_input`, which recognises the magic).

## 4. Per-epoch rules dispatch

A scope cell names its rules in `slots[2]`. The host implements `H_LENS_KERNEL` (v1) and `H_LENS_KERNEL_V2`; every
other value is refused, as today.

- **Epoch.** A commit `T_i` is in the epoch of the rules named by `S_i`, the scope governing it (fixed at its
  start, §0). A cell's epoch is that of its birth commit. A rotation commit is still in the old epoch; its new scope's
  rules apply from the next commit.
- **Which rules evaluate a chain.** The lens and the gate at commit `T_n` run the rules of `T_n`'s epoch over the
  whole log. A v2 kernel refuses (`−24`) an input whose last commit is in a v1 epoch, so every module only runs
  over logs it owns. The host finds `S_n` by parsing (the newest local scope born before `T_n`; §3 check 1 makes
  that the governing one), and the kernel recomputes it in its fold.
- **v2 reads v1 epochs as v1 did.** For a cell born in a v1 epoch the v2 kernel expects every payload or slot
  equal to a cell id as a reference — v1's reading — so statuses of history are kept. For a cell born in a v2
  epoch it expects the typed positions only.
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
  a v2 epoch is prevented by the host's dispatch alone (and the twin, which reads epochs the same way). The property
  suite checks the dispatch against the interpreter's own record of each commit's rules (I8).

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

## 6. Conformance (prototype)

- `kernel2/` builds `lens2.wasm` reproducibly (pinned Rust 1.88.0); its hash is `H_LENS_KERNEL_V2`.
- `test_vars1.py` tests 36–41: an opaque digest equal to a later cell's id is admitted and stays opaque under v2,
  while the same digest written in a v1 epoch still refuses that cell, after the rotation too, and in a chain that
  never rotates (36); typed reading of `cell` versus `digest`/`hash` and v1 reading of v1-born cells at a v2 tip
  (37); no rotation back (38); projections at a v1 and a v2 tip of one chain, gate and bundle (39); the module
  refuses a dropped or an added reference, a v1-epoch log and a v1 encoding (40); a v2 genesis (41).
- `test_vars1_props.py`: the generator starts under v1 or v2, rotates to v2 (and tries to rotate back), emits
  custom schemas with `cell`, `digest` and `hash` fields, digests naming a planned cell, and foreign cells whose
  fields all name an older cell of their origin under an acceptance (hereditary acceptance through a typed or an
  opaque field). I0–I11 hold on every admitted tip of either version; I8–I11 run the module of the tip's epoch;
  I2's Stale oracle reads references from the spec (`spec_value_refs`), not from `vars1.py`.
- Mutants, each killed: v2 reads like v1 in the module (tests 36, 37, 40); no downgrade check (38); no last-epoch
  check (40); typed slots ignored (37, 40); the lens's hereditary acceptance reading every position (props, I0);
  module and host both reading v2 like v1 (props, I2).
- `proofs/Vars1/Refs.lean`: typed references are stable when cells are added (an opaque value never becomes a
  reference), v1's reading is not (explicit counterexample), and the governing rules never go back from v2 to v1
  along an admitted chain, so a cell's epoch is fixed at birth.

## 7. Adoption (not done)

Adopting v2 for `refs/vars/heads/minds` needs: the owner's explicit go-ahead; `kernel2/lens2.wasm` stored as an
atom; a rotation whose new scope names `H_LENS_KERNEL_V2`, sealed by the admission quorum; and every member's
verifier updated to a host that implements v2 first.
