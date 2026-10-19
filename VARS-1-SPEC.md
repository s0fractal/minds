# VARS-1

A hash-native graph of claims, computations and verdicts, stored in git, evaluated by a compiled lens.

Reference implementation `vars1.py`; lens kernel `kernel/lens.wasm`; proofs `proofs/`. Depends on
`sigma-glyph` at `c864d3e` (Book I, `impl/sigma_resume.py`).

## 0. Terms

- **scope**: an authority domain. Its history is the ref `refs/vars/heads/<scope>`.
- **origin(c)**: the text before the first `/` in the UTF-8 preimage of `c.H_slot_name`. A cell is **local** in
  `<scope>` iff `origin(c) = <scope>`, otherwise **foreign**.
- **S_i**: the scope cell governing commit `T_i` (fixed at the start of `T_i`).
- `id(x) = SHA-256(bytes(x))`. Every object is addressed by its id.

## 1. Objects

### 1.1 Atoms (`cas/atoms/`)

Non-canonical bytes are refused, never normalized.

| Family | Prefix | Rule |
|---|---|---|
| SigmaNodeV2 | `0x00`/`0x01`/`0x02`/`0xff` | Book I node: 34 or 66 bytes |
| Environment | `{"schema":"sigma-resume.environment@draft-1",…}` | canonical JSON of `sigma_resume.py` |
| ComputationRoot | `{"schema":"sigma-resume.root@draft-1",…}` | canonical JSON of `sigma_resume.py`; its id is `computation_id` |
| MachineState | `SGS1` | `SGS1 ‖ computation_id ‖ preorder tree`, at most 64 MiB |
| U64 | `U64\0` | 8 bytes big-endian, value ≤ 2^53−1 |
| HVEC | `HVEC` | `n ≤ 65535` hashes; strictly ascending where it is a set |
| POL1 | `POL1` | `threshold:u16be ‖ id(HVEC of Ed25519 keys)`; keys strong (§1.3); `1 ≤ threshold ≤ n` |
| UTF8 | `UTF8` | valid UTF-8, no NUL or CR, no leading/trailing space, tab or newline; ≤ 64 KiB |
| Wasm module | `\0asm\1\0\0\0` | identity is its hash; a host executes only the rules it implements (§4.3) |

**Intrinsic constants** (known without reading the store):

| Name | Preimage | SHA-256 |
|---|---|---|
| `H_I` | Book I `I` | `2f33694d09810641fa5b8c47a7c0dc42e1b99eb8c9784a00aaee9a66330f4162` |
| `H_K` | Book I `K` | `bc0c2fe26e44e2aed8ce500a74963bc270fd4a49ec0c2e4837ce7a64bb0a486c` |
| `H_S` | Book I `S` | `887045bc22935aec5cba2dc11400d4e4357bc34d06681a6e92f06e7795b1f8a6` |
| `H_FALSE` | Book I `APPLY(K, I)` | `65cd957fee7ec9fb310bc9d9712cec1726c78f8026fda679ac8f237938a32098` |
| `H_INVALID` | Book I invalid | `af69b5176c7ac3855c2eac3d1f6159c74d5328e92aac0a33cdba68bbaeba4507` |
| `H_EMPTY` | `HVEC` | `f7607964cdb9f811072ded78efc20c622f54483eb7b101da5605329dc908872e` |
| `H_META_SCHEMA` | `VARS-META-SCHEMA-V1` | `7f0f250c08d367c8f2ba2c3b700f1a9bacbb44c240dade81c5c39c9ea7f9f15e` |
| `H_ZERO` | `U64\0` + 8 zero bytes | `bd8ce1f0a5c552141dc052a9b66a200003a1b34dbf947dea1c1e32b9969cfe3c` |
| `H_NORMAL_FORM` | `UTF8NORMAL_FORM` | `90d5b63c645ec4891cbe37c649b606e6b55ef03c3a04d3d00a7145f83fc4b1b7` |
| `H_PAUSED` | `UTF8PAUSED` | `26e65e29da47e4aa37d009f91ba64992b6dea96b633057fb433237c0622314e4` |
| `H_BLOCKED_REF` | `UTF8BLOCKED_REFERENCE` | `f092fc6a2f96c160648da203ac2e9e4a98a3c4bc3ea99fd8ae811120f4ccc9f5` |
| `H_CYCLE_PROVEN` | `UTF8CYCLE_PROVEN` | `55e3031a9afc06976f2769dfc44a08437ee892bf2f91116a86a05f8b1494e20e` |
| `H_REPLAYED` | `UTF8REPLAYED` | `4412ca4ade087a21844e613975a7c6db1e581deeb870219b48cf093003f05063` |
| `H_ATTESTED` | `UTF8ATTESTED` | `7e5f2fdf987cac883a0453016a9541553d700e3a6f3a807839f22d5ca07b802c` |
| `H_VERDICT_INVALID` | `UTF8INVALID` | `b3966965c112d6d2613255fc018e34774dbc17c8517705b95946ea925b95096d` |
| `H_NOT_ASSESSED` | `UTF8NOT_ASSESSED` | `801ad348011ddbb757f8a1f1d2210451f7ac5945e77aec8d53cafbd87f8861ad` |
| `H_PROVISIONAL` | `UTF8provisional` | `b9d665ebd73a6d287e1e40b8c29cf2839d973b461511bfc7b0dd5623b9fe41e5` |
| `H_OWNER` | `UTF8owner` | `4f97d7922a77cd279f75b8483542a9235330d4402ab15373e23c21bb7877905e` |

`H_LENS_KERNEL = 993c237fca82d922f61e23759bf43486f17d861a7353c77768fd33c221723263` is not intrinsic: it is the
id of `kernel/lens.wasm`, stored as an atom in every genesis (§4.3).

### 1.2 Cells (`cas/cells/`)

Unsigned, `296 + 32·K` bytes:

```
0..4      "VAR1"
4..7      000000
7..8      K (arity, 0..64)
8..40     H_schema       schema cell id (H_META_SCHEMA for a schema cell)
40..72    H_slot_name    id(UTF8 "<scope>/<name>")
72..104   H_payload
104..136  H_relies       id(HVEC of cell ids) or H_EMPTY
136..168  H_attests      "
168..200  H_supersedes   "
200..232  H_retires      "
232..264  H_invalidates  "
264..296  H_loss         id(UTF8, 1..4096 bytes) or H_EMPTY
296..     slots[0..K]
```

1. **Loss.** `H_supersedes ≠ H_EMPTY` or `H_retires ≠ H_EMPTY` requires `H_loss ≠ H_EMPTY`.
2. **Edges.** Every element of the five edge vectors is a cell id, never the cell itself. `supersedes` joins
   cells of the same schema. `attests` targets a contract, decision or question. A scope cell appears only in
   `supersedes` of a scope cell of the same origin.
3. **Names.** `<scope>/<name>`, at most 128 bytes, segments `[A-Za-z0-9][A-Za-z0-9_.-]*` (scope:
   `[A-Za-z0-9][A-Za-z0-9_-]{0,31}`), no `..`, no segment ending in `.` or `.lock`. `core/schema.*` is reserved
   for the standard schemas. A name is `<origin>/SCOPE` iff the cell is a scope cell.
4. **Schemas.** A schema cell has `H_payload = H_EMPTY`, all edges and loss `H_EMPTY`, and `slots` = ids of
   `UTF8 "field:type"` descriptors. Any other cell's `H_schema` is a schema cell with the same arity.
5. **Dependencies.** A contract or decision with `required_comp ≠ H_EMPTY` relies on a computation cell whose
   payload is that `computation_id`. A verdict with `ckpt_or_witness ≠ H_EMPTY` relies on that cell.
6. **One binding per name.** A newly admitted local non-scope cell `c` must reach every other local cell with
   its name along `supersedes` edges: the first hop is any element of `supersedes(c)`, every later hop is an
   edge already authorized (§4.1) by the end of `c`'s commit. In one commit it suffices that one cell of each
   same-name pair reaches the other.

### 1.3 Seals (`cas/seals/`)

164 bytes: `"SEAL" ‖ H_target ‖ H_scope_ctx ‖ actor_pubkey ‖ signature`, the Ed25519 signature over the first
100 bytes. A seal binds an endorsement to one cell and one scope epoch.

Verification is strict and cofactorless: `actor_pubkey` and `R` are canonical (`y < 2^255−19`), not one of the
ten small-order or torsion encodings rejected by warrant's `weak_public_key`, and decode to curve points;
`S < L`; and `[S]B = R + [k]A` with `k = SHA-512(R ‖ A ‖ msg) mod L`.

## 2. Standard schemas

Each is a schema cell named `core/schema.<name>` with the descriptors below.

| Schema | Descriptors | Id |
|---|---|---|
| axiom | — | `aaf70509e078bf1f833492eb82a116e4122232d424cf1668c05a9dd25855dcda` |
| contract | `tier:utf8`, `required_comp:root`, `expected_outcome:hash`, `evaluator_policy:pol1` | `391bbd2090d93f580fe033df9109cff948d46a07db24b9db05d55dc84e84277b` |
| computation | — | `1c97bc0b74ffc978ade540c55592b294b0d9f2502b94b969f89ef00d99dd10bb` |
| checkpoint | `computation_id:root`, `credit_total:u64`, `spent_total:u64`, `peak_size:u64`, `kernel_outcome:utf8`, `actions:u64` | `77655a8f5ca5b1c6347634e9a5848fdacee6efefd58569242d39f43410747639` |
| cycle_witness | `computation_id:root`, `entry_spent:u64`, `cycle_actions:u64`, `cycle_cost:u64` | `065f1b5b54fa199d65fb7f3e185e6f024d7523e829af1ad98269de018a8fb548` |
| decision | as contract | `5a48e9c69afc5c3cebb3ca2980052151f2aaa539052702e0e23f7ba5504eb6fb` |
| question | `expected_schema:cell`, `evaluator_policy:pol1` | `1293a1513baa6e0e1edfdcf8c8f4b992efa1391ddbc0889efe9698d59c9b0cdf` |
| acceptance | `source_scope:utf8`, `foreign_scope_cell:cell` | `c661936c020c0d817b8516b93454af5a30fe4282d854c1b0f628731c80f95d66` |
| scope | `admission_policy:pol1`, `acceptance_policy:pol1`, `rules:wasm` | `9aab50548f8fc7c5e2090fa89a73440af7de5e92d800b928261f13f20a4bd2a9` |
| verdict | `ckpt_or_witness:cell`, `verdict_code:utf8`, `verifier_id:utf8` | `ad702699d5fc7b3d94138c38643c9889f1520a6e1c20760aa6b11a8e273dfdae` |
| projection | `tip:utf8`, `rules:wasm`, `input:digest`, `state:digest`, `witness_policy:pol1` | `8029ae880cb62a8034f47ec44e8f5c5982ebc14a14be2c6893a3ab8f968aa818` |

**Types.** `utf8`: a UTF8 atom or intrinsic UTF8 constant. `u64`: a U64 atom or `H_ZERO`. `pol1`: a POL1 atom
whose key vector is present. `root`: a ComputationRoot whose Environment is present. `wasm`: a wasm atom.
`cell`: a cell. `hash`: anything present or intrinsic. `digest`: any 32 bytes, not required to be stored. `H_EMPTY` is allowed only in `required_comp`,
`expected_outcome`, `evaluator_policy` and `ckpt_or_witness`.

**Payloads and meaning.** axiom, contract, decision, question: `id(UTF8 statement)`. computation:
`computation_id`. checkpoint: `id(SGS1 state)`, with `slots[0]` equal to the state's `computation_id`;
`kernel_outcome` ∈ {`H_NORMAL_FORM`, `H_PAUSED`, `H_BLOCKED_REF`}; a checkpoint chains to its parent through
`relies`, never `supersedes`. cycle_witness: `id(entry state)`, `1 ≤ cycle_actions ≤ cycle_cost`. tier ∈
{`H_PROVISIONAL`, `H_OWNER`}. acceptance: the foreign cell it admits; `source_scope = origin(target)`, and
`foreign_scope_cell` is a self-sealed scope cell of that origin. scope: `id(UTF8 scope name)`. verdict: the
contract, decision or question it judges; `verdict_code` ∈ {`H_REPLAYED`, `H_ATTESTED`, `H_VERDICT_INVALID`,
`H_NOT_ASSESSED`}, and `H_ATTESTED` exactly when `ckpt_or_witness = H_EMPTY`. projection: `H_EMPTY` (§4.4).

## 3. Store and gate

`refs/vars/heads/<scope>` is a linear chain; peers are fetched to `refs/vars/peers/<peer>/<scope>`. Each commit's
tree is `cas/{atoms,cells,seals}/<2 hex>/<62 hex>`, every entry a regular file (`100644`) whose bytes hash to
its path.

A commit `T_new` on top of `T_old` is admitted iff all checks pass, then the ref moves by compare-and-swap
(`git update-ref <ref> T_new T_old`). Every refusal is an error of the gate, never a crash.

1. **Chain.** Genesis has no parent and exactly one local scope cell `S_0`, with empty edges, self-sealed to its
   admission quorum. Any later commit has exactly the parent `T_old` and at most one new local scope cell, which
   supersedes exactly the governing scope and is sealed by its admission quorum.
2. **Append-only.** `git diff-tree -r --no-renames --diff-filter=a T_old T_new` is empty.
3. **Objects and seals.** Every object passes §1; every slot has its schema type (§2); every scope cell has
   `rules = H_LENS_KERNEL`. Every new seal on a local cell has `H_scope_ctx = id(S_base)` and a key of
   `S_base`'s admission policy (acceptance policy for an acceptance cell). A **cross-seal** — a seal on a
   foreign cell whose context is a local scope cell — follows the same rule. Every new local cell other than a
   standard schema has at least one such seal. The evaluator policy of a local contract, decision or question
   has keys within the admission policy.
4. **References and replay.** Every referenced hash is present (cells where §1.2 requires cells). Every
   checkpoint replays as in §5; a cycle witness passes `sigma_resume.verify_cycle`.
5. **Foreign cells.** A foreign cell arrives with its closure (cells, atoms, seals) and with a self-sealed scope
   cell of its origin. Seals count for it only under that scope and its admission keys.

6. **Projections.** For every new projection cell, `tip` is the hex id of an earlier commit of this chain,
   `rules = H_LENS_KERNEL`, and `(input, state)` equal the gate's own recomputation at `tip` (§4.4); otherwise
   the commit is refused.

The fold (§4.1) then runs over the whole chain, including step 3b. The seal and authority rules of step 3 (seal
contexts and keys, cross-seals, a seal on every new cell, evaluator policies within the roster, foreign scopes)
and the fold itself are decided by the rules object (§4.3); the host contributes parsing, hashing and signature
verification.

## 4. Fold and lens

### 4.1 Fold (authority, non-retroactive)

For each commit `T_i` with governing scope `S_i`:

- `Endorsers_i(u)`: keys of seals on `u` with `H_scope_ctx = id(S_i)` and a key of `S_i` (admission policy;
  acceptance policy for an acceptance cell). For a foreign `u` these are its cross-seals. For an edge `w → v`,
  `Endorsers_i(w)` is counted with `S_i`'s acceptance keys when `v` is an acceptance cell, else its admission keys.
- `InitialEndorsers(v)`: `Endorsers_birth(v)(v)` for a local `v`; fixed at birth.
- `CumulativeEndorsers(v)`: every admitted seal on a local `v`, each checked under its own commit's scope. For a
  foreign `v`, `ForeignEndorsers(v, S_f)` counts seals under a self-sealed scope `S_f` of its origin.

Governing policy and author rights of a target `v`:

| `v` | `Pol_i(v)` | `AuthorCanEvict(v)` |
|---|---|---|
| scope, or contract/decision with tier owner | `S_i` admission | no |
| acceptance | `S_i` acceptance | no |
| contract/decision with tier provisional | its evaluator policy, else `S_i` admission | yes |
| question | its evaluator policy, else `S_i` admission | yes |
| anything else | `S_i` admission | yes |

Latches (never undone):

1. A local acceptance cell pinned to a self-sealed foreign scope whose `Endorsers_i` meet `S_i`'s acceptance
   policy is **Authorized**. A local acceptance whose `foreign_scope_cell` is not self-sealed refuses `T_i`.
2. A local custom schema cell whose `Endorsers_i` meet `S_i`'s admission policy is **Authorized**. Foreign
   acceptance and schema cells are never Authorized in `<scope>`.
3. An edge `w → v` of kind invalidates is **authorized** if `Endorsers_i(w)` meet `Pol_i(v)`. Of kind
   supersedes or retires, also if `AuthorCanEvict(v)`, `v` is local, and `Endorsers_i(w)` meets
   `InitialEndorsers(v)`.
3b. Every new local non-scope cell satisfies §1.2 rule 6, or `T_i` is refused.
4. A new scope cell `S'` becomes `S_{i+1}` after steps 1–3.

### 4.2 Lens (status at the tip)

Edges point from newer to older cells. **Pass 1**, newest first:

- `Accepted(x)`: `x` is local or a standard schema; or an Active, Authorized acceptance has payload `x`; or an
  Accepted cell of the same foreign origin references `x`.
- `Invalidated(v)`: an Effective, Accepted `w` has an authorized invalidates edge to `v` (and, if `w` is a
  verdict, its code is `H_VERDICT_INVALID`). `Effective = ¬Invalidated`.
- `Retired(v)`: an Effective, Accepted `w` has an authorized retires edge to `v`.
- `Superseded(v)`: some `w` has an authorized supersedes edge to `v` and is Effective and Accepted, or is itself
  Superseded.
- `Active(v)`: Effective, Accepted, not Retired, not Superseded, and every supersedes edge of `v` is authorized.

**Pass 2.** `Live(x)` for a foreign `x`: an Active, non-Stale, Authorized acceptance has payload `x`, or a Live
cell of the same origin references `x`. `Stale` is the least fixed point of

`Stale(v) ⇔ Active(v) ∧ ((∃ d ∈ relies(v): ¬Active(d) ∨ Stale(d)) ∨ (v foreign ∧ ¬Live(v)))`.

It is computed by rounds from `Stale = ∅`: recompute `Live` newest first, then update `Stale` oldest first in
place; stop when a round changes nothing. The operator is monotone, so at most `|cells| + 1` rounds are needed;
a round that removes a cell from `Stale` is a fault.

**Pass 3.** For an Active, non-Stale contract, decision or question `v`: `EvalPol(v)` is its evaluator policy,
else the tip scope's admission policy. A witness `w` is Active, non-Stale, attests `v`, and:

- contract/decision without `required_comp`: a verdict on `v` with `H_ATTESTED`;
- contract/decision with `required_comp = r` and `expected_outcome = e`: a verdict on `v` with `H_REPLAYED`
  whose `ckpt_or_witness` is an Active, non-Stale checkpoint of `r` claiming `H_NORMAL_FORM`, replay-verified
  over its lineage (§5), whose state's term hash is `e`; or a cycle witness of `r` when `e = H_CYCLE_PROVEN`;
- question: a cell of the expected schema.

A witness is excluded if an Active, non-Stale verdict on `v` with `H_VERDICT_INVALID` and the same
`verifier_id`, endorsed by a key of `EvalPol(v)`, exists. `WitnessEndorsers(w)` is `CumulativeEndorsers(w)`
for a local `w`, else the `ForeignEndorsers` under its live scopes. `v` is **Settled** iff the union of witness
endorsers meets `EvalPol(v)`; otherwise **Provisional**. Scope and custom schema cells are Settled iff
Authorized; a projection is Settled iff its `CumulativeEndorsers` meet its `witness_policy`; every other Active,
non-Stale cell is Settled.

### 4.3 Rules object

The fold of §4.1 (with the seal rules of §3 step 3) and Passes 1–2 of §4.2 are compiled to `kernel/lens.wasm`
(`kernel/src/lib.rs`, Rust → wasm32, built reproducibly from `kernel/`). A scope names them in `slots[2]` by
`H_LENS_KERNEL`; the gate refuses any other value, and every genesis stores the module as an atom. The host runs
the module on every admission and every lens: it decides admission authority and the statuses of Passes 1–2.
The host parses bytes, hashes, verifies Ed25519 signatures and orders cells; Pass 3 (replay, witnesses, Settled)
stays in the host.

Input, u32 little-endian words (`H` = 32 raw bytes):

```
C N NK P                                     commits, cells, interned keys, policies
P × (H id, threshold, m, key[m])             every POL1 atom with strong keys and threshold ≤ m
N × (H id, H schema, H payload, H name, H loss, origin, birth, K, K × H slot,
     5 × (count, index[count]))              relies, attests, supersedes, retires, invalidates
S, S × (target, ctx, key, commit)            seals whose signatures the host verified
```

Cells are in forward topological order: every edge, and every payload or slot that is a cell id, names an older
index born no later. `origin` 0 is the evaluated scope; `birth` and `commit` are the first commit holding the
object. The module embeds the standard schema ids, `H_META_SCHEMA`, `H_EMPTY`, `H_OWNER`, `H_PROVISIONAL` and
`H_VERDICT_INVALID`, and reads kinds, tiers, policy slots and verdict codes from the cell hashes itself.

Output: a u32 length, the governing scope's index, one status byte per cell (accepted, invalidated, effective,
retired, superseded, active, stale), one Authorized byte per cell (scope, acceptance, schema), and one byte per
invalidates, retires and supersedes edge in input order (authorized). A negative result is a malformed input
(−1…−5) or a refusal of the commit log (−10…−23: genesis shape and quorum, seal context, seal key, cross-seal,
unsealed cell, evaluator policy, unscoped foreign cell, scope rotation, acceptance pin, rule 6, unknown policy).

`vars1.py` keeps a Python fold and Passes 1–2 as a differential twin: a refusal by one and not the other, or any
differing latch, scope or status bit, is a host fault (`TwinDivergence`), never a gate refusal.

### 4.4 Projections

A projection `Π = (tip, rules, input, state)` states the result of the rules at a commit: `input =
SHA-256(kernel input for the chain up to tip)` and `state = SHA-256(kernel output)` (§4.3). The gate recomputes
both before admitting it (§3 check 6), so a chain never holds a false projection. Its witnesses sign it with
ordinary seals; once they meet `witness_policy` it is Settled.

A client without the history checks a Settled projection by its witness seals alone; that is trust in the
witness quorum, stated by the policy. Anyone holding the chain can recompute `input` and `state`, and the rules
are deterministic and named by hash, so a false projection signed outside a chain is refuted by recomputation.

## 5. Replay against Book I

`computation_id`, `environment_id` and SGS1 state ids are bit-identical with `sigma_resume.py`. A checkpoint
replays from its highest-spent same-computation parent in `relies`, or from `ComputationRoot`, through
`sigma_resume.advance`, which must reproduce its state, `spent_total`, `peak_size` and claimed outcome.

The parent's state is trusted only if the parent is itself replay-verified: status is computed over the whole
lineage, oldest first. A transition costing more than the host ceiling (10,000,000 ATP; also 64 MiB of state,
term depth 4096) is admitted on structure alone as `NOT_ASSESSED`, and so is every descendant. A
`NOT_ASSESSED` checkpoint never serves as a `REPLAYED` witness.

## 6. Conformance

- `test_vars1.py`: golden vectors, gate refusals, the scenarios of §§3–5, every Ed25519 vector of
  `primitives/vectors/verify-sig.json`, and the schema table above. Every fold and `lens()` runs the kernel and
  its Python twin, and every `lens()` is re-run on the kernel.
- `test_vars1_props.py`: seeded random admission sequences; on each admitted tip, gate refusals and the lens
  never crash or diverge from the twin (I0), one Active binding per name (I1), `Stale` equals an independent fixed
  point (I2), latched edges equal a spec oracle (I3), acceptance, custom-schema and scope latches equal a spec
  oracle (I3c), Settled implies a full replay from root (I4), latches only grow (I5), order and hash-seed
  independence (I6), the fold governs with the unique Active local scope (I7), a fresh kernel run reproduces
  the lens (I8), and the Lean-proved executable lens (`proofs/Vars1/Exec.lean`) computes the kernel's status
  bytes from the kernel's own input and fold output (I9).
- `proofs/`: the theorems listed in `proofs/README.md`.
