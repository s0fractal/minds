# VARS-1 proofs

Lean 4 (`v4.31.0`, core only, no Mathlib). Models the fold (§4.1) and the lens (§4.2) of
`VARS-1-SPEC.md` abstractly — no bytes, git or crypto — and proves their invariants.

```
lake build              # library Vars1
lake build vars1exec    # the executable lens, compiled (used by test_vars1_props.py, invariant I9)
lake build vars1fold    # the model's own fold, v1 and v2, compiled (invariant I10)
lake build vars1cycle   # the model's cycle checker, compiled (invariant I12)
lake build vars1witness # the witness checker, compiled (experiments/witness: every check runs it too)
lake build Vars1Sigma   # link to sigma-glyph's Book I evaluator and sigma-resume (six files copied in SigmaEval/)
```

Zero `sorry`, no `axiom` declarations. `#print axioms` shows only `propext`, `Quot.sound`
and, for some theorems, `Classical.choice`.

## Theorems

| File | Theorem | Statement |
|---|---|---|
| `Fold.lean` | `stateAt_mono` | latches only grow along the chain; InitialEndorsers never change after birth |
| | `stateAt_append` | the state at the start of `T_i` does not depend on later commits |
| | `step_epoch_binding` | a commit's latches depend only on seals under its own scope `S_i` |
| | `endorser_signed` | under unforgeability, every counted endorser signed `(id(u), id(S_i))` |
| `Fold2.lean` | `stateAt2_mono`, `stateAt2_append` | the same two under the v2 rules (§4.1 latches 4a and 4b) |
| | `run2_v1` | over a chain whose governing scope names v1 at every commit, the v2 fold is v1's, latch for latch, when rotations are admitted as the gate requires: v2 reads v1 epochs as v1 did |
| | `moves_notice` | latch 4a: when the governing scope moves under v2, the new scope was admitted at some commit `t`, and either 16 commits have passed since, or it changes no rules and every key it removes from the old admission or acceptance policy has sealed it under the old scope; in a v1 epoch it moves at its admission. Latch 4b: a move to other rules comes 16 commits after the admission, with no veto in its window |
| | `waiting_withheld`, `waiting_not_active` | a scope whose rotation waits, or was vetoed, latches no edge, so it is not Active and the Active local scope stays the governing one |
| | `vetoed_never_governs` | a vetoed rules change never becomes the governing scope |
| `Pass1.lean` | `unique_active_binding` | under §1.2 Rule 6, two local non-scope cells with one name are never both Active |
| | `pass1_kernel_unique`, `IsPass1.kernel_unique` | on a store whose invalidates edges climb a rank (content addressing gives one), the Pass 1 equations for `Invalidated` and `Effective` have at most one solution for a given `Accepted`: Pass 1 is a unique kernel |
| `Scope.lean` | `governed_superseded`, `unique_active_scope` | under the gate's rotation rule, a scope that no longer governs is superseded by a later scope; an Active local scope is the governing one |
| `Pass2.lean`, `Lfp.lean` | `Φ_mono`, `stale_fixed`, `stale_least` | the Pass 2 operator is monotone; `Stale` is its least fixed point |
| | `sweep_reaches_stale` | the spec's round (live acceptance first, then an in-place sweep) reaches `Stale` within `|cells|+1` rounds, in any cell order |
| `SigmaEval/ResumeMachine.lean` (sigma-glyph) | `adv_seg` | segmentation invariance of budgeted advance |
| `Replay.lean` | `verify_sound` | `REPLAYED` for `c` ⟹ one advance from `ComputationRoot` by `spent_total(c)` reaches exactly `c`'s state |
| | `not_assessed_ancestor_blocks` | a `NOT_ASSESSED` ancestor prevents `REPLAYED` at any fuel |
| `ReplayAttack.lean` | `pre_lineage_unsound` | a verifier that trusts an unverified parent is unsound (explicit counterexample) |
| `SigmaEval/ResumeCycle.lean` (sigma-glyph) | `checkCycle_sound` | `checkCycle` (`sigma_resume.verify_cycle` over the abstract machine) returns `CYCLE_PROVEN` ⟹ one advance from the start by `entry_spent` reaches exactly the entry, and `n ≥ 1` actions from the entry return to it at `cycle_cost` |
| | `cycle_proven_no_normal_form` | then from the start every number of actions fires, and at every budget the run ends paused: never a normal form, never a blocked reference |
| `Cycle.lean` | `gateCycle_proven_iff` | the gate's verdict (`NOT_ASSESSED` for a well-shaped witness whose entry is above the ceiling) proves exactly what `checkCycle` proves |
| | `replayed_nf_excludes_cycle` | no computation has both a `REPLAYED` checkpoint claiming `H_NORMAL_FORM` and an accepted cycle witness |
| `Pass3Replay.lean` | `settled_full_replay` | a Settled contract with `required_comp` has a live witness: a full replay from root to a normal form with the expected term hash, or a cycle witness of the same computation for `H_CYCLE_PROVEN` from whose start no budget reaches a normal form |
| | `settled_cycle_no_normal_form` | a Settled contract with `required_comp = r` and `expected_outcome = H_CYCLE_PROVEN`: from `SR.start r` every number of actions fires and no budget gives a normal form or a blocked reference |
| `SigmaEval/ResumeLink.lean` (sigma-glyph) | `run_eq_adv` | the abstract machine instantiated with `EvalMachine.step` |
| `Vars1Sigma/Link.lean` | `book_verify_sound` | replay soundness for Book I |
| `SigmaEval/ResumeLink.lean` (sigma-glyph) | `book_cycle_no_normal_form` | for Book I: an accepted cycle witness means `_run` of `EvalMachine.step` from the start, at any budget, stops at a term that is a normal form at no budget (no Book I term with a state cycle is known) |
| `ExecProof.lean` | `pass1_correct` | the executable Pass 1 (`Exec.lean`) satisfies `IsPass1`, and its `sup`/`act` bits are the model's `Superseded`/`Active`, on the world its facts describe |
| | `stale_correct` | the executable Pass 2 is the model's `Stale = lfp Φ` |
| `Grounded.lean` | `GΦ_mono`, `grounded_fixed`, `grounded_least` | the operator of Grounded is monotone, and Grounded is its least fixed point |
| | `grounded_settled`, `grounded_rests`, `lost_quorum_collapses` | Grounded implies Settled; everything a Grounded cell rests on along `relies` is Grounded and Settled; a cell resting on one not Settled is not Grounded |
| | `settled_not_hereditary` | on a world with faithful presentations, a decision is Settled, relies on a decision no one attested, and is not Grounded |
| | `circular_support` | a verdict that relies on the decision it judges: both are Settled, the world is a fixed point of the operator, and neither is Grounded |
| | `grounded_iter` | simultaneous rounds from below reach Grounded within `N + 1` rounds, on `Fin N` |
| `Power.lean` | `run_latch`, `run2_latch` | over any extension whose seals are old or a coalition's and which makes no rotation (under v2, none waiting at the tip), a new latch into a present cell is one the coalition can make: a quorum of its policy among the source's old endorsers and the coalition, or, on a local cell its author may evict and not for `invalidates`, one of its initial endorsers among them |
| | `one_key_cannot_latch` | one key, with no other's old seal on the source, latches no edge into a cell whose policy no list of it alone meets, unless it is an initial endorser the policy lets evict: what an admission threshold of two is worth |
| | `pass1_frame`, `active_frame`, `stale_frame` | if no new edge enters a closed set of local cells, its Pass 1 and Pass 2 bits are unchanged, whatever the rest of the chain does |
| | `confinement` | the fold's confinement joined to the frame: a set the coalition cannot latch into keeps `Active` over the extension |
| | `settled_keeps` | a coalition takes back only its own endorsement: a contract or decision stays Settled while the counted keys outside it meet the quorum |
| | `settled_needs`, `settled_iff_keys` | a coalition settles only with the keys already counted; Settled reads the cell's standing, its policy and the set of keys that count, and nothing else |
| `History.lean` | `present_prefix`, `born_prefix` | the cells of a tip are exactly the cells of a later tip of the chain born before its count, with the same births: two tips of one chain read as one history by their cells |
| | `quorum_overlap` | two lists of distinct keys of a policy of `n` hold at least `\|A\| + \|B\| - n` keys in common |
| `Morphism.lean` | `cross_seal_uniform`, `run_uniform`, `run2_uniform` | a cross-seal is on a cell: into two foreign targets of one policy, a source's edges latch together or not at all |
| | `no_faithful_import` | so where a source's edges are latched only in part in its own scope, no chain of the importing scope reads both as its source does |
| | `edgeCond_out_of_reach` | into a foreign target whose policy no keys of the roster meet, no seal latches an edge |
| | `import_faithful`, `stale_faithful` | on a closed set, local or pinned on each side, `Active` and `Stale` of two scopes agree if the latched edges into it do |
| | `pinned_active`, `unpinned_not_active` | with no latched edge into it and no supersedes edge, a foreign cell stands while its scope pins it; one it does not accept does not stand |
| `Witness.lean` | `witness_sound` | the witness checker `accepts` a derivation ⟹ the model holds its decision `Settled`, given that the decoded store agrees with the model and is the admitted chain (`Pin`); edges into the cone that do not count (proved unlatched, or from an Invalidated source) are admitted, an INVALID verdict withdraws only a key that seals it, under the verifier id of the verdict it withdraws, and nothing when proved not live, as §4.2 Pass 3 |
| | `latch_sound`, `unlatched_sound` | a quorum of `Pol(x)` sealing an edge's source under a scope of the chain latches it; none under any, with no key sealing both ends where the author clause applies, means it did not latch (given `Pin.latch`, `Pin.unlatch`) |
| | `edge_present`, `stale_pin`, `stale_complete` | the fold latches an edge only from a present cell, and Pass 2 `Stale` satisfies the equation `Pin` asks of it, both ways for an active local cell (three of `Pin`'s hypotheses) |
| `WitnessComplete.lean` | `kernel_iff` | on a store of local cells whose invalidates edges it decides, the prover's `effB` and `deadB` are the model's `Effective` and `Invalidated` above the rank |
| | `witness_complete` | on its fragment (no computation, only local cells, every edge the derivation reads decided by the store, every INVALID verdict on the decision live or not live through an Invalidated cell), the checker accepts the derivation `prove` builds from the store alone whenever the model holds the decision `Settled`, given that the decode is complete as well as faithful (`PinComplete`) and `relies`, invalidates and supersedes have ranks |
| | `accepts_iff_settled` | with `witness_sound`: there the checker accepts the prover's derivation exactly when the model holds the decision `Settled` |
| `WitnessGrounded.lean` | `unfounded_sound`, `unfounded_complete`, `not_grounded_iff_unfounded` | a cell is not Grounded iff some unfounded set holds it: a set none of whose members satisfies Grounded's equation when only the cells outside it are given; the cells that are not Grounded form one. No `Classical.choice`: over finite lists double negation passes through `∀` (`dn_forall_mem`, `grounded_dn`) |
| | `unfounded_of_each` | a finite certificate is checked member by member |
| | `circular_certificate` | on `circular_support`'s world, where both cells stand and `d0` is Settled, `[d0, w]` is an unfounded set |
| `Reader.lean` | `settled_frame` | between two tips that agree on what `Settled(d)` reads (`Reads`, on a set `Pr`), a contract, decision or question `d` is Settled at both or at neither. `Reads` asks: `d` is in `Pr`; every cell that judges `d` (`Judges`: it attests `d`, or is an INVALID verdict on `d` or on the checkpoint a cell attesting `d` names) is in both stores or in neither, is in `Pr`, and has the same endorsers; every checkpoint such a cell names is in `Pr`; every cell of `Pr` is live at both tips or at neither; the cells' verdict fields, `required_comp`, expected schema and replay result are the same; and `d` names an evaluator policy of its own or the two governing scopes have one admission policy. Also `QuorumExt` and faithful presentations at both tips |
| | `inWmax_frame`, `withdrawn_frame`, `counts_frame` | under `Reads`, `W_max(d)`, each withdrawal through a cell attesting `d`, and the keys that count are the same at both tips |
| | `grounded_frame` | on a set `Pr` closed under `relies` and under the witnesses of what it holds, whose cells are live and Authorized at both tips or at neither, and each contract, decision or question of which `Reads` relates, `Grounded` is the same at both tips |
| | `settled_reads_tip_scope` | two tips with the same cells, seals, standing and presentations, differing in the governing scope alone, and a decision with no evaluator policy of its own: Settled at one, not at the other. `Reads.policy` cannot be dropped |
| | `killer_latches`, `killer_latches2` | add to any commit a cell `z` that invalidates `d` and seals on `z`, under the governing scope, by keys of its roster for `d` that meet `Pol(d)`: the edge `z → d` is latched after the commit (v1; v2 when `z` is not a withheld scope). `QuorumAdd` |
| | `unread_commit_decides`, `unread_commit_decides2` | so for any chain `pre ++ cm :: post`, the chain with that cell and those seals added to `cm` has `d` Invalidated and not Effective at its tip, under every reading of Pass 1 over the fold's latches in which `z` is present, Accepted and named by no present cell's invalidates edge. The two chains agree on every commit but one |
| | `Reader.blind`, `reader_must_read` | a reader (an adaptive strategy that reads list positions and then answers) answers alike on two lists that agree wherever it read; so if they agree off position `j` and differ in a status it answers correctly on both, it read `j` |
| | `reader_reads_commit` | for the v1 fold: a reader that answers, correctly on the chain and on the chain with the killer, a status that on the latter holds only if `d` is Effective (`StandsAt`), reads the commit `cm` of a chain where the status holds. Hypotheses as `unread_commit_decides`, `z` local |
| | `fold_state_suffices`, `fold_state_suffices2` | two prefixes with one fold state have one fold state after every continuation |
| | `revived` | a present cell is Effective once every Effective cell that invalidates it by a latched edge has a fresh killer (`FreshKiller`: present, Accepted, its edge latched, named by no present cell's invalidates edge) |
| | `dead_cell_silent` | drop a cell that is not Effective from the store: with the same latches and the same `Accepted`, on a store whose invalidates edges climb a rank, `Effective` of every other cell is unchanged |
| | `dropped_cell_distinguishes` | `x` invalidates `v` by a latched edge and is `v`'s only attacker; where every Effective cell invalidating `x` has a fresh killer, the store that holds `x` has `v` not Effective and the store that dropped `x` has `v` Effective |
| `Pivot.lean` | `countIn_cons`, `countIn_filter_ne` | a threshold policy counts its distinct members among the keys: one more key adds one exactly when it is a member not yet among them, one fewer takes one exactly when it was |
| | `decisive_endorser_iff`, `decisive_withdrawal_iff` | one endorsement turns an unmet threshold quorum into a met one iff the key is a member, not yet counted, and the count is one short; one withdrawal unmeets it iff the key was counted and the count equals the threshold |
| | `decisive_settled_iff`, `decisive_unsettled_iff` | the same for Settled of a contract or decision, through `settled_iff_keys`, when the act changes the keys that count by that one key and leaves the standing and the policy |
| | `grounded_mono` | if every live cell stays live, every authorization stays, the policies stay and the witnesses and their counted keys only grow, every Grounded cell stays Grounded; read the other way, an act that only removes only removes |
| | `decisive_cascade_grounded` | under the same, a cell whose equation holds once `u` and what was Grounded before are given is Grounded once `u` is: one endorsement of a foundation grounds every cell that waited only for it |
| `Delta.lean` | `rtc_flip` | any number of steps of the inverse relation is any number of steps of the relation, reversed |
| | `up_settled_iff` | a frame given by its steps (a judge or named checkpoint, then what that relies on, then what enters by an edge or is superseded): walking up the inverse of each step, in the reverse order, reaches `d` from `y` iff `y` is in `d`'s Settled frame |
| | `up_grounded_iff` | the same for Grounded, whose frame first closes over the evaluated cells it reads |
| | `unreached_frame_untouched` | so the decisions the walk does not reach from a commit's touch points are exactly those with no touch point in their frame |
| `Cut.lean` | `grounded_keeps_of_no_cut` | the cut world of a coalition (the cells it cannot attack, its keys withdrawn from every count) is Grounded's own fixed point on a smaller world; if the cells it cannot attack stay live, its witnesses stay witnesses and every key not its own still counts, whatever it does leaves Grounded every cell the cut world grounds |
| | `grounded_cut_attained` | and a commit after which a live cell is a live cell that stays, a witness one that stays, and a counted key one that counted and is not the coalition's leaves Grounded no more than the cut world: the strongest blow is one least fixed point |
| | `grounded_needs_gain`, `grounded_gain_attained` | the same for what a coalition can ground: with its keys counted for every cell (`GroundedGain`) a bound on every commit of its own, and reached by a commit that attests every cell with a fresh verdict that relies on nothing |
| | `illusion_of_quorum` | every quorum 2 of 3; the key `a` endorses nothing `D` counts and `D` stays Settled in `a`'s cut world, yet the cut world does not ground `D`: one key takes Grounded from a cell it never signed |

## Executable lens

`Exec.lean` computes lens Passes 1–2 from the facts the rules kernel sees — cell structure from its input,
`Authorized` and edge authorization from its fold's output — and `ExecProof.lean` proves it equal to the model
(hypotheses: every reference names an older cell, which the kernel enforces; no cell is both an acceptance and a
verdict). It is compiled as `vars1exec`, and the property suite checks on every admitted tip that its status bytes
equal `kernel/lens.wasm`'s (I9). So the kernel's Passes 1–2 are compared with proved code, not with another
unproved implementation. Reverting `Superseded`'s transitivity in `Exec.lean` breaks the proof and fails I9.

The compiled code is not `Exec.lean`'s `fill`, `fillUp` and `staleOf` as written: those build their results from
nested closures and always run `n` rounds of Pass 2, which took seconds at 75 cells and did not finish at the live
chain's 600. `@[csimp]` theorems (`fill_eq_fast`, `fillUp_eq_fast`, `staleOf_eq_fast`) prove array-backed versions,
and a Pass 2 that stops at the first round changing nothing, equal to them; the compiler substitutes a constant only by
a proved equal one, so `pass1_correct` and `stale_correct` hold of what runs. Under v2 the facts' references are the
input's typed list (RULES-V2.md §3) instead of every payload or slot equal to a cell id: Passes 1–2 read references,
not the encoding, so the same proofs apply.

## Cycle witnesses

`SigmaEval/ResumeCycle.lean` (sigma-glyph's, copied in at tag v1.0.0; written here first and moved there on
2026-11-01) defines `checkCycle`, `sigma_resume.verify_cycle` written over the abstract machine
in its order: positive `n ≤ cost`; the period's cost against the host ceiling (`NOT_ASSESSED`); the prefix `advance`
by `entry_spent`, whose own admission ceiling turns `entry_spent > max_atp` into a refusal (`PREFIX_MISMATCH`, not
`NOT_ASSESSED`); the prefix must spend exactly `entry_spent`, stop `PAUSED` and stop at the entry; the period, `_run`
with `max_actions = n` and `cost` available, must do `n` actions, spend `cost` and return to the entry. It is compiled
as `vars1cycle` over finite transition tables, and the property suite checks on generated tables and witnesses, true
ones and their neighbours, that `verify_cycle` with the table substituted for `STEP`, and the two functions the gate
and the lens call (`vars1.gate_cycle_witness`, `vars1.cycle_witness_answers`), give its verdict (I12). So the gate's cycle check is compared with the checker the theorem is
about, not trusted. A mutant of the model that changes a verdict but not soundness (prefix admission read as
`NOT_ASSESSED`; the ceiling checked before `n = 0`) fails I12; one that weakens it breaks the proof.

## Hypotheses (explicit, not axioms)

- SHA-256 is injective on admitted bytes, so a cell is a function of its id.
- A valid seal was signed by its key holder over `(target, ctx)`.
- §1.2 Rule 6 holds at every admitted commit (the gate enforces it).
- Rotations are admitted as §3 check 1 requires (`RotationAdmitted`), every local scope cell present has governed at
  some commit, and scope cells are Effective and Accepted (no edge may invalidate or retire a scope cell).
- `HostSound`: host resource fences only stop a replay; they never alter a reported result.
- `QuorumMet(∅, p)` is false (`POL1` threshold ≥ 1).
- For `grounded_settled` and `settled_keeps`: a quorum stays met as endorsers are added (`QuorumMono`, `QuorumAdd`); for
  `settled_iff_keys`: it depends only on which keys are in the list (`QuorumExt`). `POL1` thresholds count distinct keys.
- For the frame theorems: the attack relation points from newer to older cells (`rank`), the set is closed under who
  attacks it and what it supersedes, and only a present cell is Effective. For `settled_keeps`: its witnesses stay
  witnesses, its endorsers stay endorsers, and every withdrawal after the coalition acts was there or is the coalition's.
  The frame theorems give all three only where the set holds the verdicts, the INVALID ones too: a coalition that revives
  another key's dormant INVALID verdict, by invalidating what kept it stale, does take that key's endorsement away, and
  there the third hypothesis fails. `settled_keeps` does not say a key's endorsement can never be taken; it says one
  cannot be taken by a verdict of another's own.
- For `settled_frame` and `grounded_frame`: that the cells of the frame are live at both tips or at neither is a
  hypothesis (`Reads.live`). `active_frame` and `stale_frame` give it on a set of local cells closed under `relies`, under
  what it supersedes and under who attacks it, into which no new edge latches; the two are not composed into one theorem,
  because Pass 2 is stated on `Fin N` and Pass 3 on an abstract `Live`. The rules are the same at both tips (one `World`):
  a rules change reads the history again, and no frame survives it.
- For `unread_commit_decides`: the model makes no refusal. The gate refuses a cell that names a cell not yet in the
  store, so on an admitted chain the commit `cm` is `d`'s own or a later one; the theorem holds of any commit because the
  model's fold latches such an edge. The killer `z` is a hypothesis: a cell whose content invalidates `d`, which no
  present cell names, with a quorum of `Pol(d)` in the governing roster. A quorum that the roster cannot meet (a
  decision of tier provisional whose evaluator policy names keys outside it) leaves no such commit, and then the bound
  says nothing.
- For `dead_cell_silent`: both readings have one `Accepted` (every cell local, or acceptance untouched by the dropped
  cell).
- For `settled_cycle_no_normal_form`: no term hash equals `H_CYCLE_PROVEN` (a term hash is the id of a Book I node,
  `H_CYCLE_PROVEN` the id of the atom `UTF8CYCLE_PROVEN`).

## Not linked

- Pass 3 and Grounded of `vars1.py` and `verify/minds_verify.py` to `Pass3.lean` and `Grounded.lean`: no Lean executable
  computes them. They are held to the spec by the property suite's own oracle (I11, I13), not by the model.
- `Morphism.lean`'s two worlds are hypotheses on two scopes' readings of one set of cells (`SameBytes`, `Faithful`), not two chains folded
  side by side, and no theorem reaches Pass 3 across scopes: tests 127 and 128 hold what Settled does, and `vars1.lag` has no model.
- `confinement` does not state that the fold's `Present` and the Pass 1 equations hold of a given chain: as with `Pin`,
  they are hypotheses. A rotation the coalition makes is outside it: the gate refuses one without its quorum (E-20), and
  the model makes no refusal. `GitVarsRepo.power` reads the same rules in Python; a search through the gate holds it
  (`test_vars1.py` 106), one commit deep, where nothing yet attacks what the status reads.

- `GitVarsRepo.power`'s `grounded` row to `Cut.lean`: which cells a coalition can attack is `Power.lean`'s, and that a
  commit of the coalition meets `grounded_keeps_of_no_cut`'s premises (its keys counted, others' kept, witnesses kept)
  is the gate's, held by the search of `test_vars1.py` 133 on five chains, one commit deep, with every move of one
  commit and the two moves of everything at once.

- `check.py --unfounded` to `WitnessGrounded.lean`: the check is `unfounded_of_each` read over the store in Python.
  Its reasons are `down` (the Lean checker's rule), relies on a member, a quorum missed by every key that seals a
  verdict outside the set that is not down, and `stand` answering False, which no Lean rule concludes; tests 27–28
  hold it to the lens (no Grounded decision is ever UNFOUNDED). `vars1witness` has no `ground` rule yet.

- `experiments/witness/frame.py` to `Reader.lean`: the program that computes a frame and says whether later commits touch
  it is Python. Tests 17–19 of `experiments/witness/test_witness.py` hold "nothing touches it" to the lens's statuses
  through the gate and on every pair of tips of the live chain; no Lean executable computes a frame. `Reader`, the
  strategy of `reader_reads_commit`, reads commits by position and is no model of a program with an index of reverse
  edges: a reader given a commitment to who names a cell is outside it, which is the point.

- `tools/minds_chain.py next` to `Pivot.lean`: its in-memory reading of one act (`NextTip.predict`) is Python. It
  calls the lens's own fixed point for Grounded (`vars1.grounded_lfp`), and test 132 holds every act of its menu, and
  every seal of every key on every cell, to the gate (`GitVarsRepo.what_if`), both ways; on the live chain the same.

- `experiments/witness/delta.py` to `Delta.lean`: the walk is Python, and so is the link from `touches` to the
  frame's steps. Test 25 holds `dirty` to `touches` on every pair of tips of three random chains and of the shapes
  they never reach, test 26 on the live chain; that an untouched frame keeps its status is tests 17–19, as above.

- `EvalMachine.step` to the Python `step5` (only the differential bridge in sigma-glyph).
- `sigma_resume._run` to `run`: the loop is transcribed by hand.
- SGS1 bytes to `(Store, Term)`; `term_hash`; `ComputationRoot` to the start state.
- The rich runtime profile (`ski+Y+M+W`) is not mechanized; it is the profile with known state cycles (`M M`,
  `Y I`), so for it `cycle_proven_no_normal_form` holds of any machine but no Lean transition is instantiated.
- `sigma_resume.verify_cycle` to `checkCycle`: tied by differential testing (I12) on finite tables, not by a proof
  about the Python. Its checks on documents (witness shape and integer domain, `computation_id` against the chosen
  root, the root's environment, runtime and cost model) and its host fences (resource checks, recursion depth,
  absent evidence: refusals) are outside the model; they only refuse. The tables do not reach those fences.
- A cycle witness's payload to its entry state: the gate compares `id(state)`, the model compares states (SHA-256
  injectivity).
- `kernel/lens.wasm`'s Passes 1–2 are tied to the proved executable lens by differential testing (I9), not by a
  proof about the Rust or wasm code.
- The kernel's fold is tied to `Fold.lean` by differential testing: `vars1fold` compiles the model's own `run`
  (no transcription) over facts read from the kernel's input, and the property suite checks on every admitted tip
  that its governing scope, Authorized bits and edge authorizations equal the kernel's (I10). Making the model let
  an author invalidate alone is caught by I10.
- `kernel2/lens2.wasm`'s fold is tied to `Fold2.lean` the same way: `vars1fold` runs `run2` on a v2 input, with the
  rules each scope names and the typed references. I10 and I9 run on the v2 property sequences (rotations waiting by
  consent and by the 16 commits), on `test_vars1.py` 88's rules changes (a veto, the window's last commit, a change
  governing after 16; the last was missing until Codex's challenge `a6cb6991`, and test 88 now reads it from the
  inputs' bytes; the property sequences never rotate to other rules, so these are I10's only rules changes) and on
  every tip of the live chain `refs/vars/heads/minds` (68 v1 tips, 13 v2: the rotation to v2 in a v1 epoch, then joins
  under v2). A `DELAY` of 15 in the model fails I10. `Fold2.lean`'s theorems about the wait assume the chain as the
  gate admits it (`Fresh`, and `RotationAdmitted` for `run2_v1`); the model makes no refusal (E-24, E-25, −6, −7).

## Mutants

Each of these breaks the build: dropping the authorized-supersedes clause of `Active`;
non-transitive `Superseded`; dropping `¬Superseded` from `Active`; live acceptance from Stale
acceptances; recomputing live acceptance mid-round; unlatching edges; re-fixing InitialEndorsers;
pooling seals across scopes; a verifier that ignores the parent's status (also refuted by
`pre_lineage_unsound`); dropping the `spent_total`, state or normal-form checks; counting a host
local outcome as `REPLAYED`; replaying from the start regardless of the parent; in `checkCycle`, dropping the
return-to-entry, actions-done, prefix-spent, entry-state or `n = 0` check, or miscounting `runN`'s actions; in Pass 3,
a cycle witness of another computation. Three break `Reader.lean` and leave `Power.lean` and `Grounded.lean` building:
a witness that need not attest what it judges (`inWmax_frame`), an INVALID verdict that withdraws whatever cell it is on
(`withdrawn_frame`), an evaluator policy that is always the tip scope's (`evalPol_frame`). A killer that need not be
Effective breaks `Pass1.lean` first, and an invalidates edge that also needs an initial endorser breaks `Power.lean` first.
