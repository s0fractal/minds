import Vars1.Fold
import Vars1.Scope

/-!
# §4.1 Commit-chain fold under `H_LENS_KERNEL_V2` (latches 4a and 4b)

v2 keeps v1's latches 1–3 and changes step 4 (RULES-V2.md, VARS-1-SPEC.md §4.1):

* **4a, rotation delay.** While the governing scope `S` names rules other than v1, a rotation to `S'` that removes a
  key of `S`'s admission or acceptance policy, before that key has sealed `S'` under `S`, **waits**: `S` keeps
  governing, and `S'`'s supersedes edge is withheld from latch 3. `S'` governs after the commit in which every
  removed key has sealed it, or after the 16th commit following its admission, whichever comes first; its supersedes
  edge latches then. In a v1 epoch every rotation takes effect at once, as v1 has it.
* **4b, rules-change quarantine.** While `S` names rules other than v1, a rotation whose `S'` names other rules than
  `S` waits the 16 commits whatever its consent. A new local cell of the window that references `S'` (by the input's
  typed reference list), sealed under `S` by a key of `S`'s admission policy, cancels it for good: `S'` never
  governs and its supersedes edge never latches.

`World2` adds what the v2 fold reads and v1's does not: the rules each scope names (`0` is v1), the keys of a policy,
and each cell's typed references. `step2` is the v2 module's fold commit by commit (`kernel2/src/lib.rs`, `fold`),
compiled into `vars1fold` and compared with the module on every tip (property I10).

Theorems here:
* `stateAt2_mono` — latches (edges, `Authorized`) never unlatch, InitialEndorsers of a born cell never change.
* `stateAt2_append` — non-retroactivity: the state at the start of `T_i` ignores every later commit.
* `stateAt2_at` — the state at the start of `T_i` has counted `i` commits.
* `run2_v1` — over a chain whose governing scope names v1 at every commit, the v2 fold is v1's (`Fold.lean`), latch
  for latch, when rotations are admitted as the gate requires (`RotationAdmitted`): v2 reads v1 epochs as v1 did.
* `moves_notice` — **latch 4a.** When the governing scope moves under rules other than v1, the new scope was
  admitted at some commit `t`, and either 16 commits have passed since, or no rules change is involved and every key
  it removes has sealed it under the old scope.
* `moves_quarantine` — **latch 4b.** When it moves to other rules under rules other than v1, 16 commits have passed
  since the admission, and no veto was born in between.
* `step2_governs` — and conversely: a rotation not vetoed governs from the commit after its wait is over, its
  supersedes edges latching then; `step2_vetoes` — a veto cancels it, and nothing moves.
* `waiting_withheld` — a scope that waits or was vetoed latches no edge of its own; `waiting_not_active` — so it is
  not Active, and the Active local scope stays the governing one.
* `vetoed_never_governs` — a vetoed rules change never becomes the governing scope.

The theorems about the wait read the chain as the gate admits it: no edge or veto before the first commit, and each
commit's new scope a cell of that commit not present before it (`Fresh`); `run2_v1` also assumes `RotationAdmitted`
(`Scope.lean`). They say nothing of refusals (E-24, E-25, −6, −7), which the model does not make: on an admitted
chain they never occur.
-/

set_option linter.unusedSectionVars false

namespace Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K]

/-- A VARS-1 world with what the v2 fold reads besides v1's: `rules c` is the rules a scope cell names (`slots[2]`;
`0` is `H_LENS_KERNEL`, v1), `keys p` the keys of a policy, `typed c` the cells `c` references by the input's typed
reference list (RULES-V2.md §3; not its edges). -/
structure World2 (C K P : Type) extends World C K P where
  rules : C → Nat
  keys : P → List K
  typed : C → List C

/-- How many commits a rotation waits at most (latches 4a and 4b). -/
def DELAY : Nat := 16

/-- v2 fold state at the start of a commit: v1's, the number of commits folded (`tick`), the waiting rotation
(its scope, the commit that admitted it, whether it is a rules change), the vetoed scopes, and the commit each
present cell was born in. -/
structure St2 (C K : Type) extends St C K where
  tick : Nat
  waiting : Option (C × Nat × Bool)
  cancelled : C → Bool
  born : C → Nat

variable (W : World2 C K P)

/-- Does scope `S` name v1? -/
def namesV1 (S : C) : Bool := W.rules S == 0

/-- Keys of `S`'s admission or acceptance policy that `S'`'s same policy lacks and that have not sealed `S'` under
`S` in commit `cm` (whose seals are those of its tree, so every seal admitted so far). -/
def unconsented (cm : Commit C K) (S S' : C) : List K :=
  let lacks (old new : P) : List K :=
    (W.keys old).filter fun k =>
      !(W.keys new).contains k && !(cm.seals.any fun s => decide (s.target = S') && decide (s.ctx = S) && decide (s.key = k))
  lacks (W.info S).pol0 (W.info S').pol0 ++ lacks (W.info S).pol1 (W.info S').pol1

/-- Latch 4a: must the rotation from `S` to `S'` wait at `cm`? Only while `S` names rules other than v1. -/
def waits (cm : Commit C K) (S S' : C) : Bool :=
  !namesV1 W S && !(unconsented W cm S S').isEmpty

/-- Latch 4b: is a rotation from `S` to `S'` a rules change that waits? Only while `S` names rules other than v1. -/
def change (S S' : C) : Bool := !namesV1 W S && W.rules S' != W.rules S

/-- A veto of the waiting `s`, admitted at `t`, at commit `cm`: a local cell born after `t` that references `s` by
its typed list and carries a seal under `S` by a key of `S`'s admission policy. -/
def vetoed (cm : Commit C K) (S s : C) (t : Nat) (present : List C) (born : C → Nat) : Bool :=
  present.any fun c =>
    (W.info c).isLocal && decide (t < born c) && (W.typed c).contains s &&
      cm.seals.any fun x => decide (x.target = c) && decide (x.ctx = S) && (W.keys (W.info S).pol0).contains x.key

/-- The rotation that a commit starts: its new scope, unless another rotation waits (the gate refuses that, E-24). -/
def pending (st : St2 C K) (cm : Commit C K) : Option C :=
  if st.waiting.isSome then none else cm.newScope

/-- Is `w` a scope whose edges latch 3 skips: the waiting one, a new one that will wait, or a vetoed one? -/
def withheld (st : St2 C K) (cm : Commit C K) (w : C) : Bool :=
  (st.waiting.map (·.1) == some w) ||
    (pending st cm == some w && (change W st.scope w || waits W cm st.scope w)) || st.cancelled w

/-- Latches 1–3 of one commit, with the rotation it starts recorded as waiting (step 4 not yet applied). -/
def latch2 (st : St2 C K) (cm : Commit C K) : St2 C K :=
  let S := st.scope
  let present' := st.present ++ cm.newCells
  let init' := initAfter W.toWorld st.toSt cm
  { scope := S
    present := present'
    initEnd := init'
    authorized := fun a => authLatch W.toWorld st.toSt cm a || decide (pending st cm = some a)
    edge := fun w v k =>
      st.edge w v k ||
        (decide (w ∈ present') && decide (v ∈ (W.info w).edges k) && !withheld W st cm w &&
          edgeCond W.toWorld cm S w v k init')
    tick := st.tick + 1
    waiting := match pending st cm with
      | some s => some (s, st.tick, change W S s)
      | none => st.waiting
    cancelled := st.cancelled
    born := fun v => if v ∈ cm.newCells ∧ v ∉ st.present then st.tick else st.born v }

/-- Step 4 at the end of commit `cm` (whose index is `now`): a vetoed rules change is cancelled; a waiting rotation
whose wait is over governs from the next commit, and its supersedes edges latch. -/
def settle2 (cm : Commit C K) (now : Nat) (st : St2 C K) : St2 C K :=
  match st.waiting with
  | none => st
  | some (s, t, ch) =>
    if ch && vetoed W cm st.scope s t st.present st.born then
      { st with waiting := none, cancelled := fun c => st.cancelled c || decide (c = s) }
    else if decide (t + DELAY ≤ now) || (!ch && !waits W cm st.scope s) then
      { st with
        scope := s
        waiting := none
        edge := fun w v k => st.edge w v k ||
          (decide (w = s) && decide (k = .supersedes) && decide (v ∈ (W.info s).supersedes)) }
    else st

/-- One commit of the v2 fold. -/
def step2 (st : St2 C K) (cm : Commit C K) : St2 C K :=
  settle2 W cm st.tick (latch2 W st cm)

/-- Fold over a list of commits. -/
def run2 (s0 : St2 C K) (cs : List (Commit C K)) : St2 C K := cs.foldl (step2 W) s0

/-- The state at the start of `T_i`. -/
def stateAt2 (s0 : St2 C K) (chain : List (Commit C K)) (i : Nat) : St2 C K :=
  run2 W s0 (chain.take i)

/-! ## Monotonicity, non-retroactivity, the commit count -/

theorem latch2_le (st : St2 C K) (cm : Commit C K) : st.toSt.le (latch2 W st cm).toSt := by
  refine ⟨?_, ?_, ?_⟩
  · intro w v k h; simp [latch2, h]
  · intro x h; simp [latch2, authLatch, h]
  · intro x hx
    refine ⟨by simp [latch2, hx], ?_⟩
    simp [latch2, initAfter, hx]

theorem settle2_le (cm : Commit C K) (now : Nat) (st : St2 C K) : st.toSt.le (settle2 W cm now st).toSt := by
  unfold settle2
  split
  · exact St.le_refl _
  · split
    · exact St.le_refl _
    · split
      · exact ⟨fun w v k h => by simp [h], fun _ h => h, fun _ h => ⟨h, rfl⟩⟩
      · exact St.le_refl _

theorem step2_le (st : St2 C K) (cm : Commit C K) : st.toSt.le (step2 W st cm).toSt :=
  St.le_trans (latch2_le W st cm) (settle2_le W cm st.tick _)

theorem run2_le (s0 : St2 C K) (cs : List (Commit C K)) : s0.toSt.le (run2 W s0 cs).toSt := by
  induction cs generalizing s0 with
  | nil => exact St.le_refl _
  | cons c cs ih => exact St.le_trans (step2_le W s0 c) (ih (step2 W s0 c))

theorem run2_append (s0 : St2 C K) (xs ys : List (Commit C K)) :
    run2 W s0 (xs ++ ys) = run2 W (run2 W s0 xs) ys := by
  simp [run2, List.foldl_append]

/-- **Latches are monotone under v2.** For `i ≤ j`, every edge and `Authorized` latch at the start of `T_i` is still
latched at the start of `T_j`, and InitialEndorsers fixed by then are unchanged. -/
theorem stateAt2_mono (s0 : St2 C K) (chain : List (Commit C K)) {i j : Nat} (hij : i ≤ j) :
    (stateAt2 W s0 chain i).toSt.le (stateAt2 W s0 chain j).toSt := by
  unfold stateAt2
  have : chain.take j = chain.take i ++ (chain.take j).drop i := by
    conv => lhs; rw [← List.take_append_drop i (chain.take j)]
    rw [List.take_take, Nat.min_eq_left hij]
  rw [this, run2_append]
  exact run2_le W _ _

/-- **Non-retroactivity under v2.** The state at the start of `T_i`, the waiting rotation and the vetoes included,
does not depend on any commit at or after `T_i`. -/
theorem stateAt2_append (s0 : St2 C K) (chain future : List (Commit C K)) {i : Nat}
    (hi : i ≤ chain.length) :
    stateAt2 W s0 (chain ++ future) i = stateAt2 W s0 chain i := by
  simp [stateAt2, List.take_append_of_le_length hi]

theorem stateAt2_succ (s0 : St2 C K) (chain : List (Commit C K)) {i : Nat}
    (hi : i < chain.length) :
    stateAt2 W s0 chain (i + 1) = step2 W (stateAt2 W s0 chain i) chain[i] := by
  unfold stateAt2
  rw [List.take_add_one, List.getElem?_eq_getElem hi, run2_append]
  rfl

theorem settle2_tick (cm : Commit C K) (now : Nat) (st : St2 C K) : (settle2 W cm now st).tick = st.tick := by
  unfold settle2
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem step2_tick (st : St2 C K) (cm : Commit C K) : (step2 W st cm).tick = st.tick + 1 := by
  simp [step2, settle2_tick, latch2]

/-- The state at the start of `T_i` has counted the `i` commits before it. -/
theorem stateAt2_at (s0 : St2 C K) (chain : List (Commit C K)) {i : Nat} (hi : i ≤ chain.length) :
    (stateAt2 W s0 chain i).tick = s0.tick + i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [stateAt2_succ W s0 chain (by omega), step2_tick, ih (by omega), Nat.add_assoc]

/-! ## v2 reads v1 epochs as v1 did -/

theorem St.ext' {a b : St C K} (h1 : a.scope = b.scope) (h2 : a.present = b.present) (h3 : a.initEnd = b.initEnd)
    (h4 : a.authorized = b.authorized) (h5 : a.edge = b.edge) : a = b := by
  cases a; cases b; simp_all

/-- One commit in a v1 epoch, with no rotation waiting and none vetoed: the v2 fold makes v1's step, provided the
commit's rotation, if any, supersedes exactly the governing scope by an edge that latch 3 authorizes (the gate's
check of its quorum, E-20). -/
theorem step2_v1 (st : St2 C K) (cm : Commit C K)
    (hw : st.waiting = none) (hc : ∀ c, st.cancelled c = false) (hv1 : namesV1 W st.scope = true)
    (hrot : ∀ S', cm.newScope = some S' →
      S' ∈ cm.newCells ∧ (W.info S').supersedes = [st.scope] ∧
      edgeCond W.toWorld cm st.scope S' st.scope .supersedes (initAfter W.toWorld st.toSt cm) = true) :
    (step2 W st cm).toSt = step W.toWorld st.toSt cm ∧ (step2 W st cm).waiting = none ∧
      (step2 W st cm).cancelled = st.cancelled := by
  have hchg : ∀ s, change W st.scope s = false := by intro s; simp [change, hv1]
  have hwaits : ∀ s, waits W cm st.scope s = false := by intro s; simp [waits, hv1]
  have hwh : ∀ w, withheld W st cm w = false := by intro w; simp [withheld, hw, hc, hchg, hwaits]
  cases hns : cm.newScope with
  | none =>
    have hp : pending st cm = none := by simp [pending, hw, hns]
    refine ⟨St.ext' ?_ ?_ ?_ ?_ ?_, ?_, ?_⟩ <;>
      simp [step2, settle2, latch2, hp, hw, step, hns, hwh]
  | some s =>
    obtain ⟨hnew, hsup, hcond⟩ := hrot s hns
    have hp : pending st cm = some s := by simp [pending, hw, hns]
    have hgov : settle2 W cm st.tick (latch2 W st cm) =
        { latch2 W st cm with
          scope := s, waiting := none
          edge := fun w v k => (latch2 W st cm).edge w v k ||
            (decide (w = s) && decide (k = .supersedes) && decide (v ∈ (W.info s).supersedes)) } := by
      simp [settle2, latch2, hp, hchg, hwaits]
    have hstep : step2 W st cm = _ := hgov
    rw [hstep]
    refine ⟨St.ext' ?_ ?_ ?_ ?_ ?_, rfl, ?_⟩
    · simp [step, hns]
    · simp [step, latch2]
    · simp [step, latch2]
    · funext a; simp [step, latch2, hp, hns, eq_comm]
    · funext w v k
      simp only [step, latch2, hwh]
      by_cases h : w = s ∧ k = .supersedes ∧ v ∈ (W.info s).supersedes
      · obtain ⟨rfl, rfl, hv⟩ := h
        rw [hsup, List.mem_singleton] at hv
        subst hv
        have hm : w ∈ st.present ++ cm.newCells := List.mem_append_right _ hnew
        have he : st.scope ∈ (W.info w).edges .supersedes := by simp [CellInfo.edges, hsup]
        simp [hm, he, hcond]
      · have : (decide (w = s) && decide (k = .supersedes) && decide (v ∈ (W.info s).supersedes)) = false := by
          by_cases h1 : w = s <;> by_cases h2 : k = .supersedes <;> simp_all
        simp [this]
    · simp [latch2]

/-- **v2 reads v1 epochs as v1 did (fold).** Over a chain whose governing scope names v1 at the start of every commit,
starting with no rotation waiting and none vetoed, the v2 fold's state at the start of every `T_i` is v1's
(`Fold.lean`), latch for latch, if rotations are admitted as the gate requires (`RotationAdmitted`, and each new scope
supersedes exactly the governing one). A rotation to v2 made in such an epoch is one of these commits: it governs at
once. -/
theorem run2_v1 (s0 : St2 C K) (chain : List (Commit C K))
    (hw : s0.waiting = none) (hc : ∀ c, s0.cancelled c = false)
    (hv1 : ∀ i, i < chain.length → namesV1 W (stateAt W.toWorld s0.toSt chain i).scope = true)
    (hR : RotationAdmitted W.toWorld s0.toSt chain)
    (hS : ∀ (i : Nat) (hi : i < chain.length) (S' : C), chain[i].newScope = some S' →
      (W.info S').supersedes = [(stateAt W.toWorld s0.toSt chain i).scope]) :
    ∀ i, i ≤ chain.length → (stateAt2 W s0 chain i).toSt = stateAt W.toWorld s0.toSt chain i ∧
      (stateAt2 W s0 chain i).waiting = none ∧ (stateAt2 W s0 chain i).cancelled = s0.cancelled := by
  intro i
  induction i with
  | zero => intro _; exact ⟨rfl, hw, rfl⟩
  | succ i ih =>
    intro hi
    have hil : i < chain.length := by omega
    obtain ⟨heq, hwi, hci⟩ := ih (by omega)
    rw [stateAt2_succ W s0 chain hil, stateAt_succ W.toWorld s0.toSt chain hil]
    have hstep := step2_v1 W (stateAt2 W s0 chain i) chain[i] hwi (by intro c; rw [hci]; exact hc c)
      (by
        have : (stateAt2 W s0 chain i).scope = (stateAt W.toWorld s0.toSt chain i).scope := by
          rw [← heq]
        rw [this]; exact hv1 i hil)
      (by
        intro S' hns
        obtain ⟨hnew, _, hcond⟩ := hR i hil S' hns
        have hsc : (stateAt2 W s0 chain i).scope = (stateAt W.toWorld s0.toSt chain i).scope := by rw [← heq]
        refine ⟨hnew, by rw [hsc]; exact hS i hil S' hns, ?_⟩
        rw [hsc]
        have : (stateAt2 W s0 chain i).toSt = stateAt W.toWorld s0.toSt chain i := heq
        rw [this]; exact hcond)
    obtain ⟨h1, h2, h3⟩ := hstep
    refine ⟨?_, h2, h3.trans hci⟩
    rw [h1, heq]

/-! ## Latches 4a and 4b: when the governing scope may move -/

/-- Every key that the rotation from `S` to `S'` removes from `S`'s admission or acceptance policy has sealed `S'`
under `S` in `cm`'s tree. -/
def Consented (cm : Commit C K) (S S' : C) : Prop :=
  ∀ k, (k ∈ W.keys (W.info S).pol0 ∧ k ∉ W.keys (W.info S').pol0 ∨
        k ∈ W.keys (W.info S).pol1 ∧ k ∉ W.keys (W.info S').pol1) →
    ∃ x ∈ cm.seals, x.target = S' ∧ x.ctx = S ∧ x.key = k

theorem filter_nil_false {α : Type} {l : List α} {p : α → Bool} (h : l.filter p = []) {x : α} (hx : x ∈ l) :
    p x = false := by
  cases hp : p x
  · rfl
  · have : x ∈ l.filter p := List.mem_filter.mpr ⟨hx, hp⟩
    rw [h] at this; cases this

theorem consented_of_waits (cm : Commit C K) (S S' : C) (hv : namesV1 W S = false)
    (h : waits W cm S S' = false) : Consented W cm S S' := by
  have hu : unconsented W cm S S' = [] := by
    cases hu : unconsented W cm S S' with
    | nil => rfl
    | cons _ _ => simp [waits, hv, hu] at h
  have hu' := List.append_eq_nil_iff.mp hu
  intro k hk
  have hseal : ∀ (new : List K), k ∉ new →
      (!new.contains k &&
        !(cm.seals.any fun s => decide (s.target = S') && decide (s.ctx = S) && decide (s.key = k))) = false →
      ∃ x ∈ cm.seals, x.target = S' ∧ x.ctx = S ∧ x.key = k := by
    intro new h2 h3
    have hc : new.contains k = false := by
      cases hc : new.contains k
      · rfl
      · exact absurd (List.contains_iff_mem.mp hc) h2
    have hany : (cm.seals.any fun s => decide (s.target = S') && decide (s.ctx = S) && decide (s.key = k)) = true := by
      cases ha : (cm.seals.any fun s => decide (s.target = S') && decide (s.ctx = S) && decide (s.key = k))
      · rw [hc, ha] at h3; cases h3
      · rfl
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp hany
    refine ⟨x, hx, ?_⟩
    cases h1 : decide (x.target = S') <;> cases h2 : decide (x.ctx = S) <;> cases h3 : decide (x.key = k) <;>
      simp only [h1, h2, h3, Bool.and_false, Bool.false_and, Bool.and_true] at hp <;> cases hp
    exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, of_decide_eq_true h3⟩
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hseal _ h2 (filter_nil_false hu'.1 h1)
  · exact hseal _ h2 (filter_nil_false hu'.2 h1)

theorem latch2_waiting (st : St2 C K) (cm : Commit C K) {s : C} {t : Nat} {ch : Bool}
    (h : (latch2 W st cm).waiting = some (s, t, ch)) :
    (st.waiting = none ∧ cm.newScope = some s ∧ t = st.tick ∧ ch = change W st.scope s) ∨
      st.waiting = some (s, t, ch) := by
  simp only [latch2] at h
  cases hp : pending st cm with
  | none =>
    rw [hp] at h; right; exact h
  | some s' =>
    rw [hp] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    left
    unfold pending at hp
    cases hw : st.waiting with
    | none => simp [hw] at hp; exact ⟨rfl, hp, rfl, rfl⟩
    | some _ => simp [hw] at hp

/-- Step 4 of one commit: the scope it leaves governing and the rotation it leaves waiting. Either nothing moved and
the waiting rotation, if any, still has a reason to wait; or the rotation that `latch2` records governs now, not
vetoed, after its 16 commits or, outside a rules change, with every removed key's seal. -/
theorem settle2_cases (cm : Commit C K) (now : Nat) (st : St2 C K) :
    ((settle2 W cm now st).scope = st.scope ∧
      ((settle2 W cm now st).waiting = none ∨
        ((settle2 W cm now st).waiting = st.waiting ∧
          ∀ s t ch, st.waiting = some (s, t, ch) → (ch = true ∨ waits W cm st.scope s = true)))) ∨
    (∃ t ch, st.waiting = some ((settle2 W cm now st).scope, t, ch) ∧ (settle2 W cm now st).waiting = none ∧
      (ch && vetoed W cm st.scope (settle2 W cm now st).scope t st.present st.born) = false ∧
      (t + DELAY ≤ now ∨ (ch = false ∧ waits W cm st.scope (settle2 W cm now st).scope = false))) := by
  unfold settle2
  cases hw : st.waiting with
  | none => left; exact ⟨rfl, Or.inl hw⟩
  | some w =>
    obtain ⟨s, t, ch⟩ := w
    simp only
    by_cases hv : (ch && vetoed W cm st.scope s t st.present st.born) = true
    · rw [if_pos hv]; left; exact ⟨rfl, Or.inl rfl⟩
    · rw [if_neg hv]
      by_cases hc : (decide (t + DELAY ≤ now) || (!ch && !waits W cm st.scope s)) = true
      · rw [if_pos hc]; right
        refine ⟨t, ch, rfl, rfl, by simpa using hv, ?_⟩
        by_cases ht : t + DELAY ≤ now
        · exact Or.inl ht
        · right; simp [ht] at hc; exact hc
      · rw [if_neg hc]; left
        refine ⟨rfl, Or.inr ⟨hw, ?_⟩⟩
        intro s' t' ch' he
        simp only [Option.some.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        cases ch <;> simp_all

/-- **Step 4 when the wait is over.** If the rotation a commit records (`latch2`: the commit's new scope, or the one
already waiting) is not vetoed there, and 16 commits have passed since its admission, or it changes no rules and no
removed key is left without its seal, it governs from the next commit and its supersedes edges latch. -/
theorem step2_governs (st : St2 C K) (cm : Commit C K) {s : C} {t : Nat} {ch : Bool}
    (hw : (latch2 W st cm).waiting = some (s, t, ch))
    (hv : (ch && vetoed W cm st.scope s t (latch2 W st cm).present (latch2 W st cm).born) = false)
    (hdue : t + DELAY ≤ st.tick ∨ (ch = false ∧ waits W cm st.scope s = false)) :
    (step2 W st cm).scope = s ∧ (step2 W st cm).waiting = none ∧
      ∀ v ∈ (W.info s).supersedes, (step2 W st cm).edge s v .supersedes = true := by
  have hc : (decide (t + DELAY ≤ st.tick) || (!ch && !waits W cm (latch2 W st cm).scope s)) = true := by
    rcases hdue with h | ⟨h1, h2⟩
    · simp [h]
    · have : (latch2 W st cm).scope = st.scope := rfl
      simp [this, h1, h2]
  unfold step2 settle2
  rw [hw]
  simp only
  rw [if_neg (by rw [show (latch2 W st cm).scope = st.scope from rfl]; simp [hv]), if_pos hc]
  exact ⟨rfl, rfl, fun v hv' => by simp [hv']⟩

/-- **A veto cancels.** If the rules change a commit records is vetoed there, it is cancelled, nothing moves, and the
wait is over. -/
theorem step2_vetoes (st : St2 C K) (cm : Commit C K) {s : C} {t : Nat}
    (hw : (latch2 W st cm).waiting = some (s, t, true))
    (hv : vetoed W cm st.scope s t (latch2 W st cm).present (latch2 W st cm).born = true) :
    (step2 W st cm).cancelled s = true ∧ (step2 W st cm).scope = st.scope ∧ (step2 W st cm).waiting = none := by
  unfold step2 settle2
  rw [hw]
  simp only
  rw [if_pos (by rw [show (latch2 W st cm).scope = st.scope from rfl]; simp [hv])]
  exact ⟨by simp, rfl, rfl⟩

/-- What the chain knows of a waiting rotation at the start of `T_i`: it was admitted at an earlier commit `t` as
that commit's new scope, under the scope that still governs, which names rules other than v1; `ch` says whether it
changes rules. -/
def WaitOK (s0 : St2 C K) (chain : List (Commit C K)) (i : Nat) : Prop :=
  ∀ s t ch, (stateAt2 W s0 chain i).waiting = some (s, t, ch) →
    t < i ∧ (∃ ht : t < chain.length, chain[t].newScope = some s) ∧
      ch = change W (stateAt2 W s0 chain i).scope s ∧ namesV1 W (stateAt2 W s0 chain i).scope = false

theorem waitOK (s0 : St2 C K) (chain : List (Commit C K)) (h0 : s0.tick = 0) (hw0 : s0.waiting = none) :
    ∀ i, i ≤ chain.length → WaitOK W s0 chain i := by
  intro i
  induction i with
  | zero => intro _ s t ch h; simp [stateAt2, run2, hw0] at h
  | succ i ih =>
    intro hi s t ch h
    have hil : i < chain.length := by omega
    have hIH := ih (by omega)
    have htick : (stateAt2 W s0 chain i).tick = i := by rw [stateAt2_at W s0 chain (by omega), h0, Nat.zero_add]
    rw [stateAt2_succ W s0 chain hil] at h ⊢
    unfold step2 at h ⊢
    rcases settle2_cases W chain[i] (stateAt2 W s0 chain i).tick (latch2 W (stateAt2 W s0 chain i) chain[i]) with
      ⟨hsc, hn | ⟨hsame, hreason⟩⟩ | ⟨_, _, _, hn, _⟩
    · rw [hn] at h; cases h
    · rw [hsame] at h
      have hr := hreason s t ch h
      rw [hsc]
      have hsc' : (latch2 W (stateAt2 W s0 chain i) chain[i]).scope = (stateAt2 W s0 chain i).scope := rfl
      rw [hsc'] at hr ⊢
      have hv : namesV1 W (stateAt2 W s0 chain i).scope = false := by
        rcases hr with hr | hr
        · rcases latch2_waiting W _ _ h with ⟨_, _, _, hch⟩ | hold
          · rw [hch] at hr; simp [change] at hr; exact hr.1
          · exact (hIH s t ch hold).2.2.2
        · simp [waits] at hr; exact hr.1
      rcases latch2_waiting W _ _ h with ⟨_, hns, ht, hch⟩ | hold
      · have : t = i := ht.trans htick
        subst this
        exact ⟨by omega, ⟨hil, hns⟩, hch, hv⟩
      · obtain ⟨ht, hnew, hch, _⟩ := hIH s t ch hold
        exact ⟨by omega, hnew, hch, hv⟩
    · rw [hn] at h; cases h

/-- **Latch 4a (notice).** If the governing scope moves from `S` (at the start of `T_j`) to `S'` (after it), then
`S'` is the new scope of some commit `t ≤ j`; in a v1 epoch `t = j`, the rotation taking effect at once; under other
rules, either 16 commits have passed since `t`, or the rotation changes no rules and every key it removes from `S`'s
admission or acceptance policy has sealed `S'` under `S`. -/
theorem moves_notice (s0 : St2 C K) (chain : List (Commit C K)) (h0 : s0.tick = 0) (hw0 : s0.waiting = none)
    {j : Nat} (hj : j < chain.length) {S S' : C} (hS : (stateAt2 W s0 chain j).scope = S)
    (hS' : (stateAt2 W s0 chain (j + 1)).scope = S') (hne : S' ≠ S) :
    ∃ t, t ≤ j ∧ (∃ ht : t < chain.length, chain[t].newScope = some S') ∧
      (namesV1 W S = true → t = j) ∧
      (namesV1 W S = false →
        t + DELAY ≤ j ∨ (change W S S' = false ∧ Consented W chain[j] S S')) ∧
      (change W S S' = true → t + DELAY ≤ j ∧
        vetoed W chain[j] S S' t (stateAt2 W s0 chain (j + 1)).present (stateAt2 W s0 chain (j + 1)).born = false) := by
  have htick : (stateAt2 W s0 chain j).tick = j := by rw [stateAt2_at W s0 chain (by omega), h0, Nat.zero_add]
  have hIH := waitOK W s0 chain h0 hw0 j (by omega)
  rw [stateAt2_succ W s0 chain hj] at hS'
  have hpres : (stateAt2 W s0 chain (j + 1)).present = (latch2 W (stateAt2 W s0 chain j) chain[j]).present ∧
      (stateAt2 W s0 chain (j + 1)).born = (latch2 W (stateAt2 W s0 chain j) chain[j]).born := by
    rw [stateAt2_succ W s0 chain hj]; unfold step2 settle2
    split
    · exact ⟨rfl, rfl⟩
    · split
      · exact ⟨rfl, rfl⟩
      · split <;> exact ⟨rfl, rfl⟩
  rw [hpres.1, hpres.2]
  unfold step2 at hS'
  rcases settle2_cases W chain[j] (stateAt2 W s0 chain j).tick (latch2 W (stateAt2 W s0 chain j) chain[j]) with
    ⟨hsc, _⟩ | ⟨t, ch, hlw, _, hnv, hcond⟩
  · exact absurd (hS'.symm.trans (hsc.trans hS)) hne
  rw [hS'] at hlw hnv hcond
  have hsc' : (latch2 W (stateAt2 W s0 chain j) chain[j]).scope = S := hS
  rw [hsc'] at hnv hcond
  -- where the waiting rotation comes from: this commit's new scope, or an earlier one still waiting
  have hsrc : (t = j ∧ (∃ ht : t < chain.length, chain[t].newScope = some S') ∧ ch = change W S S') ∨
      (t < j ∧ (∃ ht : t < chain.length, chain[t].newScope = some S') ∧ ch = change W S S' ∧
        namesV1 W S = false) := by
    rcases latch2_waiting W _ _ hlw with ⟨_, hns, ht, hch⟩ | hold
    · have : t = j := ht.trans htick
      subst this
      left; exact ⟨rfl, ⟨hj, hns⟩, by rw [← hS]; exact hch⟩
    · right; have := hIH S' t ch hold; rw [hS] at this; exact this
  have hle : t ≤ j := by rcases hsrc with ⟨h, _⟩ | ⟨h, _⟩ <;> omega
  have hnew : ∃ ht : t < chain.length, chain[t].newScope = some S' := by
    rcases hsrc with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> exact h
  have hch : ch = change W S S' := by rcases hsrc with ⟨_, _, h⟩ | ⟨_, _, h, _⟩ <;> exact h
  rw [htick] at hcond
  refine ⟨t, hle, hnew, ?_, ?_, ?_⟩
  · intro hv
    rcases hsrc with ⟨h, _⟩ | ⟨_, _, _, h⟩
    · exact h
    · rw [hv] at h; cases h
  · intro hv
    rcases hcond with h | ⟨hc, hw⟩
    · exact Or.inl h
    · exact Or.inr ⟨hch ▸ hc, consented_of_waits W _ _ _ hv hw⟩
  · intro hc
    rw [← hch] at hc
    rw [hc] at hnv hcond
    refine ⟨?_, by simpa using hnv⟩
    rcases hcond with h | ⟨h, _⟩
    · exact h
    · cases h

/-! ## A waiting or vetoed scope latches nothing -/

/-- **Hypothesis (§3 check 1).** No edge is latched before the chain, nothing is vetoed, and each commit's new scope
is a cell of that commit not present before it. -/
def Fresh (s0 : St2 C K) (chain : List (Commit C K)) : Prop :=
  (∀ w v k, s0.edge w v k = false) ∧ (∀ c, s0.cancelled c = false) ∧
    ∀ (i : Nat) (hi : i < chain.length) (S' : C), chain[i].newScope = some S' →
      S' ∈ chain[i].newCells ∧ S' ∉ (stateAt2 W s0 chain i).present

/-- The invariant behind `waiting_withheld`: edges latch only from present cells; a waiting scope and a vetoed one
are present and latch no edge; a waiting scope is not vetoed. -/
def HoldOK (st : St2 C K) : Prop :=
  (∀ w v k, st.edge w v k = true → w ∈ st.present) ∧
  (∀ s t ch, st.waiting = some (s, t, ch) → s ∈ st.present ∧ st.cancelled s = false ∧ ∀ v k, st.edge s v k = false) ∧
  (∀ s, st.cancelled s = true → s ∈ st.present ∧ ∀ v k, st.edge s v k = false)

theorem step2_holdOK (st : St2 C K) (cm : Commit C K) (hI : HoldOK st)
    (hfresh : ∀ S', cm.newScope = some S' → S' ∈ cm.newCells ∧ S' ∉ st.present) :
    HoldOK (step2 W st cm) := by
  obtain ⟨hA, hB, hC⟩ := hI
  -- latch 3 of this commit, edge by edge
  have hL : ∀ w v k, (latch2 W st cm).edge w v k = true →
      st.edge w v k = true ∨ (w ∈ st.present ++ cm.newCells ∧ withheld W st cm w = false) := by
    intro w v k h
    simp only [latch2, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    rcases h with h | ⟨⟨⟨⟨hw, _⟩, hwh⟩, _⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨hw, hwh⟩
  have hLA : ∀ w v k, (latch2 W st cm).edge w v k = true → w ∈ (latch2 W st cm).present := by
    intro w v k h
    rcases hL w v k h with h | ⟨hw, _⟩
    · exact List.mem_append_left _ (hA w v k h)
    · exact hw
  -- the rotation latch2 records: this commit's new scope, or the one already waiting
  have hLW : ∀ s t ch, (latch2 W st cm).waiting = some (s, t, ch) →
      s ∈ (latch2 W st cm).present ∧ st.cancelled s = false ∧
      ∀ v k, (latch2 W st cm).edge s v k = true → (ch = false ∧ waits W cm st.scope s = false) := by
    intro s t ch h
    rcases latch2_waiting W _ _ h with ⟨hw, hns, _, hch⟩ | hold
    · obtain ⟨hnew, hnp⟩ := hfresh s hns
      have hnc : st.cancelled s = false := by
        cases hc : st.cancelled s
        · rfl
        · exact absurd (hC s hc).1 hnp
      refine ⟨List.mem_append_right _ hnew, hnc, ?_⟩
      intro v k he
      rcases hL s v k he with h | ⟨_, hwh⟩
      · exact absurd (hA s v k h) hnp
      · have hp : pending st cm = some s := by simp [pending, hw, hns]
        simp only [withheld, hw, hp, hnc] at hwh
        rw [hch]; simpa using hwh
    · obtain ⟨hpres, hnc, hno⟩ := hB s t ch hold
      refine ⟨List.mem_append_left _ hpres, hnc, ?_⟩
      intro v k he
      rcases hL s v k he with h | ⟨_, hwh⟩
      · rw [hno v k] at h; cases h
      · simp [withheld, hold] at hwh
  -- a scope vetoed before this commit stays present and latches nothing in latch 3
  have hLC : ∀ c, st.cancelled c = true → c ∈ (latch2 W st cm).present ∧ ∀ v k, (latch2 W st cm).edge c v k = false := by
    intro c hc
    refine ⟨List.mem_append_left _ (hC c hc).1, ?_⟩
    intro v k
    cases he : (latch2 W st cm).edge c v k
    · rfl
    · rcases hL c v k he with h | ⟨_, hwh⟩
      · rw [(hC c hc).2 v k] at h; cases h
      · simp [withheld, hc] at hwh
  have hLcan : (latch2 W st cm).cancelled = st.cancelled := rfl
  have hLs : (latch2 W st cm).scope = st.scope := rfl
  unfold step2
  generalize latch2 W st cm = L at hLA hLW hLC hLcan hLs
  unfold settle2 HoldOK
  cases hw : L.waiting with
  | none =>
    simp only
    refine ⟨hLA, ?_, ?_⟩
    · intro s t ch h; first | (rw [hw] at h; cases h) | cases h
    · intro c hc; rw [hLcan] at hc; exact hLC c hc
  | some w =>
    obtain ⟨s, t, ch⟩ := w
    obtain ⟨hsp, hsc, hse⟩ := hLW s t ch hw
    simp only
    by_cases hv : (ch && vetoed W cm L.scope s t L.present L.born) = true
    · rw [if_pos hv]
      refine ⟨hLA, by simp, ?_⟩
      intro c hc
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      rcases hc with hc | rfl
      · rw [hLcan] at hc; exact hLC c hc
      · refine ⟨hsp, fun v k => ?_⟩
        cases he : L.edge c v k
        · rfl
        · have := (hse v k he).1; simp [this] at hv
    · rw [if_neg hv]
      by_cases hg : (decide (t + DELAY ≤ st.tick) || (!ch && !waits W cm L.scope s)) = true
      · rw [if_pos hg]
        refine ⟨?_, by simp, ?_⟩
        · intro w v k h
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
          rcases h with h | ⟨⟨rfl, _⟩, _⟩
          · exact hLA w v k h
          · exact hsp
        · intro c hc
          rw [hLcan] at hc
          obtain ⟨hcp, hce⟩ := hLC c hc
          refine ⟨hcp, fun v k => ?_⟩
          have hne : c ≠ s := by intro h; rw [h, hsc] at hc; cases hc
          simp [hce v k, hne]
      · rw [if_neg hg]
        refine ⟨hLA, ?_, ?_⟩
        · intro s' t' ch' h'
          rw [hw] at h'
          simp only [Option.some.injEq, Prod.mk.injEq] at h'
          obtain ⟨rfl, rfl, rfl⟩ := h'
          refine ⟨hsp, by rw [hLcan]; exact hsc, fun v k => ?_⟩
          cases he : L.edge s v k
          · rfl
          · obtain ⟨h1, h2⟩ := hse v k he
            rw [hLs, h1, h2] at hg; simp at hg
        · intro c hc; rw [hLcan] at hc; exact hLC c hc

theorem holdOK (s0 : St2 C K) (chain : List (Commit C K)) (hF : Fresh W s0 chain) (hw0 : s0.waiting = none) :
    ∀ i, i ≤ chain.length → HoldOK (stateAt2 W s0 chain i) := by
  obtain ⟨he0, hc0, hnew⟩ := hF
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨fun w v k h => by simp [stateAt2, run2, he0] at h, fun s t ch h => by simp [stateAt2, run2, hw0] at h,
      fun c h => by simp [stateAt2, run2, hc0] at h⟩
  | succ i ih =>
    intro hi
    have hil : i < chain.length := by omega
    rw [stateAt2_succ W s0 chain hil]
    exact step2_holdOK W _ _ (ih (by omega)) (fun S' h => hnew i hil S' h)

/-- **Latches 4a and 4b: a waiting or vetoed scope latches nothing.** At the start of every `T_i`, a scope whose
rotation waits, or was vetoed, has no latched edge of its own, if the chain is `Fresh`. -/
theorem waiting_withheld (s0 : St2 C K) (chain : List (Commit C K)) (hF : Fresh W s0 chain)
    (hw0 : s0.waiting = none) {i : Nat} (hi : i ≤ chain.length) {s : C}
    (hs : (∃ t ch, (stateAt2 W s0 chain i).waiting = some (s, t, ch)) ∨ (stateAt2 W s0 chain i).cancelled s = true) :
    ∀ v k, (stateAt2 W s0 chain i).edge s v k = false := by
  obtain ⟨_, hB, hC⟩ := holdOK W s0 chain hF hw0 i hi
  rcases hs with ⟨t, ch, h⟩ | h
  · exact (hB s t ch h).2.2
  · exact (hC s h).2

/-- So a waiting or vetoed scope, which supersedes the scope it would replace, is not Active (§4.2) under the
latched edges: the Active local scope stays the governing one (VARS-1-SPEC.md §4.1 latch 4a). -/
theorem waiting_not_active (s0 : St2 C K) (chain : List (Commit C K)) (hF : Fresh W s0 chain)
    (hw0 : s0.waiting = none) {i : Nat} (hi : i ≤ chain.length) {s : C}
    (hs : (∃ t ch, (stateAt2 W s0 chain i).waiting = some (s, t, ch)) ∨ (stateAt2 W s0 chain i).cancelled s = true)
    (hsup : (W.info s).supersedes ≠ []) (Eff Acc Ret : C → Prop) :
    ¬ Active W.toWorld (stateAt2 W s0 chain i).edge Eff Acc Ret s := by
  intro hact
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil _ hsup
  have := hact.2.2.2.2 u hu
  rw [waiting_withheld W s0 chain hF hw0 hi hs] at this
  cases this

theorem step2_cancelled (st : St2 C K) (cm : Commit C K) {c : C} (h : st.cancelled c = true) :
    (step2 W st cm).cancelled c = true := by
  unfold step2 settle2
  have hL : (latch2 W st cm).cancelled c = true := h
  split
  · exact hL
  · split
    · simp [hL]
    · split
      · exact hL
      · exact hL

theorem cancelled_mono (s0 : St2 C K) (chain : List (Commit C K)) {i : Nat} {c : C}
    (h : (stateAt2 W s0 chain i).cancelled c = true) :
    ∀ j, i ≤ j → j ≤ chain.length → (stateAt2 W s0 chain j).cancelled c = true := by
  intro j
  induction j with
  | zero => intro hij _; have : i = 0 := by omega
            subst this; exact h
  | succ j ih =>
    intro hij hj
    rcases Nat.lt_or_ge j i with hlt | hge
    · have : i = j + 1 := by omega
      subst this; exact h
    rw [stateAt2_succ W s0 chain (by omega)]
    exact step2_cancelled W _ _ (ih hge (by omega))

/-- **Latch 4b: a vetoed change never governs.** Once a rules change is vetoed (at the start of `T_i` it is
cancelled), no later commit moves the governing scope to it, if the chain is `Fresh`. With `waiting_withheld`, its
supersedes edge never latches either. -/
theorem vetoed_never_governs (s0 : St2 C K) (chain : List (Commit C K)) (hF : Fresh W s0 chain)
    (hw0 : s0.waiting = none) {i j : Nat} (hij : i ≤ j) (hj : j < chain.length) {s : C}
    (hc : (stateAt2 W s0 chain i).cancelled s = true)
    (hmove : (stateAt2 W s0 chain (j + 1)).scope ≠ (stateAt2 W s0 chain j).scope) :
    (stateAt2 W s0 chain (j + 1)).scope ≠ s := by
  have hcj := cancelled_mono W s0 chain hc j hij (by omega)
  obtain ⟨_, hB, hC⟩ := holdOK W s0 chain hF hw0 j (by omega)
  have hsp := (hC s hcj).1
  intro heq
  rw [stateAt2_succ W s0 chain hj] at hmove heq
  unfold step2 at hmove heq
  rcases settle2_cases W chain[j] (stateAt2 W s0 chain j).tick (latch2 W (stateAt2 W s0 chain j) chain[j]) with
    ⟨hsc, _⟩ | ⟨t, ch, hlw, _, _, _⟩
  · exact hmove hsc
  rw [heq] at hlw
  rcases latch2_waiting W _ _ hlw with ⟨_, hns, _, _⟩ | hold
  · exact (hF.2.2 j hj s hns).2 hsp
  · have := (hB s t ch hold).2.1
    rw [hcj] at this; cases this

end Vars1
