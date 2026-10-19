import Vars1.Model

/-!
# §4.1 Commit-chain fold

`step W st cm` processes one commit `T_i` against the scope `S_i = st.scope`
that governs at its start: InitialEndorsers for the cells born here, latching
steps 1–3, then the end-of-commit scope transition (step 4). Step 3b (Rule 6)
is not a state change: it is a rejection condition, stated as the hypothesis
`Rule6Admitted` in `Vars1/Pass1.lean`.

Theorems here:
* `stateAt_mono` — latches (edges, `Authorized`) never unlatch along the chain,
  and InitialEndorsers of an already-born cell never change.
* `stateAt_append` — the state at the start of `T_i` is unchanged by any commits
  after `T_i` (non-retroactivity).
* `step_edge_iff` — an edge is newly latched at `T_i` exactly by the §4.1 step 3
  condition evaluated under `S_i`.
* `step_epoch_binding` — the latches made at `T_i` depend on the seals of `T_i`
  only through those whose `H_scope_ctx = id(S_i)`.
* `endorser_signed` — under unforgeability, every counted endorser of `u` at
  `T_i` signed `(u, S_i)`.
-/

set_option linter.unusedSectionVars false

namespace Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K]

/-- Fold state at the start of a commit. -/
structure St (C K : Type) where
  scope : C
  present : List C
  initEnd : C → List K
  authorized : C → Bool
  edge : C → C → Kind → Bool

variable (W : World C K P)

/-- The roster that restricts `Endorsers_i`: `S_i.slots[1]` when endorsing or
evicting a `schema.acceptance` cell, else `S_i.slots[0]`. -/
def roster (S v : C) : P :=
  if (W.info v).schema = .acceptance then (W.info S).pol1 else (W.info S).pol0

/-- The seal predicate behind `Endorsers_i(u)`: target `u`, context `id(S)`, key in roster `r`. -/
def sealCounts (S u : C) (r : P) (s : Seal C K) : Bool :=
  decide (s.target = u) && decide (s.ctx = S) && W.member r s.key

/-- `Endorsers_i(u)`, restricted to roster `r`, over the valid seals of `T_i`. -/
def endorsers (cm : Commit C K) (S u : C) (r : P) : List K :=
  (cm.seals.filter (sealCounts W S u r)).map (·.key)

/-- `(Pol_i(v), AuthorCanEvict(v))` under scope `S` (§4.1). -/
def pol (S v : C) : P × Bool :=
  let c := W.info v
  let s := W.info S
  match c.schema with
  | .scope => (s.pol0, false)
  | .acceptance => (s.pol1, false)
  | .contract | .decision =>
      if c.ownerPol then (s.pol0, false) else (c.customPol.getD s.pol0, true)
  | .question => (c.customPol.getD s.pol0, true)
  | _ => (s.pol0, true)

/-- §4.1 step 3: may edge `(w, v, k)` latch at a commit with seals `cm` under
scope `S`, given InitialEndorsers `init`? The author clause is local-only
and never applies to `invalidates`. -/
def edgeCond (cm : Commit C K) (S w v : C) (k : Kind) (init : C → List K) : Bool :=
  let E := endorsers W cm S w (roster W S v)
  W.quorum E (pol W S v).1 ||
    (decide (k ≠ .invalidates) && (pol W S v).2 && (W.info v).isLocal &&
      E.any (fun e => (init v).contains e))

/-- §4.1 steps 1–2: may cell `a` latch `Authorized` under `S`? -/
def authCond (cm : Commit C K) (S a : C) : Bool :=
  (W.info a).isLocal &&
    ((decide ((W.info a).schema = .acceptance) &&
        W.quorum (endorsers W cm S a (W.info S).pol1) (W.info S).pol1) ||
     (decide ((W.info a).schema = .metaSchema) &&
        W.quorum (endorsers W cm S a (W.info S).pol0) (W.info S).pol0))

/-- The steps 1–2 `Authorized` bits after commit `cm` (before the step 4 scope latch). -/
def authLatch (st : St C K) (cm : Commit C K) (a : C) : Bool :=
  st.authorized a || (decide (a ∈ st.present ++ cm.newCells) && authCond W cm st.scope a)

/-- InitialEndorsers after commit `cm`: fixed at birth, local cells only. -/
def initAfter (st : St C K) (cm : Commit C K) : C → List K := fun v =>
  if v ∈ cm.newCells ∧ v ∉ st.present ∧ (W.info v).isLocal = true then
    endorsers W cm st.scope v (roster W st.scope v)
  else st.initEnd v

/-- One commit of the fold. All latching uses `S_i = st.scope`; the scope moves
only at the end (step 4). -/
def step (st : St C K) (cm : Commit C K) : St C K :=
  let S := st.scope
  let present' := st.present ++ cm.newCells
  let init' := initAfter W st cm
  { scope := cm.newScope.getD S
    present := present'
    initEnd := init'
    authorized := fun a => authLatch W st cm a || decide (cm.newScope = some a)
    edge := fun w v k =>
      st.edge w v k ||
        (decide (w ∈ present') && decide (v ∈ (W.info w).edges k) &&
          edgeCond W cm S w v k init') }

/-- Fold over a list of commits. -/
def run (s0 : St C K) (cs : List (Commit C K)) : St C K := cs.foldl (step W) s0

/-- The state at the start of `T_i` (after commits `T_0 … T_{i-1}`). Its `scope` is `S_i`. -/
def stateAt (s0 : St C K) (chain : List (Commit C K)) (i : Nat) : St C K :=
  run W s0 (chain.take i)

/-! ## Monotonicity of latches -/

/-- `a ≤ b`: every latch of `a` is a latch of `b`, and every cell present in `a`
is present in `b` with the same InitialEndorsers. -/
def St.le (a b : St C K) : Prop :=
  (∀ w v k, a.edge w v k = true → b.edge w v k = true) ∧
  (∀ x, a.authorized x = true → b.authorized x = true) ∧
  (∀ x, x ∈ a.present → x ∈ b.present ∧ b.initEnd x = a.initEnd x)

theorem St.le_refl (a : St C K) : a.le a :=
  ⟨fun _ _ _ h => h, fun _ h => h, fun _ h => ⟨h, rfl⟩⟩

theorem St.le_trans {a b c : St C K} (h1 : a.le b) (h2 : b.le c) : a.le c :=
  ⟨fun w v k h => h2.1 w v k (h1.1 w v k h),
   fun x h => h2.2.1 x (h1.2.1 x h),
   fun x h => by
     obtain ⟨hb, hbe⟩ := h1.2.2 x h
     obtain ⟨hc, hce⟩ := h2.2.2 x hb
     exact ⟨hc, hce.trans hbe⟩⟩

theorem step_le (st : St C K) (cm : Commit C K) : st.le (step W st cm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w v k h; simp [step, h]
  · intro x h; simp [step, authLatch, h]
  · intro x hx
    refine ⟨by simp [step, hx], ?_⟩
    simp [step, initAfter, hx]

theorem run_le (s0 : St C K) (cs : List (Commit C K)) : s0.le (run W s0 cs) := by
  induction cs generalizing s0 with
  | nil => exact St.le_refl _
  | cons c cs ih => exact St.le_trans (step_le W s0 c) (ih (step W s0 c))

theorem run_append (s0 : St C K) (xs ys : List (Commit C K)) :
    run W s0 (xs ++ ys) = run W (run W s0 xs) ys := by
  simp [run, List.foldl_append]

/-- **Theorem 1a (latches are monotone).** For `i ≤ j`, every edge and
`Authorized` latch at the start of `T_i` is still latched at the start of `T_j`,
and InitialEndorsers fixed by then are unchanged. -/
theorem stateAt_mono (s0 : St C K) (chain : List (Commit C K)) {i j : Nat} (hij : i ≤ j) :
    (stateAt W s0 chain i).le (stateAt W s0 chain j) := by
  unfold stateAt
  have : chain.take j = chain.take i ++ (chain.take j).drop i := by
    conv => lhs; rw [← List.take_append_drop i (chain.take j)]
    rw [List.take_take, Nat.min_eq_left hij]
  rw [this, run_append]
  exact run_le W _ _

/-- **Theorem 1b (non-retroactivity).** The state at the start of `T_i` —
hence `S_i` and every latch made before `T_i` — does not depend on any commit at
or after `T_i`. -/
theorem stateAt_append (s0 : St C K) (chain future : List (Commit C K)) {i : Nat}
    (hi : i ≤ chain.length) :
    stateAt W s0 (chain ++ future) i = stateAt W s0 chain i := by
  simp [stateAt, List.take_append_of_le_length hi]

/-- The state after `T_i` is one `step` from the state at its start, under `S_i`. -/
theorem stateAt_succ (s0 : St C K) (chain : List (Commit C K)) {i : Nat}
    (hi : i < chain.length) :
    stateAt W s0 chain (i + 1) = step W (stateAt W s0 chain i) chain[i] := by
  unfold stateAt
  rw [List.take_add_one, List.getElem?_eq_getElem hi, run_append]
  rfl

/-- **Theorem 1c (what latches at `T_i`).** An edge is latched after `T_i` iff it
was latched before, or §4.1 step 3 holds under `S_i` for a source cell present in `T_i`. -/
theorem step_edge_iff (st : St C K) (cm : Commit C K) (w v : C) (k : Kind) :
    (step W st cm).edge w v k = true ↔
      st.edge w v k = true ∨
        (w ∈ st.present ++ cm.newCells ∧ v ∈ (W.info w).edges k ∧
          edgeCond W cm st.scope w v k (initAfter W st cm) = true) := by
  simp [step, and_assoc]

/-! ## Epoch binding -/

/-- The seals of a commit whose context is `S`. -/
def sealsUnder (cm : Commit C K) (S : C) : List (Seal C K) :=
  cm.seals.filter (fun s => decide (s.ctx = S))

theorem endorsers_eq_under (cm : Commit C K) (S u : C) (r : P) :
    endorsers W cm S u r = ((sealsUnder cm S).filter (sealCounts W S u r)).map (·.key) := by
  unfold endorsers sealsUnder
  congr 1
  rw [List.filter_filter]
  congr 1
  funext s
  unfold sealCounts
  by_cases h : s.ctx = S <;> simp [h]

theorem endorsers_congr (cm1 cm2 : Commit C K) (S : C)
    (h : sealsUnder cm1 S = sealsUnder cm2 S) (u : C) (r : P) :
    endorsers W cm1 S u r = endorsers W cm2 S u r := by
  rw [endorsers_eq_under, endorsers_eq_under, h]

/-- **Theorem 1d (epoch binding).** Two commits that introduce the
same cells and carry the same seals under context `S_i` latch exactly the same
edges and `Authorized` bits, and fix the same InitialEndorsers: seals signed
under any other scope context are never pooled at `T_i`. -/
theorem step_epoch_binding (st : St C K) (cm1 cm2 : Commit C K)
    (hcells : cm1.newCells = cm2.newCells)
    (hseals : sealsUnder cm1 st.scope = sealsUnder cm2 st.scope) :
    (step W st cm1).edge = (step W st cm2).edge ∧
    authLatch W st cm1 = authLatch W st cm2 ∧
    (step W st cm1).initEnd = (step W st cm2).initEnd ∧
    (step W st cm1).present = (step W st cm2).present := by
  have hE := endorsers_congr W cm1 cm2 st.scope hseals
  have hinit : initAfter W st cm1 = initAfter W st cm2 := by
    funext v; simp [initAfter, hcells, hE]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext w v k
    simp only [step, edgeCond, hinit, hE, hcells]
  · funext a; simp only [authLatch, authCond, hE, hcells]
  · simp only [step, hinit]
  · simp only [step, hcells]

/-! ## Unforgeability -/

/-- **Theorem 1e.** If every valid seal of `T_i` was signed by its key holder
(hypothesis `unforgeable`), every counted endorser of `u` at `T_i` signed
exactly the pair `(id(u), id(S_i))`. -/
theorem endorser_signed (Signed : K → C → C → Prop) (cm : Commit C K)
    (unforgeable : ∀ s ∈ cm.seals, Signed s.key s.target s.ctx)
    (S u : C) (r : P) (k : K) (hk : k ∈ endorsers W cm S u r) : Signed k u S := by
  simp only [endorsers, List.mem_map, List.mem_filter] at hk
  obtain ⟨s, ⟨hs, hc⟩, rfl⟩ := hk
  simp [sealCounts] at hc
  obtain ⟨⟨ht, hctx⟩, _⟩ := hc
  have := unforgeable s hs
  rw [ht, hctx] at this
  exact this

end Vars1
