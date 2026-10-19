/-!
# Book I replay soundness (§3.2 Check #4)

Stage 1 treated Book I replay as an opaque oracle. Here it is a small-step
semantics and a lineage verifier, and Pass 3's oracle is defined from them
(`Vars1/Pass3Replay.lean`).

* `Machine` — a deterministic transition `step : S → Act S` whose fired actions
  cost at least 1 ATP (Book I §3.4 "minimum cost of any action is 1";
  `EvalMachine.step_cost_pos` in sigma-glyph).
* `adv M s b` — `sigma_resume._run`: fire actions greedily while the next one is
  affordable from what is left of `b`; stop at a normal form, a blocked
  reference, or the first unaffordable action (PAUSED). Returns the final state
  and the ATP spent.
* `Ckpts` — the checkpoint cells: computation, `spent_total`, decoded state,
  `H_relies`, the `H_NORMAL_FORM` claim, and `SR.start` per computation.
* `parent` — the highest-spent same-computation checkpoint in `H_relies`
  (`vars1._parent_checkpoint`, first maximum on ties, as Python's `max`).
* `replayOne` — `vars1._replay_from_parent`: one transition from the parent's
  state (or from `SR.start` at `parent_spent = 0`) by `Δspent`.
* `verify` — `vars1.verify_checkpoint_replay` in gate mode: the parent's lineage
  first, oldest-first; a non-`REPLAYED` ancestor status is inherited.

The host's evaluator is any function `host : S → Nat → Option (S × Nat)` that,
when it reports a result, reports `adv`'s (`HostSound`). `none` is a local
outcome (RESOURCE_FAULT, ADMISSION_REFUSED, INCOMPLETE, recursion depth): the
Gate maps it to `NOT_ASSESSED`. Every theorem holds for every such host.

Theorems:
* `adv_seg` — segmentation invariance: if advancing by `a` spends exactly `a`,
  advancing by `a` and then by `b` equals advancing by `a + b`.
* `verify_sound` — replay soundness: `REPLAYED` for `c` implies one advance
  from `SR.start (comp c)` by `spent_total(c)` spends exactly that and reaches
  exactly `state(c)`.
* `verify_ancestor_replayed`, `not_assessed_ancestor_blocks` — every ancestor of
  a `REPLAYED` checkpoint is `REPLAYED`; any `NOT_ASSESSED` ancestor makes the
  descendant not `REPLAYED`.
-/

namespace Vars1.Replay

/-- What the transition does from a state. -/
inductive Act (S : Type) where
  /-- normal form (`step5` returns `None`) -/
  | nf
  /-- the demanded hash is absent (`Unresolved`, BLOCKED_REFERENCE) -/
  | blocked
  /-- the demanded action, its successor state and its ATP price -/
  | fire (s : S) (cost : Nat)

/-- A deterministic, positively priced transition system. -/
structure Machine where
  S : Type
  step : S → Act S
  cost_pos : ∀ s s' c, step s = .fire s' c → 0 < c

variable (M : Machine)

/-- `sigma_resume._run` without host fences: greedy, atomic, pre-checked charging. -/
def adv (s : M.S) (b : Nat) : M.S × Nat :=
  match _hstep : M.step s with
  | .fire s' c =>
      if c ≤ b then ((adv s' (b - c)).1, c + (adv s' (b - c)).2) else (s, 0)
  | .nf => (s, 0)
  | .blocked => (s, 0)
termination_by b
decreasing_by have := M.cost_pos s s' c _hstep; omega

theorem adv_eq (s : M.S) (b : Nat) :
    adv M s b =
      match M.step s with
      | .fire s' c =>
          if c ≤ b then ((adv M s' (b - c)).1, c + (adv M s' (b - c)).2) else (s, 0)
      | .nf => (s, 0)
      | .blocked => (s, 0) := by
  rw [adv]; split <;> simp_all

/-- `adv` never spends more than its budget (Book I §3.4). -/
theorem adv_le (s : M.S) (b : Nat) : (adv M s b).2 ≤ b := by
  induction b using Nat.strongRecOn generalizing s with
  | _ b ih =>
    rw [adv_eq]
    split
    · rename_i s' c h
      split
      · have hc := M.cost_pos s s' c h
        have := ih (b - c) (by omega) s'
        simp only; omega
      · simp
    · simp
    · simp

/-- **Segmentation invariance.** When the first segment spends its whole budget
(no budget refusal stopped it early), the run splits at that point. -/
theorem adv_seg (s s₁ s₂ : M.S) (a b d : Nat)
    (h₁ : adv M s a = (s₁, a)) (h₂ : adv M s₁ b = (s₂, d)) :
    adv M s (a + b) = (s₂, a + d) := by
  induction a using Nat.strongRecOn generalizing s with
  | _ a ih =>
    rw [adv_eq] at h₁
    rw [adv_eq]
    split
    · rename_i s' c hstep
      rw [hstep] at h₁
      have hc := M.cost_pos s s' c hstep
      by_cases hca : c ≤ a
      · simp only [hca, if_true, Prod.mk.injEq] at h₁
        have hrest : adv M s' (a - c) = (s₁, a - c) := by
          rw [Prod.ext_iff]; exact ⟨h₁.1, by omega⟩
        have := ih (a - c) (by omega) s' hrest
        have e : a + b - c = a - c + b := by omega
        simp only [show c ≤ a + b by omega, if_true, e, this, Prod.mk.injEq]
        exact ⟨trivial, by omega⟩
      · simp only [hca, if_false, Prod.mk.injEq] at h₁
        obtain ⟨rfl, ha⟩ := h₁
        subst ha
        simp only [Nat.zero_add]
        rw [← h₂, adv_eq M s b, hstep]
    · rename_i hstep
      rw [hstep] at h₁
      simp only [Prod.mk.injEq] at h₁
      obtain ⟨rfl, ha⟩ := h₁
      subst ha
      rw [adv_eq, hstep] at h₂
      simp_all
    · rename_i hstep
      rw [hstep] at h₁
      simp only [Prod.mk.injEq] at h₁
      obtain ⟨rfl, ha⟩ := h₁
      subst ha
      rw [adv_eq, hstep] at h₂
      simp_all

/-- `true` exactly on a normal form. -/
def Act.isNF {S : Type} : Act S → Bool
  | .nf => true
  | _ => false

/-- The checkpoint cells of a store. `R` names computations (`computation_id`). -/
structure Ckpts (C R : Type) (M : Machine) where
  isCkpt : C → Bool
  comp : C → R
  spent : C → Nat
  /-- `decode_state(atoms[c.H_payload])`; a function of the cell under SHA-256
  injectivity on admitted bytes (`Vars1/Axioms.lean`). -/
  state : C → M.S
  relies : C → List C
  /-- `c.slots[4] == H_NORMAL_FORM` -/
  claimsNF : C → Bool
  /-- `SR.start`: the cold input thunk of `ComputationRoot(r)` -/
  start : R → M.S

/-- Replay status of a checkpoint. `refused` is a `VarsError` (the Gate rejects
the commit, Pass 3 rejects the witness). -/
inductive Status where
  | replayed | notAssessed | refused
  deriving DecidableEq, Repr

variable {C R : Type} [DecidableEq R] {M}

/-- The first element of maximal `spent` (Python `max(..., key=spent)`). -/
def best (spent : C → Nat) : List C → Option C
  | [] => none
  | x :: xs =>
      match best spent xs with
      | none => some x
      | some y => if spent y > spent x then some y else some x

theorem best_mem (spent : C → Nat) : ∀ (l : List C) (p : C), best spent l = some p → p ∈ l
  | [], _, h => by simp [best] at h
  | x :: xs, p, h => by
    simp only [best] at h
    split at h
    · simp_all
    · rename_i y hy
      split at h
      · cases h; exact List.mem_cons_of_mem _ (best_mem spent xs _ hy)
      · cases h; exact List.mem_cons_self

variable (L : Ckpts C R M)

/-- `_parent_checkpoint`: the highest-spent same-computation checkpoint in `H_relies`. -/
def parent (c : C) : Option C :=
  best L.spent ((L.relies c).filter (fun p => L.isCkpt p && decide (L.comp p = L.comp c)))

theorem parent_comp {c p : C} (h : parent L c = some p) : L.comp p = L.comp c := by
  have := best_mem _ _ _ h
  simp [List.mem_filter] at this
  exact this.2.2

/-- Where the replay of `c` starts: the parent's state and `spent_total`, or
`SR.start` at `parent_spent = 0`. -/
def base (c : C) : M.S × Nat :=
  match parent L c with
  | none => (L.start (L.comp c), 0)
  | some p => (L.state p, L.spent p)

/-- The host evaluator reports `adv`'s result whenever it reports at all. -/
def HostSound (host : M.S → Nat → Option (M.S × Nat)) : Prop :=
  ∀ s b r, host s b = some r → r = adv M s b

variable [DecidableEq M.S] (maxAtp : Nat) (host : M.S → Nat → Option (M.S × Nat))

/-- `_replay_from_parent` in gate mode. The checks of `vars1.py` left out here
(credit ≥ spent, peak size, PAUSED/BLOCKED claims) only ever refuse, so leaving
them out makes this verifier more permissive and the theorems stronger. -/
def replayOne (c : C) : Status :=
  let b := base L c
  if L.spent c < b.2 then .refused
  else if maxAtp < L.spent c - b.2 then .notAssessed
  else
    match host b.1 (L.spent c - b.2) with
    | none => .notAssessed
    | some r =>
        if r.1 = L.state c ∧ r.2 = L.spent c - b.2 ∧
            (L.claimsNF c = true → (M.step r.1).isNF = true) then .replayed
        else .refused

/-- `verify_checkpoint_replay` in gate mode. Fuel bounds the lineage walk; an
exhausted walk (a cyclic lineage) is refused, as `vars1.py` raises on cycles. -/
def verify : Nat → C → Status
  | 0, _ => .refused
  | f + 1, c =>
      match parent L c with
      | none => replayOne L maxAtp host c
      | some p =>
          match verify f p with
          | .replayed => replayOne L maxAtp host c
          | s => s

/-- What one `REPLAYED` transition establishes. -/
theorem replayOne_sound (hs : HostSound host) {c : C}
    (h : replayOne L maxAtp host c = .replayed) :
    (base L c).2 ≤ L.spent c ∧
    adv M (base L c).1 (L.spent c - (base L c).2) = (L.state c, L.spent c - (base L c).2) ∧
    (L.claimsNF c = true → (M.step (L.state c)).isNF = true) := by
  unfold replayOne at h
  simp only at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hle _ r hr
  split at h
  · rename_i hok
    obtain ⟨h1, h2, h3⟩ := hok
    refine ⟨by omega, ?_, by rw [← h1]; exact h3⟩
    rw [← hs _ _ _ hr, Prod.ext_iff]; exact ⟨h1, h2⟩
  · cases h

/-- **Replay soundness.** If the lineage verifier returns
`REPLAYED` for `c`, a single advance from `SR.start` of `c`'s computation by
`spent_total(c)` spends exactly `spent_total(c)` and reaches exactly `state(c)`. -/
theorem verify_sound (hs : HostSound host) :
    ∀ (f : Nat) (c : C), verify L maxAtp host f c = .replayed →
      adv M (L.start (L.comp c)) (L.spent c) = (L.state c, L.spent c)
  | 0, _, h => by simp [verify] at h
  | f + 1, c, h => by
    simp only [verify] at h
    have hb := replayOne_sound L maxAtp host hs (c := c)
    split at h
    · rename_i hp
      obtain ⟨-, hadv, -⟩ := hb h
      simpa [base, hp] using hadv
    · rename_i p hp
      split at h
      · rename_i hvp
        have ih := verify_sound hs f p hvp
        obtain ⟨hle, hadv, -⟩ := hb h
        simp only [base, hp] at hle hadv
        rw [parent_comp L hp] at ih
        have := adv_seg M _ _ _ _ _ _ ih hadv
        rwa [Nat.add_sub_cancel' hle] at this
      · simp_all

/-- A `REPLAYED` checkpoint's own transition is `REPLAYED`. -/
theorem verify_replayOne : ∀ (f : Nat) (c : C), verify L maxAtp host f c = .replayed →
    replayOne L maxAtp host c = .replayed
  | 0, _, h => by simp [verify] at h
  | f + 1, c, h => by
    simp only [verify] at h
    split at h
    · exact h
    · split at h
      · exact h
      · simp_all

/-- A non-`refused` verdict is stable under more fuel. -/
theorem verify_fuel_succ : ∀ (f : Nat) (c : C) (s : Status),
    verify L maxAtp host f c = s → s ≠ .refused → verify L maxAtp host (f + 1) c = s
  | 0, _, s, h, hs => by simp [verify] at h; exact absurd h.symm hs
  | f + 1, c, s, h, hs => by
    rw [verify] at h ⊢
    split at h
    · exact h
    · rename_i p hp
      generalize hv : verify L maxAtp host f p = v at h
      cases v with
      | replayed => rw [verify_fuel_succ f p _ hv (by simp)]; exact h
      | notAssessed => rw [verify_fuel_succ f p _ hv (by simp)]; exact h
      | refused => simp at h; exact absurd h.symm hs

theorem verify_fuel_le {f g : Nat} {c : C} {s : Status} (hfg : f ≤ g)
    (h : verify L maxAtp host f c = s) (hs : s ≠ .refused) : verify L maxAtp host g c = s := by
  induction hfg with
  | refl => exact h
  | step _ ih => exact verify_fuel_succ L maxAtp host _ _ _ ih hs

/-- `q` is in the lineage of `c` (`c` itself, its parent, its parent's parent, …). -/
inductive Lin : C → C → Prop
  | refl (c : C) : Lin c c
  | up {q p c : C} : parent L c = some p → Lin q p → Lin q c

theorem verify_parent_replayed {f : Nat} {c p : C} (hp : parent L c = some p)
    (h : verify L maxAtp host f c = .replayed) : verify L maxAtp host f p = .replayed := by
  cases f with
  | zero => simp [verify] at h
  | succ f =>
    simp only [verify, hp] at h
    split at h
    · rename_i hvp
      exact verify_fuel_succ L maxAtp host _ _ _ hvp (by simp)
    · simp_all

/-- Every ancestor of a `REPLAYED` checkpoint is `REPLAYED` (Spec §3.2:
ReplayVerified(c) ⟹ ReplayVerified(p) ∧ ValidTransition(p, c)). -/
theorem verify_ancestor_replayed {f : Nat} {q c : C} (hl : Lin L q c)
    (h : verify L maxAtp host f c = .replayed) : verify L maxAtp host f q = .replayed := by
  induction hl with
  | refl => exact h
  | up hp _ ih => exact ih (verify_parent_replayed L maxAtp host hp h)

/-- **A `NOT_ASSESSED` ancestor blocks `REPLAYED`.** Whether the ancestor's own
transition was not assessed (over the ceiling, or a local host outcome) or it
inherited the status from further up, no descendant is `REPLAYED`, at any fuel. -/
theorem not_assessed_ancestor_blocks {f g : Nat} {q c : C} (hl : Lin L q c)
    (hq : replayOne L maxAtp host q = .notAssessed ∨ verify L maxAtp host g q = .notAssessed) :
    verify L maxAtp host f c ≠ .replayed := by
  intro h
  have hq' := verify_ancestor_replayed L maxAtp host hl h
  rcases hq with hq | hq
  · rw [verify_replayOne L maxAtp host f q hq'] at hq; cases hq
  · have a := verify_fuel_le L maxAtp host (Nat.le_max_left f g) hq' (by simp)
    have b := verify_fuel_le L maxAtp host (Nat.le_max_right f g) hq (by simp)
    rw [a] at b; cases b

/-- Corollary: every checkpoint in the lineage of a `REPLAYED` checkpoint is
reached by one advance from `SR.start`. -/
theorem verify_lineage_sound (hs : HostSound host) {f : Nat} {q c : C} (hl : Lin L q c)
    (h : verify L maxAtp host f c = .replayed) :
    adv M (L.start (L.comp q)) (L.spent q) = (L.state q, L.spent q) :=
  verify_sound L maxAtp host hs f q (verify_ancestor_replayed L maxAtp host hl h)

end Vars1.Replay
