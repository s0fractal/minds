/-!
# Inductive Trajectory Safety (`D22`) & Horizon-Bounded Semantic Mass (`D26`)

Constructively formalizes the last two open ontology pillars (`F3 / D22` and `F7 / D26`):

  1. **Three-Part Trajectory Safety Law (`D22`):**
     Base (`inv x₀`), adversarial inductive step (`inv x → safeAct x a → step x a e x' → inv x'`),
     and compositional `SafeRun` induction proving that no safe trajectory of any length can ever
     reach an unsafe state.

  2. **Horizon-Bounded Semantic Mass (`D26`):**
     Over finite horizon `H : Nat` with exact integer weights and deduplicated `actId`s:
     - `semanticMass_mono_horizon`: monotonic in horizon `H₁ ≤ H₂`.
     - `semanticMass_bounded`: bounded above by `totalWeight acts` for ALL horizons `H` (finite
       convergence, never diverges).
     - `retold_zero_mass` & `forked_zero_mass`: retelling or forking an act adds strictly `0` mass
       (anti-Sybil non-inflation).
     - `duplicate_act_zero_mass`: replaying an already-counted `actId` adds strictly `0` mass.
     - `refuteId_non_inflationary`: error-driven revision (refuting an act via a counterexample)
       monotonically lowers or preserves semantic mass (`semanticMass H (refuteId id acts) ≤ semanticMass H acts`).

All theorems compile with zero `sorry` and zero `Classical.choice`.
-/

namespace Vars1.Trajectory

/-! ## 1. Three-Part Trajectory Safety Law (`D22 / F3`) -/

/-- A trajectory system with constitutional invariant `inv`, admissible action guard `safeAct`,
and adversarial environment step relation `step`. -/
structure TrajectorySystem (S A E : Type) where
  inv            : S → Prop
  safeAct        : S → A → Prop
  step           : S → A → E → S → Prop
  step_preserves : ∀ x a e x', inv x → safeAct x a → step x a e x' → inv x'

/-- Horizon-indexed safe trajectory: every transition starts from a state satisfying `inv`,
uses a `safeAct`, and advances under `step`. -/
inductive SafeRun {S A E : Type} (T : TrajectorySystem S A E) : S → S → Nat → Prop where
  | nil (x : S) (hinv : T.inv x) : SafeRun T x x 0
  | cons {x y z : S} {a : A} {e : E} {n : Nat} :
      T.inv x → T.safeAct x a → T.step x a e y → SafeRun T y z n → SafeRun T x z (n + 1)

theorem safeRun_start_inv {S A E : Type} {T : TrajectorySystem S A E} {x y : S} {n : Nat}
    (h : SafeRun T x y n) : T.inv x := by
  cases h with
  | nil _ hinv => exact hinv
  | cons hinv _ _ _ => exact hinv

theorem safeRun_end_inv {S A E : Type} {T : TrajectorySystem S A E} {x y : S} {n : Nat}
    (h : SafeRun T x y n) : T.inv y := by
  induction h with
  | nil _ hinv => exact hinv
  | cons _ _ _ _ ih => exact ih

/-- Compositional trajectory safety: concatenating two safe runs yields a safe run. -/
theorem safeRun_compose {S A E : Type} {T : TrajectorySystem S A E} {x y z : S} {m n : Nat}
    (h1 : SafeRun T x y m) (h2 : SafeRun T y z n) : SafeRun T x z (m + n) := by
  induction h1 with
  | nil _ _ =>
      simpa [Nat.zero_add] using h2
  | cons hinv hsa hstep _ ih =>
      have hcomp := SafeRun.cons hinv hsa hstep (ih h2)
      simpa [Nat.succ_add] using hcomp

/-- No safe trajectory of any length can reach a state violating `inv`. -/
theorem safeRun_no_unsafe_end {S A E : Type} {T : TrajectorySystem S A E} {x y : S} {n : Nat}
    (hbad : ¬ T.inv y) : ¬ SafeRun T x y n :=
  fun hrun => hbad (safeRun_end_inv hrun)

/-- Single-step extension of a safe run preserves `inv` under any adversarial environment move. -/
theorem safeRun_snoc {S A E : Type} {T : TrajectorySystem S A E} {x y z : S} {a : A} {e : E} {n : Nat}
    (hrun : SafeRun T x y n) (hsa : T.safeAct y a) (hstep : T.step y a e z) :
    SafeRun T x z (n + 1) := by
  have hy : T.inv y := safeRun_end_inv hrun
  have hz : T.inv z := T.step_preserves y a e z hy hsa hstep
  exact safeRun_compose hrun (SafeRun.cons hy hsa hstep (SafeRun.nil z hz))

/-! ## 2. Horizon-Bounded Semantic Mass & Error-Driven Revision (`D26 / F7`) -/

inductive ActOrigin where
  | verified : ActOrigin
  | retold   : ActOrigin
  | forked   : ActOrigin
  deriving DecidableEq, Repr

structure SemanticAct where
  actId   : Nat
  stepIdx : Nat
  weight  : Nat
  origin  : ActOrigin
  refuted : Bool
  deriving DecidableEq, Repr

/-- Contribution of a single act at horizon `H`: non-zero ONLY if genuinely `verified`,
not `refuted`, and within horizon `stepIdx ≤ H`. -/
def actMass (H : Nat) (a : SemanticAct) : Nat :=
  if a.origin = .verified ∧ a.refuted = false ∧ a.stepIdx ≤ H then a.weight else 0

/-- Total raw weight of a list of acts (upper bound for convergence across all horizons). -/
def totalWeight : List SemanticAct → Nat
  | [] => 0
  | a :: rest => a.weight + totalWeight rest

/-- Deduplicated horizon-bounded semantic mass: each `actId` is counted at most once. -/
def semanticMassAux (H : Nat) (seen : List Nat) : List SemanticAct → Nat
  | [] => 0
  | a :: rest =>
      if a.actId ∈ seen then
        semanticMassAux H seen rest
      else
        actMass H a + semanticMassAux H (a.actId :: seen) rest

def semanticMass (H : Nat) (acts : List SemanticAct) : Nat :=
  semanticMassAux H [] acts

/-- Error-driven revision: mark every occurrence of `targetId` as refuted. -/
def refuteId (targetId : Nat) : List SemanticAct → List SemanticAct
  | [] => []
  | a :: rest =>
      let a' := if a.actId = targetId then { a with refuted := true } else a
      a' :: refuteId targetId rest

theorem retold_zero_mass (H : Nat) (a : SemanticAct) (h : a.origin = .retold) :
    actMass H a = 0 := by
  unfold actMass
  simp [h]

theorem forked_zero_mass (H : Nat) (a : SemanticAct) (h : a.origin = .forked) :
    actMass H a = 0 := by
  unfold actMass
  simp [h]

theorem refuted_zero_mass (H : Nat) (a : SemanticAct) (h : a.refuted = true) :
    actMass H a = 0 := by
  unfold actMass
  simp [h]

theorem actMass_le_weight (H : Nat) (a : SemanticAct) : actMass H a ≤ a.weight := by
  unfold actMass
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

theorem actMass_mono_horizon {H₁ H₂ : Nat} (hle : H₁ ≤ H₂) (a : SemanticAct) :
    actMass H₁ a ≤ actMass H₂ a := by
  unfold actMass
  split
  · rename_i h1
    have h2 : a.origin = .verified ∧ a.refuted = false ∧ a.stepIdx ≤ H₂ :=
      ⟨h1.1, h1.2.1, Nat.le_trans h1.2.2 hle⟩
    simp [h2]
  · exact Nat.zero_le _

theorem semanticMassAux_mono_horizon {H₁ H₂ : Nat} (hle : H₁ ≤ H₂) :
    ∀ seen acts, semanticMassAux H₁ seen acts ≤ semanticMassAux H₂ seen acts := by
  intro seen acts
  induction acts generalizing seen with
  | nil => exact Nat.le_refl 0
  | cons a rest ih =>
      simp only [semanticMassAux]
      split
      · exact ih seen
      · exact Nat.add_le_add (actMass_mono_horizon hle a) (ih (a.actId :: seen))

/-- **Horizon Monotonicity (`D26`)**: widening the horizon `H₁ ≤ H₂` monotonically increases or
preserves semantic mass. -/
theorem semanticMass_mono_horizon {H₁ H₂ : Nat} (hle : H₁ ≤ H₂) (acts : List SemanticAct) :
    semanticMass H₁ acts ≤ semanticMass H₂ acts :=
  semanticMassAux_mono_horizon hle [] acts

theorem semanticMassAux_bounded (H : Nat) :
    ∀ seen acts, semanticMassAux H seen acts ≤ totalWeight acts := by
  intro seen acts
  induction acts generalizing seen with
  | nil => exact Nat.le_refl 0
  | cons a rest ih =>
      simp only [semanticMassAux, totalWeight]
      split
      · exact Nat.le_trans (ih seen) (Nat.le_add_left _ _)
      · exact Nat.add_le_add (actMass_le_weight H a) (ih (a.actId :: seen))

/-- **Finite Convergence Bound (`D26`)**: for every horizon `H`, `semanticMass H acts ≤ totalWeight acts`. -/
theorem semanticMass_bounded (H : Nat) (acts : List SemanticAct) :
    semanticMass H acts ≤ totalWeight acts :=
  semanticMassAux_bounded H [] acts

/-- **Anti-Sybil Replay Idempotence**: replaying an already-seen `actId` contributes `0` mass. -/
theorem duplicate_act_zero_mass (H : Nat) (seen : List Nat) (a : SemanticAct)
    (rest : List SemanticAct) (hmem : a.actId ∈ seen) :
    semanticMassAux H seen (a :: rest) = semanticMassAux H seen rest := by
  simp [semanticMassAux, hmem]

theorem actMass_refute_le (H : Nat) (a : SemanticAct) :
    actMass H { a with refuted := true } ≤ actMass H a := by
  rw [refuted_zero_mass H { a with refuted := true } rfl]
  exact Nat.zero_le _

theorem semanticMassAux_refuteId_le (H targetId : Nat) :
    ∀ seen acts, semanticMassAux H seen (refuteId targetId acts) ≤ semanticMassAux H seen acts := by
  intro seen acts
  induction acts generalizing seen with
  | nil => exact Nat.le_refl 0
  | cons a rest ih =>
      by_cases heq : a.actId = targetId
      · simp only [refuteId, heq, ↓reduceIte, semanticMassAux]
        split
        · exact ih seen
        · exact Nat.add_le_add (actMass_refute_le H a) (ih (targetId :: seen))
      · simp only [refuteId, heq, ↓reduceIte, semanticMassAux]
        split
        · exact ih seen
        · exact Nat.add_le_add (Nat.le_refl _) (ih (a.actId :: seen))

/-- **Error-Driven Learning Non-Inflation**: refuting an act with a counterexample never increases
semantic mass (`semanticMass H (refuteId target acts) ≤ semanticMass H acts`). -/
theorem refuteId_non_inflationary (H targetId : Nat) (acts : List SemanticAct) :
    semanticMass H (refuteId targetId acts) ≤ semanticMass H acts :=
  semanticMassAux_refuteId_le H targetId [] acts

/-! ## 3. Concrete Constructive Witness (`D22` + `D26`) -/

/-- Three-state trajectory system: `0` and `1` satisfy `inv`, `2` is unsafe. -/
def toySys : TrajectorySystem (Fin 3) Bool Bool where
  inv s := s.val < 2
  safeAct _ a := a = true
  step s a e s' :=
    (s.val < 2 ∧ a = true ∧ ((e = true ∧ s'.val = 1) ∨ (e = false ∧ s'.val = 0))) ∨
    (a = false ∧ s'.val = 2)
  step_preserves := by
    intro x a e x' _ hsa hstep
    rcases hstep with ⟨_, _, ⟨_, h1⟩ | ⟨_, h0⟩⟩ | ⟨haf, _⟩
    · rw [h1]; decide
    · rw [h0]; decide
    · rw [hsa] at haf; cases haf

def toyLedger : List SemanticAct :=
  [ ⟨1, 0, 10, .verified, false⟩,
    ⟨2, 1, 7, .verified, false⟩,
    ⟨3, 1, 50, .forked, false⟩,
    ⟨4, 1, 50, .retold, false⟩,
    ⟨1, 1, 10, .verified, false⟩ ]

/-- Concrete witness: 2-step safe trajectory holds, unsafe state `2` is unreachable,
forked/retold/duplicate acts add `0` mass (`10 + 7 = 17`), and refuting act `1` lowers mass to `7`. -/
theorem d22_d26_witness :
    SafeRun toySys ⟨0, by decide⟩ ⟨1, by decide⟩ 2 ∧
    ¬ SafeRun toySys ⟨0, by decide⟩ ⟨2, by decide⟩ 2 ∧
    semanticMass 5 toyLedger = 17 ∧
    semanticMass 5 (refuteId 1 toyLedger) = 7 := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · have h0 : toySys.inv ⟨0, by decide⟩ := show (0 : Nat) < 2 by decide
    have h1 : toySys.inv ⟨1, by decide⟩ := show (1 : Nat) < 2 by decide
    have s1 : toySys.step ⟨0, by decide⟩ true false ⟨0, by decide⟩ :=
      Or.inl ⟨by decide, rfl, Or.inr ⟨rfl, rfl⟩⟩
    have s2 : toySys.step ⟨0, by decide⟩ true true ⟨1, by decide⟩ :=
      Or.inl ⟨by decide, rfl, Or.inl ⟨rfl, rfl⟩⟩
    exact SafeRun.cons h0 rfl s1 (SafeRun.cons h0 rfl s2 (SafeRun.nil _ h1))
  · exact safeRun_no_unsafe_end (show ¬ ((2 : Nat) < 2) by decide)

end Vars1.Trajectory
