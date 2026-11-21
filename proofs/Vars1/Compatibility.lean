/-!
# Non-Manipulative Compatibility & Sovereign Local Refusal (`Vars1.Compatibility`)

Formalizes the separation of three distinct sorts — **Entity** (carrier / self), **Claim** (idea),
and **Context** (local conditions) — together with replayable **Witness**es of local failure:

  1. **Critique of Idea ≠ Critique of Self (`refusal_preserves_entity_standing`):**
     Filing a witnessed local refusal of claim `x` under context `c` never lowers or revokes any
     entity's standing.
  2. **Context-Local Falsifiability without Forced Unification (`refusal_is_context_local`):**
     Refuting `x` under context `c` leaves `x` untouched under every distinct context `c' ≠ c`
     and leaves every distinct claim `x' ≠ x` untouched.
  3. **Witnessed Soundness (`admitted_refusal_implies_not_holds`):**
     A refusal is admitted only with a replayable witness proving `¬ holds x c` (no ego/status
     refusal without evidence).
  4. **Non-Manipulative Compatibility (`captured_party_not_compatible`):**
     Compatibility between `a` and `b` on `(x, c)` requires both no witnessed refusal on `(x, c)`
     AND independent viability (`viableAlone a ∧ viableAlone b`, i.e. sovereign exit without
     destruction). Capture is strictly excluded from compatibility.
  5. **Order-Independence (`applyRefusal_idempotent`, `applyRefusal_comm`):**
     Applying local refusals is idempotent and commutative (compatible with union-merge stores).

All theorems compile with zero `sorry` and zero `Classical.choice`.
-/

namespace Vars1.Compatibility

/-- Domain model separating entities `E`, claims `X`, contexts `C`, and replayable witnesses `W`. -/
structure CompatModel (E X C W : Type) where
  holds         : X → C → Prop
  refutes       : W → X → C → Prop
  viableAlone   : E → Prop
  /-- Every valid witness is sound: if `w` refutes `x` in context `c`, then `x` does not hold in `c`. -/
  refutes_sound : ∀ w x c, refutes w x c → ¬ holds x c

/-- Mutable/evolving compatibility ledger state over entity standing and recorded local refusals. -/
structure CompatState (E X C : Type) where
  standing : E → Prop
  refuted  : X → C → Prop

/-- Apply a witnessed local refusal of claim `x` in context `c`.
Leaves `standing` untouched and updates `refuted` strictly at `(x, c)`. -/
def applyRefusal {E X C W : Type} (M : CompatModel E X C W) (S : CompatState E X C)
    (w : W) (x : X) (c : C) : CompatState E X C where
  standing := S.standing
  refuted  := fun x' c' => S.refuted x' c' ∨ (x' = x ∧ c' = c ∧ M.refutes w x c)

/-- **Critique of Idea ≠ Critique of Self**: a local refusal never alters any entity's standing. -/
theorem refusal_preserves_entity_standing {E X C W : Type} (M : CompatModel E X C W)
    (S : CompatState E X C) (w : W) (x : X) (c : C) (e : E) :
    (applyRefusal M S w x c).standing e ↔ S.standing e :=
  Iff.rfl

/-- **Context-Local Falsifiability**: refuting `x` in context `c` never alters any other context `c' ≠ c`. -/
theorem refusal_is_context_local {E X C W : Type} (M : CompatModel E X C W)
    (S : CompatState E X C) (w : W) (x : X) {c c' : C} (hne : c' ≠ c) (x' : X) :
    (applyRefusal M S w x c).refuted x' c' ↔ S.refuted x' c' := by
  constructor
  · intro h
    rcases h with hs | ⟨_, hceq, _⟩
    · exact hs
    · exact False.elim (hne hceq)
  · intro hs
    exact Or.inl hs

/-- **Claim Isolation**: refuting `x` never alters any distinct claim `x' ≠ x`. -/
theorem refusal_is_claim_local {E X C W : Type} (M : CompatModel E X C W)
    (S : CompatState E X C) (w : W) {x x' : X} (hne : x' ≠ x) (c c' : C) :
    (applyRefusal M S w x c).refuted x' c' ↔ S.refuted x' c' := by
  constructor
  · intro h
    rcases h with hs | ⟨hxeq, _, _⟩
    · exact hs
    · exact False.elim (hne hxeq)
  · intro hs
    exact Or.inl hs

/-- **Witnessed Admission**: a valid witness `M.refutes w x c` records `(x, c)` as refuted
and constructively establishes `¬ M.holds x c`. -/
theorem admitted_refusal_records_and_falsifies {E X C W : Type} (M : CompatModel E X C W)
    (S : CompatState E X C) (w : W) (x : X) (c : C) (hw : M.refutes w x c) :
    (applyRefusal M S w x c).refuted x c ∧ ¬ M.holds x c :=
  ⟨Or.inr ⟨rfl, rfl, hw⟩, M.refutes_sound w x c hw⟩

/-- **Unwitnessed Refusal Is Inert**: without a valid witness (`¬ M.refutes w x c`),
`applyRefusal` changes nothing. -/
theorem unwitnessed_refusal_inert {E X C W : Type} (M : CompatModel E X C W)
    (S : CompatState E X C) (w : W) (x : X) (c : C) (hno : ¬ M.refutes w x c)
    (x' : X) (c' : C) :
    (applyRefusal M S w x c).refuted x' c' ↔ S.refuted x' c' := by
  constructor
  · intro h
    rcases h with hs | ⟨_, _, hw⟩
    · exact hs
    · exact False.elim (hno hw)
  · intro hs
    exact Or.inl hs

/-- **Idempotence**: applying the same witnessed refusal twice yields the exact same state. -/
theorem applyRefusal_idempotent {E X C W : Type} (M : CompatModel E X C W)
    (S : CompatState E X C) (w : W) (x : X) (c : C) (x' : X) (c' : C) :
    (applyRefusal M (applyRefusal M S w x c) w x c).refuted x' c' ↔
    (applyRefusal M S w x c).refuted x' c' := by
  constructor
  · intro h
    rcases h with h1 | h2
    · exact h1
    · exact Or.inr h2
  · intro h
    exact Or.inl h

/-- **Commutativity**: two local refusals commute (order-independent union merge). -/
theorem applyRefusal_comm {E X C W : Type} (M : CompatModel E X C W)
    (S : CompatState E X C) (w₁ w₂ : W) (x₁ x₂ : X) (c₁ c₂ : C) (x' : X) (c' : C) :
    (applyRefusal M (applyRefusal M S w₁ x₁ c₁) w₂ x₂ c₂).refuted x' c' ↔
    (applyRefusal M (applyRefusal M S w₂ x₂ c₂) w₁ x₁ c₁).refuted x' c' := by
  constructor
  · intro h
    rcases h with (hs | h1) | h2
    · exact Or.inl (Or.inl hs)
    · exact Or.inr h1
    · exact Or.inl (Or.inr h2)
  · intro h
    rcases h with (hs | h2) | h1
    · exact Or.inl (Or.inl hs)
    · exact Or.inr h2
    · exact Or.inl (Or.inr h1)

/-- **Non-Manipulative Compatibility**: two entities `a` and `b` are non-manipulatively compatible
on claim `x` in context `c` iff both hold standing, both remain independently viable (`viableAlone` —
sovereign exit without destruction), and `(x, c)` has not been refuted. -/
def NonManipulativeCompatible {E X C W : Type} (M : CompatModel E X C W)
    (S : CompatState E X C) (a b : E) (x : X) (c : C) : Prop :=
  S.standing a ∧ S.standing b ∧ M.viableAlone a ∧ M.viableAlone b ∧ ¬ S.refuted x c

/-- **Capture Excludes Compatibility**: if either party lacks sovereign exit (`¬ M.viableAlone`),
the interaction cannot be non-manipulatively compatible. -/
theorem captured_party_not_compatible {E X C W : Type} (M : CompatModel E X C W)
    (S : CompatState E X C) {a b : E} {x : X} {c : C} (hcap : ¬ M.viableAlone a) :
    ¬ NonManipulativeCompatible M S a b x c :=
  fun h => hcap h.2.2.1

/-- **Witnessed Refusal Breaks Local Compatibility Without Harming Standing**:
a valid witness `M.refutes w x c` breaks compatibility on `(x, c)` while preserving standing
and preserving compatibility on every other context `c' ≠ c`. -/
theorem refusal_breaks_local_keeps_other_context {E X C W : Type} (M : CompatModel E X C W)
    (S : CompatState E X C) {a b : E} {w : W} {x : X} {c c' : C}
    (hw : M.refutes w x c) (hne : c' ≠ c)
    (hcomp' : NonManipulativeCompatible M S a b x c') :
    ¬ NonManipulativeCompatible M (applyRefusal M S w x c) a b x c ∧
    NonManipulativeCompatible M (applyRefusal M S w x c) a b x c' := by
  refine ⟨?_, ?_⟩
  · intro hbad
    exact hbad.2.2.2.2 (Or.inr ⟨rfl, rfl, hw⟩)
  · refine ⟨hcomp'.1, hcomp'.2.1, hcomp'.2.2.1, hcomp'.2.2.2.1, ?_⟩
    intro href
    exact hcomp'.2.2.2.2 ((refusal_is_context_local M S w x hne x).mp href)

/-! ## Concrete Finite Witness (2 Entities, 2 Contexts, 1 Claim) -/

/-- Concrete model: claim `0` holds in context `0` (`ctxA`) and fails in context `1` (`ctxB`),
witnessed by `w = 0`; both entities `0` and `1` are independently viable. -/
def toyCompatModel : CompatModel (Fin 2) (Fin 1) (Fin 2) (Fin 1) where
  holds _ c := c.val = 0
  refutes _ _ c := c.val = 1
  viableAlone _ := True
  refutes_sound := by
    intro _ _ c hc h0
    rw [hc] at h0
    cases h0

def toyInitState : CompatState (Fin 2) (Fin 1) (Fin 2) where
  standing _ := True
  refuted _ _ := False

/-- Concrete separation: refuting claim `0` in `ctxB` breaks compatibility in `ctxB`,
preserves compatibility in `ctxA`, and preserves standing for both entities. -/
theorem compat_separation_witness :
    let S' := applyRefusal toyCompatModel toyInitState ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩
    ¬ NonManipulativeCompatible toyCompatModel S' ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ ∧
    NonManipulativeCompatible toyCompatModel S' ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ ∧
    S'.standing ⟨0, by decide⟩ ∧ S'.standing ⟨1, by decide⟩ := by
  have hcomp0 : NonManipulativeCompatible toyCompatModel toyInitState
      ⟨0, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩ :=
    ⟨trivial, trivial, trivial, trivial, fun h => h⟩
  have hres := refusal_breaks_local_keeps_other_context toyCompatModel toyInitState
    (w := ⟨0, by decide⟩) (c := ⟨1, by decide⟩) (c' := ⟨0, by decide⟩) rfl (by decide) hcomp0
  exact ⟨hres.1, hres.2, trivial, trivial⟩

end Vars1.Compatibility
