import Vars1.Pass1

/-!
# One Active local scope

The gate admits a scope rotation only as a new local scope cell that supersedes the governing scope, sealed by its
admission quorum (§3 check 1). `RotationAdmitted` states that shape on the chain. From it:

* `governed_superseded` — a scope that governed at some commit and no longer governs at a later one has a latched
  `supersedes` edge, by then, from a scope that governed in between.
* `unique_active_scope` — if every local scope cell present at the tip has governed at some commit, and scope cells
  are Effective and Accepted (no edge may invalidate or retire a scope cell, and local cells are accepted), then at
  most one local scope cell is Active at the tip: the governing one.

Property I7 of the test suite checks the same statement on the implementation.
-/

set_option linter.unusedSectionVars false

namespace Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K]

/-- **Hypothesis (§3 check 1).** Each rotation `newScope = S'` at `T_i` is a new cell that supersedes the scope
governing `T_i`, and that edge satisfies §4.1 step 3 at `T_i` (the gate requires the admission quorum). -/
def RotationAdmitted (W : World C K P) (s0 : St C K) (chain : List (Commit C K)) : Prop :=
  ∀ (i : Nat) (hi : i < chain.length) (S' : C), chain[i].newScope = some S' →
    S' ∈ chain[i].newCells ∧ (stateAt W s0 chain i).scope ∈ (W.info S').supersedes ∧
    edgeCond W chain[i] (stateAt W s0 chain i).scope S' (stateAt W s0 chain i).scope .supersedes
      (initAfter W (stateAt W s0 chain i) chain[i]) = true

theorem stateAt_succ_scope (W : World C K P) (s0 : St C K) (chain : List (Commit C K)) {n : Nat}
    (hn : n < chain.length) :
    (stateAt W s0 chain (n + 1)).scope = chain[n].newScope.getD (stateAt W s0 chain n).scope := by
  rw [stateAt_succ W s0 chain hn]
  rfl

/-- A scope that governed at `i` and does not govern at `n ≥ i` is named in `supersedes` of a scope that governed
at some `j ≤ n`, by an edge latched at `n`. -/
theorem governed_superseded (W : World C K P) (s0 : St C K) (chain : List (Commit C K))
    (hR : RotationAdmitted W s0 chain) (i : Nat) :
    ∀ n, i ≤ n → n ≤ chain.length →
      (stateAt W s0 chain i).scope ≠ (stateAt W s0 chain n).scope →
      ∃ S', (∃ j, j ≤ n ∧ (stateAt W s0 chain j).scope = S') ∧
        (stateAt W s0 chain i).scope ∈ (W.info S').supersedes ∧
        (stateAt W s0 chain n).edge S' (stateAt W s0 chain i).scope .supersedes = true := by
  intro n
  induction n with
  | zero =>
    intro hin _ hne
    have : i = 0 := by omega
    subst this
    exact absurd rfl hne
  | succ n ih =>
    intro hin hn hne
    rcases Nat.lt_or_ge n i with hlt | hge
    · have : i = n + 1 := by omega
      subst this
      exact absurd rfl hne
    have hnl : n < chain.length := by omega
    by_cases hsame : (stateAt W s0 chain i).scope = (stateAt W s0 chain n).scope
    · -- the scope changed at commit `n`: that rotation supersedes it
      have hs := stateAt_succ_scope W s0 chain hnl
      cases hns : chain[n].newScope with
      | none =>
        rw [hns] at hs
        exact absurd (hsame.trans hs.symm) hne
      | some S' =>
        obtain ⟨hnew, hmem, hcond⟩ := hR n hnl S' hns
        refine ⟨S', ⟨n + 1, Nat.le_refl _, by rw [hs, hns]; rfl⟩, hsame ▸ hmem, ?_⟩
        rw [stateAt_succ W s0 chain hnl, step_edge_iff, hsame]
        exact Or.inr ⟨List.mem_append_right _ hnew, hmem, hcond⟩
    · obtain ⟨S', ⟨j, hj, hjs⟩, hmem, hedge⟩ := ih hge (by omega) hsame
      exact ⟨S', ⟨j, by omega, hjs⟩, hmem,
        (stateAt_mono W s0 chain (Nat.le_succ n)).1 _ _ _ hedge⟩

/-- **Theorem (one Active local scope).** Suppose rotations are admitted as the gate requires, every local scope cell
present at the tip governed at some commit, and scope cells are Effective and Accepted. Then a local scope cell that
is Active at the tip — under the tip's latched edges — is the governing scope; so two Active local scope cells are
equal. -/
theorem unique_active_scope (W : World C K P) (s0 : St C K) (chain : List (Commit C K))
    (hR : RotationAdmitted W s0 chain)
    (hG : ∀ c, (W.info c).schema = .scope → (W.info c).isLocal = true →
      c ∈ (stateAt W s0 chain chain.length).present ∨ c = s0.scope →
      ∃ i, i ≤ chain.length ∧ (stateAt W s0 chain i).scope = c)
    (Eff Acc Ret : C → Prop)
    (hEA : ∀ j, j ≤ chain.length → Eff (stateAt W s0 chain j).scope ∧ Acc (stateAt W s0 chain j).scope)
    {c : C} (hsc : (W.info c).schema = .scope) (hloc : (W.info c).isLocal = true)
    (hpres : c ∈ (stateAt W s0 chain chain.length).present ∨ c = s0.scope)
    (hact : Active W (stateAt W s0 chain chain.length).edge Eff Acc Ret c) :
    c = (stateAt W s0 chain chain.length).scope := by
  obtain ⟨i, hi, rfl⟩ := hG c hsc hloc hpres
  by_cases heq : (stateAt W s0 chain i).scope = (stateAt W s0 chain chain.length).scope
  · exact heq
  exfalso
  have hne := heq
  obtain ⟨S', ⟨j, hj, hjs⟩, hmem, hedge⟩ :=
    governed_superseded W s0 chain hR i chain.length hi (Nat.le_refl _) hne
  have hEff := (hEA j hj).1
  have hAcc := (hEA j hj).2
  rw [hjs] at hEff hAcc
  exact hact.2.2.1 (Superseded.direct hmem hedge hEff hAcc)

end Vars1
