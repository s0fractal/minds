/-!
# Relational Identity vs. Fork Continuity (`D21` / Thesis 2)

Resolves the conflict between the authorization lineage criterion (`AuthPath`) and Thesis 2
("fork births a new entity") by separating two distinct warrant sorts over a causal lineage DAG:

  1. `EnabledBy` — authorizes a transition to exist (`step` or `fork`) and preserves constitutional
     invariants `I*`. Both linear continuations and forks satisfy `AuthPath` and inherit provenance.
  2. `IdentityContinuation` — authorizes single-branch identity continuity (`step` only, never `fork`),
     subject to `UniqueContinuation` (at most one identity-continuing successor per node).

Constructive theorems (0 `sorry`, 0 `Classical.choice`):
  - `sameEntity_implies_authPath`: `AuthPath` is necessary for `SameEntity`.
  - `sameEntity_implies_ancestor`: `SameEntity` preserves causal provenance (`Ancestor`).
  - `unique_continuation_no_split_brain`: under `UniqueContinuation`, two distinct successors of
    the same parent cannot both continue its identity (forbids split-brain identity duplication).
  - `no_incoming_continuation_not_same`: a node born without an incoming `IdentityContinuation`
    edge (such as any `fork` child) is never `SameEntity` as an ancestor.
  - `fork_target_not_same_as_any_other` & `fork_not_same_entity`: under `fork_no_continuation`,
    any node born via `fork` is strictly distinct from every other node (including across
    multi-hop `step` detours).
  - `fork_no_obligation_theft`: a `fork` transition inherits provenance without silently cloning
    external relational obligations or trust standing onto the new entity.
  - `d21_fork_authorized_and_ancestor` & `d21_fork_new_entity_and_isolated`: concrete `Fin 3`
    witness where `inv 0 = inv 2 = 42` (identical byte invariants) and `AuthPath 0 2` holds,
    yet `¬ SameEntity 0 2` and `¬ rels 2 1`.
-/

namespace Vars1.Identity

/-! ## 1. Lineage DAG with Separated Warrant Sorts -/

inductive EdgeKind where
  | step : EdgeKind
  | fork : EdgeKind
  deriving DecidableEq, Repr

/-- A lineage graph over entity nodes `N` with byte/constitutional invariants `I` and
external relational standing `R`. -/
structure LineageGraph (N I R : Type) where
  inv          : N → I
  rels         : N → R → Prop
  enabled      : N → N → EdgeKind → Prop
  continues    : N → N → Prop
  invOk        : I → I → Prop
  /-- Every identity continuation must be an enabled non-forking `step` edge. -/
  continues_is_step    : ∀ u v, continues u v → enabled u v .step
  /-- Every enabled transition satisfies the constitutional meta-invariant `I*`. -/
  enabled_inv_ok       : ∀ u v k, enabled u v k → invOk (inv u) (inv v)
  /-- Fork birth excludes identity continuation: a node born by `fork` has no incoming
  `IdentityContinuation` edge from any node. -/
  fork_no_continuation : ∀ p c, enabled p c .fork → ∀ x, ¬ continues x c

/-- Uniqueness of identity continuation: a node has at most one identity-continuing successor
(prevents split-brain identity cloning). -/
def UniqueContinuation {N I R : Type} (G : LineageGraph N I R) : Prop :=
  ∀ u v₁ v₂, G.continues u v₁ → G.continues u v₂ → v₁ = v₂

/-- Path-indexed causal ancestry (any sequence of enabled `step` or `fork` edges). -/
inductive Ancestor {N I R : Type} (G : LineageGraph N I R) : N → N → Prop where
  | refl (u : N) : Ancestor G u u
  | edge {u v w : N} {k : EdgeKind} : G.enabled u v k → Ancestor G v w → Ancestor G u w

/-- Path-indexed authorization admissibility (`AuthPath`): every edge along the path is enabled
and satisfies the constitutional invariant `invOk` (`I*`). -/
inductive AuthPath {N I R : Type} (G : LineageGraph N I R) : N → N → Prop where
  | refl (u : N) : AuthPath G u u
  | step {u v w : N} {k : EdgeKind} :
      G.enabled u v k → G.invOk (G.inv u) (G.inv v) → AuthPath G v w → AuthPath G u w

/-- Strict single-branch identity continuity (`SameEntity`): transitive closure of
`IdentityContinuation` edges only (never crosses a `fork`). -/
inductive SameEntity {N I R : Type} (G : LineageGraph N I R) : N → N → Prop where
  | refl (u : N) : SameEntity G u u
  | cont {u v w : N} : G.continues u v → SameEntity G v w → SameEntity G u w

theorem sameEntity_trans {N I R : Type} {G : LineageGraph N I R} {u v w : N}
    (h1 : SameEntity G u v) (h2 : SameEntity G v w) : SameEntity G u w := by
  induction h1 with
  | refl _ => exact h2
  | cont hc _ ih => exact SameEntity.cont hc (ih h2)

theorem authPath_trans {N I R : Type} {G : LineageGraph N I R} {u v w : N}
    (h1 : AuthPath G u v) (h2 : AuthPath G v w) : AuthPath G u w := by
  induction h1 with
  | refl _ => exact h2
  | step he hi _ ih => exact AuthPath.step he hi (ih h2)

/-- `AuthPath` is necessary for `SameEntity`: every identity-continuing lineage is
constitutionally authorized. -/
theorem sameEntity_implies_authPath {N I R : Type} {G : LineageGraph N I R} {u v : N}
    (h : SameEntity G u v) : AuthPath G u v := by
  induction h with
  | refl x => exact AuthPath.refl x
  | cont hc _ ih =>
      have he := G.continues_is_step _ _ hc
      exact AuthPath.step he (G.enabled_inv_ok _ _ .step he) ih

/-- `SameEntity` preserves causal provenance (`Ancestor`). -/
theorem sameEntity_implies_ancestor {N I R : Type} {G : LineageGraph N I R} {u v : N}
    (h : SameEntity G u v) : Ancestor G u v := by
  induction h with
  | refl x => exact Ancestor.refl x
  | cont hc _ ih => exact Ancestor.edge (G.continues_is_step _ _ hc) ih

/-- **No Split-Brain Identity Theorem**: under `UniqueContinuation`, two distinct direct
continuations from the same parent are impossible. -/
theorem unique_continuation_no_split_brain {N I R : Type} {G : LineageGraph N I R}
    (huniq : UniqueContinuation G) {u v₁ v₂ : N}
    (h1 : G.continues u v₁) (h2 : G.continues u v₂) (hne : v₁ ≠ v₂) : False :=
  hne (huniq u v₁ v₂ h1 h2)

/-- If nothing continues into `c` (e.g., `c` was born by `fork`), then `SameEntity G p c` forces `p = c`. -/
theorem sameEntity_eq_of_no_incoming {N I R : Type} {G : LineageGraph N I R} {p c : N}
    (h : SameEntity G p c) (hno : ∀ x, ¬ G.continues x c) : p = c := by
  induction h with
  | refl _ => rfl
  | @cont a b d hc _ ih =>
      have hbd : b = d := ih hno
      subst hbd
      exact False.elim (hno a hc)

/-- If a node `c` has no incoming `IdentityContinuation` edge (e.g. born by `fork`), then no
strictly earlier node `p ≠ c` can satisfy `SameEntity G p c`. -/
theorem no_incoming_continuation_not_same {N I R : Type} {G : LineageGraph N I R} {p c : N}
    (hne : p ≠ c) (hno : ∀ x, ¬ G.continues x c) : ¬ SameEntity G p c :=
  fun h => hne (sameEntity_eq_of_no_incoming h hno)

/-- Any node `c` born via a `fork` edge cannot satisfy `SameEntity G a c` for any other node
`a ≠ c`, ruling out multi-hop `step` detours that attempt to rejoin a fork-born node. -/
theorem fork_target_not_same_as_any_other {N I R : Type} {G : LineageGraph N I R} {p c a : N}
    (hfork : G.enabled p c .fork) (hne : a ≠ c) : ¬ SameEntity G a c :=
  no_incoming_continuation_not_same hne (G.fork_no_continuation p c hfork)

/-- **Fork Births a New Entity Theorem (Thesis 2 / D21)**: for any `LineageGraph`, a non-self
`fork` edge `p → c` strictly separates entity identity (`¬ SameEntity G p c`). -/
theorem fork_not_same_entity {N I R : Type} {G : LineageGraph N I R} {p c : N}
    (hne : p ≠ c) (hfork : G.enabled p c .fork) : ¬ SameEntity G p c :=
  fork_target_not_same_as_any_other hfork hne

/-! ## 2. Relational Isolation on Fork (No Silent Obligation / Trust Cloning) -/

/-- Relational discipline on `fork`: a node born by `fork` starts with no cloned external
relations from its parent (`∀ r, ¬ G.rels child r`), even though its byte invariants match. -/
def ForkIsolatesRelations {N I R : Type} (G : LineageGraph N I R) : Prop :=
  ∀ p c, G.enabled p c .fork → ∀ r, ¬ G.rels c r

theorem fork_no_obligation_theft {N I R : Type} {G : LineageGraph N I R}
    (hiso : ForkIsolatesRelations G) {p c : N} {r : R}
    (hfork : G.enabled p c .fork) : ¬ G.rels c r :=
  hiso p c hfork r

/-! ## 3. Constructive Resolution of F2 / D21 (Concrete Finite Witness) -/

/-- Three-node witness: `0` (root), `1` (continued self via `step`), `2` (new entity born via `fork`).
All three nodes carry identical byte invariants (`inv _ = 42`), proving byte identity ≠ entity identity. -/
def d21Graph : LineageGraph (Fin 3) Nat Nat where
  inv _ := 42
  rels n r := (n.val = 0 ∨ n.val = 1) ∧ r = 1
  enabled u v k :=
    (u.val = 0 ∧ v.val = 1 ∧ k = .step) ∨
    (u.val = 0 ∧ v.val = 2 ∧ k = .fork)
  continues u v := u.val = 0 ∧ v.val = 1
  invOk i1 i2 := i1 = i2
  continues_is_step := by
    intro u v ⟨h0, h1⟩
    exact Or.inl ⟨h0, h1, rfl⟩
  enabled_inv_ok := by
    intro _ _ _ _
    rfl
  fork_no_continuation := by
    intro _ _ hf _ ⟨_, h1⟩
    rcases hf with ⟨_, _, hk⟩ | ⟨_, hc2, _⟩
    · exact EdgeKind.noConfusion hk
    · rw [hc2] at h1; cases h1

theorem d21_unique_continuation : UniqueContinuation d21Graph := by
  intro _ v₁ v₂ ⟨_, h1⟩ ⟨_, h2⟩
  exact Fin.ext (h1.trans h2.symm)

theorem d21_fork_isolates_relations : ForkIsolatesRelations d21Graph := by
  intro _ _ hf _ ⟨h01, _⟩
  rcases hf with ⟨_, _, hk⟩ | ⟨_, hc2, _⟩
  · exact EdgeKind.noConfusion hk
  · rcases h01 with h0 | h1
    · rw [hc2] at h0; cases h0
    · rw [hc2] at h1; cases h1

/-- Node `1` (`step`) IS the same entity as `0` and carries relation `r = 1`. -/
theorem d21_step_same_entity : SameEntity d21Graph ⟨0, by decide⟩ ⟨1, by decide⟩ :=
  SameEntity.cont ⟨rfl, rfl⟩ (SameEntity.refl _)

/-- Node `2` (`fork`) IS constitutionally authorized (`AuthPath`) with identical byte invariants
(`inv 0 = inv 2 = 42`) and inherits causal provenance (`Ancestor`)... -/
theorem d21_fork_authorized_and_ancestor :
    AuthPath d21Graph ⟨0, by decide⟩ ⟨2, by decide⟩ ∧
    Ancestor d21Graph ⟨0, by decide⟩ ⟨2, by decide⟩ ∧
    d21Graph.inv ⟨0, by decide⟩ = d21Graph.inv ⟨2, by decide⟩ := by
  have hf : d21Graph.enabled ⟨0, by decide⟩ ⟨2, by decide⟩ .fork := Or.inr ⟨rfl, rfl, rfl⟩
  exact ⟨AuthPath.step hf rfl (AuthPath.refl _), Ancestor.edge hf (Ancestor.refl _), rfl⟩

/-- ...YET node `2` (`fork`) is STRICTLY NOT the same entity as `0`, and inherits NONE of `0`'s
external relational standing (`¬ rels 2 1`) — resolving F2 / D21 constructively! -/
theorem d21_fork_new_entity_and_isolated :
    ¬ SameEntity d21Graph ⟨0, by decide⟩ ⟨2, by decide⟩ ∧
    ¬ d21Graph.rels ⟨2, by decide⟩ 1 := by
  have hf : d21Graph.enabled ⟨0, by decide⟩ ⟨2, by decide⟩ .fork := Or.inr ⟨rfl, rfl, rfl⟩
  exact ⟨fork_not_same_entity (by decide) hf, fork_no_obligation_theft d21_fork_isolates_relations hf⟩

end Vars1.Identity
