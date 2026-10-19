/-!
# Least fixed points of monotone operators on predicates, and bounded iteration

Knaster–Tarski on `α → Prop` (no Mathlib), plus a counting argument on `Fin N`:
any "round" operator that, from a sound post-fixed state, never removes a cell,
never overshoots the least fixed point, and is stable only at a pre-fixed state,
reaches the least fixed point within `N + 1` rounds.
-/

namespace Vars1

/-- Pointwise inclusion of predicates. -/
def Sub {α : Type} (S T : α → Prop) : Prop := ∀ v, S v → T v

/-- `F` is monotone. -/
def Mono {α : Type} (F : (α → Prop) → (α → Prop)) : Prop :=
  ∀ S T, Sub S T → Sub (F S) (F T)

/-- The least fixed point: the intersection of all pre-fixed points. -/
def lfp {α : Type} (F : (α → Prop) → (α → Prop)) : α → Prop :=
  fun v => ∀ S, Sub (F S) S → S v

theorem lfp_least {α : Type} (F : (α → Prop) → (α → Prop)) (S : α → Prop)
    (h : Sub (F S) S) : Sub (lfp F) S := fun _ hv => hv S h

theorem lfp_pre {α : Type} {F : (α → Prop) → (α → Prop)} (hF : Mono F) :
    Sub (F (lfp F)) (lfp F) :=
  fun v hv S hS => hS v (hF _ _ (lfp_least F S hS) v hv)

theorem lfp_post {α : Type} {F : (α → Prop) → (α → Prop)} (hF : Mono F) :
    Sub (lfp F) (F (lfp F)) :=
  lfp_least F _ (hF _ _ (lfp_pre hF))

theorem lfp_fixed {α : Type} {F : (α → Prop) → (α → Prop)} (hF : Mono F) (v : α) :
    F (lfp F) v ↔ lfp F v :=
  ⟨lfp_pre hF v, lfp_post hF v⟩

/-! ## Counting on `Fin N` -/

open Classical in
/-- Number of cells in a predicate. -/
noncomputable def count {N : Nat} (S : Fin N → Prop) : Nat :=
  (List.finRange N).countP (fun v => decide (S v))

theorem countP_le_of_imp {α : Type} (p q : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = true → q x = true) : l.countP p ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    by_cases hp : p a = true
    · simp [hp, h a List.mem_cons_self hp]; omega
    · simp at hp; simp [hp]; split <;> omega

theorem countP_lt_of_imp {α : Type} (p q : α → Bool) (l : List α)
    (h : ∀ x ∈ l, p x = true → q x = true) (y : α) (hy : y ∈ l)
    (hq : q y = true) (hp : p y = false) : l.countP p < l.countP q := by
  induction l with
  | nil => simp at hy
  | cons a l ih =>
    simp only [List.countP_cons]
    have hle := countP_le_of_imp p q l (fun x hx => h x (List.mem_cons_of_mem a hx))
    rcases List.mem_cons.mp hy with rfl | hyl
    · simp [hq, hp]; omega
    · have := ih (fun x hx => h x (List.mem_cons_of_mem a hx)) hyl
      by_cases hpa : p a = true
      · simp [hpa, h a List.mem_cons_self hpa]; omega
      · simp at hpa; simp [hpa]; split <;> omega

open Classical in
theorem count_le {N : Nat} (S : Fin N → Prop) : count S ≤ N := by
  unfold count
  have := List.countP_le_length (p := fun v => decide (S v)) (l := List.finRange N)
  simpa using this

theorem count_lt {N : Nat} {S T : Fin N → Prop} (h : Sub S T) (y : Fin N)
    (hT : T y) (hS : ¬ S y) : count S < count T := by
  classical
  unfold count
  apply countP_lt_of_imp _ _ _ (fun x _ hx => by simpa using h x (by simpa using hx)) y
    (List.mem_finRange y) (by simpa using hT) (by simpa using hS)

/-! ## Bounded iteration -/

/-- `R` iterated `k` times from the empty predicate. -/
def iter {α : Type} (R : (α → Prop) → (α → Prop)) : Nat → (α → Prop)
  | 0 => fun _ => False
  | k + 1 => R (iter R k)

/-- The invariant of a sound iterate: below the least fixed point and post-fixed. -/
def Sound {α : Type} (F : (α → Prop) → (α → Prop)) (S : α → Prop) : Prop :=
  Sub S (lfp F) ∧ Sub S (F S)

/-- What a round operator `R` for `F` must satisfy. -/
structure RoundOp {α : Type} (F : (α → Prop) → (α → Prop)) (R : (α → Prop) → (α → Prop)) :
    Prop where
  /-- From a sound state a round never removes a cell and stays sound. -/
  grow : ∀ S, Sound F S → Sub S (R S) ∧ Sound F (R S)
  /-- A round that changes nothing stops at a pre-fixed point. -/
  stable : ∀ S, Sound F S → Sub (R S) S → Sub (F S) S

theorem iter_sound {α : Type} {F R : (α → Prop) → (α → Prop)} (hR : RoundOp F R) :
    ∀ k, Sound F (iter R k) ∧ Sub (iter R k) (iter R (k + 1))
  | 0 => ⟨⟨fun _ h => h.elim, fun _ h => h.elim⟩, fun _ h => h.elim⟩
  | k + 1 =>
    let ⟨hs, _⟩ := iter_sound hR k
    let ⟨_, hs'⟩ := hR.grow _ hs
    ⟨hs', (hR.grow _ hs').1⟩

/-- **Bounded iteration.** For any round operator `R` of a monotone `F` on
`Fin N`, round `N + 1` changes nothing, every round only adds cells, and the
result after `N` rounds is exactly the least fixed point of `F`. -/
theorem iter_reaches_lfp {N : Nat} {F R : (Fin N → Prop) → (Fin N → Prop)}
    (hR : RoundOp F R) :
    (∀ k, Sub (iter R k) (iter R (k + 1))) ∧
    (∀ v, iter R (N + 1) v ↔ iter R N v) ∧
    (∀ v, iter R N v ↔ lfp F v) := by
  have asc : ∀ k, Sub (iter R k) (iter R (k + 1)) := fun k => (iter_sound hR k).2
  -- Either some round j < k was stable, or the k-th iterate has ≥ k cells.
  have grow : ∀ k, (∃ j, j < k ∧ Sub (iter R (j + 1)) (iter R j)) ∨ k ≤ count (iter R k) := by
    intro k
    induction k with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ k ih =>
      rcases ih with ⟨j, hj, hs⟩ | hc
      · exact Or.inl ⟨j, Nat.lt_succ_of_lt hj, hs⟩
      · classical
        by_cases hst : Sub (iter R (k + 1)) (iter R k)
        · exact Or.inl ⟨k, Nat.lt_succ_self k, hst⟩
        · right
          have : ∃ y, iter R (k + 1) y ∧ ¬ iter R k y := by
            apply Classical.byContradiction
            intro hn
            apply hst
            intro v hv
            apply Classical.byContradiction
            intro hnv
            exact hn ⟨v, hv, hnv⟩
          obtain ⟨y, hy1, hy0⟩ := this
          have := count_lt (asc k) y hy1 hy0
          omega
  -- Once a round is stable, every later iterate equals it.
  have frozen : ∀ j, Sub (iter R (j + 1)) (iter R j) → ∀ m, j ≤ m → iter R m = iter R j := by
    intro j hj m hm
    have h1 : iter R (j + 1) = iter R j :=
      funext fun v => propext ⟨hj v, asc j v⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    induction d with
    | zero => rfl
    | succ d ih =>
      show R (iter R (j + d)) = iter R j
      rw [ih (Nat.le_add_right j d)]; exact h1
  obtain ⟨j, hjN, hjs⟩ : ∃ j, j < N + 1 ∧ Sub (iter R (j + 1)) (iter R j) := by
    rcases grow (N + 1) with h | hc
    · exact h
    · have := count_le (iter R (N + 1)); omega
  have eN : iter R N = iter R j := frozen j hjs N (by omega)
  have eN1 : iter R (N + 1) = iter R j := frozen j hjs (N + 1) (by omega)
  refine ⟨asc, fun v => by rw [eN, eN1], ?_⟩
  -- The stable iterate is pre-fixed (hence ⊇ lfp) and sound (hence ⊆ lfp).
  have hsN := (iter_sound hR N).1
  have hstab : Sub (R (iter R N)) (iter R N) := by
    intro v hv
    have : iter R (N + 1) v := hv
    rw [eN1, ← eN] at this
    exact this
  have hpre := hR.stable _ hsN hstab
  exact fun v => ⟨hsN.1 v, lfp_least F _ hpre v⟩

/-- Jacobi rounds (apply `F` to every cell at once) are a round operator. -/
theorem jacobi_round {α : Type} {F : (α → Prop) → (α → Prop)} (hF : Mono F) :
    RoundOp F F where
  grow _ hS := ⟨hS.2, fun v hv => lfp_pre hF v (hF _ _ hS.1 v hv), hF _ _ hS.2⟩
  stable _ _ h := h

end Vars1
