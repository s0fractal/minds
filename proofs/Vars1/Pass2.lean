import Vars1.Lfp

/-!
# §4.2 Pass 2: `Stale` as a least fixed point

Cells are `Fin N` (the finite set `𝒞` at the tip). Pass 1 results (`Active`,
`Authorized`) and cell structure are inputs.

* `LiveAcc L x` — `LiveAcceptedScopes(x) ≠ ∅` when the current `Stale` set is
  `L`: a pin by a local, `Active`, `Authorized`, non-`L` acceptance cell whose
  payload is `x`, propagated along same-origin references.
* `Ψ L D` — the Pass 2 right-hand side, with `LiveAcceptedScopes` computed from
  `L` and dependency staleness read from `D`.
* `Φ S = Ψ S S` — the operator whose least fixed point is `Stale`.

Theorems:
* `Φ_mono` — Φ is monotone (dependency staleness grows, `LiveAcc` shrinks).
* `stale_fixed`, `stale_least` — `Stale := lfp Φ` satisfies the §4.2 equation
  and is below every set that satisfies it as a pre-fixed point.
* `jacobi_reaches_stale` / `sweep_reaches_stale` — both the simultaneous round
  and the spec's in-place forward sweep (each round recomputes `LiveAcc` from
  the round's start, then updates cells in order reading already-updated
  values) only add cells, change nothing in round `N + 1`, and end at `Stale`.
-/

namespace Vars1

/-- Pass 2 inputs over `N` cells. -/
structure Pass2In (N : Nat) where
  active : Fin N → Prop
  authorized : Fin N → Prop
  isLocal : Fin N → Prop
  isAcceptance : Fin N → Prop
  payload : Fin N → Option (Fin N)
  origin : Fin N → Nat
  relies : Fin N → List (Fin N)
  refs : Fin N → List (Fin N)

variable {N : Nat} (I : Pass2In N)

/-- `LiveAcceptedScopes(x) ≠ ∅` given the current `Stale` set `L`. -/
inductive LiveAcc (L : Fin N → Prop) : Fin N → Prop where
  | pin {a x : Fin N} : I.isAcceptance a → I.isLocal a → I.active a → I.authorized a →
      ¬ L a → I.payload a = some x → LiveAcc L x
  | down {y x : Fin N} : LiveAcc L y → x ∈ I.refs y → I.origin y = I.origin x → LiveAcc L x

/-- Pass 2 right-hand side with `LiveAcceptedScopes` from `L`, dependencies from `D`. -/
def Ψ (L D : Fin N → Prop) (v : Fin N) : Prop :=
  I.active v ∧
    ((∃ d ∈ I.relies v, ¬ I.active d ∨ D d) ∨ (¬ I.isLocal v ∧ ¬ LiveAcc I L v))

/-- The §4.2 Pass 2 operator. -/
def Φ (S : Fin N → Prop) : Fin N → Prop := Ψ I S S

/-- **Pass 2 `Stale`** (§4.2): the least fixed point of `Φ`. -/
def Stale : Fin N → Prop := lfp (Φ I)

/-- `LiveAcceptedScopes` only shrinks as `Stale` grows. -/
theorem liveAcc_anti {L L' : Fin N → Prop} (h : Sub L L') {x : Fin N}
    (hx : LiveAcc I L' x) : LiveAcc I L x := by
  induction hx with
  | pin ha hl hact hauth hn hp => exact LiveAcc.pin ha hl hact hauth (fun hL => hn (h _ hL)) hp
  | down _ hr ho ih => exact LiveAcc.down ih hr ho

/-- Ψ is monotone in both arguments. -/
theorem Ψ_mono {L L' D D' : Fin N → Prop} (hL : Sub L L') (hD : Sub D D') :
    Sub (Ψ I L D) (Ψ I L' D') := by
  intro v ⟨ha, h⟩
  refine ⟨ha, ?_⟩
  rcases h with ⟨d, hd, h⟩ | ⟨hl, hn⟩
  · exact Or.inl ⟨d, hd, h.imp id (hD d)⟩
  · exact Or.inr ⟨hl, fun h' => hn (liveAcc_anti I hL h')⟩

/-- **Theorem 3a.** The Pass 2 operator is monotone. -/
theorem Φ_mono : Mono (Φ I) := fun _ _ h => Ψ_mono I h h

/-- **Theorem 3b.** `Stale` satisfies the §4.2 Pass 2 equation. -/
theorem stale_fixed (v : Fin N) :
    Stale I v ↔ I.active v ∧
      ((∃ d ∈ I.relies v, ¬ I.active d ∨ Stale I d) ∨
        (¬ I.isLocal v ∧ ¬ LiveAcc I (Stale I) v)) :=
  (lfp_fixed (Φ_mono I) v).symm

/-- **Theorem 3c.** `Stale` is below every pre-fixed point of the equation. -/
theorem stale_least (S : Fin N → Prop) (h : Sub (Φ I S) S) : Sub (Stale I) S :=
  lfp_least _ S h

/-- **Theorem 3d.** Simultaneous rounds reach `Stale` within `N + 1` rounds. -/
theorem jacobi_reaches_stale :
    (∀ k, Sub (iter (Φ I) k) (iter (Φ I) (k + 1))) ∧
    (∀ v, iter (Φ I) (N + 1) v ↔ iter (Φ I) N v) ∧
    (∀ v, iter (Φ I) N v ↔ Stale I v) :=
  iter_reaches_lfp (jacobi_round (Φ_mono I))

/-! ## The spec's round: in-place forward sweep -/

/-- After updating cells `0 … k-1` of a round that started from `S`:
`LiveAcc` is fixed from `S`, dependency staleness reads the current values. -/
def sweep (S : Fin N → Prop) : Nat → (Fin N → Prop)
  | 0 => S
  | k + 1 => fun v => if v.val = k then Ψ I S (sweep S k) v else sweep S k v

/-- One spec round. -/
def round (S : Fin N → Prop) : Fin N → Prop := sweep I S N

theorem sweep_untouched (S : Fin N → Prop) (v : Fin N) :
    ∀ k, k ≤ v.val → sweep I S k v = S v
  | 0, _ => rfl
  | k + 1, hk => by
    show (if v.val = k then _ else _) = _
    rw [if_neg (by omega)]
    exact sweep_untouched S v k (by omega)

theorem sweep_settled (S : Fin N → Prop) (v : Fin N) :
    ∀ d, sweep I S (v.val + 1 + d) v = Ψ I S (sweep I S v.val) v
  | 0 => by show (if v.val = v.val then _ else _) = _; rw [if_pos rfl]
  | d + 1 => by
    show (if v.val = v.val + 1 + d then _ else _) = _
    rw [if_neg (by omega)]
    exact sweep_settled S v d

theorem round_eq (S : Fin N → Prop) (v : Fin N) :
    round I S v = Ψ I S (sweep I S v.val) v := by
  have h := sweep_settled I S v (N - (v.val + 1))
  have e : v.val + 1 + (N - (v.val + 1)) = N := by have := v.isLt; omega
  rw [e] at h
  exact h

/-- From a post-fixed `S`, the sweep never removes a cell. -/
theorem sweep_ge (S : Fin N → Prop) (hS : Sub S (Φ I S)) : ∀ k, Sub S (sweep I S k)
  | 0 => fun _ h => h
  | k + 1 => by
    intro v hv
    show (if v.val = k then _ else _)
    split
    · exact Ψ_mono I (fun _ h => h) (sweep_ge S hS k) v (hS v hv)
    · exact sweep_ge S hS k v hv

theorem sweep_asc (S : Fin N → Prop) (hS : Sub S (Φ I S)) : ∀ k, Sub (sweep I S k) (sweep I S (k + 1)) := by
  intro k v hv
  show (if v.val = k then _ else _)
  split
  · rename_i h
    rw [sweep_untouched I S v k (by omega)] at hv
    exact Ψ_mono I (fun _ h => h) (sweep_ge I S hS k) v (hS v hv)
  · exact hv

theorem sweep_le_round (S : Fin N → Prop) (hS : Sub S (Φ I S)) :
    ∀ k, k ≤ N → Sub (sweep I S k) (round I S) := by
  intro k hk
  have add : ∀ d, Sub (sweep I S k) (sweep I S (k + d)) := by
    intro d
    induction d with
    | zero => exact fun _ h => h
    | succ d ih => exact fun v h => sweep_asc I S hS (k + d) v (ih v h)
  have e : k + (N - k) = N := by omega
  have := add (N - k)
  rw [e] at this
  exact this

theorem sweep_le_stale (S : Fin N → Prop) (hS : Sub S (Stale I)) : ∀ k, Sub (sweep I S k) (Stale I)
  | 0 => hS
  | k + 1 => by
    intro v hv
    revert hv
    show (if v.val = k then _ else _) → _
    split
    · intro hv
      exact lfp_pre (Φ_mono I) v (Ψ_mono I hS (sweep_le_stale S hS k) v hv)
    · exact sweep_le_stale S hS k v

/-- **Theorem 3e.** The spec's in-place forward sweep is a round operator for Φ. -/
theorem sweep_round : RoundOp (Φ I) (round I) where
  grow S hS := by
    have hge : Sub S (round I S) := sweep_ge I S hS.2 N
    refine ⟨hge, sweep_le_stale I S hS.1 N, ?_⟩
    intro v hv
    rw [round_eq] at hv
    exact Ψ_mono I hge (sweep_le_round I S hS.2 v.val (Nat.le_of_lt v.isLt)) v hv
  stable S hS h := by
    intro v hv
    apply h v
    rw [round_eq]
    exact Ψ_mono I (fun _ h => h) (sweep_ge I S hS.2 v.val) v hv

/-- **Theorem 3f.** Spec rounds from `Stale = ∅` only add cells, round
`N + 1` changes nothing, and the result is exactly `Stale`. -/
theorem sweep_reaches_stale :
    (∀ k, Sub (iter (round I) k) (iter (round I) (k + 1))) ∧
    (∀ v, iter (round I) (N + 1) v ↔ iter (round I) N v) ∧
    (∀ v, iter (round I) N v ↔ Stale I v) :=
  iter_reaches_lfp (sweep_round I)

end Vars1
