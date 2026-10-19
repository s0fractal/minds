import Vars1.Fold

/-!
# Rules v2: typed cell references (RULES-V2.md)

A cell's payload and slots are values `H`; `lookup` says which values are ids of cells present. The rules read some
positions (0 the payload, `1 + s` slot `s`) as references:

* v1 reads every position whose value is a cell id;
* v2 reads only typed positions (`typed p`): the payload of a verdict or acceptance and the slots declared `cell`.

`CellInfo.refs` (`Model.lean`) is the list these readings produce, so every theorem over it — Passes 1–2, their
executable form and its proof — holds for either reading; what changes is which cells end up in it. Here:

* `v2_opaque` — under v2 an untyped position is never a reference, whatever cells exist;
* `v2_stable` — when cells are only added, and every typed position already names a present cell (the gate's
  `cell` type check), v2 references do not change: an opaque digest stays opaque when its preimage is admitted;
* `v1_unstable` — v1 references do change when a cell is added (explicit counterexample), which is why v1 needs the
  gate's interim rule; `v1_stable_of_interim` — under that rule (no new cell has an id the cell already holds),
  they do not;
* `v2_persists` — under the rotation rule of §4 (no rotation from v2 back to v1), once the governing scope names
  v2 every later one does; `epoch_append` — the rules of a cell's birth commit, its epoch, never change after it.
-/

namespace Vars1.Refs

/-- The two rules identities: `H_LENS_KERNEL` and `H_LENS_KERNEL_V2`. -/
inductive Rules where
  | v1 | v2
  deriving DecidableEq, Repr

variable {H C : Type}

/-- The references `(p, c)` a reader `rd` finds in the values `vals`, the first at position `p`. -/
def refsFrom (rd : Nat → H → Option C) : Nat → List H → List (Nat × C)
  | _, [] => []
  | p, v :: vs =>
    match rd p v with
    | some c => (p, c) :: refsFrom rd (p + 1) vs
    | none => refsFrom rd (p + 1) vs

/-- The positions `(p, v)` of the values `vals`, the first at `p`. -/
def positions : Nat → List H → List (Nat × H)
  | _, [] => []
  | p, v :: vs => (p, v) :: positions (p + 1) vs

/-- v1: a value is a reference iff it is a cell id. -/
def readV1 (lookup : H → Option C) : Nat → H → Option C := fun _ v => lookup v

/-- v2: only typed positions are read. -/
def readV2 (lookup : H → Option C) (typed : Nat → Bool) : Nat → H → Option C :=
  fun p v => if typed p then lookup v else none

/-- A cell's references under rules `r`, from its payload and slots `vals`. -/
def refs (r : Rules) (lookup : H → Option C) (typed : Nat → Bool) (vals : List H) : List (Nat × C) :=
  match r with
  | .v1 => refsFrom (readV1 lookup) 0 vals
  | .v2 => refsFrom (readV2 lookup typed) 0 vals

/-- `lookup'` keeps every cell of `lookup`: cells are only added. -/
def Extends (lookup lookup' : H → Option C) : Prop :=
  ∀ v c, lookup v = some c → lookup' v = some c

theorem refsFrom_congr (rd rd' : Nat → H → Option C) : ∀ (p : Nat) (vals : List H),
    (∀ q v, (q, v) ∈ positions p vals → rd q v = rd' q v) → refsFrom rd p vals = refsFrom rd' p vals
  | _, [], _ => rfl
  | p, v :: vs, h => by
    have h0 : rd p v = rd' p v := h p v (by simp [positions])
    have ih := refsFrom_congr rd rd' (p + 1) vs (fun q w hq => h q w (by simp [positions, hq]))
    simp only [refsFrom, h0, ih]

theorem refsFrom_mem (rd : Nat → H → Option C) : ∀ (p : Nat) (vals : List H) (q : Nat) (c : C),
    (q, c) ∈ refsFrom rd p vals → ∃ v, (q, v) ∈ positions p vals ∧ rd q v = some c
  | _, [], _, _, h => by simp [refsFrom] at h
  | p, v :: vs, q, c, h => by
    unfold refsFrom at h
    cases hr : rd p v with
    | none =>
      rw [hr] at h
      obtain ⟨w, hw, hrw⟩ := refsFrom_mem rd (p + 1) vs q c h
      exact ⟨w, by simp [positions, hw], hrw⟩
    | some d =>
      rw [hr] at h
      simp only [List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨v, by simp [positions], hr⟩
      · obtain ⟨w, hw, hrw⟩ := refsFrom_mem rd (p + 1) vs q c h
        exact ⟨w, by simp [positions, hw], hrw⟩

/-- **Opaque positions.** Under v2 an untyped position is never a reference, whatever cells are present. -/
theorem v2_opaque (lookup : H → Option C) (typed : Nat → Bool) (vals : List H) (q : Nat) (c : C)
    (hq : typed q = false) : (q, c) ∉ refs .v2 lookup typed vals := by
  intro h
  obtain ⟨v, _, hv⟩ := refsFrom_mem _ 0 vals q c h
  simp [readV2, hq] at hv

/-- **Stability of typed references.** When cells are only added, and every typed position already names a present
cell (the gate's `cell` check at admission), a cell's v2 references are unchanged: a digest equal to the id of a
cell admitted later stays opaque. -/
theorem v2_stable (lookup lookup' : H → Option C) (typed : Nat → Bool) (vals : List H)
    (hext : Extends lookup lookup')
    (hres : ∀ q v, (q, v) ∈ positions 0 vals → typed q = true → (lookup v).isSome) :
    refs .v2 lookup' typed vals = refs .v2 lookup typed vals := by
  apply refsFrom_congr
  intro q v hq
  unfold readV2
  cases ht : typed q with
  | false => rfl
  | true =>
    simp only [if_true]
    have hs := hres q v hq ht
    cases hl : lookup v with
    | none => simp [hl] at hs
    | some c => exact hext v c hl

/-- **v1 references are not stable** (explicit counterexample): one value, no cell, then a cell with that id. -/
theorem v1_unstable : ∃ (lookup lookup' : Nat → Option Nat) (vals : List Nat),
    Extends lookup lookup' ∧ refs .v1 lookup' (fun _ => false) vals ≠ refs .v1 lookup (fun _ => false) vals :=
  ⟨fun _ => none, fun v => if v = 7 then some 0 else none, [7], fun _ _ h => by simp at h,
    by simp [refs, refsFrom, readV1]⟩

/-- **The interim rule keeps v1 stable.** If no added cell has an id the cell holds as a value, its v1 references
are unchanged. The gate enforces this for every cell born in a v1 epoch, in every later epoch too. -/
theorem v1_stable_of_interim (lookup lookup' : H → Option C) (vals : List H) (typed : Nat → Bool)
    (hext : Extends lookup lookup')
    (hnew : ∀ q v, (q, v) ∈ positions 0 vals → lookup v = none → lookup' v = none) :
    refs .v1 lookup' typed vals = refs .v1 lookup typed vals := by
  apply refsFrom_congr
  intro q v hq
  unfold readV1
  cases hl : lookup v with
  | none => exact hnew q v hq hl
  | some c => exact hext v c hl

/-! ## Epochs along the fold -/

section Epochs

variable {C K P : Type} [DecidableEq C] [DecidableEq K]
variable (W : World C K P) (rulesOf : C → Rules)

/-- RULES-V2 §4: a rotation committed under a v2 scope names v2. -/
def NoDowngrade (s0 : St C K) (chain : List (Commit C K)) : Prop :=
  ∀ i (hi : i < chain.length) s, chain[i].newScope = some s →
    rulesOf (stateAt W s0 chain i).scope = .v2 → rulesOf s = .v2

/-- **v2 persists.** Once the scope governing a commit names v2, so does the scope governing every later one. -/
theorem v2_persists (s0 : St C K) (chain : List (Commit C K)) (h : NoDowngrade W rulesOf s0 chain)
    {i j : Nat} (hij : i ≤ j) (hj : j ≤ chain.length)
    (hv : rulesOf (stateAt W s0 chain i).scope = .v2) : rulesOf (stateAt W s0 chain j).scope = .v2 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => simpa using hv
  | succ d ih =>
    have hk : i + d < chain.length := by omega
    have hprev := ih (by omega)
    rw [show i + (d + 1) = (i + d) + 1 by omega, stateAt_succ W s0 chain hk]
    simp only [step]
    cases hs : chain[i + d].newScope with
    | none => simpa using hprev
    | some s => simpa using h (i + d) hk s hs hprev

/-- **A cell's epoch is fixed at birth.** The rules governing commit `b` do not depend on any later commit. -/
theorem epoch_append (s0 : St C K) (chain future : List (Commit C K)) {b : Nat} (hb : b ≤ chain.length) :
    rulesOf (stateAt W s0 (chain ++ future) b).scope = rulesOf (stateAt W s0 chain b).scope := by
  rw [stateAt_append W s0 chain future hb]

end Epochs

end Vars1.Refs
