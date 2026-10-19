import Vars1.Fold

/-!
# §4.2 Pass 1 and §1.2 Rule 6

`Superseded` is the inductive (least) relation of §4.2 Pass 1 (it is
transitive through superseders that are themselves only `Superseded`).
`Active` is the Pass 1 definition, including the authorized-supersedes clause.

`Effective`, `Accepted` and `Retired` are left as **arbitrary** predicates in
the uniqueness theorem: the theorem holds for every choice of them. `IsPass1`
records the §4.2 equations those predicates satisfy in the spec; it is a
definition only, and the uniqueness theorem does not need it.

Rule 6 (§1.2, checked as §4.1 step 3b) is the hypothesis `Rule6Admitted` on
the admitted chain.
-/

set_option linter.unusedSectionVars false

namespace Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K]

section Pass1
variable (W : World C K P) (AE : C → C → Kind → Bool)

/-- §4.2 Pass 1 `Superseded`, as the least relation closed under both rules. -/
inductive Superseded (Eff Acc : C → Prop) : C → Prop where
  | direct {w v : C} : v ∈ (W.info w).supersedes → AE w v .supersedes = true →
      Eff w → Acc w → Superseded Eff Acc v
  | trans {w v : C} : v ∈ (W.info w).supersedes → AE w v .supersedes = true →
      Superseded Eff Acc w → Superseded Eff Acc v

/-- §4.2 Pass 1 `Active` (with the authorized-supersedes clause). -/
def Active (Eff Acc Ret : C → Prop) (v : C) : Prop :=
  Eff v ∧ ¬ Ret v ∧ ¬ Superseded W AE Eff Acc v ∧ Acc v ∧
    ∀ u ∈ (W.info v).supersedes, AE v u .supersedes = true

/-- Cross-scope acceptance reachability of Pass 1 (`AcceptedScopes(x) ≠ ∅`):
a pin by an `Active`, `Authorized` local acceptance cell whose payload is `x`,
propagated from a child `y` to `x` when `y` references `x` with the same origin. -/
inductive AccReach (Auth : C → Bool) (ActiveP : C → Prop) : C → Prop where
  | pin {a x : C} : (W.info a).schema = .acceptance → (W.info a).isLocal = true →
      ActiveP a → Auth a = true → (W.info a).payload = some x → AccReach Auth ActiveP x
  | down {y x : C} : AccReach Auth ActiveP y → x ∈ (W.info y).refs →
      (W.info y).origin = (W.info x).origin → AccReach Auth ActiveP x

/-- The §4.2 Pass 1 equations for `Invalidated`, `Effective`, `Retired`,
`Accepted` over the cells `Present` at the tip (`isIntrinsic` = an intrinsic
standard schema). A definition of what the spec requires; not used as a
hypothesis by `unique_active_binding`. -/
structure IsPass1 (Present isIntrinsic : C → Prop) (Auth : C → Bool)
    (Inv Eff Ret Acc : C → Prop) : Prop where
  inv_eq : ∀ v, Inv v ↔ ∃ w, Eff w ∧ Acc w ∧ v ∈ (W.info w).invalidates ∧
      AE w v .invalidates = true ∧
      ((W.info w).schema ≠ .verdict ∨ (W.info w).verdictInvalid = true)
  eff_eq : ∀ u, Eff u ↔ Present u ∧ ¬ Inv u
  ret_eq : ∀ v, Ret v ↔ ∃ w, Eff w ∧ Acc w ∧ v ∈ (W.info w).retires ∧
      AE w v .retires = true
  acc_eq : ∀ x, Acc x ↔ isIntrinsic x ∨ (W.info x).isLocal = true ∨
      AccReach W Auth (Active W AE Eff Acc Ret) x

/-- Path along latched `supersedes` edges: `SupPath AE x p` when `p` is reached
from `x` by zero or more latched `supersedes` hops. -/
inductive SupPath : C → C → Prop where
  | refl (x : C) : SupPath x x
  | tail {x y z : C} : SupPath x y → z ∈ (W.info y).supersedes →
      AE y z .supersedes = true → SupPath x z

/-- Rule 6 reachability: the first hop is any element of `supersedes(c)`, every
later hop is a latched `supersedes` edge. -/
def BindReach (c p : C) : Prop :=
  ∃ x ∈ (W.info c).supersedes, SupPath W AE x p

/-- Superseded propagates along a latched supersedes path. -/
theorem superseded_of_path (Eff Acc : C → Prop) {x p : C}
    (hx : Superseded W AE Eff Acc x) (hp : SupPath W AE x p) :
    Superseded W AE Eff Acc p := by
  induction hp with
  | refl => exact hx
  | tail _ hz hae ih => exact Superseded.trans hz hae ih

/-- If `c` is `Active` and reaches `p` (Rule 6 shape), then `p` is `Superseded`. -/
theorem superseded_of_active_reach (Eff Acc Ret : C → Prop) {c p : C}
    (hc : Active W AE Eff Acc Ret c) (hr : BindReach W AE c p) :
    Superseded W AE Eff Acc p := by
  obtain ⟨x, hx, hp⟩ := hr
  obtain ⟨heff, _, _, hacc, hall⟩ := hc
  exact superseded_of_path W AE Eff Acc (Superseded.direct hx (hall x hx) heff hacc) hp

end Pass1

theorem SupPath.mono (W : World C K P) {AE AE' : C → C → Kind → Bool}
    (h : ∀ w v k, AE w v k = true → AE' w v k = true) {x p : C}
    (hp : SupPath W AE x p) : SupPath W AE' x p := by
  induction hp with
  | refl => exact SupPath.refl _
  | tail _ hz hae ih => exact SupPath.tail ih hz (h _ _ _ hae)

theorem BindReach.mono (W : World C K P) {AE AE' : C → C → Kind → Bool}
    (h : ∀ w v k, AE w v k = true → AE' w v k = true) {c p : C}
    (hr : BindReach W AE c p) : BindReach W AE' c p := by
  obtain ⟨x, hx, hp⟩ := hr
  exact ⟨x, hx, SupPath.mono W h hp⟩

/-! ## Rule 6 on the admitted chain -/

/-- A local, non-scope binding. -/
def Binding (W : World C K P) (c : C) : Prop :=
  (W.info c).isLocal = true ∧ (W.info c).schema ≠ .scope

/-- **Hypothesis: §1.2 Rule 6 / §4.1 step 3b holds at every admitted commit.**
For each commit `T_i`, each new local non-scope cell `c`, and each other local
cell `p` present by the end of `T_i` with the same slot name: `c` reaches `p`
using the edges latched by the end of `T_i`, or `p` is new in the same commit
and reaches `c`. -/
def Rule6Admitted (W : World C K P) (s0 : St C K) (chain : List (Commit C K)) : Prop :=
  ∀ (i : Nat) (hi : i < chain.length), ∀ c ∈ chain[i].newCells, Binding W c →
    ∀ p ∈ (stateAt W s0 chain (i + 1)).present, (W.info p).isLocal = true → p ≠ c →
      (W.info p).slotName = (W.info c).slotName →
      BindReach W (stateAt W s0 chain (i + 1)).edge c p ∨
        (p ∈ chain[i].newCells ∧ BindReach W (stateAt W s0 chain (i + 1)).edge p c)

theorem mem_present_of_born (W : World C K P) (s0 : St C K) (chain : List (Commit C K))
    {j : Nat} (hj : j < chain.length) {p : C} (hp : p ∈ chain[j].newCells)
    {m : Nat} (hm : j + 1 ≤ m) : p ∈ (stateAt W s0 chain m).present := by
  have h1 : p ∈ (stateAt W s0 chain (j + 1)).present := by
    rw [stateAt_succ W s0 chain hj]
    simp [step, hp]
  exact ((stateAt_mono W s0 chain hm).2.2 p h1).1

/-- **Theorem 2 (unique Active binding).** On a chain that
satisfied Rule 6 at every commit, two distinct local non-scope cells born in the
chain with the same slot name are never both `Active` at the tip — for every
choice of `Effective`, `Accepted`, `Retired`. -/
theorem unique_active_binding (W : World C K P) (s0 : St C K) (chain : List (Commit C K))
    (h6 : Rule6Admitted W s0 chain) (Eff Acc Ret : C → Prop)
    {c p : C} {i j : Nat} (hi : i < chain.length) (hj : j < chain.length)
    (hc : c ∈ chain[i].newCells) (hp : p ∈ chain[j].newCells)
    (hbc : Binding W c) (hbp : Binding W p) (hne : p ≠ c)
    (hname : (W.info p).slotName = (W.info c).slotName) :
    let AE := (stateAt W s0 chain chain.length).edge
    ¬ (Active W AE Eff Acc Ret c ∧ Active W AE Eff Acc Ret p) := by
  intro AE ⟨hac, hap⟩
  -- Lift a reach made by the end of `T_k` to the tip.
  have lift : ∀ k, k < chain.length → ∀ x y,
      BindReach W (stateAt W s0 chain (k + 1)).edge x y → BindReach W AE x y :=
    fun k hk x y hr => BindReach.mono W (stateAt_mono W s0 chain (Nat.succ_le_of_lt hk)).1 hr
  -- From a reach, the reached cell is Superseded, contradicting its Active.
  have kill : ∀ x y, Active W AE Eff Acc Ret x → Active W AE Eff Acc Ret y →
      BindReach W AE x y → False :=
    fun x y hx hy hr => hy.2.2.1 (superseded_of_active_reach W AE Eff Acc Ret hx hr)
  rcases Nat.le_total j i with hji | hij
  · -- `p` is present by the end of `T_i`; apply Rule 6 to `c` at `T_i`.
    have hpres := mem_present_of_born W s0 chain hj hp (Nat.succ_le_succ hji)
    rcases h6 i hi c hc hbc p hpres hbp.1 hne hname with hr | ⟨_, hr⟩
    · exact kill c p hac hap (lift i hi c p hr)
    · exact kill p c hap hac (lift i hi p c hr)
  · have hpres := mem_present_of_born W s0 chain hi hc (Nat.succ_le_succ hij)
    rcases h6 j hj p hp hbp c hpres hbc.1 (Ne.symm hne) hname.symm with hr | ⟨_, hr⟩
    · exact kill p c hap hac (lift j hj p c hr)
    · exact kill c p hac hap (lift j hj c p hr)

end Vars1
