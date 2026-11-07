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

/-! ## Pass 1 has one kernel on a ranked store

`Invalidated` and `Effective` are fixed by two of the Pass 1 equations (`IsPass1.inv_eq`, `eff_eq`): `Effective` is
a kernel, in Richardson's sense, of the digraph of authorized invalidates edges from Accepted killers. Cells are
named by the hash of their contents, so a cell invalidates only cells that name no one naming it: there is a rank
`ht` that every invalidates edge from a present cell climbs. On such a store the equations have at most one solution
for a given `Accepted`, by induction on the rank: a cell's status is fixed by the status of the cells that attack it.
The witness prover computes one (`effB`, `effB_iff` in `Vars1/WitnessComplete.lean`), so there is exactly one; a
liar's paradox ("this notice invalidates itself") cannot be written. -/

/-- **The Pass 1 kernel is unique.** Two solutions of the `Invalidated`/`Effective` equations over the same
`Accepted`, on a store whose invalidates edges climb a rank, agree on every cell. -/
theorem pass1_kernel_unique (W : World C K P) (AE : C → C → Kind → Bool) (Present Acc : C → Prop)
    (ht : C → Nat) (hht : ∀ w v, Present w → v ∈ (W.info w).invalidates → ht w < ht v)
    {Inv Eff Inv' Eff' : C → Prop}
    (hinv : ∀ v, Inv v ↔ ∃ w, Eff w ∧ Acc w ∧ v ∈ (W.info w).invalidates ∧ AE w v .invalidates = true ∧
      ((W.info w).schema ≠ .verdict ∨ (W.info w).verdictInvalid = true))
    (heff : ∀ u, Eff u ↔ Present u ∧ ¬ Inv u)
    (hinv' : ∀ v, Inv' v ↔ ∃ w, Eff' w ∧ Acc w ∧ v ∈ (W.info w).invalidates ∧ AE w v .invalidates = true ∧
      ((W.info w).schema ≠ .verdict ∨ (W.info w).verdictInvalid = true))
    (heff' : ∀ u, Eff' u ↔ Present u ∧ ¬ Inv' u) :
    ∀ v, (Inv v ↔ Inv' v) ∧ (Eff v ↔ Eff' v) := by
  have key : ∀ m v, ht v < m → (Inv v ↔ Inv' v) := by
    intro m
    induction m with
    | zero => intro v h; exact absurd h (Nat.not_lt_zero _)
    | succ m ih =>
      intro v hv
      have heq : ∀ w, Present w → v ∈ (W.info w).invalidates → (Eff w ↔ Eff' w) := by
        intro w hp hw
        have hlt : ht w < m := by have := hht w v hp hw; omega
        rw [heff, heff', ih w hlt]
      constructor
      · intro h
        obtain ⟨w, hw, ha, hvw, hae, hk⟩ := (hinv v).mp h
        exact (hinv' v).mpr ⟨w, (heq w ((heff w).mp hw).1 hvw).mp hw, ha, hvw, hae, hk⟩
      · intro h
        obtain ⟨w, hw, ha, hvw, hae, hk⟩ := (hinv' v).mp h
        exact (hinv v).mpr ⟨w, (heq w ((heff' w).mp hw).1 hvw).mpr hw, ha, hvw, hae, hk⟩
  intro v
  have hi := key (ht v + 1) v (Nat.lt_succ_self _)
  exact ⟨hi, by rw [heff, heff', hi]⟩

/-- `pass1_kernel_unique` for two readings that meet all of §4.2 Pass 1 (`IsPass1`) with the same `Accepted`. -/
theorem IsPass1.kernel_unique {W : World C K P} {AE : C → C → Kind → Bool} {Present isIntrinsic : C → Prop}
    {Auth : C → Bool} {Inv Eff Ret Inv' Eff' Ret' Acc : C → Prop}
    (h1 : IsPass1 W AE Present isIntrinsic Auth Inv Eff Ret Acc)
    (h2 : IsPass1 W AE Present isIntrinsic Auth Inv' Eff' Ret' Acc)
    (ht : C → Nat) (hht : ∀ w v, Present w → v ∈ (W.info w).invalidates → ht w < ht v) :
    ∀ v, (Inv v ↔ Inv' v) ∧ (Eff v ↔ Eff' v) :=
  pass1_kernel_unique W AE Present Acc ht hht h1.inv_eq h1.eff_eq h2.inv_eq h2.eff_eq

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
