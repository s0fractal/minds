import Vars1.Reader

/-!
# Where the Nerode bound stops: cells no coalition can bring back (`Immortal`, `Tomb`)

`Reader.lean` proves that nothing in the fold's state can be dropped: an Invalidated cell is silent now
(`dead_cell_silent`), but a continuation that gives every Effective cell invalidating it a fresh killer revives it, and
then the store that dropped it answers differently (`dropped_cell_distinguishes`). That continuation needs a new
invalidates edge to latch into the killer. `Power.lean` says who can latch one: over any extension whose seals are old
or a coalition's and which makes no rotation, a new latch into a present cell is one the coalition `CanLatch`
(`run_latch`). When it cannot, for every cell of a set whose latched attackers are all killed by the set itself, the
set stays Effective in every such extension, and what it kills stays dead: for that coalition the revival of
`dropped_cell_distinguishes` cannot happen, and the dead cell can be dropped.

* `ImmortalSet` — every cell of the set is present, and every cell with a latched invalidates edge into a member, of a
  kind that kills, is itself killed by a member (`KillsBy`: Accepted, the edge latched, a killing kind).
* `unattacked_immortal` — the base case: a present cell nothing has latched an invalidates edge into.
* `immortal_eff` — at a tip whose invalidates edges climb a rank, every member of an immortal set is Effective
  (strong induction on the rank: an attacker's killer is older than the attacker, which is older than the member).
* `tomb_dead` — so a cell a member kills is Invalidated: a **tomb**.
* `immortal_persists` — the set stays immortal at a later tip if presence, latches and acceptance only grow and no
  invalidates edge into a member latches that was not latched before.
* `no_new_latch` — and, for the v1 fold, that last premise is what `run_latch` gives over a coalition's extension
  when the coalition cannot latch an invalidates edge into the member from any source (`UnkillableBy`).
* `immortal_no_fresh_killer` — no member has a fresh killer at the later tip, so the premise `hrev` of
  `dropped_cell_distinguishes` fails for every tomb's killer.
* `tomb_never_revives`, `tomb_drop_indistinguishable` — a tomb is not Effective at any such later tip, and there a
  store that dropped it answers like the store that kept it on every other cell (`dead_cell_silent`).

What is not here: an extension with a rotation, which `Power.lean` leaves to the admission quorum (`moves_notice`) and
which can bring back keys; and the v2 fold, whose `run2_latch` gives the same premise in the same way.
-/

set_option linter.unusedSectionVars false

namespace Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K]

section Tomb

variable (W : World C K P)

/-- `y` kills `x`: Accepted, an invalidates edge to `x` latched, of a kind that kills (not a verdict, or an INVALID
one). -/
def KillsBy (AE : C → C → Kind → Bool) (Acc : C → Prop) (y x : C) : Prop :=
  Acc y ∧ x ∈ (W.info y).invalidates ∧ AE y x .invalidates = true ∧
    ((W.info y).schema ≠ .verdict ∨ (W.info y).verdictInvalid = true)

/-- **An immortal set**: its cells are present, and every cell with a latched invalidates edge of a killing kind into a
member is killed by a member. -/
def ImmortalSet (AE : C → C → Kind → Bool) (Present Acc : C → Prop) (I : C → Prop) : Prop :=
  ∀ y, I y → Present y ∧ ∀ w, y ∈ (W.info w).invalidates → AE w y .invalidates = true →
    ((W.info w).schema ≠ .verdict ∨ (W.info w).verdictInvalid = true) → ∃ y₂, I y₂ ∧ KillsBy W AE Acc y₂ w

variable {W} {AE AE' : C → C → Kind → Bool} {Present Present' isI isI' : C → Prop} {Auth Auth' : C → Bool}
  {Inv Eff Ret Acc Inv' Eff' Ret' Acc' : C → Prop}

/-- **The base case**: a present cell with no latched invalidates edge into it is an immortal set on its own. -/
theorem unattacked_immortal {AE : C → C → Kind → Bool} {Present Acc : C → Prop} {y : C} (hp : Present y)
    (hn : ∀ w, AE w y .invalidates = false) : ImmortalSet W AE Present Acc (· = y) := by
  rintro _ rfl
  exact ⟨hp, fun w _ hae _ => absurd hae (by simp [hn w])⟩

/-- **An immortal set is Effective**, at a tip whose invalidates edges climb a rank. -/
theorem immortal_eff (h : IsPass1 W AE Present isI Auth Inv Eff Ret Acc) (ht : C → Nat)
    (hht : ∀ w v, Present w → v ∈ (W.info w).invalidates → ht w < ht v) {I : C → Prop}
    (hI : ImmortalSet W AE Present Acc I) : ∀ y, I y → Eff y := by
  suffices ∀ n y, ht y < n → I y → Eff y from fun y hy => this _ y (Nat.lt_succ_self _) hy
  intro n
  induction n with
  | zero => intro y hy; exact absurd hy (Nat.not_lt_zero _)
  | succ n ih =>
    intro y hlt hy
    obtain ⟨hp, hg⟩ := hI y hy
    refine (h.eff_eq y).mpr ⟨hp, fun hi => ?_⟩
    obtain ⟨w, hw, -, hm, hae, hk⟩ := (h.inv_eq y).mp hi
    obtain ⟨y₂, hy₂, ha₂, hm₂, hae₂, hk₂⟩ := hg w hm hae hk
    have hpw := ((h.eff_eq w).mp hw).1
    have h1 := hht y₂ w (hI y₂ hy₂).1 hm₂
    have h2 := hht w y hpw hm
    have he₂ : Eff y₂ := ih y₂ (by omega) hy₂
    exact ((h.eff_eq w).mp hw).2 ((h.inv_eq w).mpr ⟨y₂, he₂, ha₂, hm₂, hae₂, hk₂⟩)

/-- **A tomb**: a cell a member of an immortal set kills is Invalidated. -/
theorem tomb_dead (h : IsPass1 W AE Present isI Auth Inv Eff Ret Acc) (ht : C → Nat)
    (hht : ∀ w v, Present w → v ∈ (W.info w).invalidates → ht w < ht v) {I : C → Prop}
    (hI : ImmortalSet W AE Present Acc I) {y x : C} (hy : I y) (hk : KillsBy W AE Acc y x) : Inv x ∧ ¬ Eff x :=
  killed W h (immortal_eff h ht hht hI y hy) hk.1 hk.2.1 hk.2.2.1 hk.2.2.2

/-- **An immortal set stays immortal** at a later tip, if presence, latches and acceptance only grow and no invalidates
edge into a member latches that was not latched before. -/
theorem immortal_persists {I : C → Prop} (hI : ImmortalSet W AE Present Acc I)
    (hpres : ∀ c, Present c → Present' c) (hae : ∀ w v, AE w v .invalidates = true → AE' w v .invalidates = true)
    (hacc : ∀ c, Acc c → Acc' c) (hnew : ∀ y w, I y → AE' w y .invalidates = true → AE w y .invalidates = true) :
    ImmortalSet W AE' Present' Acc' I := by
  intro y hy
  obtain ⟨hp, hg⟩ := hI y hy
  refine ⟨hpres y hp, fun w hm hae' hk => ?_⟩
  obtain ⟨y₂, hy₂, ha₂, hm₂, hae₂, hk₂⟩ := hg w hm (hnew y w hy hae') hk
  exact ⟨y₂, hy₂, hacc y₂ ha₂, hm₂, hae y₂ w hae₂, hk₂⟩

/-- **No member has a fresh killer**: a cell whose latched invalidates edge enters a member is killed by a member,
so a present cell names it. The premise `hrev` of `dropped_cell_distinguishes` cannot hold for a tomb's killer. -/
theorem immortal_no_fresh_killer {I : C → Prop} (hI : ImmortalSet W AE Present Acc I) {y z : C} (hy : I y) :
    ¬ FreshKiller W AE Present Acc y z := by
  rintro ⟨-, -, hm, hae, hk, hfresh⟩
  obtain ⟨y₂, hy₂, -, hm₂, -, -⟩ := (hI y hy).2 z hm hae hk
  exact hfresh y₂ (hI y₂ hy₂).1 hm₂

/-- **A tomb never revives**: at every later tip where the set stays immortal (`immortal_persists`), the cell a member
kills now is Invalidated. -/
theorem tomb_never_revives (h' : IsPass1 W AE' Present' isI' Auth' Inv' Eff' Ret' Acc') (ht : C → Nat)
    (hht : ∀ w v, Present' w → v ∈ (W.info w).invalidates → ht w < ht v) {I : C → Prop}
    (hI : ImmortalSet W AE Present Acc I)
    (hpres : ∀ c, Present c → Present' c) (hae : ∀ w v, AE w v .invalidates = true → AE' w v .invalidates = true)
    (hacc : ∀ c, Acc c → Acc' c) (hnew : ∀ y w, I y → AE' w y .invalidates = true → AE w y .invalidates = true)
    {y x : C} (hy : I y) (hk : KillsBy W AE Acc y x) : Inv' x ∧ ¬ Eff' x :=
  tomb_dead h' ht hht (immortal_persists hI hpres hae hacc hnew) hy
    ⟨hacc y hk.1, hk.2.1, hae y x hk.2.2.1, hk.2.2.2⟩

/-- **Dropping a tomb is indistinguishable later.** At such a later tip, a store that dropped the tomb `x` (with the
same latches and acceptance) gives every other cell the Effective it has in the store that kept it. -/
theorem tomb_drop_indistinguishable (h' : IsPass1 W AE' Present' isI' Auth' Inv' Eff' Ret' Acc')
    {Present'' isI'' : C → Prop} {Auth'' : C → Bool} {Inv'' Eff'' Ret'' : C → Prop}
    (h'' : IsPass1 W AE' Present'' isI'' Auth'' Inv'' Eff'' Ret'' Acc') (ht : C → Nat)
    (hht : ∀ w v, Present' w → v ∈ (W.info w).invalidates → ht w < ht v) {I : C → Prop}
    (hI : ImmortalSet W AE Present Acc I)
    (hpres : ∀ c, Present c → Present' c) (hae : ∀ w v, AE w v .invalidates = true → AE' w v .invalidates = true)
    (hacc : ∀ c, Acc c → Acc' c) (hnew : ∀ y w, I y → AE' w y .invalidates = true → AE w y .invalidates = true)
    {y x : C} (hy : I y) (hk : KillsBy W AE Acc y x) (hdrop : ∀ c, Present'' c ↔ Present' c ∧ c ≠ x) :
    ∀ c, c ≠ x → (Eff' c ↔ Eff'' c) :=
  dead_cell_silent W h' h'' ht (fun w v hw hv => hht w v ((hdrop w).mp hw).1 hv)
    (tomb_never_revives h' ht hht hI hpres hae hacc hnew hy hk).2 hdrop

end Tomb

/-! ## The premise from the fold (v1) -/

section Fold

variable (W : World C K P)

/-- No source can latch an invalidates edge into `y` over a coalition's extension. -/
def UnkillableBy (old : List (Seal C K)) (Co : K → Prop) (st : St C K) (y : C) : Prop :=
  ∀ w, y ∈ (W.info w).invalidates → ¬ CanLatch W old Co st.scope w y .invalidates (st.initEnd y)

/-- **No new latch.** Over an extension whose seals are old or the coalition's and which makes no rotation, an
invalidates edge into a present cell the coalition cannot attack is latched after it only if it was latched before. -/
theorem no_new_latch {old : List (Seal C K)} {Co : K → Prop} {st : St C K} {y : C} (hy : y ∈ st.present)
    (hu : UnkillableBy W old Co st y) (ext : List (Commit C K))
    (hext : ∀ cm ∈ ext, SealsFrom old Co cm ∧ cm.newScope = none) (w : C)
    (h : (run W st ext).edge w y .invalidates = true) : st.edge w y .invalidates = true :=
  (run_latch ext st hext hy h).elim id (fun ⟨hm, hc⟩ => absurd hc (hu w hm))

/-- Latches and presence only grow along the fold. -/
theorem run_keeps : ∀ (ext : List (Commit C K)) (st : St C K),
    (∀ c, c ∈ st.present → c ∈ (run W st ext).present) ∧
      (∀ w v k, st.edge w v k = true → (run W st ext).edge w v k = true)
  | [], _ => ⟨fun _ h => h, fun _ _ _ h => h⟩
  | cm :: ext, st => by
    obtain ⟨hp, he⟩ := run_keeps ext (step W st cm)
    refine ⟨fun c hc => hp c (by simp [step, hc]), fun w v k h => he w v k ?_⟩
    exact (step_edge_iff W st cm w v k).mpr (Or.inl h)

end Fold

end Vars1
