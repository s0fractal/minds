import Vars1.Grounded

/-!
# A certificate that a cell is not Grounded (`UnfoundedSet`)

`Grounded` is the least fixed point of `GΦ` (`Grounded.lean`). To show a cell Grounded, a derivation builds a finite
support from below. To show it is not, pointing at one dead cell is not enough: in `circular_support` every cell
stands and `d0` is Settled, yet nothing is Grounded, because the only support runs in a circle. What shows `¬ Grounded`
in general is the dual of Knaster–Tarski: a set `U` holding the cell, none of whose members `GΦ` admits when every
cell outside `U` is given. Then the complement of `U` is closed under `GΦ`, so it holds the least fixed point, and
nothing in `U` is Grounded.

* `unfounded_sound` — a cell of an unfounded set is not Grounded.
* `unfounded_complete` — every cell that is not Grounded lies in one: the cells that are not Grounded. No
  `Classical.choice`: the operator's quantifiers run over finite lists (what a cell relies on, a quorum's keys, its
  witnesses), and over a finite list double negation passes through `∀` (`dn_forall_mem`), so `GΦ` of the cells that are
  not not Grounded is not not `GΦ` of the Grounded ones.
* `not_grounded_iff_unfounded` — the two together.
* `unfounded_of_each` — a finite certificate is checked cell by cell: for each member, `GΦ` fails when only the cells
  outside the list are given (it is not live, it relies on a member, or the keys counting through witnesses outside the
  list miss its quorum). This is what a checker reads.
* `circular_certificate` — on `circular_support`'s world, `[d0, w]` is such a certificate, though both stand and `d0` is
  Settled.
-/

set_option linter.unusedSectionVars false

namespace Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K]

/-- Over a finite list, double negation passes through `∀`. -/
theorem dn_forall_mem {α : Type} {Q : α → Prop} : ∀ (l : List α), (∀ x ∈ l, ¬¬ Q x) → ¬¬ ∀ x ∈ l, Q x
  | [], _ => fun hn => hn (fun _ h => absurd h (List.not_mem_nil))
  | a :: t, h => fun hn =>
      h a List.mem_cons_self (fun ha =>
        dn_forall_mem t (fun x hx => h x (List.mem_cons_of_mem _ hx)) (fun ht =>
          hn (fun x hx => (List.mem_cons.mp hx).elim (fun e => e ▸ ha) (ht x))))

section Unfounded

variable (W : World C K P) (X : Pass3In C K P) (wmax : C → List C) (cnt : C → C → List K)

/-- **An unfounded set**: no member satisfies Grounded's equation when only the cells outside the set are given. -/
def IsUnfounded (U : C → Prop) : Prop := Sub (GΦ W X wmax cnt (fun c => ¬ U c)) (fun c => ¬ U c)

/-- **A cell of an unfounded set is not Grounded.** -/
theorem unfounded_sound {U : C → Prop} (hU : IsUnfounded W X wmax cnt U) {d : C} (hd : U d) :
    ¬ Grounded W X wmax cnt d :=
  fun hg => grounded_least W X wmax cnt _ hU d hg hd

/-- Grounded's equation over the cells that are not not Grounded gives a cell that is not not Grounded. -/
theorem grounded_dn {v : C} (h : GΦ W X wmax cnt (fun c => ¬¬ Grounded W X wmax cnt c) v) :
    ¬¬ Grounded W X wmax cnt v := by
  obtain ⟨hl, hr, hk⟩ := h
  intro hn
  rw [← grounded_fixed] at hn
  refine dn_forall_mem _ hr (fun hrG => ?_)
  cases hs : (W.info v).schema <;> simp only [hs] at hk
  case metaSchema => exact hn ⟨hl, hrG, by simp only [hs]; exact hk⟩
  case scope => exact hn ⟨hl, hrG, by simp only [hs]; exact hk⟩
  all_goals first
    | (obtain ⟨E, hq, hE⟩ := hk
       refine dn_forall_mem E (Q := fun k => ∃ u ∈ wmax v, Grounded W X wmax cnt u ∧ k ∈ cnt v u)
         (fun k hk' => ?_) (fun hE' => hn ⟨hl, hrG, by simp only [hs]; exact ⟨E, hq, hE'⟩⟩)
       obtain ⟨u, hu, hg, hc⟩ := hE k hk'
       exact fun hn' => hg (fun g => hn' ⟨u, hu, g, hc⟩))
    | exact hn ⟨hl, hrG, by simp only [hs]⟩

/-- **Every cell that is not Grounded lies in an unfounded set**: the cells that are not Grounded form one. -/
theorem unfounded_complete {d : C} (hd : ¬ Grounded W X wmax cnt d) :
    ∃ U : C → Prop, IsUnfounded W X wmax cnt U ∧ U d :=
  ⟨fun c => ¬ Grounded W X wmax cnt c, fun _ hv => grounded_dn W X wmax cnt hv, hd⟩

/-- **The duality.** -/
theorem not_grounded_iff_unfounded {d : C} :
    ¬ Grounded W X wmax cnt d ↔ ∃ U : C → Prop, IsUnfounded W X wmax cnt U ∧ U d :=
  ⟨unfounded_complete W X wmax cnt, fun ⟨_, hU, hd⟩ => unfounded_sound W X wmax cnt hU hd⟩

/-- **A finite certificate, checked cell by cell.** -/
theorem unfounded_of_each {U : List C} (h : ∀ v ∈ U, ¬ GΦ W X wmax cnt (fun c => c ∉ U) v) :
    IsUnfounded W X wmax cnt (· ∈ U) :=
  fun v hv hmem => h v hmem hv

end Unfounded

/-! ## The circle -/

section Circle

/-- `circular_support`'s presentation: the verdict `w` is `d0`'s only witness and counts its one key. -/
def circWmax : Ex → List Ex := fun v => if v = .d0 then [.w] else []
def circCnt : Ex → Ex → List Unit := fun _ x => if x = .w then [()] else []

/-- **The circle's certificate.** On `circular_support`'s world both `d0` and `w` stand, and `d0` is Settled, so no
dead cell explains why neither is Grounded; `[d0, w]` is an unfounded set: `d0`'s only witness is in it, and `w`
relies on `d0`. -/
theorem circular_certificate :
    Live (exPass3 circularInfo) .d0 ∧ Live (exPass3 circularInfo) .w ∧
    Settled (exWorld circularInfo) (exPass3 circularInfo) circWmax circCnt .d0 ∧
    IsUnfounded (exWorld circularInfo) (exPass3 circularInfo) circWmax circCnt (· ∈ [Ex.d0, Ex.w]) ∧
    ¬ Grounded (exWorld circularInfo) (exPass3 circularInfo) circWmax circCnt .d0 ∧
    ¬ Grounded (exWorld circularInfo) (exPass3 circularInfo) circWmax circCnt .w := by
  have hU : IsUnfounded (exWorld circularInfo) (exPass3 circularInfo) circWmax circCnt (· ∈ [Ex.d0, Ex.w]) := by
    refine unfounded_of_each _ _ _ _ (fun v hv => ?_)
    rintro ⟨-, hr, hk⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · simp only [exWorld, circularInfo, exCell] at hk
      obtain ⟨E, hE, hmem⟩ := hk
      simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq] at hE
      cases E with
      | nil => exact hE rfl
      | cons k _ =>
        obtain ⟨c, hc, hg, -⟩ := hmem k (by simp)
        simp only [circWmax, if_true, List.mem_singleton] at hc
        subst hc
        simp at hg
    · exact hr .d0 (by simp [exWorld, circularInfo, exCell]) (by simp)
  refine ⟨live_ex _ _, live_ex _ _, ⟨live_ex _ _, ?_⟩, hU, unfounded_sound _ _ _ _ hU (by simp),
    unfounded_sound _ _ _ _ hU (by simp)⟩
  simp [exWorld, circularInfo, exCell, circWmax, circCnt]

end Circle

end Vars1
