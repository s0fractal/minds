import Vars1.Fold2

/-!
# One history: what two tips of a chain say of each other, and what two witnesses cannot deny

§4.4: a witness vouches for one history. Two projections whose inputs are not one history, sealed by one key, are a
proof against that key. The proof must never fall on an honest key, and a quorum must say how many keys it reaches.

* `born_prefix`, `present_prefix` — **an honest pair reads as one history.** The cells of a chain at a tip are exactly
  the cells of any later tip of it born before that tip's commit count, each with the same birth. So what
  `compare_histories` reads is true of every two tips of one chain, whatever the rules read (the fold does not look at
  them for this): no honest witness of one chain is called a forker by its cells. The seals of the kernel input are not
  in this model's state (a commit's seals are those of its tree), so their half is tested, not proved.
* `quorum_overlap` — **accountable.** Two lists of distinct keys of one policy of `n` keys hold at least
  `|A| + |B| - n` keys in common: two conflicting tips witnessed by `q`-of-`n` each name at least `2q - n` keys that
  signed both, and for `q ≤ n / 2` there may be none, which is what a reader pinning fewer keys gets.
-/

set_option linter.unusedSectionVars false

namespace Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K]

section Birth

variable (W : World2 C K P)

theorem settle2_keeps (cm : Commit C K) (now : Nat) (st : St2 C K) :
    (settle2 W cm now st).present = st.present ∧ (settle2 W cm now st).born = st.born := by
  unfold settle2
  split
  · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩

theorem step2_present (st : St2 C K) (cm : Commit C K) : (step2 W st cm).present = st.present ++ cm.newCells :=
  (settle2_keeps W cm st.tick (latch2 W st cm)).1

theorem step2_born (st : St2 C K) (cm : Commit C K) (v : C) :
    (step2 W st cm).born v = if v ∈ cm.newCells ∧ v ∉ st.present then st.tick else st.born v := by
  show (settle2 W cm st.tick (latch2 W st cm)).born v = _
  rw [(settle2_keeps W cm st.tick (latch2 W st cm)).2]
  rfl

/-- A chain's state keeps its cells below its count: what is present was born before the current commit. -/
def BornBelow (st : St2 C K) : Prop := ∀ v ∈ st.present, st.born v < st.tick

theorem step2_bornBelow {st : St2 C K} (h : BornBelow st) (cm : Commit C K) : BornBelow (step2 W st cm) := by
  intro v hv
  rw [step2_present] at hv
  rw [step2_tick, step2_born]
  split
  · omega
  · rename_i hn
    rcases List.mem_append.mp hv with hp | hc
    · have := h v hp; omega
    · have : v ∈ st.present := by
        apply Classical.byContradiction
        intro hnp
        exact hn ⟨hc, hnp⟩
      have := h v this; omega

/-- What the state keeps along a chain: the invariant, the count, and that a cell's birth and presence do not change. -/
theorem run2_prefix : ∀ (ys : List (Commit C K)) (st : St2 C K), BornBelow st →
    BornBelow (run2 W st ys) ∧ st.tick ≤ (run2 W st ys).tick ∧
      (∀ v ∈ st.present, v ∈ (run2 W st ys).present ∧ (run2 W st ys).born v = st.born v) ∧
      (∀ v ∈ (run2 W st ys).present, v ∉ st.present → st.tick ≤ (run2 W st ys).born v)
  | [], st, h => ⟨h, Nat.le_refl _, fun _ hv => ⟨hv, rfl⟩, fun _ hv hn => absurd hv hn⟩
  | cm :: ys, st, h => by
    have h1 := step2_bornBelow W h cm
    obtain ⟨hb, ht, hk, hnew⟩ := run2_prefix ys (step2 W st cm) h1
    have hrun : run2 W st (cm :: ys) = run2 W (step2 W st cm) ys := rfl
    rw [hrun]
    have htick : (step2 W st cm).tick = st.tick + 1 := step2_tick W st cm
    refine ⟨hb, by omega, ?_, ?_⟩
    · intro v hv
      have hv1 : v ∈ (step2 W st cm).present := by rw [step2_present]; exact List.mem_append_left _ hv
      obtain ⟨hp, hbn⟩ := hk v hv1
      refine ⟨hp, hbn.trans ?_⟩
      rw [step2_born]
      simp [hv]
    · intro v hv hn
      by_cases hp : v ∈ (step2 W st cm).present
      · have hbn := (hk v hp).2
        rw [hbn, step2_born]
        rw [step2_present] at hp
        have hc : v ∈ cm.newCells := by
          rcases List.mem_append.mp hp with h' | h'
          · exact absurd h' hn
          · exact h'
        simp [hc, hn]
      · have := hnew v hv hp
        omega

/-- **An honest pair reads as one history: births.** A cell present at a tip keeps its birth at every later tip. -/
theorem born_prefix (st : St2 C K) (h : BornBelow st) (ys : List (Commit C K)) {v : C} (hv : v ∈ st.present) :
    v ∈ (run2 W st ys).present ∧ (run2 W st ys).born v = st.born v :=
  (run2_prefix W ys st h).2.2.1 v hv

/-- **An honest pair reads as one history: cells.** The cells of a tip are exactly the cells of a later tip of the same
chain born before its count. -/
theorem present_prefix (st : St2 C K) (h : BornBelow st) (ys : List (Commit C K)) (v : C) :
    v ∈ st.present ↔ v ∈ (run2 W st ys).present ∧ (run2 W st ys).born v < st.tick := by
  obtain ⟨-, -, hk, hnew⟩ := run2_prefix W ys st h
  constructor
  · intro hv
    obtain ⟨hp, hb⟩ := hk v hv
    exact ⟨hp, hb ▸ h v hv⟩
  · rintro ⟨hp, hb⟩
    apply Classical.byContradiction
    intro hn
    have := hnew v hp hn
    omega

end Birth

/-! ## Accountable -/

section Overlap

/-- A list of distinct elements of a list is no longer than it, when that list has distinct elements. -/
theorem nodup_length_le {A B : List K} (ha : A.Nodup) (hs : ∀ x ∈ A, x ∈ B) : A.length ≤ B.length := by
  induction A generalizing B with
  | nil => simp
  | cons a A ih =>
    have hnd := List.nodup_cons.mp ha
    have hb : a ∈ B := hs a (by simp)
    have hsub : ∀ x ∈ A, x ∈ B.erase a := by
      intro x hx
      have hne : x ≠ a := fun h => hnd.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hs x (List.mem_cons_of_mem _ hx))
    have := ih hnd.2 hsub
    rw [List.length_erase_of_mem hb] at this
    have hpos : 0 < B.length := List.length_pos_of_mem hb
    simp only [List.length_cons]
    omega

/-- **Accountable.** Two lists of distinct keys drawn from `n` keys have at least `|A| + |B| - n` keys in common. -/
theorem quorum_overlap {A B Pol : List K} (ha : A.Nodup) (hb : B.Nodup) (hA : ∀ k ∈ A, k ∈ Pol) (hB : ∀ k ∈ B, k ∈ Pol)
    (hp : Pol.Nodup) : A.length + B.length ≤ Pol.length + (A.filter (· ∈ B)).length := by
  -- the keys of `A` outside `B`, then all of `B`: distinct, and all of the policy
  have hsplit : (A.filter (· ∈ B)).length + (A.filter (· ∉ B)).length = A.length := by
    clear ha hA
    induction A with
    | nil => rfl
    | cons a A ih =>
      by_cases hm : a ∈ B
      · simp only [List.filter_cons, hm, not_true_eq_false, decide_true, decide_false, if_true, if_false,
          List.length_cons, Bool.false_eq_true]
        omega
      · simp only [List.filter_cons, hm, not_false_eq_true, decide_true, decide_false, if_true, if_false,
          List.length_cons, Bool.false_eq_true]
        omega
  have hnd : ((A.filter (· ∉ B)) ++ B).Nodup := by
    refine List.nodup_append.mpr ⟨ha.filter _, hb, ?_⟩
    intro x hx y hy hxy
    subst hxy
    have := (List.mem_filter.mp hx).2
    simp only [decide_eq_true_eq] at this
    exact this hy
  have hsub : ∀ k ∈ (A.filter (· ∉ B)) ++ B, k ∈ Pol := by
    intro k hk
    rcases List.mem_append.mp hk with h | h
    · exact hA k (List.mem_filter.mp h).1
    · exact hB k h
  have := nodup_length_le hnd hsub
  rw [List.length_append] at this
  omega

end Overlap

end Vars1
