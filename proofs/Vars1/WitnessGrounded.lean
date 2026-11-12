import Vars1.Grounded
import Vars1.WitnessComplete

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

/-! ## The positive rule: `ground` in the witness checker

`Witness.lean` has a rule `ground d` (`groundOK`) and proves it sound (`witness_ground_sound`): `acceptsGround`
implies `Grounded`. Here is the converse on a fragment. The prover runs Grounded's equation in rounds from below, as
`grounded_iter` does on `Fin N`, over candidate cells and with the checker's own reading of each (`groundStep`):
round `R + 1` holds the candidates whose relies are in round `R` and, if they are contracts or decisions, whose quorum
is met by the endorsements `pairs` names through verdicts in round `R`. Each round's new cells get a `ground` line
after their `stand`, `down` and `endorse` lines (`roundLines`). The rounds are lists, not a recursion on cells: a
verdict may rely on the decision it judges, and a recursion would unfold such a circle round by round.

The candidates (`groundCands`) are the cells reached from the decision down `relies` and to the cells whose payload a
reached cell is (`suppClose`, or every cell when its steps run out), that stand by `standsB`; what `pairs` names for
each is tabled once (`groundCheck`). Neither changes with the round.

* `groundSet_mono`, `stable_all`, `groundSet_bound` — rounds only add cells; once a round adds none, none ever does;
  and round `N`, for `N` the candidates, holds every cell any round holds.
* `round_run` — the rounds' lines run, and conclude each cell of the round grounded and standing.
* `grounded_round` — a Grounded cell is in some round, when every live cell its Grounded reads (`Support`: down
  `relies` and to the verdicts of `W_max`) is a candidate, in the settle checker's fragment, and not a scope, a schema
  or a question (`GFragment`); `candidates_cover` — `groundCands` holds them.
* `ground_complete`, `groundCheck_iff` — the checker accepts `proveGround` for every round count at or after the
  candidates' number, or after a round that adds nothing; what `vars1witness --ground` runs (`groundCheck`) answers
  true exactly when the cell is Grounded.
-/

namespace Witness

open Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K] [DecidableEq P]
variable (S : Store C K P) {U : List C} {pr : C → List (C × K)}

/-- The endorsements of `c` that `pr` names through verdicts in `G` (`pr` is `pairs`, tabled once). -/
def gpairs (pr : C → List (C × K)) (G : List C) (c : C) : List (C × K) := (pr c).filter fun p => decide (p.1 ∈ G)

/-- Grounded's equation as the prover decides it for a candidate, given the cells `G` found Grounded so far. -/
def groundStep (pr : C → List (C × K)) (G : List C) (c : C) : Bool :=
  (S.relies c).all (fun r => decide (r ∈ G)) &&
    match S.schema c with
    | .scope | .metaSchema | .question => false
    | .contract | .decision => decide (S.req c = none) && decide (evalPol S c ∈ S.pols) &&
        decide (S.thr (evalPol S c) ≤ (dedup ((gpairs pr G c).map Prod.snd)).length)
    | _ => true

/-- The candidates found Grounded after `R` rounds from below. -/
def groundSet (pr : C → List (C × K)) (U : List C) : Nat → List C
  | 0 => []
  | R + 1 => let G := groundSet pr U R; U.filter (groundStep S pr G)

def groundPrem (n : Nat) (pr : C → List (C × K)) (G : List C) (c : C) : List (Concl C K) :=
  .stands c :: ((S.relies c).map .grounded ++ (gpairs pr G c).map (fun p => .grounded p.1) ++
    (gpairs pr G c).map (fun p => .stands p.1) ++ (gpairs pr G c).map (fun p => .endorsed p.1 p.2) ++
    (downs S n c).map .down)

/-- The lines that ground `c`, once the cells of `G` are grounded and stand. -/
def groundCellLines (n : Nat) (pr : C → List (C × K)) (G : List C) (c : C) : List (Line C K) :=
  standLines S n n c ++ (downs S n c).flatMap (downLines S n n) ++
    (gpairs pr G c).flatMap (fun p => [endorseLine p]) ++ [⟨.ground, .grounded c, groundPrem S n pr G c⟩]

/-- The rounds' lines: each round grounds the cells it adds. -/
def roundLines (n : Nat) (pr : C → List (C × K)) (U : List C) : Nat → List (Line C K)
  | 0 => []
  | R + 1 =>
    let G := groundSet S pr U R
    roundLines n pr U R ++ ((groundSet S pr U (R + 1)).filter fun c => decide (c ∉ G)).flatMap
      (groundCellLines S n pr G)

/-- **The prover for Grounded.** The edge lines, then `R` rounds over the candidates `U`. -/
def proveGround (n : Nat) (pr : C → List (C × K)) (U : List C) (R : Nat) : List (Line C K) :=
  edgeLines S ++ roundLines S n pr U R

/-- Round `R + 1` adds no cell. -/
def stableB (pr : C → List (C × K)) (U : List C) (R : Nat) : Bool :=
  let G := groundSet S pr U R
  (groundSet S pr U (R + 1)).all fun c => decide (c ∈ G)

/-- What the rounds ask of their candidates: cells of the store that stand by `standsB`, for which `pr` names
`pairs`. -/
def Cands (n : Nat) (pr : C → List (C × K)) (U : List C) : Prop :=
  ∀ c ∈ U, c ∈ S.cells ∧ standsB S n n c = true ∧ pr c = pairs S n c

/-! ### Rounds only add cells, and stop -/

theorem mem_gpairs {G : List C} {c : C} {p : C × K} : p ∈ gpairs pr G c ↔ p ∈ pr c ∧ p.1 ∈ G := by
  simp [gpairs, List.mem_filter]

theorem mem_groundSet {R : Nat} {c : C} :
    c ∈ groundSet S pr U (R + 1) ↔ c ∈ U ∧ groundStep S pr (groundSet S pr U R) c = true := by
  simp [groundSet, List.mem_filter]

theorem groundSet_sub : ∀ {R : Nat} {c : C}, c ∈ groundSet S pr U R → c ∈ U
  | 0, _, h => by simp [groundSet] at h
  | _ + 1, _, h => ((mem_groundSet S).mp h).1

theorem groundStep_mono {G G' : List C} (hG : ∀ c ∈ G, c ∈ G') {c : C}
    (h : groundStep S pr G c = true) : groundStep S pr G' c = true := by
  unfold groundStep at h ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h ⊢
  obtain ⟨hrel, hm⟩ := h
  refine ⟨fun r hr => hG r (hrel r hr), ?_⟩
  cases hs : S.schema c <;> simp only [hs] at hm ⊢
  case contract | decision =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm ⊢
    refine ⟨hm.1, Nat.le_trans hm.2 (nodup_length_le (nodup_dedup _) fun k hk => ?_)⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (mem_dedup.mp hk)
    obtain ⟨hp, hq1⟩ := (mem_gpairs (pr := pr)).mp hq
    exact mem_dedup.mpr (List.mem_map.mpr ⟨q, (mem_gpairs (pr := pr)).mpr ⟨hp, hG _ hq1⟩, rfl⟩)
  all_goals exact hm

theorem groundSet_mono : ∀ {R : Nat} {c : C}, c ∈ groundSet S pr U R → c ∈ groundSet S pr U (R + 1)
  | 0, _, h => by simp [groundSet] at h
  | R + 1, c, h => by
    obtain ⟨hc, hstep⟩ := (mem_groundSet S).mp h
    exact (mem_groundSet S).mpr ⟨hc, groundStep_mono S (fun _ hx => groundSet_mono hx) hstep⟩

theorem groundSet_add {R : Nat} {c : C} (h : c ∈ groundSet S pr U R) : ∀ k, c ∈ groundSet S pr U (R + k)
  | 0 => h
  | k + 1 => groundSet_mono S (groundSet_add h k)

theorem groundSet_mono_le {R R' : Nat} (hle : R ≤ R') {c : C} (h : c ∈ groundSet S pr U R) :
    c ∈ groundSet S pr U R' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact groundSet_add S h k

/-- Once a round adds no cell, no later round does. -/
theorem stable_all {r : Nat} (hs : stableB S pr U r = true) :
    ∀ (R : Nat) {c : C}, c ∈ groundSet S pr U R → c ∈ groundSet S pr U r := by
  simp only [stableB, List.all_eq_true, decide_eq_true_eq] at hs
  have up : ∀ k {c : C}, c ∈ groundSet S pr U (r + k) → c ∈ groundSet S pr U r := by
    intro k
    induction k with
    | zero => exact fun h => h
    | succ k ih =>
      intro c h
      obtain ⟨hc, hstep⟩ := (mem_groundSet S).mp (show c ∈ groundSet S pr U (r + k + 1) from h)
      exact hs c ((mem_groundSet S).mpr ⟨hc, groundStep_mono S (fun _ hx => ih hx) hstep⟩)
  intro R c h
  rcases Nat.le_total R r with hle | hle
  · exact groundSet_mono_le S hle h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact up k h

/-- The length of a filter over a cons. -/
theorem filter_cons_len {α : Type} (p : α → Bool) (a : α) (t : List α) :
    ((a :: t).filter p).length = (t.filter p).length + (if p a = true then 1 else 0) := by
  cases h : p a <;> simp [h]

theorem filter_true_length {α : Type} : ∀ (l : List α), (l.filter fun _ => true).length = l.length
  | [] => rfl
  | a :: t => by simp only [List.filter_cons, if_true, List.length_cons, filter_true_length t]

/-- Filtering by a weaker test keeps fewer, unless the two agree on the list. -/
theorem filter_lt_or_eq {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) →
      (l.filter p).length < (l.filter q).length ∨ ∀ x ∈ l, q x = true → p x = true
  | [], _ => Or.inr (fun _ h => absurd h List.not_mem_nil)
  | a :: t, h => by
    have ht : ∀ x ∈ t, p x = true → q x = true := fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [filter_cons_len p a t, filter_cons_len q a t]
    have hpq := h a List.mem_cons_self
    rcases filter_lt_or_eq p q t ht with hlt | heq
    · left
      cases hp : p a <;> cases hq : q a
      · simp only [Bool.false_eq_true, if_false]; omega
      · simp only [Bool.false_eq_true, if_false, if_true]; omega
      · exact absurd (hpq hp) (by simp [hq])
      · simp only [if_true]; omega
    · have hlen : (t.filter p).length = (t.filter q).length := by
        rw [List.filter_congr (p := p) (q := q) (fun x hx => by
          cases hp : p x <;> cases hq : q x
          · rfl
          · exact absurd (heq x hx hq) (by simp [hp])
          · exact absurd (ht x hx hp) (by simp [hq])
          · rfl)]
      cases hp : p a <;> cases hq : q a
      · exact Or.inr fun x hx hqx => (List.mem_cons.mp hx).elim (fun e => by subst e; simp [hq] at hqx)
          (fun hx => heq x hx hqx)
      · left; simp only [hlen, Bool.false_eq_true, if_false, if_true]; omega
      · exact absurd (hpq hp) (by simp [hq])
      · exact Or.inr fun x hx hqx => (List.mem_cons.mp hx).elim (fun e => e ▸ hp) (fun hx => heq x hx hqx)

/-- **Round `N` holds every cell any round holds**, `N` the candidates: until a round adds nothing, each adds a
candidate. -/
theorem groundSet_bound : ∀ (R : Nat) {c : C}, c ∈ groundSet S pr U R → c ∈ groundSet S pr U U.length := by
  let f : Nat → Nat := fun R => (U.filter fun c => decide (c ∈ groundSet S pr U R)).length
  have claim : ∀ R, (∃ r, r ≤ R ∧ stableB S pr U r = true) ∨ R ≤ f R := by
    intro R
    induction R with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ R ih =>
      rcases ih with ⟨r, hr, hs⟩ | hR
      · exact Or.inl ⟨r, Nat.le_succ_of_le hr, hs⟩
      · rcases filter_lt_or_eq (fun c => decide (c ∈ groundSet S pr U R))
          (fun c => decide (c ∈ groundSet S pr U (R + 1)))
          U (fun x _ hx => by simpa using groundSet_mono S (by simpa using hx)) with hlt | heq
        · exact Or.inr (Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hR hlt))
        · refine Or.inl ⟨R, Nat.le_succ R, ?_⟩
          simp only [stableB, List.all_eq_true, decide_eq_true_eq]
          intro c hc
          simpa using heq c (groundSet_sub S hc) (by simpa using hc)
  intro R c h
  rcases claim U.length with ⟨r, hr, hs⟩ | hN
  · exact groundSet_mono_le S hr (stable_all S hs R h)
  · rcases filter_lt_or_eq (fun c => decide (c ∈ groundSet S pr U U.length)) (fun _ => true) U
      (fun _ _ _ => rfl) with hlt | hall
    · exfalso
      have h1 : (U.filter fun _ => true).length = U.length := filter_true_length U
      have h2 : f U.length = (U.filter fun c => decide (c ∈ groundSet S pr U U.length)).length := rfl
      omega
    · simpa using hall c (groundSet_sub S h) rfl

/-- The round count `vars1witness --ground` uses: the first round below the candidates' number after which no round
adds a cell, or that number. -/
def groundRounds (pr : C → List (C × K)) (U : List C) : Nat :=
  ((List.range U.length).find? (stableB S pr U)).getD U.length

theorem groundRounds_ok (pr : C → List (C × K)) (U : List C) :
    U.length ≤ groundRounds S pr U ∨ stableB S pr U (groundRounds S pr U) = true := by
  unfold groundRounds
  cases h : (List.range U.length).find? (stableB S pr U) with
  | none => exact Or.inl (Nat.le_refl _)
  | some r => exact Or.inr (List.find?_some h)

/-! ### The rounds' lines run -/

/-- The checker's `countsFor` holds of a pair the prover names, given the premises it names. -/
theorem countsFor_of_pair {n : Nat} {d w : C} {k : K} {prem : List (Concl C K)} (hwk : (w, k) ∈ pairs S n d)
    (hst : Concl.stands w ∈ prem) (hdown : ∀ b ∈ downs S n d, Concl.down b ∈ prem) :
    countsFor S d prem w k = true := by
  obtain ⟨hw', hkK', -, hnw'⟩ := mem_pairs S hwk
  have hc := (List.mem_filter.mp hw').2
  simp only [countable, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hvs, hvp⟩, hva⟩, hvt⟩, hvw⟩, -⟩ := hc
  simp only [countsFor, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨⟨⟨hst, hvs⟩, hvp⟩, hva⟩, hvt⟩, hvw⟩, hkK'⟩, fun b hb => ?_⟩
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hnw'
  cases hwd : withdraws S d w k b with
  | false => exact Or.inl rfl
  | true =>
    refine Or.inr ?_
    rcases hnw' b hb with h | h
    · rw [hwd] at h; exact Bool.noConfusion h
    · have hinv : invalidOn S d b = true := by
        simp only [withdraws, Bool.and_eq_true] at hwd
        simp only [invalidOn, Bool.and_eq_true]
        exact hwd.1.1
      exact hdown b (List.mem_filter.mpr ⟨hb, by simp [hinv, h]⟩)

/-- One candidate's lines run once the cells of `G` are grounded and stand. -/
theorem cell_run {n : Nat} {G : List C} {c : C} (hc : c ∈ S.cells) (hst : standsB S n n c = true)
    (hpr : pr c = pairs S n c) (h : groundStep S pr G c = true) (done : List (Concl C K))
    (hd : EdgeFacts S done) (hG : ∀ x ∈ G, Concl.grounded x ∈ done ∧ Concl.stands x ∈ done) :
    Reaches S done (groundCellLines S n pr G c) [.grounded c, .stands c] := by
  have h' := h
  unfold groundStep at h'
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h'
  obtain ⟨hrel, hm⟩ := h'
  have hgp : ∀ {p : C × K}, p ∈ gpairs pr G c → p ∈ pairs S n c ∧ p.1 ∈ G := fun hp => by
    have := (mem_gpairs (pr := pr)).mp hp
    rw [hpr] at this
    exact this
  have hA := stand_run S n n c hst done hd
  have hAB := reaches_append S hA fun o _ hs =>
    reaches_flatMap S (EdgeFacts S) (edgeFacts_mono S) (downLines S n n) (fun b => [.down b]) (downs S n c)
      (fun b hb o ho => by
        have := (List.mem_filter.mp hb).2
        simp only [Bool.and_eq_true] at this
        exact down_run S n n b this.2 o ho) o (hd.mono S hs)
  have hABC := reaches_append S hAB fun o _ _ =>
    reaches_flatMap S (fun _ => True) (fun _ _ _ _ => trivial) (fun p => [endorseLine p])
      (fun p => [Concl.endorsed p.1 p.2]) (gpairs pr G c)
      (fun p hp done _ => by
        obtain ⟨w, k⟩ := p
        have hok : lineOK S done (endorseLine (w, k)) = true :=
          lineOK_of S (by simp [endorseLine])
            (by simp [ruleOK, endorseLine, Concl.rule, (mem_pairs S (hgp hp).1).2.2.1])
        exact reaches_single S hok) o trivial
  refine (reaches_append S hABC fun o hg hs => reaches_single S (l := ⟨.ground, .grounded c, groundPrem S n pr G c⟩)
    (lineOK_of S ?_ ?_)).weaken S ?_
  · -- every premise was concluded
    intro p hp
    simp only [groundPrem, List.mem_cons, List.mem_append, List.mem_map] at hp
    rcases hp with rfl | ((((⟨r, hr, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩) | ⟨b, hb, rfl⟩)
    · exact hg _ (by simp)
    · exact hs _ (hG r (hrel r hr)).1
    · exact hs _ (hG _ (hgp hq).2).1
    · exact hs _ (hG _ (hgp hq).2).2
    · exact hg _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, hq, by simp⟩))
    · exact hg _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b, hb, by simp⟩)))
  · -- the rule checks
    simp only [ruleOK, Concl.rule, decide_true, Bool.true_and]
    unfold groundOK
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨hc, List.mem_cons_self⟩, fun r hr => ?_⟩, ?_⟩
    · simp only [groundPrem, List.mem_cons, List.mem_append, List.mem_map]
      exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inl ⟨r, hr, rfl⟩))))
    cases hs : S.schema c <;> simp only [hs] at hm ⊢
    case contract | decision =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
      obtain ⟨⟨hreq, hpol⟩, hthr⟩ := hm
      simp only [groundQuorum, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      refine ⟨⟨⟨hreq, hpol⟩, fun p hp => ?_⟩, Nat.le_trans hthr (nodup_length_le (nodup_dedup _) fun k hk => ?_)⟩
      · simp only [groundPrem, List.mem_cons, List.mem_append, List.mem_map] at hp
        rcases hp with rfl | ((((⟨r, -, rfl⟩ | ⟨q, -, rfl⟩) | ⟨q, -, rfl⟩) | ⟨q, hq, rfl⟩) | ⟨b, -, rfl⟩)
        · rfl
        · rfl
        · rfl
        · rfl
        · simp only [Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨countsFor_of_pair S (hgp hq).1 ?_ ?_, ?_⟩
          · simp only [groundPrem, List.mem_cons, List.mem_append, List.mem_map]
            exact Or.inr (Or.inl (Or.inl (Or.inr ⟨q, hq, rfl⟩)))
          · intro b hb
            simp only [groundPrem, List.mem_cons, List.mem_append, List.mem_map]
            exact Or.inr (Or.inr ⟨b, hb, rfl⟩)
          · simp only [groundPrem, List.mem_cons, List.mem_append, List.mem_map]
            exact Or.inr (Or.inl (Or.inl (Or.inl (Or.inr ⟨q, hq, rfl⟩))))
        · rfl
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (mem_dedup.mp hk)
        apply mem_dedup.mpr
        apply endorsedKeys_of_mem (w := q.1)
        simp only [groundPrem, List.mem_cons, List.mem_append, List.mem_map]
        exact Or.inr (Or.inl (Or.inr ⟨q, hq, rfl⟩))
    all_goals exact hm
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · simp
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (by simp)))

/-- **The rounds' lines run**, and conclude each cell of the last round grounded and standing. -/
theorem round_run (n : Nat) (hC : Cands S n pr U) : ∀ (R : Nat) (done : List (Concl C K)), EdgeFacts S done →
    Reaches S done (roundLines S n pr U R) ((groundSet S pr U R).flatMap fun c => [.grounded c, .stands c])
  | 0, done, _ => ⟨done, rfl, by simp [groundSet], fun _ h => h⟩
  | R + 1, done, hd => by
    have h1 := round_run n hC R done hd
    refine (reaches_append S h1 fun o hg hs => reaches_flatMap S
      (fun o => EdgeFacts S o ∧ ∀ x ∈ groundSet S pr U R, Concl.grounded x ∈ o ∧ Concl.stands x ∈ o)
      (fun a b ha hab => ⟨ha.1.mono S hab, fun x hx => ⟨hab _ (ha.2 x hx).1, hab _ (ha.2 x hx).2⟩⟩)
      (groundCellLines S n pr (groundSet S pr U R)) (fun c => [.grounded c, .stands c])
      ((groundSet S pr U (R + 1)).filter fun c => decide (c ∉ groundSet S pr U R))
      (fun c hc o ho => by
        have hcR := (List.mem_filter.mp hc).1
        obtain ⟨hcc, hst, hpr⟩ := hC c (groundSet_sub S hcR)
        exact cell_run S hcc hst hpr ((mem_groundSet S).mp hcR).2 o ho.1 ho.2) o
      ⟨hd.mono S hs, fun x hx => ⟨hg _ (List.mem_flatMap.mpr ⟨x, hx, by simp⟩),
        hg _ (List.mem_flatMap.mpr ⟨x, hx, by simp⟩)⟩⟩).weaken S ?_
    intro q hq
    obtain ⟨c, hc, hq⟩ := List.mem_flatMap.mp hq
    by_cases hold : c ∈ groundSet S pr U R
    · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, hold, hq⟩)
    · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨c, List.mem_filter.mpr ⟨hc, by simp [hold]⟩, hq⟩)

/-! ### Completeness -/

/-- What Grounded reads for `d`: `d`, and from each live cell it reads, what that cell relies on and the verdicts of
its `W_max`. -/
inductive Support (W : World C K P) (X : Pass3In C K P) (wmax : C → List C) (d : C) : C → Prop where
  | self : Support W X wmax d d
  | relies {c r : C} : Support W X wmax d c → Live X c → r ∈ (W.info c).relies → Support W X wmax d r
  | witness {c w : C} : Support W X wmax d c → Live X c → w ∈ wmax c → Support W X wmax d w

/-- The fragment of the `ground` checker: every live cell `d`'s Grounded reads is in the settle checker's fragment
(`Fragment`) and is not a scope, a schema or a question. -/
structure GFragment (W : World C K P) (X : Pass3In C K P) (Inv : C → Prop) (wmax : C → List C) (d : C) : Prop where
  frag : ∀ c, Support W X wmax d c → Live X c → Fragment S W X Inv c
  schema : ∀ c, Support W X wmax d c → Live X c →
    S.schema c ≠ .scope ∧ S.schema c ≠ .metaSchema ∧ S.schema c ≠ .question

/-- The cells `ground` may read next from `c`: what it relies on, and the cells whose payload it is. -/
def next (c : C) : List C := S.relies c ++ S.cells.filter fun w => decide (S.payload w = some c)

/-- The candidates from `U`: closed under `next` within `k` steps, or, when the steps run out, every cell. -/
def suppClose : Nat → List C → List C
  | 0, _ => S.cells
  | k + 1, U => if (U.flatMap (next S)).all (fun x => decide (x ∈ U)) then U
      else suppClose k (U ++ dedup ((U.flatMap (next S)).filter fun x => decide (x ∉ U)))

theorem suppClose_spec : ∀ (k : Nat) (U : List C) {d : C}, d ∈ U →
    suppClose S k U = S.cells ∨ (d ∈ suppClose S k U ∧ ∀ c ∈ suppClose S k U, ∀ x ∈ next S c, x ∈ suppClose S k U)
  | 0, _, _, _ => Or.inl rfl
  | k + 1, U, d, hd => by
    cases h : (U.flatMap (next S)).all (fun x => decide (x ∈ U)) with
    | true =>
      simp only [suppClose, h, if_true]
      refine Or.inr ⟨hd, fun c hc x hx => ?_⟩
      simp only [List.all_eq_true, decide_eq_true_eq] at h
      exact h x (List.mem_flatMap.mpr ⟨c, hc, hx⟩)
    | false =>
      simp only [suppClose, h, Bool.false_eq_true, if_false]
      exact suppClose_spec k _ (List.mem_append_left _ hd)

/-- The candidates from `d` that stand by `standsB`. -/
def groundCands (n : Nat) (d : C) : List C :=
  (suppClose S (S.cells.length + 1) [d]).filter fun c => decide (c ∈ S.cells) && standsB S n n c

/-- The value tabled for `c`. -/
def assocOf {β : Type} (c : C) : List (C × β) → Option β
  | [] => none
  | (a, b) :: t => if c = a then some b else assocOf c t

theorem assocOf_map {β : Type} (f : C → β) : ∀ (V : List C) {c : C}, c ∈ V →
    assocOf c (V.map fun x => (x, f x)) = some (f c)
  | [], _, h => absurd h List.not_mem_nil
  | a :: t, c, h => by
    simp only [List.map_cons, assocOf]
    by_cases hca : c = a
    · subst hca; simp
    · simp only [hca, if_false]
      exact assocOf_map f t ((List.mem_cons.mp h).resolve_left hca)

/-- **The checker for Grounded as `vars1witness --ground` runs it**: the prover's derivation over the candidates, with
`pairs` tabled once for each, to the first round that adds nothing. -/
def groundCheck (n : Nat) (d : C) : Bool :=
  let V := groundCands S n d
  let tbl := V.map fun c => (c, pairs S n c)
  let pr := fun c => (assocOf c tbl).getD []
  acceptsGround S (proveGround S n pr V (groundRounds S pr V)) d

/-- Finitely many things that each hold from some round on hold together from one round on. -/
theorem exists_round {α : Type} {Q : Nat → α → Prop} (hQ : ∀ R a, Q R a → Q (R + 1) a) :
    ∀ (l : List α), (∀ a ∈ l, ∃ R, Q R a) → ∃ R, ∀ a ∈ l, Q R a
  | [], _ => ⟨0, fun _ h => absurd h List.not_mem_nil⟩
  | a :: t, h => by
    have up : ∀ {R : Nat} {b : α}, Q R b → ∀ k, Q (R + k) b := fun hb k => by
      induction k with
      | zero => exact hb
      | succ k ih => exact hQ _ _ ih
    obtain ⟨Ra, ha⟩ := h a List.mem_cons_self
    obtain ⟨Rt, ht⟩ := exists_round hQ t (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨Ra + Rt, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact up ha Rt
    · have := up (ht b hb) Ra
      rwa [Nat.add_comm] at this

section Complete

variable {S}
variable {W : World C K P} {X : Pass3In C K P} {wmax : C → List C} {cnt : C → C → List K}
variable {AE : C → C → Kind → Bool} {Present isIntrinsic : C → Prop} {Auth : C → Bool} {Inv Eff Ret Acc : C → Prop}

/-- **The candidates hold every live cell Grounded reads**: a set closed under `next` that holds `d` does. -/
theorem support_mem (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X)
    (hwmax : WmaxFaithful W X S.cells wmax) {d : C} (hg : GFragment S W X Inv wmax d) {U : List C} (hd : d ∈ U)
    (hU : ∀ c ∈ U, ∀ x ∈ next S c, x ∈ U) : ∀ c, Support W X wmax d c → Live X c → c ∈ U := by
  intro c hs
  induction hs with
  | self => exact fun _ => hd
  | @relies c r hsup hlc hr ih =>
    intro _
    have hc := live_mem pin hlc
    exact hU c (ih hlc) r (List.mem_append_left _ ((pin.relies c hc) ▸ hr))
  | @witness c w hsup hlc hw ih =>
    intro _
    have hc := live_mem pin hlc
    obtain ⟨hwc, -, -, hrest⟩ := (hwmax c w).mp hw
    obtain ⟨-, -, hq⟩ := hg.schema c hsup hlc
    have hp : S.payload w = some c := by
      rw [pin.schema c hc] at hrest
      cases hs : S.schema c <;> simp only [hs] at hrest hq
      case contract | decision => exact (pin.payload w hwc c hc).mp hrest.2.1
      all_goals first | exact absurd rfl hq | exact hrest.elim
    exact hU c (ih hlc) w (List.mem_append_right _ (List.mem_filter.mpr ⟨hwc, by simp [hp]⟩))

/-- The candidates hold every live cell Grounded reads. -/
theorem candidates_cover (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X)
    (hwmax : WmaxFaithful W X S.cells wmax) {rank ht : C → Nat} {n : Nat} (hr : Ranked S rank ht n) {d : C}
    (hg : GFragment S W X Inv wmax d) : ∀ c, Support W X wmax d c → Live X c → c ∈ groundCands S n d := by
  intro c hs hl
  have hc := live_mem pin hl
  have hst : standsB S n n c = true :=
    stands_of_cone pin (hg.frag c hs hl) hr hl n c (hr.bound c hc).1 Cone.self
  refine List.mem_filter.mpr ⟨?_, by simp [hc, hst]⟩
  rcases suppClose_spec S (S.cells.length + 1) [d] (List.mem_singleton_self d) with h | ⟨hd, hU⟩
  · rw [h]; exact hc
  · exact support_mem pin hwmax hg hd hU c hs hl

/-- **A Grounded cell is in some round.** The cells of the support that are in some round form a pre-fixed point of
Grounded's equation, so they hold its least fixed point. -/
theorem grounded_round (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) (pc : PinComplete S W X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt)
    {rank ht : C → Nat} {n : Nat} (hr : Ranked S rank ht n) {d : C} (hg : GFragment S W X Inv wmax d)
    (hC : Cands S n pr U) (hU : ∀ c, Support W X wmax d c → Live X c → c ∈ U)
    (h : Grounded W X wmax cnt d) : ∃ R, d ∈ groundSet S pr U R := by
  let T : C → Prop := fun c => Support W X wmax d c → Live X c → ∃ R, c ∈ groundSet S pr U R
  have hT : Sub (GΦ W X wmax cnt T) T := by
    rintro v ⟨hl, hrel, hk⟩ hsup -
    have hv := live_mem pin hl
    have hvU := hU v hsup hl
    have hpr := (hC v hvU).2.2
    have hf := hg.frag v hsup hl
    obtain ⟨hs1, hs2, hs3⟩ := hg.schema v hsup hl
    obtain ⟨R1, hR1⟩ := exists_round (Q := fun R r => r ∈ groundSet S pr U R) (fun _ _ h => groundSet_mono S h)
      (S.relies v) (fun r hr' => by
        have hr'' : r ∈ (W.info v).relies := (pin.relies v hv).symm ▸ hr'
        exact hrel r hr'' (Support.relies hsup hl hr'') (pin.reliesLive v r hl.1 hl.2 hr''))
    -- the round after `R` holds `v` once its relies and its quorum's verdicts are in round `R`
    have step : ∀ R, R1 ≤ R → (match S.schema v with
        | .scope | .metaSchema | .question => false
        | .contract | .decision => decide (S.req v = none) && decide (evalPol S v ∈ S.pols) &&
            decide (S.thr (evalPol S v) ≤ (dedup ((gpairs pr (groundSet S pr U R) v).map Prod.snd)).length)
        | _ => true) = true → ∃ R', v ∈ groundSet S pr U R' := by
      intro R hle hm
      refine ⟨R + 1, (mem_groundSet S).mpr ⟨hvU, ?_⟩⟩
      unfold groundStep
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      exact ⟨fun r hr => groundSet_mono_le S hle (hR1 r hr), hm⟩
    rw [pin.schema v hv] at hk
    cases hs : S.schema v <;> simp only [hs] at hk hs1 hs2 hs3
    case contract | decision =>
      have hsch : S.schema v = .decision ∨ S.schema v = .contract := by simp [hs]
      have hep : Vars1.evalPol W X v = Witness.evalPol S v := by
        unfold Vars1.evalPol Witness.evalPol
        rw [pin.schema v hv, pin.customPol v hv, pin.scope, pin.pol0, hs]
      obtain ⟨E, hq, hE⟩ := hk
      rw [hep] at hq
      have hpol := pc.pols v hv hsch
      obtain ⟨ks, hnd, hkE, hkK, hthr⟩ := pin.quorumConv _ hpol _ hq
      obtain ⟨R2, hR2⟩ := exists_round (Q := fun R k => ∃ w, (w, k) ∈ pairs S n v ∧ w ∈ groundSet S pr U R)
        (fun _ _ ⟨w, hw, hg'⟩ => ⟨w, hw, groundSet_mono S hg'⟩) ks (fun k hk => by
          obtain ⟨w, hw, hTw, hkw⟩ := hE k (hkE k hk)
          obtain ⟨R, hR⟩ := hTw (Support.witness hsup hl hw) ((hwmax v w).mp hw).2.1
          exact ⟨R, w, pair_of_counts pin pc hwmax hcnt hr hsch hf hl hw hkw (hkK k hk), hR⟩)
      refine step (R1 + R2) (Nat.le_add_right _ _) ?_
      simp only [hs, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨hf.req, hpol⟩, Nat.le_trans hthr (nodup_length_le hnd fun k hk => ?_)⟩
      obtain ⟨w, hwk, hw⟩ := hR2 k hk
      have hwk' : (w, k) ∈ pr v := by rw [hpr]; exact hwk
      exact mem_dedup.mpr (List.mem_map.mpr ⟨(w, k), (mem_gpairs (pr := pr)).mpr
        ⟨hwk', groundSet_mono_le S (Nat.le_add_left _ _) hw⟩, rfl⟩)
    all_goals first
      | exact absurd rfl hs1
      | exact absurd rfl hs2
      | exact absurd rfl hs3
      | exact step R1 (Nat.le_refl _) (by simp [hs])
  exact grounded_least W X wmax cnt T hT d h Support.self ((grounded_fixed W X wmax cnt d).mpr h).1

/-- **Completeness of the `ground` rule on its fragment.** If the model holds `d` Grounded, the checker accepts the
prover's derivation over candidates that hold the live cells Grounded reads, for every round count at or after their
number, and after any round that adds nothing. -/
theorem ground_complete (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) (pc : PinComplete S W X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt)
    {rank ht : C → Nat} {n : Nat} (hr : Ranked S rank ht n) {d : C} (hg : GFragment S W X Inv wmax d)
    (hC : Cands S n pr U) (hU : ∀ c, Support W X wmax d c → Live X c → c ∈ U)
    (h : Grounded W X wmax cnt d) {R : Nat} (hR : U.length ≤ R ∨ stableB S pr U R = true) :
    acceptsGround S (proveGround S n pr U R) d = true := by
  obtain ⟨R0, h0⟩ := grounded_round pin pc hwmax hcnt hr hg hC hU h
  have hd : d ∈ groundSet S pr U R := by
    rcases hR with hle | hs
    · exact groundSet_mono_le S hle (groundSet_bound S R0 h0)
    · exact stable_all S hs R0 h0
  obtain ⟨o0, e0, he0, -⟩ := edge_run S []
  obtain ⟨out, hrun, hgs, -⟩ := round_run S n hC R o0 he0
  unfold acceptsGround proveGround
  rw [run_append, e0]
  simp only [Option.bind_some]
  rw [hrun]
  simp only [decide_eq_true_eq]
  exact hgs _ (List.mem_flatMap.mpr ⟨d, hd, by simp⟩)

/-- **`vars1witness --ground` decides Grounded on its fragment.** Under the hypotheses of soundness and completeness,
`groundCheck` answers true exactly when the model holds the cell Grounded. -/
theorem groundCheck_iff (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) (pc : PinComplete S W X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt)
    {rank ht : C → Nat} {n : Nat} (hr : Ranked S rank ht n) {d : C} (hg : GFragment S W X Inv wmax d) :
    groundCheck S n d = true ↔ Grounded W X wmax cnt d := by
  let V := groundCands S n d
  let pr' : C → List (C × K) := fun c => (assocOf c (V.map fun c => (c, pairs S n c))).getD []
  have hC : Cands S n pr' V := by
    intro c hc
    have hf := (List.mem_filter.mp hc).2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hf
    refine ⟨hf.1, hf.2, ?_⟩
    show (assocOf c (V.map fun c => (c, pairs S n c))).getD [] = pairs S n c
    rw [assocOf_map (fun c => pairs S n c) V hc]
    rfl
  show acceptsGround S (proveGround S n pr' V (groundRounds S pr' V)) d = true ↔ _
  exact ⟨witness_ground_sound pin hwmax hcnt, fun h => ground_complete pin pc hwmax hcnt hr hg hC
    (candidates_cover pin hwmax hr hg) h (groundRounds_ok S _ _)⟩

end Complete

end Witness

end Vars1
