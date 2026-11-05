import Vars1.Lfp
import Vars1.Pass3

/-!
# §4.2 Grounded: what Settled does not carry across `relies`

`Stale` reads `Active` of the cells a cell relies on, not their `Settled`. So a decision can be Settled while a decision
it relies on has lost its quorum, or never had one, and a quorum's loss stops at the first `relies`.
`settled_not_hereditary` is that, on a world that satisfies the presentations.

`Grounded` is the hereditary reading: a cell stands, what it relies on is Grounded, and, if Pass 3 evaluates it, its
quorum is met by witnesses that are themselves Grounded. Witnesses are newer than what they judge and grounds older
than what relies on them, so a verdict may rely on the very decision it judges: the operator is not well founded by
age. It is monotone, and `Grounded` is its **least** fixed point (Knaster–Tarski, `Lfp.lean`): a support that runs in a
circle grounds nothing (`circular_support`), though everything on the circle is Settled and the circle is a fixed point.

Theorems:
* `GΦ_mono`, `grounded_fixed`, `grounded_least` — the operator is monotone; `Grounded` is its least fixed point.
* `grounded_settled` — Grounded implies Settled, when a quorum stays met as endorsers are added (`QuorumMono`).
* `grounded_relies`, `grounded_rests` — it is hereditary: everything a Grounded cell rests on along `relies` is
  Grounded, so Settled; `lost_quorum_collapses` — a cell relying on something not Settled is not Grounded.
* `grounded_iter` — simultaneous rounds from below reach it within `N + 1` rounds, on `Fin N`.
-/

set_option linter.unusedSectionVars false

namespace Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K]

section Operator

variable (W : World C K P) (X : Pass3In C K P) (wmax : C → List C) (cnt : C → C → List K)

/-- The operator of Grounded: `v` stands, what it relies on is in `G`, and if Pass 3 evaluates it, its quorum is met by
keys that count through witnesses in `G`. A scope or custom schema needs its Authorized latch, as Settled does. -/
def GΦ (G : C → Prop) (v : C) : Prop :=
  Live X v ∧ (∀ d ∈ (W.info v).relies, G d) ∧
  match (W.info v).schema with
  | .metaSchema | .scope => X.authorized v
  | .contract | .decision | .question =>
      ∃ E : List K, W.quorum E (evalPol W X v) = true ∧ ∀ k ∈ E, ∃ w ∈ wmax v, G w ∧ k ∈ cnt v w
  | _ => True

/-- **Grounded** (§4.2): the least fixed point of `GΦ`. -/
def Grounded : C → Prop := lfp (GΦ W X wmax cnt)

/-- The operator of Grounded is monotone. -/
theorem GΦ_mono : Mono (GΦ W X wmax cnt) := by
  intro S T hST v ⟨hl, hr, hk⟩
  refine ⟨hl, fun d hd => hST d (hr d hd), ?_⟩
  cases hs : (W.info v).schema <;> simp only [hs] at hk ⊢
  case metaSchema => exact hk
  case scope => exact hk
  all_goals first
    | trivial
    | (obtain ⟨E, hq, hE⟩ := hk
       exact ⟨E, hq, fun k hk' => let ⟨w, hw, hg, hc⟩ := hE k hk'; ⟨w, hw, hST w hg, hc⟩⟩)

/-- `Grounded` satisfies its equation. -/
theorem grounded_fixed (v : C) : GΦ W X wmax cnt (Grounded W X wmax cnt) v ↔ Grounded W X wmax cnt v :=
  lfp_fixed (GΦ_mono W X wmax cnt) v

/-- `Grounded` is below every pre-fixed point of its equation: no support that is not founded counts. -/
theorem grounded_least (S : C → Prop) (h : Sub (GΦ W X wmax cnt S) S) : Sub (Grounded W X wmax cnt) S :=
  lfp_least _ S h

/-- A quorum stays met as endorsers are added. -/
def QuorumMono : Prop := ∀ (E E' : List K) (p : P), (∀ k ∈ E, k ∈ E') → W.quorum E p = true → W.quorum E' p = true

/-- **Grounded implies Settled.** -/
theorem grounded_settled (hq : QuorumMono W) : Sub (Grounded W X wmax cnt) (Settled W X wmax cnt) := by
  apply grounded_least
  rintro v ⟨hl, -, hk⟩
  refine ⟨hl, ?_⟩
  cases hs : (W.info v).schema <;> simp only [hs] at hk ⊢
  case metaSchema => exact hk
  case scope => exact hk
  all_goals first
    | trivial
    | (obtain ⟨E, hE, hmem⟩ := hk
       refine hq E _ _ (fun k hk' => ?_) hE
       obtain ⟨w, hw, -, hc⟩ := hmem k hk'
       exact List.mem_flatMap.mpr ⟨w, hw, hc⟩)

/-- What a Grounded cell relies on is Grounded. -/
theorem grounded_relies {v d : C} (hv : Grounded W X wmax cnt v) (hd : d ∈ (W.info v).relies) :
    Grounded W X wmax cnt d :=
  ((grounded_fixed W X wmax cnt v).mpr hv).2.1 d hd

/-- `d` is reached from `v` along `relies`. -/
inductive Rests : C → C → Prop where
  | refl (v : C) : Rests v v
  | step {v u d : C} : u ∈ (W.info v).relies → Rests u d → Rests v d

/-- **Hereditary.** Everything a Grounded cell rests on along `relies` is Grounded, so Settled. -/
theorem grounded_rests (hq : QuorumMono W) {v d : C} (hr : Rests W v d) (hv : Grounded W X wmax cnt v) :
    Grounded W X wmax cnt d ∧ Settled W X wmax cnt d := by
  induction hr with
  | refl v => exact ⟨hv, grounded_settled W X wmax cnt hq _ hv⟩
  | step hu _ ih => exact ih (grounded_relies W X wmax cnt hv hu)

/-- **A lost quorum collapses.** A cell that rests, along `relies`, on a cell that is not Settled is not Grounded. -/
theorem lost_quorum_collapses (hq : QuorumMono W) {v d : C} (hr : Rests W v d) (hd : ¬ Settled W X wmax cnt d) :
    ¬ Grounded W X wmax cnt v :=
  fun hv => hd (grounded_rests W X wmax cnt hq hr hv).2

end Operator

/-- **Rounds.** On `Fin N`, simultaneous rounds of the operator from below only add cells, change nothing in round
`N + 1`, and end at `Grounded`. -/
theorem grounded_iter {K P : Type} [DecidableEq K] {N : Nat} (W : World (Fin N) K P) (X : Pass3In (Fin N) K P)
    (wmax : Fin N → List (Fin N)) (cnt : Fin N → Fin N → List K) :
    (∀ k, Sub (iter (GΦ W X wmax cnt) k) (iter (GΦ W X wmax cnt) (k + 1))) ∧
    (∀ v, iter (GΦ W X wmax cnt) (N + 1) v ↔ iter (GΦ W X wmax cnt) N v) ∧
    (∀ v, iter (GΦ W X wmax cnt) N v ↔ Grounded W X wmax cnt v) :=
  iter_reaches_lfp (jacobi_round (GΦ_mono W X wmax cnt))

/-! ## Two worlds that show the difference -/

section Examples

/-- A cell of the two small worlds below. -/
inductive Ex where
  | d0 | d1 | w
  deriving DecidableEq

/-- A world of one key and one policy with threshold one. `dCell` says what each cell is. -/
def exWorld (info : Ex → CellInfo Ex Unit) : World Ex Unit Unit where
  info := info
  member := fun _ _ => true
  quorum := fun E _ => !E.isEmpty

/-- A cell with the given schema, relies and verdict target. -/
def exCell (schema : Schema) (relies attests : List Ex) (payload : Option Ex) : CellInfo Ex Unit where
  schema := schema
  isLocal := true
  origin := 0
  slotName := 0
  relies := relies
  attests := attests
  supersedes := []
  retires := []
  invalidates := []
  refs := []
  payload := payload
  ownerPol := false
  customPol := none
  verdictInvalid := false
  pol0 := ()
  pol1 := ()

/-- Every cell stands, and the verdict `w` is ATTESTED. -/
def exPass3 (info : Ex → CellInfo Ex Unit) : Pass3In Ex Unit Unit where
  active := fun _ => True
  stale := fun _ => False
  authorized := fun _ => True
  cumulative := fun c => if c = .w then [()] else []
  foreignEnd := fun _ _ => []
  liveScopes := fun _ => []
  verdict := fun c => { attested := decide (c = .w), replayed := false, invalid := false, witness := none, verifier := 0 }
  req := fun _ => none
  expectedSchema := fun _ => .verdict
  replayOK := fun _ _ => False
  scopeTip := .d0

/-- `d0` is a decision nobody attested, `d1` a decision that relies on it, `w` an ATTESTED verdict on `d1`. -/
def hereditaryInfo : Ex → CellInfo Ex Unit
  | .d0 => exCell .decision [] [] none
  | .d1 => exCell .decision [.d0] [] none
  | .w => exCell .verdict [] [.d1] (some .d1)

/-- `d0` is a decision, and the only verdict on it, `w`, relies on it. -/
def circularInfo : Ex → CellInfo Ex Unit
  | .d0 => exCell .decision [] [] none
  | .d1 => exCell .axiom [] [] none
  | .w => exCell .verdict [.d0] [.d0] (some .d0)

theorem live_ex (info : Ex → CellInfo Ex Unit) (c : Ex) : Live (exPass3 info) c := ⟨trivial, fun h => h⟩

/-- No verdict of these worlds is INVALID, and only `w` is sealed. -/
theorem ex_cnt (info : Ex → CellInfo Ex Unit) (hl : ∀ c, (info c).isLocal = true) (cells : List Ex) :
    CntFaithful (exWorld info) (exPass3 info) cells (fun _ w => if w = .w then [()] else []) := by
  intro v w k
  have e : k ∈ witnessEndorsers (exWorld info) (exPass3 info) w ↔ w = .w := by
    have : (exWorld info).info = info := rfl
    cases w <;> simp [witnessEndorsers, this, hl, exPass3]
  have hnw : ¬ Withdrawn (exWorld info) (exPass3 info) cells v w k := by
    rintro ⟨b, -, -, -, -, hi, -⟩
    simp [exPass3] at hi
  have hm : match ((exWorld info).info v).schema with
      | .contract | .decision => ¬ Withdrawn (exWorld info) (exPass3 info) cells v w k
      | _ => True := by
    split <;> first | exact hnw | trivial
  constructor
  · intro h
    have : w = .w := by
      by_cases hw : w = .w
      · exact hw
      · simp [hw] at h
    exact ⟨e.mpr this, hm⟩
  · rintro ⟨h, -⟩
    simp [e.mp h]

theorem ex_quorum_mono (info : Ex → CellInfo Ex Unit) : QuorumMono (exWorld info) := by
  intro E E' _ hsub h
  simp only [exWorld, Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq] at h ⊢
  intro he
  apply h
  cases E with
  | nil => rfl
  | cons k _ =>
    have := hsub k (by simp)
    simp [he] at this

/-- **Settled is not hereditary.** On a world whose presentations are faithful, `d1` is Settled, relies on `d0`, which
no one attested and is not Settled, and is not Grounded. -/
theorem settled_not_hereditary :
    ∃ (W : World Ex Unit Unit) (X : Pass3In Ex Unit Unit) (cells : List Ex) (wmax : Ex → List Ex)
      (cnt : Ex → Ex → List Unit),
      WmaxFaithful W X cells wmax ∧ CntFaithful W X cells cnt ∧
      Settled W X wmax cnt .d1 ∧ .d0 ∈ (W.info .d1).relies ∧ ¬ Settled W X wmax cnt .d0 ∧
      ¬ Grounded W X wmax cnt .d1 := by
  let W := exWorld hereditaryInfo
  let X := exPass3 hereditaryInfo
  let wmax : Ex → List Ex := fun v => if v = .d1 then [.w] else []
  let cnt : Ex → Ex → List Unit := fun _ w => if w = .w then [()] else []
  have hset0 : ¬ Settled W X wmax cnt .d0 := by
    rintro ⟨-, h⟩
    simp [W, wmax, exWorld, hereditaryInfo, exCell] at h
  refine ⟨W, X, [.d0, .d1, .w], wmax, cnt, ?_, ?_, ?_, ?_, hset0, ?_⟩
  · intro v w
    cases v <;> cases w <;>
      simp [InWmax, W, X, wmax, exWorld, exPass3, hereditaryInfo, exCell, Live]
  · exact ex_cnt hereditaryInfo (by intro c; cases c <;> rfl) _
  · refine ⟨live_ex _ _, ?_⟩
    simp [W, wmax, cnt, exWorld, hereditaryInfo, exCell]
  · simp [W, exWorld, hereditaryInfo, exCell]
  · intro hg
    have hq : QuorumMono W := ex_quorum_mono _
    exact hset0 (grounded_rests W X wmax cnt hq
      (Rests.step (by simp [W, exWorld, hereditaryInfo, exCell]) (Rests.refl _)) hg).2

/-- **Support that runs in a circle grounds nothing.** The only verdict on `d0` relies on `d0`. On a world whose
presentations are faithful, `d0` is Settled and the whole world is a fixed point of the operator, and yet neither `d0`
nor the verdict is Grounded: `Grounded` is the least fixed point, and the greatest would take the circle for support. -/
theorem circular_support :
    ∃ (W : World Ex Unit Unit) (X : Pass3In Ex Unit Unit) (cells : List Ex) (wmax : Ex → List Ex)
      (cnt : Ex → Ex → List Unit),
      WmaxFaithful W X cells wmax ∧ CntFaithful W X cells cnt ∧
      Settled W X wmax cnt .d0 ∧ .d0 ∈ (W.info .w).relies ∧ .d0 ∈ (W.info .w).attests ∧
      (∀ v, GΦ W X wmax cnt (fun _ => True) v) ∧
      ¬ Grounded W X wmax cnt .d0 ∧ ¬ Grounded W X wmax cnt .w := by
  let W := exWorld circularInfo
  let X := exPass3 circularInfo
  let wmax : Ex → List Ex := fun v => if v = .d0 then [.w] else []
  let cnt : Ex → Ex → List Unit := fun _ w => if w = .w then [()] else []
  have hnot : Sub (Grounded W X wmax cnt) (fun c => c = .d1) := by
    apply grounded_least
    rintro v ⟨-, hr, hk⟩
    cases v with
    | d1 => rfl
    | w => exact absurd (hr .d0 (by simp [W, exWorld, circularInfo, exCell])) (by simp)
    | d0 =>
      simp only [W, exWorld, circularInfo, exCell] at hk
      obtain ⟨E, hE, hmem⟩ := hk
      simp only [Bool.not_eq_true', List.isEmpty_eq_false_iff, ne_eq] at hE
      cases E with
      | nil => exact absurd rfl hE
      | cons k _ =>
        obtain ⟨c, hc, hg, -⟩ := hmem k (by simp)
        simp only [wmax, if_true, List.mem_singleton] at hc
        subst hc
        simp at hg
  refine ⟨W, X, [.d0, .d1, .w], wmax, cnt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v w
    cases v <;> cases w <;>
      simp [InWmax, W, X, wmax, exWorld, exPass3, circularInfo, exCell, Live]
  · exact ex_cnt circularInfo (by intro c; cases c <;> rfl) _
  · refine ⟨live_ex _ _, ?_⟩
    simp [W, wmax, cnt, exWorld, circularInfo, exCell]
  · simp [W, exWorld, circularInfo, exCell]
  · simp [W, exWorld, circularInfo, exCell]
  · intro v
    refine ⟨live_ex _ _, fun _ _ => trivial, ?_⟩
    cases v
    · simp only [W, exWorld, circularInfo, exCell]
      exact ⟨[()], by simp, fun k _ => ⟨.w, by simp [wmax], trivial, by simp [cnt]⟩⟩
    · simp [W, exWorld, circularInfo, exCell]
    · simp [W, exWorld, circularInfo, exCell]
  · exact fun h => by simpa using hnot _ h
  · exact fun h => by simpa using hnot _ h

end Examples

end Vars1
