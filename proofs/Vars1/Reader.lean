import Vars1.Power
import Vars1.Grounded

/-!
# What a reader must read to decide a decision's status

"Decision `d` is in force at tip `T`" has a part that can travel as a proof and a part that is someone's word that
they read the whole tip. This file is the size law of that message, in three parts.

**1. The frame of Pass 3** (`Power.lean` has Passes 1–2: `pass1_frame`, `active_frame`, `stale_frame`).
`Reads` names what `Settled(d)` reads at a tip, as a set `Pr` and five conditions between two tips:

* `Pr` holds `d`, every cell of the tip that **judges** `d` (`Judges`: a cell that attests `d`, or an INVALID verdict
  on `d` or on the checkpoint a cell attesting `d` names), and every checkpoint or cycle witness such a cell names;
* `live` — every cell of `Pr` is live (`Active`, not `Stale`) at both tips or at neither. This is what
  `active_frame` and `stale_frame` give on a set closed under `relies`, under what it supersedes, and under every cell
  with a latched edge into it, into which no new edge latches;
* `judges` — no new cell judges `d`, and no new seal counts on a cell that does;
* the cells' contents are the same (`verdict`, `req`, `expected`, `replay`: they are functions of a cell's id);
* `policy` — **the scope caveat**: `d` names an evaluator policy of its own, or the two tips' governing scopes have
  one admission policy.

`settled_frame`: between two tips that `Reads` relates, `Settled(d)` is the same. `grounded_frame`: on a set closed
under `relies` and under the witnesses of what it holds, each evaluated cell of which `Reads` relates, `Grounded` is
the same. `settled_reads_tip_scope` shows the caveat is real: two tips that differ in nothing but the governing scope,
and a decision with no policy of its own that is Settled at one and not at the other.

**2. The lower bound.** `unread_commit_decides`, `unread_commit_decides2`: take any chain and any one commit of it,
and add to that commit one cell that invalidates `d` and the seals of a quorum of `Pol(d)` on it. Whatever the rest
of the chain is, `d` is Invalidated at the tip, under every reading of Pass 1. The two chains agree on every other
commit. `reader_reads_commit`: so a reader (`Reader`: an adaptive strategy that reads commits by position and then
answers) that answers Settled correctly on every chain reads every such commit of a chain where `d` is Settled.
Nothing in a cell names what refers to it: the negative part of a witness has no address.

**3. What state suffices.** `fold_state_suffices`: two prefixes with one fold state have one fold state after every
continuation; the state holds every present cell, every latch and every InitialEndorsers, so it is as large as the
store. Nothing in it can be dropped: `dead_cell_silent` says an Invalidated cell changes no `Effective` bit now, and
`dropped_cell_distinguishes` that after a continuation which invalidates what invalidated it (`revived`), the store
that kept it and the store that dropped it differ on a cell both hold. So no summary smaller than the store decides
every future status under the same rules; a rules change reads the commits again, which is what the log is for.
-/

set_option linter.unusedSectionVars false

namespace Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K]

/-! ## 1. The frame of Pass 3 -/

section Frame3

variable (W : World C K P) (X X' : Pass3In C K P) (cells cells' : List C) (Pr : C → Prop)

/-- A contract, decision or question: what Pass 3 evaluates against a policy. -/
def Evaluated (v : C) : Prop :=
  (W.info v).schema = .contract ∨ (W.info v).schema = .decision ∨ (W.info v).schema = .question

/-- `c` judges `d`: it attests `d` (a candidate witness), or it is an INVALID verdict on `d` or on the checkpoint or
cycle witness that a cell attesting `d` names (what may withdraw an endorsement). These are the cells whose seals
`Settled(d)` reads. -/
def Judges (d c : C) : Prop :=
  d ∈ (W.info c).attests ∨
  ((W.info c).schema = .verdict ∧ (X.verdict c).invalid = true ∧
    ((W.info c).payload = some d ∨
      ∃ w, d ∈ (W.info w).attests ∧ (X.verdict w).witness ≠ none ∧ (X.verdict c).witness = (X.verdict w).witness))

/-- **What `Settled(d)` reads**, between two tips `(X, cells)` and `(X', cells')`, on a set `Pr`. -/
structure Reads (d : C) : Prop where
  verdict : X'.verdict = X.verdict
  req : X'.req = X.req
  expected : X'.expectedSchema = X.expectedSchema
  replay : X'.replayOK = X.replayOK
  /-- the cells of the frame are live at both tips or at neither -/
  live : ∀ c, Pr c → (Live X c ↔ Live X' c)
  self : Pr d
  /-- no new cell judges `d`; those there are lie in the frame, and no new seal counts on one -/
  judges : ∀ c, Judges W X d c → (c ∈ cells ↔ c ∈ cells') ∧
    (c ∈ cells → Pr c ∧ ∀ k, k ∈ witnessEndorsers W X c ↔ k ∈ witnessEndorsers W X' c)
  /-- the checkpoints and cycle witnesses its judges name lie in the frame -/
  named : ∀ w c, d ∈ (W.info w).attests → w ∈ cells → (X.verdict w).witness = some c → Pr c
  /-- the scope caveat: a policy of its own, or one admission policy at both tips -/
  policy : (W.info d).customPol ≠ none ∨ (W.info X'.scopeTip).pol0 = (W.info X.scopeTip).pol0

variable {W X X' cells cells' Pr}

theorem judges_congr (hv : X'.verdict = X.verdict) {d c : C} : Judges W X' d c ↔ Judges W X d c := by
  unfold Judges
  rw [hv]

theorem Reads.symm {d : C} (h : Reads W X X' cells cells' Pr d) : Reads W X' X cells' cells Pr d where
  verdict := h.verdict.symm
  req := h.req.symm
  expected := h.expected.symm
  replay := h.replay.symm
  live := fun c hc => (h.live c hc).symm
  self := h.self
  judges := fun c hj => by
    obtain ⟨hm, hr⟩ := h.judges c ((judges_congr h.verdict).mp hj)
    refine ⟨hm.symm, fun hc' => ?_⟩
    obtain ⟨hp, he⟩ := hr (hm.mpr hc')
    exact ⟨hp, fun k => (he k).symm⟩
  named := fun w c ha hc' hwc => by
    have hc : w ∈ cells := (h.judges w (Or.inl ha)).1.mpr hc'
    rw [h.verdict] at hwc
    exact h.named w c ha hc hwc
  policy := h.policy.imp id Eq.symm

/-- The evaluator policy of an evaluated cell is the same at both tips. -/
theorem evalPol_frame {d : C} (hs : Evaluated W d) (h : Reads W X X' cells cells' Pr d) :
    evalPol W X d = evalPol W X' d := by
  unfold evalPol
  rcases h.policy with hp | hp
  · cases hc : (W.info d).customPol with
    | none => exact absurd hc hp
    | some p => rcases hs with hs | hs | hs <;> simp [hs]
  · rw [hp]

/-- One direction of `inWmax_frame`. -/
theorem inWmax_sub {d : C} (h : Reads W X X' cells cells' Pr d) {w : C} (hin : InWmax W X cells d w) :
    InWmax W X' cells' d w := by
  obtain ⟨hc, hl, ha, hm⟩ := hin
  obtain ⟨hmem, hr⟩ := h.judges w (Or.inl ha)
  obtain ⟨hpw, -⟩ := hr hc
  refine ⟨hmem.mp hc, (h.live w hpw).mp hl, ha, ?_⟩
  rw [h.verdict, h.req, h.expected, h.replay]
  cases hs : (W.info d).schema <;> simp only [hs] at hm ⊢ <;> try exact hm
  all_goals
    obtain ⟨h1, h2, h3⟩ := hm
    refine ⟨h1, h2, ?_⟩
    cases hq : X.req d <;> simp only [hq] at h3 ⊢
    · exact h3
    · obtain ⟨h4, c, hwc, hlc, hok⟩ := h3
      exact ⟨h4, c, hwc, (h.live c (h.named w c ha hc hwc)).mp hlc, hok⟩

/-- **`W_max(d)` is the same at both tips.** -/
theorem inWmax_frame {d : C} (h : Reads W X X' cells cells' Pr d) (w : C) :
    InWmax W X cells d w ↔ InWmax W X' cells' d w :=
  ⟨inWmax_sub h, inWmax_sub h.symm⟩

/-- One direction of `withdrawn_frame`. -/
theorem withdrawn_sub {d : C} (h : Reads W X X' cells cells' Pr d) {w : C} (ha : d ∈ (W.info w).attests) {k : K}
    (hwd : Withdrawn W X cells d w k) : Withdrawn W X' cells' d w k := by
  obtain ⟨b, hb, hlb, hsb, hor, hinv, hver, hk⟩ := hwd
  have hj : Judges W X d b := Or.inr ⟨hsb, hinv, hor.imp id fun hh => ⟨w, ha, hh.1, hh.2⟩⟩
  obtain ⟨hmem, hr⟩ := h.judges b hj
  obtain ⟨hpb, he⟩ := hr hb
  unfold Withdrawn
  rw [h.verdict]
  exact ⟨b, hmem.mp hb, (h.live b hpb).mp hlb, hsb, hor, hinv, hver, (he k).mp hk⟩

/-- **A withdrawal is the same at both tips**, through a cell that attests `d`. -/
theorem withdrawn_frame {d : C} (h : Reads W X X' cells cells' Pr d) {w : C} (ha : d ∈ (W.info w).attests) (k : K) :
    Withdrawn W X cells d w k ↔ Withdrawn W X' cells' d w k :=
  ⟨withdrawn_sub h ha, withdrawn_sub h.symm ha⟩

/-- **The keys that count are the same at both tips**, through a cell of the tip that attests `d`. -/
theorem counts_frame {d : C} (h : Reads W X X' cells cells' Pr d) {w : C} (ha : d ∈ (W.info w).attests)
    (hc : w ∈ cells) (k : K) : Counts W X cells d w k ↔ Counts W X' cells' d w k := by
  obtain ⟨-, hr⟩ := h.judges w (Or.inl ha)
  obtain ⟨-, he⟩ := hr hc
  have hwd := withdrawn_frame h ha k
  unfold Counts
  rw [he k]
  cases hs : (W.info d).schema <;> first | exact Iff.rfl | rw [hwd]

/-- The keys that count through `W_max(d)` are the same at both tips, whatever the presentations. -/
theorem counted_frame {wmax wmax' : C → List C} {cnt cnt' : C → C → List K}
    (hw : WmaxFaithful W X cells wmax) (hc : CntFaithful W X cells cnt)
    (hw' : WmaxFaithful W X' cells' wmax') (hc' : CntFaithful W X' cells' cnt')
    {d : C} (h : Reads W X X' cells cells' Pr d) (k : K) :
    k ∈ (wmax d).flatMap (cnt d) ↔ k ∈ (wmax' d).flatMap (cnt' d) := by
  constructor
  · intro hk
    obtain ⟨w, hin, hcw⟩ := List.mem_flatMap.mp hk
    have hI := (hw d w).mp hin
    exact List.mem_flatMap.mpr ⟨w, (hw' d w).mpr ((inWmax_frame h w).mp hI),
      (hc' d w k).mpr ((counts_frame h hI.2.2.1 hI.1 k).mp ((hc d w k).mp hcw))⟩
  · intro hk
    obtain ⟨w, hin, hcw⟩ := List.mem_flatMap.mp hk
    have hI' := (hw' d w).mp hin
    have hI := (inWmax_frame h w).mpr hI'
    exact List.mem_flatMap.mpr ⟨w, (hw d w).mpr hI,
      (hc d w k).mpr ((counts_frame h hI.2.2.1 hI.1 k).mpr ((hc' d w k).mp hcw))⟩

/-- **The frame of `Settled`.** Between two tips that `Reads` relates on a contract, decision or question `d`, `d` is
Settled at both or at neither. What the second tip adds elsewhere, cells, seals and latches, does not matter. -/
theorem settled_frame (hext : QuorumExt W) {wmax wmax' : C → List C} {cnt cnt' : C → C → List K}
    (hw : WmaxFaithful W X cells wmax) (hc : CntFaithful W X cells cnt)
    (hw' : WmaxFaithful W X' cells' wmax') (hc' : CntFaithful W X' cells' cnt')
    {d : C} (hs : Evaluated W d) (h : Reads W X X' cells cells' Pr d) :
    Settled W X wmax cnt d ↔ Settled W X' wmax' cnt' d := by
  have hq := hext _ _ (evalPol W X d) (counted_frame hw hc hw' hc' h)
  have hp := evalPol_frame hs h
  have hl := h.live d h.self
  unfold Settled
  rw [← hp, ← hq, hl]
  rcases hs with hs | hs | hs <;> simp only [hs]

/-- One direction of `grounded_frame`: a pre-fixed point of one tip's operator from the other's `Grounded`. -/
theorem grounded_sub {wmax wmax' : C → List C} {cnt cnt' : C → C → List K}
    (hlive : ∀ v, Pr v → Live X v → Live X' v)
    (hrel : ∀ v, Pr v → ∀ u ∈ (W.info v).relies, Pr u)
    (hauth : ∀ v, Pr v → X.authorized v → X'.authorized v)
    (hpol : ∀ v, Pr v → Evaluated W v → evalPol W X v = evalPol W X' v)
    (hwit : ∀ v, Pr v → ∀ w ∈ wmax v, Pr w ∧ w ∈ wmax' v ∧ ∀ k ∈ cnt v w, k ∈ cnt' v w) :
    ∀ v, Pr v → Grounded W X wmax cnt v → Grounded W X' wmax' cnt' v := by
  have hpre : Sub (GΦ W X wmax cnt (fun v => Pr v → Grounded W X' wmax' cnt' v))
      (fun v => Pr v → Grounded W X' wmax' cnt' v) := by
    rintro v ⟨hl, hr, hk⟩ hv
    refine (grounded_fixed W X' wmax' cnt' v).mp ⟨hlive v hv hl, fun u hu => hr u hu (hrel v hv u hu), ?_⟩
    have key : (∃ E : List K, W.quorum E (evalPol W X v) = true ∧
          ∀ k ∈ E, ∃ w ∈ wmax v, (Pr w → Grounded W X' wmax' cnt' w) ∧ k ∈ cnt v w) → Evaluated W v →
        ∃ E : List K, W.quorum E (evalPol W X' v) = true ∧
          ∀ k ∈ E, ∃ w ∈ wmax' v, Grounded W X' wmax' cnt' w ∧ k ∈ cnt' v w := by
      rintro ⟨E, hq, hE⟩ hev
      refine ⟨E, by rw [← hpol v hv hev]; exact hq, fun k hk' => ?_⟩
      obtain ⟨w, hw, hg, hcw⟩ := hE k hk'
      obtain ⟨hpw, hw', hcw'⟩ := hwit v hv w hw
      exact ⟨w, hw', hg hpw, hcw' k hcw⟩
    cases hs : (W.info v).schema <;> simp only [hs] at hk ⊢
    case metaSchema => exact hauth v hv hk
    case scope => exact hauth v hv hk
    case contract => exact key hk (Or.inl hs)
    case decision => exact key hk (Or.inr (Or.inl hs))
    case question => exact key hk (Or.inr (Or.inr hs))
    all_goals trivial
  intro v hv hg
  exact grounded_least W X wmax cnt _ hpre v hg hv

/-- **The frame of `Grounded`.** On a set closed under `relies` and under the witnesses of what it holds, whose cells
are live and Authorized at both tips or at neither, and each evaluated cell of which `Reads` relates, `Grounded` is
the same at both tips. The scope caveat is asked of every evaluated cell of the set (`Reads.policy`). -/
theorem grounded_frame {wmax wmax' : C → List C} {cnt cnt' : C → C → List K}
    (hw : WmaxFaithful W X cells wmax) (hc : CntFaithful W X cells cnt)
    (hw' : WmaxFaithful W X' cells' wmax') (hc' : CntFaithful W X' cells' cnt')
    (hlive : ∀ v, Pr v → (Live X v ↔ Live X' v))
    (hrel : ∀ v, Pr v → ∀ u ∈ (W.info v).relies, Pr u)
    (hauth : ∀ v, Pr v → (X.authorized v ↔ X'.authorized v))
    (hup : ∀ v, Pr v → ∀ w, InWmax W X cells v w → Pr w)
    (hreads : ∀ v, Pr v → Evaluated W v → Reads W X X' cells cells' Pr v)
    {v : C} (hv : Pr v) : Grounded W X wmax cnt v ↔ Grounded W X' wmax' cnt' v := by
  have hnone : ∀ u w, ¬ Evaluated W u → ¬ InWmax W X cells u w := by
    rintro u w hne ⟨-, -, -, hm⟩
    cases hs : (W.info u).schema <;> simp only [hs] at hm
    case contract => exact hne (Or.inl hs)
    case decision => exact hne (Or.inr (Or.inl hs))
    case question => exact hne (Or.inr (Or.inr hs))
  have hnone' : ∀ u w, ¬ Evaluated W u → ¬ InWmax W X' cells' u w := by
    rintro u w hne ⟨-, -, -, hm⟩
    cases hs : (W.info u).schema <;> simp only [hs] at hm
    case contract => exact hne (Or.inl hs)
    case decision => exact hne (Or.inr (Or.inl hs))
    case question => exact hne (Or.inr (Or.inr hs))
  constructor
  · refine grounded_sub (fun u hu => (hlive u hu).mp) hrel (fun u hu => (hauth u hu).mp)
      (fun u hu he => evalPol_frame he (hreads u hu he)) (fun u hu w hwm => ?_) v hv
    have hI := (hw u w).mp hwm
    have he : Evaluated W u := Classical.byContradiction fun hne => hnone u w hne hI
    have hr := hreads u hu he
    exact ⟨hup u hu w hI, (hw' u w).mpr ((inWmax_frame hr w).mp hI),
      fun k hk => (hc' u w k).mpr ((counts_frame hr hI.2.2.1 hI.1 k).mp ((hc u w k).mp hk))⟩
  · refine grounded_sub (fun u hu => (hlive u hu).mpr) hrel (fun u hu => (hauth u hu).mpr)
      (fun u hu he => (evalPol_frame he (hreads u hu he)).symm) (fun u hu w hwm => ?_) v hv
    have hI' := (hw' u w).mp hwm
    have he : Evaluated W u := Classical.byContradiction fun hne => hnone' u w hne hI'
    have hr := hreads u hu he
    have hI := (inWmax_frame hr w).mpr hI'
    exact ⟨hup u hu w hI, (hw u w).mpr hI,
      fun k hk => (hc u w k).mpr ((counts_frame hr hI.2.2.1 hI.1 k).mpr ((hc' u w k).mp hk))⟩

end Frame3

/-! ### The scope caveat is real -/

section Caveat

/-- The cells of the world below: two scope cells, a decision and a verdict on it. -/
inductive Sc where
  | sA | sB | d | w
  deriving DecidableEq

/-- A cell of the caveat's world. Keys and policies are `Bool`: policy `p` is "one of the key `p`". -/
def scCell (schema : Schema) (attests supersedes : List Sc) (payload : Option Sc) (pol0 : Bool) : CellInfo Sc Bool where
  schema := schema
  isLocal := true
  origin := 0
  slotName := 0
  relies := []
  attests := attests
  supersedes := supersedes
  retires := []
  invalidates := []
  refs := []
  payload := payload
  ownerPol := false
  customPol := none
  verdictInvalid := false
  pol0 := pol0
  pol1 := pol0

/-- Scope `sA` admits by the key `false`; `sB`, which supersedes it, by the key `true`. The decision `d` names no
policy of its own, and `w` is an ATTESTED verdict on it. -/
def scInfo : Sc → CellInfo Sc Bool
  | .sA => scCell .scope [] [] none false
  | .sB => scCell .scope [] [.sA] none true
  | .d => scCell .decision [] [] none false
  | .w => scCell .verdict [.d] [] (some .d) false

def scWorld : World Sc Bool Bool where
  info := scInfo
  member := fun p k => p == k
  quorum := fun E p => E.contains p

/-- Every cell stands, the key `false` sealed the verdict, and the governing scope at the tip is `tip`. -/
def scPass3 (tip : Sc) : Pass3In Sc Bool Bool where
  active := fun _ => True
  stale := fun _ => False
  authorized := fun _ => True
  cumulative := fun c => if c = .w then [false] else []
  foreignEnd := fun _ _ => []
  liveScopes := fun _ => []
  verdict := fun c => { attested := decide (c = .w), replayed := false, invalid := false, witness := none, verifier := 0 }
  req := fun _ => none
  expectedSchema := fun _ => .verdict
  replayOK := fun _ _ => False
  scopeTip := tip

theorem sc_wmax (tip : Sc) (cells : List Sc) (hw : Sc.w ∈ cells) :
    WmaxFaithful scWorld (scPass3 tip) cells (fun v => if v = .d then [.w] else []) := by
  intro a b
  cases a <;> cases b <;> simp [InWmax, scWorld, scPass3, scInfo, scCell, Live, hw]

theorem sc_cnt (tip : Sc) (cells : List Sc) :
    CntFaithful scWorld (scPass3 tip) cells (fun _ c => if c = .w then [false] else []) := by
  intro v a k
  have e : k ∈ witnessEndorsers scWorld (scPass3 tip) a ↔ (a = .w ∧ k = false) := by
    cases a <;> simp [witnessEndorsers, scWorld, scPass3, scInfo, scCell]
  have hnw : ¬ Withdrawn scWorld (scPass3 tip) cells v a k := by
    rintro ⟨b, -, -, -, -, hi, -⟩
    simp [scPass3] at hi
  have hm : match (scWorld.info v).schema with
      | .contract | .decision => ¬ Withdrawn scWorld (scPass3 tip) cells v a k
      | _ => True := by
    split <;> first | exact hnw | trivial
  constructor
  · intro h
    by_cases ha : a = .w
    · simp [ha] at h
      exact ⟨e.mpr ⟨ha, h⟩, hm⟩
    · simp [ha] at h
  · rintro ⟨h, -⟩
    obtain ⟨ha, hk⟩ := e.mp h
    simp [ha, hk]

/-- **Settled reads the scope at the tip.** Two tips with the same cells, the same seals and the same statuses of
Passes 1–2, that differ in the governing scope alone (a rotation whose admission policy is another), and a decision
that names no evaluator policy: it is Settled at the first and not at the second. So `Reads.policy` cannot be
dropped from `settled_frame`: for such a decision the frame holds the governing scope. -/
theorem settled_reads_tip_scope :
    ∃ (W : World Sc Bool Bool) (X X' : Pass3In Sc Bool Bool) (cells : List Sc) (wmax : Sc → List Sc)
      (cnt : Sc → Sc → List Bool),
      X' = { X with scopeTip := .sB } ∧ (W.info .d).customPol = none ∧
      WmaxFaithful W X cells wmax ∧ CntFaithful W X cells cnt ∧
      WmaxFaithful W X' cells wmax ∧ CntFaithful W X' cells cnt ∧
      Settled W X wmax cnt .d ∧ ¬ Settled W X' wmax cnt .d := by
  refine ⟨scWorld, scPass3 .sA, scPass3 .sB, [.sA, .sB, .d, .w], _, _, rfl, rfl,
    sc_wmax .sA _ (by simp), sc_cnt .sA _, sc_wmax .sB _ (by simp), sc_cnt .sB _, ?_, ?_⟩
  · refine ⟨⟨trivial, fun h => h⟩, ?_⟩
    simp [scWorld, scInfo, scCell, evalPol, scPass3]
  · rintro ⟨-, h⟩
    simp [scWorld, scInfo, scCell, evalPol, scPass3] at h

end Caveat

/-! ## 2. The lower bound: an unread commit may hold the cell that kills -/

section Kill

variable (W : World C K P) {AE : C → C → Kind → Bool} {Present isI : C → Prop} {Auth : C → Bool}
  {Inv Eff Ret Acc : C → Prop}

/-- A present cell that no present cell invalidates is Effective. -/
theorem unattacked_eff (h1 : IsPass1 W AE Present isI Auth Inv Eff Ret Acc) {z : C} (hp : Present z)
    (hz : ∀ u, Present u → z ∉ (W.info u).invalidates) : Eff z := by
  refine (h1.eff_eq z).mpr ⟨hp, fun hi => ?_⟩
  obtain ⟨u, hu, -, hm, -⟩ := (h1.inv_eq z).mp hi
  exact hz u ((h1.eff_eq u).mp hu).1 hm

/-- An Effective, Accepted killer with a latched invalidates edge leaves its target Invalidated. -/
theorem killed (h1 : IsPass1 W AE Present isI Auth Inv Eff Ret Acc) {z d : C} (hz : Eff z) (ha : Acc z)
    (hm : d ∈ (W.info z).invalidates) (hae : AE z d .invalidates = true)
    (hk : (W.info z).schema ≠ .verdict ∨ (W.info z).verdictInvalid = true) : Inv d ∧ ¬ Eff d :=
  have hi : Inv d := (h1.inv_eq d).mpr ⟨z, hz, ha, hm, hae, hk⟩
  ⟨hi, fun he => ((h1.eff_eq d).mp he).2 hi⟩

/-- A killer of `y` as a store may add it: present, Accepted, its invalidates edge to `y` latched, and named by no
present cell's invalidates edge (a cell is named by the hash of its bytes, so nothing older can name it). -/
def FreshKiller (AE : C → C → Kind → Bool) (Present Acc : C → Prop) (y z : C) : Prop :=
  Present z ∧ Acc z ∧ y ∈ (W.info z).invalidates ∧ AE z y .invalidates = true ∧
    ((W.info z).schema ≠ .verdict ∨ (W.info z).verdictInvalid = true) ∧
    ∀ u, Present u → z ∉ (W.info u).invalidates

/-- A fresh killer kills. -/
theorem FreshKiller.kills (h1 : IsPass1 W AE Present isI Auth Inv Eff Ret Acc) {y z : C}
    (hz : FreshKiller W AE Present Acc y z) : Inv y ∧ ¬ Eff y :=
  killed W h1 (unattacked_eff W h1 hz.1 hz.2.2.2.2.2) hz.2.1 hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2.1

/-- **Revival.** A present cell is Effective once every Effective cell that invalidates it by a latched edge has a
fresh killer: what displaced it can be displaced. -/
theorem revived (h1 : IsPass1 W AE Present isI Auth Inv Eff Ret Acc) {x : C} (hx : Present x)
    (hk : ∀ y, Eff y → x ∈ (W.info y).invalidates → AE y x .invalidates = true →
      ∃ z, FreshKiller W AE Present Acc y z) : Eff x := by
  refine (h1.eff_eq x).mpr ⟨hx, fun hi => ?_⟩
  obtain ⟨y, hy, -, hm, hae, -⟩ := (h1.inv_eq x).mp hi
  obtain ⟨z, hz⟩ := hk y hy hm hae
  exact (hz.kills W h1).2 hy

/-- Seals on `z` under scope `S`, one by each key of `E`. -/
def sealsOn (S z : C) (E : List K) : List (Seal C K) := E.map fun e => ⟨z, S, e⟩

/-- A commit with one more cell, `z`, and the seals of `E` on it under `S`. -/
def withKiller (cm : Commit C K) (S z : C) (E : List K) : Commit C K :=
  ⟨cm.newCells ++ [z], cm.seals ++ sealsOn S z E, cm.newScope⟩

theorem endorsers_withKiller (cm : Commit C K) (S z : C) (r : P) {E : List K}
    (hE : ∀ e ∈ E, W.member r e = true) : ∀ e ∈ E, e ∈ endorsers W (withKiller cm S z E) S z r := by
  intro e he
  simp only [endorsers, List.mem_map, List.mem_filter]
  refine ⟨⟨z, S, e⟩, ⟨?_, by simp [sealCounts, hE e he]⟩, rfl⟩
  exact List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩)

/-- §4.1 latch 3 holds for the killer's edge. -/
theorem edgeCond_withKiller (hadd : QuorumAdd W) (cm : Commit C K) (S : C) {z d : C} {E : List K}
    (init : C → List K) (hE : ∀ e ∈ E, W.member (roster W S d) e = true) (hq : W.quorum E (pol W S d).1 = true) :
    edgeCond W (withKiller cm S z E) S z d .invalidates init = true := by
  simp only [edgeCond, Bool.or_eq_true]
  exact Or.inl (hadd E _ _ (endorsers_withKiller W cm S z _ hE) hq)

/-- **The killer's edge latches, under v1.** Add to any commit a cell `z` that invalidates `d` and the seals on it of
keys of the governing scope's roster that meet `Pol(d)`: the edge `z → d` is latched after that commit. -/
theorem killer_latches (hadd : QuorumAdd W) (st : St C K) (cm : Commit C K) {z d : C} {E : List K}
    (hm : d ∈ (W.info z).invalidates) (hE : ∀ e ∈ E, W.member (roster W st.scope d) e = true)
    (hq : W.quorum E (pol W st.scope d).1 = true) :
    (step W st (withKiller cm st.scope z E)).edge z d .invalidates = true ∧
      z ∈ (step W st (withKiller cm st.scope z E)).present := by
  refine ⟨(step_edge_iff W st _ z d .invalidates).mpr (Or.inr ⟨?_, hm, edgeCond_withKiller W hadd cm _ _ hE hq⟩), ?_⟩
  · simp [withKiller]
  · simp [step, withKiller]

/-- **An unread commit may hold the cell that kills (v1).** Take any chain `pre ++ cm :: post` and add to the one
commit `cm` a cell `z` that invalidates `d`, with the seals of a quorum of `Pol(d)` under the scope governing there.
Then at the tip, whatever `pre`, `cm` and `post` are, every reading of Pass 1 in which `z` is present, Accepted and
named by no present cell's invalidates edge has `d` Invalidated, so not Effective, not Active and not Settled. The
two chains agree on every commit but that one. -/
theorem unread_commit_decides (hadd : QuorumAdd W) (s0 : St C K) (pre post : List (Commit C K)) (cm : Commit C K)
    {d z : C} {E : List K} (hm : d ∈ (W.info z).invalidates)
    (hkind : (W.info z).schema ≠ .verdict ∨ (W.info z).verdictInvalid = true)
    (hE : ∀ e ∈ E, W.member (roster W (run W s0 pre).scope d) e = true)
    (hq : W.quorum E (pol W (run W s0 pre).scope d).1 = true)
    (h1 : IsPass1 W (run W s0 (pre ++ withKiller cm (run W s0 pre).scope z E :: post)).edge Present isI Auth
      Inv Eff Ret Acc)
    (hp : ∀ c, c ∈ (run W s0 (pre ++ withKiller cm (run W s0 pre).scope z E :: post)).present → Present c)
    (hacc : Acc z) (hfresh : ∀ u, Present u → z ∉ (W.info u).invalidates) :
    Inv d ∧ ¬ Eff d := by
  have hrun : run W s0 (pre ++ withKiller cm (run W s0 pre).scope z E :: post) =
      run W (step W (run W s0 pre) (withKiller cm (run W s0 pre).scope z E)) post := by
    rw [run_append]; rfl
  obtain ⟨he, hz⟩ := killer_latches W hadd (run W s0 pre) cm hm hE hq
  have hle := run_le W (step W (run W s0 pre) (withKiller cm (run W s0 pre).scope z E)) post
  have hedge : (run W s0 (pre ++ withKiller cm (run W s0 pre).scope z E :: post)).edge z d .invalidates = true := by
    rw [hrun]; exact hle.1 z d _ he
  have hpz : Present z := hp z (by rw [hrun]; exact (hle.2.2 z hz).1)
  exact killed W h1 (unattacked_eff W h1 hpz hfresh) hacc hm hedge hkind

end Kill

section Kill2

variable (W : World2 C K P) {Present isI : C → Prop} {Auth : C → Bool} {Inv Eff Ret Acc : C → Prop}

/-- **The killer's edge latches, under v2**, when `z` is not a scope whose edges latch 3 withholds. -/
theorem killer_latches2 (hadd : QuorumAdd W.toWorld) (st : St2 C K) (cm : Commit C K) {z d : C} {E : List K}
    (hm : d ∈ (W.info z).invalidates) (hE : ∀ e ∈ E, W.member (roster W.toWorld st.scope d) e = true)
    (hq : W.quorum E (pol W.toWorld st.scope d).1 = true)
    (hnw : withheld W st (withKiller cm st.scope z E) z = false) :
    (step2 W st (withKiller cm st.scope z E)).edge z d .invalidates = true ∧
      z ∈ (step2 W st (withKiller cm st.scope z E)).present := by
  have hc := edgeCond_withKiller W.toWorld hadd cm st.scope (z := z)
    (initAfter W.toWorld st.toSt (withKiller cm st.scope z E)) hE hq
  have hl : (latch2 W st (withKiller cm st.scope z E)).edge z d .invalidates = true := by
    have hz : z ∈ (withKiller cm st.scope z E).newCells := by simp [withKiller]
    have hm' : d ∈ (W.info z).edges .invalidates := hm
    simp [latch2, hz, hm', hnw, hc]
  refine ⟨(settle2_le W _ st.tick _).1 z d _ hl, ?_⟩
  rw [History_step2_present]
  simp [withKiller]
where
  History_step2_present : (step2 W st (withKiller cm st.scope z E)).present =
      st.present ++ (withKiller cm st.scope z E).newCells := by
    show (settle2 W _ st.tick (latch2 W st _)).present = _
    unfold settle2
    split
    · rfl
    · split
      · rfl
      · split <;> rfl

/-- **An unread commit may hold the cell that kills (v2).** As `unread_commit_decides`, for the v2 fold. -/
theorem unread_commit_decides2 (hadd : QuorumAdd W.toWorld) (s0 : St2 C K) (pre post : List (Commit C K))
    (cm : Commit C K) {d z : C} {E : List K} (hm : d ∈ (W.info z).invalidates)
    (hkind : (W.info z).schema ≠ .verdict ∨ (W.info z).verdictInvalid = true)
    (hE : ∀ e ∈ E, W.member (roster W.toWorld (run2 W s0 pre).scope d) e = true)
    (hq : W.quorum E (pol W.toWorld (run2 W s0 pre).scope d).1 = true)
    (hnw : withheld W (run2 W s0 pre) (withKiller cm (run2 W s0 pre).scope z E) z = false)
    (h1 : IsPass1 W.toWorld (run2 W s0 (pre ++ withKiller cm (run2 W s0 pre).scope z E :: post)).edge Present isI
      Auth Inv Eff Ret Acc)
    (hp : ∀ c, c ∈ (run2 W s0 (pre ++ withKiller cm (run2 W s0 pre).scope z E :: post)).present → Present c)
    (hacc : Acc z) (hfresh : ∀ u, Present u → z ∉ (W.info u).invalidates) :
    Inv d ∧ ¬ Eff d := by
  have hrun : run2 W s0 (pre ++ withKiller cm (run2 W s0 pre).scope z E :: post) =
      run2 W (step2 W (run2 W s0 pre) (withKiller cm (run2 W s0 pre).scope z E)) post := by
    rw [run2_append]; rfl
  obtain ⟨he, hz⟩ := killer_latches2 W hadd (run2 W s0 pre) cm hm hE hq hnw
  have hle := run2_le W (step2 W (run2 W s0 pre) (withKiller cm (run2 W s0 pre).scope z E)) post
  have hedge : (run2 W s0 (pre ++ withKiller cm (run2 W s0 pre).scope z E :: post)).edge z d .invalidates = true := by
    rw [hrun]; exact hle.1 z d _ he
  have hpz : Present z := hp z (by rw [hrun]; exact (hle.2.2 z hz).1)
  exact killed W.toWorld h1 (unattacked_eff W.toWorld h1 hpz hfresh) hacc hm hedge hkind

end Kill2

/-! ### Readers -/

section Readers

variable {α : Type}

/-- A reader of a chain: an adaptive strategy that reads commits by position, each choice depending on what it has
read, and then answers. It has no other access: nothing tells it which commits name a cell. -/
inductive Reader (α : Type) where
  | say (b : Bool) : Reader α
  | read (i : Nat) (next : Option α → Reader α) : Reader α

/-- A reader's answer on a chain, and the positions it read. -/
def Reader.run : Reader α → List α → Bool × List Nat
  | .say b, _ => (b, [])
  | .read i next, s => ((next s[i]?).run s |>.1, i :: ((next s[i]?).run s |>.2))

/-- A reader cannot tell two chains apart that agree wherever it read. -/
theorem Reader.blind : ∀ (r : Reader α) (s s' : List α), (∀ i ∈ (r.run s).2, s[i]? = s'[i]?) → r.run s' = r.run s
  | .say b, _, _, _ => rfl
  | .read i next, s, s', h => by
    have hi : s[i]? = s'[i]? := h i (by simp [Reader.run])
    have ih := Reader.blind (next s[i]?) s s' (fun j hj => h j (by simp [Reader.run, hj]))
    simp only [Reader.run]
    rw [← hi, ih]

/-- **The adversary's argument.** If two chains agree everywhere but at position `j` and differ in the status, a
reader that answers the status correctly on both reads position `j` of the first. -/
theorem reader_must_read (status : List α → Prop) (r : Reader α) (s s' : List α)
    (hcorrect : (r.run s).1 = true ↔ status s) (hcorrect' : (r.run s').1 = true ↔ status s') (j : Nat)
    (hagree : ∀ i, i ≠ j → s[i]? = s'[i]?) (hs : status s) (hs' : ¬ status s') : j ∈ (r.run s).2 := by
  by_cases hj : j ∈ (r.run s).2
  · exact hj
  · have hb := Reader.blind r s s' (fun i hi => hagree i (fun h => hj (h ▸ hi)))
    have h1 := hcorrect.mpr hs
    exact absurd (hcorrect'.mp (by rw [hb]; exact h1)) hs'

theorem getElem?_off (pre post : List α) (a b : α) : ∀ i, i ≠ pre.length → (pre ++ a :: post)[i]? = (pre ++ b :: post)[i]? := by
  induction pre with
  | nil =>
    intro i hi
    cases i with
    | zero => exact absurd rfl hi
    | succ i => simp
  | cons x pre ih =>
    intro i hi
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.cons_append, List.getElem?_cons_succ]
      exact ih i (fun h => hi (by simp [h]))

end Readers

section ReaderBound

variable (W : World C K P)

/-- `d` is Effective at the tip of `chain`, under some reading of Pass 1 over the fold's latches and cells in which
every local cell is Accepted. Settled implies it, through Live and Active. -/
def StandsAt (s0 : St C K) (d : C) (chain : List (Commit C K)) : Prop :=
  ∃ (isI : C → Prop) (Auth : C → Bool) (Inv Eff Ret Acc : C → Prop),
    IsPass1 W (run W s0 chain).edge (· ∈ (run W s0 chain).present) isI Auth Inv Eff Ret Acc ∧ Eff d

/-- **A correct reader reads the commit (v1).** Let `status` be any property of a chain that, on the chain with the
killer, holds only if `d` is Effective at its tip (Settled, or Grounded, of `d` is one). Take a chain
`pre ++ cm :: post` where it holds, a commit `cm` of it at which keys of the governing roster meet `Pol(d)`, and a
local cell `z` that invalidates `d` and that no cell of the chain with it names. A reader that answers `status`
correctly on the chain and on the chain with `z` and those keys' seals added to `cm` reads the commit `cm`. -/
theorem reader_reads_commit (hadd : QuorumAdd W) (s0 : St C K) (d : C) (status : List (Commit C K) → Prop)
    (r : Reader (Commit C K)) (pre post : List (Commit C K)) (cm : Commit C K)
    {z : C} {E : List K} (hm : d ∈ (W.info z).invalidates) (hloc : (W.info z).isLocal = true)
    (hkind : (W.info z).schema ≠ .verdict ∨ (W.info z).verdictInvalid = true)
    (hE : ∀ e ∈ E, W.member (roster W (run W s0 pre).scope d) e = true)
    (hq : W.quorum E (pol W (run W s0 pre).scope d).1 = true)
    (hfresh : ∀ u ∈ (run W s0 (pre ++ withKiller cm (run W s0 pre).scope z E :: post)).present,
      z ∉ (W.info u).invalidates)
    (hsound : status (pre ++ withKiller cm (run W s0 pre).scope z E :: post) →
      StandsAt W s0 d (pre ++ withKiller cm (run W s0 pre).scope z E :: post))
    (hcorrect : (r.run (pre ++ cm :: post)).1 = true ↔ status (pre ++ cm :: post))
    (hcorrect' : (r.run (pre ++ withKiller cm (run W s0 pre).scope z E :: post)).1 = true ↔
      status (pre ++ withKiller cm (run W s0 pre).scope z E :: post))
    (hs : status (pre ++ cm :: post)) :
    pre.length ∈ (r.run (pre ++ cm :: post)).2 := by
  refine reader_must_read status r _ _ hcorrect hcorrect' pre.length (getElem?_off pre post _ _) hs (fun hst => ?_)
  obtain ⟨isI, Auth, Inv, Eff, Ret, Acc, h1, he⟩ := hsound hst
  exact (unread_commit_decides W hadd s0 pre post cm hm hkind hE hq h1 (fun c hc => hc)
    (acc_local h1 hloc) hfresh).2 he

end ReaderBound

/-! ## 3. What state suffices, and that nothing in it can be dropped -/

section Nerode

variable (W : World C K P) {AE : C → C → Kind → Bool} {Present Present' isI isI' : C → Prop} {Auth Auth' : C → Bool}
  {Inv Eff Ret Acc Inv' Eff' Ret' Acc' : C → Prop}

/-- **The fold's state suffices for the fold (v1).** Two prefixes that end in one state end in one state after every
continuation. The state holds every present cell, every latch and every cell's InitialEndorsers; a continuation's
commits carry the seals of their trees. -/
theorem fold_state_suffices (s0 : St C K) (p p' f : List (Commit C K)) (h : run W s0 p = run W s0 p') :
    run W s0 (p ++ f) = run W s0 (p' ++ f) := by
  rw [run_append, run_append, h]

/-- **A dead cell is silent now.** Drop an Invalidated cell `x` from the store. With the same latches and the same
`Accepted`, `Effective` of every other cell is what it was: at this tip a summary without `x` answers the same. -/
theorem dead_cell_silent (h : IsPass1 W AE Present isI Auth Inv Eff Ret Acc)
    (h' : IsPass1 W AE Present' isI' Auth' Inv' Eff' Ret' Acc)
    (ht : C → Nat) (hht : ∀ w v, Present' w → v ∈ (W.info w).invalidates → ht w < ht v)
    {x : C} (hdead : ¬ Eff x) (hdrop : ∀ c, Present' c ↔ Present c ∧ c ≠ x) :
    ∀ c, c ≠ x → (Eff c ↔ Eff' c) := by
  have hinv : ∀ v, Inv v ↔ ∃ w, (Eff w ∧ w ≠ x) ∧ Acc w ∧ v ∈ (W.info w).invalidates ∧
      AE w v .invalidates = true ∧ ((W.info w).schema ≠ .verdict ∨ (W.info w).verdictInvalid = true) := by
    intro v
    rw [h.inv_eq v]
    constructor
    · rintro ⟨w, hw, hr⟩
      exact ⟨w, ⟨hw, fun e => hdead (e ▸ hw)⟩, hr⟩
    · rintro ⟨w, ⟨hw, -⟩, hr⟩
      exact ⟨w, hw, hr⟩
  have heff : ∀ u, (Eff u ∧ u ≠ x) ↔ Present' u ∧ ¬ Inv u := by
    intro u
    rw [hdrop u]
    constructor
    · rintro ⟨he, hne⟩
      obtain ⟨hp, hni⟩ := (h.eff_eq u).mp he
      exact ⟨⟨hp, hne⟩, hni⟩
    · rintro ⟨⟨hp, hne⟩, hni⟩
      exact ⟨(h.eff_eq u).mpr ⟨hp, hni⟩, hne⟩
  have hu := pass1_kernel_unique W AE Present' Acc ht hht hinv heff h'.inv_eq h'.eff_eq
  intro c hc
  rw [← (hu c).2]
  exact ⟨fun he => ⟨he, hc⟩, fun he => he.1⟩

/-- **And it speaks later.** `x` invalidates `v` by a latched edge and is `v`'s only attacker. In the store that kept
`x`, after a continuation that gives every Effective cell invalidating `x` a fresh killer, `x` is Effective again and
`v` is Invalidated. In the store that dropped `x`, `v` is Effective. So the two stores, which `dead_cell_silent` says
answer alike before the continuation, differ after it on a cell both hold: no cell can be dropped from the summary,
though it is Invalidated. -/
theorem dropped_cell_distinguishes (h : IsPass1 W AE Present isI Auth Inv Eff Ret Acc)
    (h' : IsPass1 W AE Present' isI' Auth' Inv' Eff' Ret' Acc') {x v : C}
    (hx : Present x) (hacc : Acc x) (hx' : ¬ Present' x) (hv' : Present' v)
    (hm : v ∈ (W.info x).invalidates) (hae : AE x v .invalidates = true)
    (hkind : (W.info x).schema ≠ .verdict ∨ (W.info x).verdictInvalid = true)
    (hrev : ∀ y, Eff y → x ∈ (W.info y).invalidates → AE y x .invalidates = true →
      ∃ z, FreshKiller W AE Present Acc y z)
    (honly : ∀ w, Present' w → v ∈ (W.info w).invalidates → AE w v .invalidates = true → w = x) :
    ¬ Eff v ∧ Eff' v := by
  refine ⟨(killed W h (revived W h hx hrev) hacc hm hae hkind).2, (h'.eff_eq v).mpr ⟨hv', fun hi => ?_⟩⟩
  obtain ⟨w, hw, -, hmw, haew, -⟩ := (h'.inv_eq v).mp hi
  have hpw := ((h'.eff_eq w).mp hw).1
  exact hx' (honly w hpw hmw haew ▸ hpw)

end Nerode

/-- **The fold's state suffices for the fold (v2).** -/
theorem fold_state_suffices2 (W : World2 C K P) (s0 : St2 C K) (p p' f : List (Commit C K))
    (h : run2 W s0 p = run2 W s0 p') : run2 W s0 (p ++ f) = run2 W s0 (p' ++ f) := by
  rw [run2_append, run2_append, h]

end Vars1
