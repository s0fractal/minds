import Vars1.Pivot

/-!
# What a coalition can do to Grounded (`GitVarsRepo.power`, its `grounded` row)

`power` lists, for one cell, the minimal coalitions of roster keys that can change its Live and Settled by commits of
their own. Those rows read the cell's own quorum (`settled_keeps`, `settled_needs`). Grounded reads more: what the cell
relies on, its witnesses and what they rely on, each with a quorum of its own, as a monotone circuit (`Grounded.lean`:
`relies` is an AND, a threshold policy a threshold gate). A coalition can strike several branches of that circuit in
one commit, and a key that endorses nothing the cell counts can still bring it down through a branch.

The theorems below make the coalition's question one computation of the same least fixed point on a smaller world. For
a fixed coalition `Co`, let `Stay` be the cells it cannot attack (no edge it can latch into them, `CanLatch` in
`Power.lean`). The **cut** world keeps only those cells and removes `Co`'s keys from every count; it is `Grounded` again,
on `cutPass3`, `cutWmax` and `cutCnt`, so `power` computes it with `grounded_lfp` once per coalition.

* `grounded_keeps_of_no_cut` — whatever the coalition does, what is Grounded in the cut world stays Grounded: the
  premises are that cells it cannot attack stay live, witnesses it cannot attack stay witnesses, and a key not its own
  that counted still counts (no key withdraws another's endorsement, `settled_keeps`). So a cell Grounded in the cut
  world is out of the coalition's reach, however many branches it strikes at once.
* `grounded_cut_attained` — and a commit that strikes everything it can (every attack, a withdrawal of every key of its
  own) leaves exactly the cut world, when nothing else changes: then Grounded after it is Grounded in the cut world.
  The two together make the `lose` row an equivalence: the coalition can take Grounded away iff the cut world does not
  ground the cell.
* `grounded_needs_gain`, `grounded_gain_attained` — the same for `gain`: the coalition's keys counting for every cell
  bound what it can ground (no other key's endorsement comes back, nothing it cannot revive comes back), and a commit
  that attests every cell of the frame with all its keys, by a fresh verdict that relies on nothing, reaches the bound.
* `illusion_of_quorum` — a world where every decision has threshold 2 of 3 keys, and the key `a` endorses nothing `D`
  counts: `D` is Grounded and stays Settled in the cut world of `{a}`, yet the cut world does not ground it. One key
  takes Grounded away from a cell it never signed, by withdrawing its own endorsement from what a witness relies on.

What is not here: that `Stay` is the set of cells the coalition cannot attack is `Power.lean`'s (`one_key_cannot_latch`,
`confinement`), on Pass 1 and 2; and that the presentations of the after-world meet these premises (witnesses, keys,
policies) is the gate's, held by the search through it in `test_vars1.py` 133. Where something already points an edge
at a cell of the frame, attacking that edge can bring a cell back, `grounded_cut_attained`'s premise fails and `power`
says `exact: false`.
-/

set_option linter.unusedSectionVars false

namespace Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K]

section Cut

variable (W : World C K P)

/-- The cut world's Pass 3 input: a cell stands only if it stays (the coalition cannot attack it). -/
def cutPass3 (X : Pass3In C K P) (Stay : C → Bool) : Pass3In C K P :=
  { X with active := fun v => X.active v ∧ Stay v = true, authorized := fun v => X.authorized v ∧ Stay v = true }

/-- The witnesses that stay. -/
def cutWmax (wmax : C → List C) (Stay : C → Bool) (v : C) : List C := (wmax v).filter Stay

/-- The keys that count, less the coalition's. -/
def cutCnt (cnt : C → C → List K) (Co : K → Bool) (v w : C) : List K := (cnt v w).filter (fun k => !Co k)

/-- **The cut**: Grounded on the world the coalition's strongest blow leaves. -/
def GroundedCut (X : Pass3In C K P) (wmax : C → List C) (cnt : C → C → List K) (Stay : C → Bool) (Co : K → Bool) :
    C → Prop :=
  Grounded W (cutPass3 X Stay) (cutWmax wmax Stay) (cutCnt cnt Co)

variable {W} {X X' : Pass3In C K P} {wmax wmax' : C → List C} {cnt cnt' : C → C → List K} {Stay : C → Bool}
  {Co : K → Bool}

theorem evalPol_cut (v : C) : evalPol W (cutPass3 X Stay) v = evalPol W X v := rfl

theorem live_cut {v : C} : Live (cutPass3 X Stay) v ↔ Live X v ∧ Stay v = true := by
  unfold Live cutPass3
  exact ⟨fun ⟨⟨ha, hs⟩, hn⟩ => ⟨⟨ha, hn⟩, hs⟩, fun ⟨⟨ha, hn⟩, hs⟩ => ⟨⟨ha, hs⟩, hn⟩⟩

/-- **No cut, no loss.** If the cells the coalition cannot attack stay live (and authorized), the policies stay, the
witnesses it cannot attack stay witnesses, and every key not its own that counted still counts, then every cell
Grounded in the cut world is Grounded after whatever the coalition does. -/
theorem grounded_keeps_of_no_cut (hlive : ∀ v, Stay v = true → Live X v → Live X' v)
    (hauth : ∀ v, Stay v = true → X.authorized v → X'.authorized v)
    (hpol : ∀ v, evalPol W X v = evalPol W X' v)
    (hwit : ∀ v w, Stay w = true → w ∈ wmax v → w ∈ wmax' v)
    (hcnt : ∀ v w k, k ∈ cnt v w → Co k = false → k ∈ cnt' v w) :
    Sub (GroundedCut W X wmax cnt Stay Co) (Grounded W X' wmax' cnt') := by
  refine grounded_mono (fun v hl => ?_) (fun v ha => ?_) (fun v => hpol v) (fun v w hw => ?_) (fun v w k hk => ?_)
  · obtain ⟨hl, hs⟩ := live_cut.mp hl
    exact hlive v hs hl
  · exact hauth v ha.2 ha.1
  · obtain ⟨hw, hs⟩ := List.mem_filter.mp hw
    exact hwit v w hs hw
  · obtain ⟨hk, hc⟩ := List.mem_filter.mp hk
    exact hcnt v w k hk (by simpa using hc)

/-- **The strongest blow reaches the cut.** If after the coalition's commit a live cell is a live cell that stays, a
witness is a witness that stays, and a key that counts counted before and is not the coalition's, then what is
Grounded after it is Grounded in the cut world. -/
theorem grounded_cut_attained (hlive : ∀ v, Live X' v → Live X v ∧ Stay v = true)
    (hauth : ∀ v, X'.authorized v → X.authorized v ∧ Stay v = true)
    (hpol : ∀ v, evalPol W X' v = evalPol W X v)
    (hwit : ∀ v w, w ∈ wmax' v → w ∈ wmax v ∧ Stay w = true)
    (hcnt : ∀ v w k, k ∈ cnt' v w → k ∈ cnt v w ∧ Co k = false) :
    Sub (Grounded W X' wmax' cnt') (GroundedCut W X wmax cnt Stay Co) := by
  refine grounded_mono (fun v hl => live_cut.mpr (hlive v hl)) (fun v ha => hauth v ha) (fun v => hpol v)
    (fun v w hw => ?_) (fun v w k hk => ?_)
  · obtain ⟨h, hs⟩ := hwit v w hw
    exact List.mem_filter.mpr ⟨h, hs⟩
  · obtain ⟨h, hc⟩ := hcnt v w k hk
    exact List.mem_filter.mpr ⟨h, by simp [hc]⟩

variable (W) in
/-- The operator of Grounded when the coalition's keys count for every cell: as `GΦ`, but a key of `Co` meets the
quorum with no witness of its own needed (a fresh verdict that relies on nothing carries it). -/
def GainΦ (X : Pass3In C K P) (wmax : C → List C) (cnt : C → C → List K) (Co : K → Bool) (G : C → Prop) (v : C) :
    Prop :=
  Live X v ∧ (∀ d ∈ (W.info v).relies, G d) ∧
  match (W.info v).schema with
  | .metaSchema | .scope => X.authorized v
  | .contract | .decision | .question =>
      ∃ E : List K, W.quorum E (evalPol W X v) = true ∧ ∀ k ∈ E, Co k = true ∨ ∃ w ∈ wmax v, G w ∧ k ∈ cnt v w
  | _ => True

theorem GainΦ_mono : Mono (GainΦ W X wmax cnt Co) := by
  intro S T hST v ⟨hl, hr, hk⟩
  refine ⟨hl, fun d hd => hST d (hr d hd), ?_⟩
  cases hs : (W.info v).schema <;> simp only [hs] at hk ⊢
  case metaSchema => exact hk
  case scope => exact hk
  all_goals first
    | trivial
    | (obtain ⟨E, hq, hE⟩ := hk
       exact ⟨E, hq, fun k hk' => (hE k hk').imp id (fun ⟨w, hw, hg, hc⟩ => ⟨w, hw, hST w hg, hc⟩)⟩)

variable (W) in
/-- **The most a coalition can ground**: the least fixed point of `GainΦ`. -/
def GroundedGain (X : Pass3In C K P) (wmax : C → List C) (cnt : C → C → List K) (Co : K → Bool) : C → Prop :=
  lfp (GainΦ W X wmax cnt Co)

/-- **What a coalition grounds, its keys could ground.** If after its commits a live cell was live, an authorization
was there, the policies stay, and a key that counts through a witness is the coalition's or counted through that
witness before, every cell Grounded after them is in `GroundedGain`. -/
theorem grounded_needs_gain (hlive : ∀ v, Live X' v → Live X v) (hauth : ∀ v, X'.authorized v → X.authorized v)
    (hpol : ∀ v, evalPol W X' v = evalPol W X v)
    (hwit : ∀ v w k, w ∈ wmax' v → k ∈ cnt' v w → Co k = true ∨ (w ∈ wmax v ∧ k ∈ cnt v w)) :
    Sub (Grounded W X' wmax' cnt') (GroundedGain W X wmax cnt Co) := by
  refine grounded_least W X' wmax' cnt' _ (fun v ⟨hl, hr, hk⟩ => (lfp_fixed GainΦ_mono v).mp ?_)
  refine ⟨hlive v hl, hr, ?_⟩
  cases hs : (W.info v).schema <;> simp only [hs] at hk ⊢
  case metaSchema => exact hauth v hk
  case scope => exact hauth v hk
  all_goals first
    | trivial
    | (obtain ⟨E, hq, hE⟩ := hk
       refine ⟨E, hpol v ▸ hq, fun k hk' => ?_⟩
       obtain ⟨w, hw', hg, hcw⟩ := hE k hk'
       rcases hwit v w k hw' hcw with h | ⟨h1, h2⟩
       · exact Or.inl h
       · exact Or.inr ⟨w, h1, hg, h2⟩)

/-- **And a commit that attests everything reaches it.** If what was live stays live, nothing it counted is lost, and
for every cell and key of the coalition a live verdict that relies on nothing counts that key, every cell of
`GroundedGain` is Grounded after it. -/
theorem grounded_gain_attained (hlive : ∀ v, Live X v → Live X' v) (hauth : ∀ v, X.authorized v → X'.authorized v)
    (hpol : ∀ v, evalPol W X v = evalPol W X' v) (hw : ∀ v w, w ∈ wmax v → w ∈ wmax' v)
    (hc : ∀ v w k, k ∈ cnt v w → k ∈ cnt' v w)
    (hfresh : ∀ v k, Co k = true → ∃ f ∈ wmax' v, Live X' f ∧ (W.info f).relies = [] ∧
      (W.info f).schema = .verdict ∧ k ∈ cnt' v f) :
    Sub (GroundedGain W X wmax cnt Co) (Grounded W X' wmax' cnt') := by
  refine lfp_least _ _ (fun v ⟨hl, hr, hk⟩ => (grounded_fixed W X' wmax' cnt' v).mp ?_)
  refine ⟨hlive v hl, hr, ?_⟩
  cases hs : (W.info v).schema <;> simp only [hs] at hk ⊢
  case metaSchema => exact hauth v hk
  case scope => exact hauth v hk
  all_goals first
    | trivial
    | (obtain ⟨E, hq, hE⟩ := hk
       refine ⟨E, hpol v ▸ hq, fun k hk' => ?_⟩
       rcases hE k hk' with hco | ⟨w, hw', hg, hcw⟩
       · obtain ⟨f, hf, hfl, hfr, hfs, hfk⟩ := hfresh v k hco
         refine ⟨f, hf, (grounded_fixed W X' wmax' cnt' f).mp ⟨hfl, by simp [hfr], ?_⟩, hfk⟩
         simp only [hfs]
       · exact ⟨w, hw v w hw', hg, hc v w k hcw⟩)

end Cut

/-! ## The illusion of a quorum -/

section Illusion

/-- The cells: decisions `d1`, `d2`, `D`; verdicts `u1a`, `u1b` on `d1`, `u2a`, `u2c` on `d2`; witnesses `w1`, `w2` of
`D`, which rely on `d1` and on `d2`. -/
inductive IC where
  | d1 | d2 | D | u1a | u1b | u2a | u2c | w1 | w2
  deriving DecidableEq

/-- Three keys. -/
inductive IK where
  | a | b | c
  deriving DecidableEq

/-- A local cell with a schema and what it relies on. -/
def icell (schema : Schema) (relies : List IC) : CellInfo IC Unit where
  schema := schema
  isLocal := true
  origin := 0
  slotName := 0
  relies := relies
  attests := []
  supersedes := []
  retires := []
  invalidates := []
  refs := []
  payload := none
  ownerPol := false
  customPol := none
  verdictInvalid := false
  pol0 := ()
  pol1 := ()

def illusionInfo : IC → CellInfo IC Unit
  | .d1 | .d2 | .D => icell .decision []
  | .w1 => icell .verdict [.d1]
  | .w2 => icell .verdict [.d2]
  | _ => icell .verdict []

/-- Every quorum is 2 of the keys `a`, `b`, `c`. -/
def illusionWorld : World IC IK Unit where
  info := illusionInfo
  member := fun _ _ => true
  quorum := fun E _ => decide (2 ≤ countIn [IK.a, .b, .c] E)

/-- Every cell stands. -/
def illusionPass3 : Pass3In IC IK Unit where
  active := fun _ => True
  stale := fun _ => False
  authorized := fun _ => True
  cumulative := fun _ => []
  foreignEnd := fun _ _ => []
  liveScopes := fun _ => []
  verdict := fun _ => { attested := true, replayed := false, invalid := false, witness := none, verifier := 0 }
  req := fun _ => none
  expectedSchema := fun _ => .verdict
  replayOK := fun _ _ => False
  scopeTip := .d1

/-- `d1` is attested by `a` and `b`, `d2` by `a` and `c`, `D` by `b` (through `w1`) and `c` (through `w2`). -/
def illusionWmax : IC → List IC
  | .d1 => [.u1a, .u1b]
  | .d2 => [.u2a, .u2c]
  | .D => [.w1, .w2]
  | _ => []

def illusionCnt (_ : IC) : IC → List IK
  | .u1a | .u2a => [.a]
  | .u1b | .w1 => [.b]
  | .u2c | .w2 => [.c]
  | _ => []

/-- Keys that are all one key count one. -/
theorem countIn_one {E : List IK} {x : IK} (h : ∀ k ∈ E, k = x) : countIn [IK.a, .b, .c] E ≤ 1 := by
  have hn : ∀ y, y ≠ x → y ∉ E := fun y hy hm => hy (h y hm)
  cases x
  · simp only [countIn, hn .b (by decide), hn .c (by decide), ↓reduceIte]
    split <;> omega
  · simp only [countIn, hn .a (by decide), hn .c (by decide), ↓reduceIte]
    split <;> omega
  · simp only [countIn, hn .a (by decide), hn .b (by decide), ↓reduceIte]
    split <;> omega

/-- **The illusion of a quorum.** Every decision needs 2 of 3 keys. The key `a` endorses nothing that `D` counts, and
`D` stays Settled in the cut world of `{a}` (its own quorum, `b` and `c`, is untouched), yet the cut world does not
ground `D`: `a` withdraws its endorsement of `d1`, `d1` falls to one key, the witness `w1` that relies on it falls,
and `D` keeps only `c`. By `grounded_cut_attained`, a commit of `a` alone takes Grounded away from `D`. -/
theorem illusion_of_quorum :
    ThresholdQuorum illusionWorld (fun _ => 2) (fun _ => [IK.a, .b, .c]) ∧
    (∀ w ∈ illusionWmax .D, IK.a ∉ illusionCnt .D w) ∧
    Grounded illusionWorld illusionPass3 illusionWmax illusionCnt .D ∧
    Settled illusionWorld (cutPass3 illusionPass3 (fun _ => true)) (cutWmax illusionWmax (fun _ => true))
      (cutCnt illusionCnt (fun k => k == .a)) .D ∧
    ¬ GroundedCut illusionWorld illusionPass3 illusionWmax illusionCnt (fun _ => true) (fun k => k == .a) .D := by
  let W := illusionWorld
  let X := illusionPass3
  have live : ∀ c, Live X c := fun _ => ⟨trivial, fun h => h⟩
  have gr : ∀ c, GΦ W X illusionWmax illusionCnt (Grounded W X illusionWmax illusionCnt) c →
      Grounded W X illusionWmax illusionCnt c := fun c h => (grounded_fixed W X illusionWmax illusionCnt c).mp h
  have hv : ∀ c, (illusionInfo c).relies = [] → (illusionInfo c).schema = .verdict →
      Grounded W X illusionWmax illusionCnt c := by
    intro c hr hs
    refine gr c ⟨live c, ?_, ?_⟩
    · intro d hd
      simp [W, illusionWorld, hr] at hd
    · simp only [W, illusionWorld, hs]
  have u1a := hv .u1a rfl rfl
  have u1b := hv .u1b rfl rfl
  have u2a := hv .u2a rfl rfl
  have u2c := hv .u2c rfl rfl
  have d1 : Grounded W X illusionWmax illusionCnt .d1 := by
    refine gr _ ⟨live _, by simp [W, illusionWorld, illusionInfo, icell], ?_⟩
    simp only [W, illusionWorld, illusionInfo, icell]
    refine ⟨[.a, .b], rfl, fun k hk => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact ⟨.u1a, by simp [illusionWmax], u1a, by simp [illusionCnt]⟩
    · exact ⟨.u1b, by simp [illusionWmax], u1b, by simp [illusionCnt]⟩
  have d2 : Grounded W X illusionWmax illusionCnt .d2 := by
    refine gr _ ⟨live _, by simp [W, illusionWorld, illusionInfo, icell], ?_⟩
    simp only [W, illusionWorld, illusionInfo, icell]
    refine ⟨[.a, .c], rfl, fun k hk => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact ⟨.u2a, by simp [illusionWmax], u2a, by simp [illusionCnt]⟩
    · exact ⟨.u2c, by simp [illusionWmax], u2c, by simp [illusionCnt]⟩
  have w1 : Grounded W X illusionWmax illusionCnt .w1 := by
    refine gr _ ⟨live _, fun d hd => ?_, by simp [W, illusionWorld, illusionInfo, icell]⟩
    simp only [W, illusionWorld, illusionInfo, icell, List.mem_singleton] at hd
    exact hd ▸ d1
  have w2 : Grounded W X illusionWmax illusionCnt .w2 := by
    refine gr _ ⟨live _, fun d hd => ?_, by simp [W, illusionWorld, illusionInfo, icell]⟩
    simp only [W, illusionWorld, illusionInfo, icell, List.mem_singleton] at hd
    exact hd ▸ d2
  refine ⟨⟨fun _ => by show [IK.a, IK.b, IK.c].Nodup; decide, fun _ _ => rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro w hw
    simp only [illusionWmax, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> simp [illusionCnt]
  · refine gr _ ⟨live _, by simp [W, illusionWorld, illusionInfo, icell], ?_⟩
    simp only [W, illusionWorld, illusionInfo, icell]
    refine ⟨[.b, .c], rfl, fun k hk => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact ⟨.w1, by simp [illusionWmax], w1, by simp [illusionCnt]⟩
    · exact ⟨.w2, by simp [illusionWmax], w2, by simp [illusionCnt]⟩
  · refine ⟨live_cut.mpr ⟨live _, rfl⟩, ?_⟩
    simp only [illusionWorld, illusionInfo, icell]
    rfl
  · -- the cut world grounds none of `d1`, `w1`, `D`
    let S : IC → Prop := fun v => v ≠ .d1 ∧ v ≠ .w1 ∧ v ≠ .D
    have hsub : Sub (GΦ W (cutPass3 X (fun _ => true)) (cutWmax illusionWmax (fun _ => true))
        (cutCnt illusionCnt (fun k => k == .a)) S) S := by
      rintro v ⟨-, hr, hk⟩
      cases v
      case w1 => exact absurd (hr .d1 (by simp [W, illusionWorld, illusionInfo, icell])) (by simp [S])
      case d1 =>
        exfalso
        simp only [W, illusionWorld, illusionInfo, icell] at hk
        obtain ⟨E, hq, hE⟩ := hk
        have hb : ∀ k ∈ E, k = .b := by
          intro k hk'
          obtain ⟨w, hw, -, hc⟩ := hE k hk'
          simp only [cutWmax, illusionWmax, List.filter_cons, List.filter_nil, if_true, List.mem_cons,
            List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl <;> simp [cutCnt, illusionCnt] at hc <;> exact hc
        have := of_decide_eq_true hq
        have := countIn_one hb
        omega
      case D =>
        exfalso
        simp only [W, illusionWorld, illusionInfo, icell] at hk
        obtain ⟨E, hq, hE⟩ := hk
        have hc' : ∀ k ∈ E, k = .c := by
          intro k hk'
          obtain ⟨w, hw, hs, hc⟩ := hE k hk'
          simp only [cutWmax, illusionWmax, List.filter_cons, List.filter_nil, if_true, List.mem_cons,
            List.not_mem_nil, or_false] at hw
          rcases hw with rfl | rfl
          · exact absurd hs (by simp [S])
          · simpa [cutCnt, illusionCnt] using hc
        have := of_decide_eq_true hq
        have := countIn_one hc'
        omega
      all_goals exact ⟨by decide, by decide, by decide⟩
    exact fun h => (grounded_least W _ _ _ S hsub _ h).2.2 rfl

end Illusion

end Vars1
