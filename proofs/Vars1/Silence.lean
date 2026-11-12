import Vars1.Reader

/-!
# Silence: what a decision profile need not be asked about

A decision profile names goals: contracts, decisions or questions whose Settled and Grounded matter to someone. A
graph that can say what to ask next (`next`, task 10) and what a reading would change (`fold-candidates`, task 14)
must also say when it has no reason to ask. Two theorems give that reason as a zero, not a price.

* `silence_outside_reads` — a change confined to a set `Q` of cells (their liveness, membership, endorsers or
  authorization may differ between two tips; nothing else) that meets no goal's frame leaves the vector of
  `(Settled, Grounded)` over the goals as it was. The frame of a goal (`GFrame`) is what `grounded_frame` reads: the
  goal, closed under `relies` and under the witnesses of `W_max`, with every cell that judges an evaluated member and
  every checkpoint those name. `reads_of_outside` is the step: such a change and such a frame give `Reads`.
* `silence_by_quorum_slack` — a cell `q` inside a goal's quorum is silent too when the keys that count through the
  goal's other witnesses already meet its policy and are the same at both tips: whatever happens to `q` (it loses its
  keys, gains some, dies, appears), the goal is Settled at a tip exactly when it is live there.

Neither is a heuristic: a question about a cell outside every frame, or about a key the quorum does not need, cannot
move a goal. What the profile lens in `experiments/decisions/profile.py` computes is these frames and this slack.

Axioms: `silence_by_quorum_slack` and `reads_of_outside` use `propext` and `Quot.sound` only; `silence_outside_reads`
adds `Classical.choice`, which it takes from `grounded_frame` (`Reader.lean`).
-/

set_option linter.unusedSectionVars false

namespace Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K]

section Silence

variable {W : World C K P} {X X' : Pass3In C K P} {cells cells' : List C}

/-- **A change confined to `Q`.** Between two tips, the verdict data, requirements and scope policy are the same, and
outside `Q` every cell is live, present, endorsed and Authorized alike. -/
structure OutsideOnly (W : World C K P) (X X' : Pass3In C K P) (cells cells' : List C) (Q : C → Prop) : Prop where
  verdict : X'.verdict = X.verdict
  req : X'.req = X.req
  expected : X'.expectedSchema = X.expectedSchema
  replay : X'.replayOK = X.replayOK
  pol0 : (W.info X'.scopeTip).pol0 = (W.info X.scopeTip).pol0
  live : ∀ c, ¬ Q c → (Live X c ↔ Live X' c)
  mem : ∀ c, ¬ Q c → (c ∈ cells ↔ c ∈ cells')
  endorsers : ∀ c, ¬ Q c → ∀ k, k ∈ witnessEndorsers W X c ↔ k ∈ witnessEndorsers W X' c
  authorized : ∀ c, ¬ Q c → (X.authorized c ↔ X'.authorized c)

/-- **The frame of a goal**: what `Grounded` and `Settled` read for it. -/
structure GFrame (W : World C K P) (X : Pass3In C K P) (cells : List C) (G : C → Prop) (o : C) : Prop where
  self : G o
  relies : ∀ v, G v → ∀ u ∈ (W.info v).relies, G u
  wmax : ∀ v, G v → ∀ w, InWmax W X cells v w → G w
  judges : ∀ v, G v → Evaluated W v → ∀ c, Judges W X v c → G c
  named : ∀ v, G v → Evaluated W v → ∀ w c, v ∈ (W.info w).attests → w ∈ cells → (X.verdict w).witness = some c → G c

/-- A change outside a goal's frame gives `Reads` on every evaluated cell of it. -/
theorem reads_of_outside {G Q : C → Prop} {o v : C} (hF : GFrame W X cells G o) (hQ : ∀ c, G c → ¬ Q c)
    (h : OutsideOnly W X X' cells cells' Q) (hv : G v) (he : Evaluated W v) : Reads W X X' cells cells' G v where
  verdict := h.verdict
  req := h.req
  expected := h.expected
  replay := h.replay
  live := fun c hc => h.live c (hQ c hc)
  self := hv
  judges := fun c hj => by
    have hc := hF.judges v hv he c hj
    exact ⟨h.mem c (hQ c hc), fun _ => ⟨hc, h.endorsers c (hQ c hc)⟩⟩
  named := fun w c ha hw hwc => hF.named v hv he w c ha hw hwc
  policy := Or.inr h.pol0

/-- **Silence outside the frames.** A change confined to a set that meets the frame of no goal leaves every goal's
`Settled` and `Grounded` as they were. -/
theorem silence_outside_reads (hext : QuorumExt W) {wmax wmax' : C → List C} {cnt cnt' : C → C → List K}
    (hw : WmaxFaithful W X cells wmax) (hc : CntFaithful W X cells cnt)
    (hw' : WmaxFaithful W X' cells' wmax') (hc' : CntFaithful W X' cells' cnt')
    {goals : List C} {G : C → C → Prop} {Q : C → Prop}
    (hF : ∀ o ∈ goals, GFrame W X cells (G o) o) (hQ : ∀ o ∈ goals, ∀ c, G o c → ¬ Q c)
    (h : OutsideOnly W X X' cells cells' Q) :
    ∀ o ∈ goals, Evaluated W o →
      (Settled W X wmax cnt o ↔ Settled W X' wmax' cnt' o) ∧
      (Grounded W X wmax cnt o ↔ Grounded W X' wmax' cnt' o) := by
  intro o ho he
  have hFo := hF o ho
  have hQo := hQ o ho
  refine ⟨settled_frame hext hw hc hw' hc' he (reads_of_outside hFo hQo h hFo.self he), ?_⟩
  exact grounded_frame hw hc hw' hc' (fun v hv => h.live v (hQo v hv)) hFo.relies
    (fun v hv => h.authorized v (hQo v hv)) hFo.wmax (fun v hv hev => reads_of_outside hFo hQo h hv hev) hFo.self

/-- **Silence by slack.** If the keys that count through a goal's witnesses other than `q` meet its policy, and those
witnesses and their keys are the same at both tips, then at each tip the goal is Settled exactly when it is live:
nothing that happens to `q` moves it, as long as the goal stays live. -/
theorem silence_by_quorum_slack (hq : QuorumMono W) {wmax wmax' : C → List C} {cnt cnt' : C → C → List K}
    {o q : C} (he : Evaluated W o) (hpol : evalPol W X o = evalPol W X' o)
    (hsame : ∀ w, w ≠ q → (w ∈ wmax o ↔ w ∈ wmax' o) ∧ ∀ k, (k ∈ cnt o w ↔ k ∈ cnt' o w))
    (hslack : W.quorum (((wmax o).filter fun w => decide (w ≠ q)).flatMap (cnt o)) (evalPol W X o) = true) :
    (Settled W X wmax cnt o ↔ Live X o) ∧ (Settled W X' wmax' cnt' o ↔ Live X' o) := by
  have hq1 : W.quorum ((wmax o).flatMap (cnt o)) (evalPol W X o) = true := by
    refine hq _ _ _ (fun k hk => ?_) hslack
    obtain ⟨w, hw, hkw⟩ := List.mem_flatMap.mp hk
    exact List.mem_flatMap.mpr ⟨w, (List.mem_filter.mp hw).1, hkw⟩
  have hq2 : W.quorum ((wmax' o).flatMap (cnt' o)) (evalPol W X' o) = true := by
    rw [← hpol]
    refine hq _ _ _ (fun k hk => ?_) hslack
    obtain ⟨w, hw, hkw⟩ := List.mem_flatMap.mp hk
    obtain ⟨hwo, hne⟩ := List.mem_filter.mp hw
    have hne' : w ≠ q := by simpa using hne
    exact List.mem_flatMap.mpr ⟨w, ((hsame w hne').1).mp hwo, ((hsame w hne').2 k).mp hkw⟩
  have key : ∀ (Y : Pass3In C K P) (wm : C → List C) (cn : C → C → List K),
      W.quorum ((wm o).flatMap (cn o)) (evalPol W Y o) = true → (Settled W Y wm cn o ↔ Live Y o) := by
    intro Y wm cn hqY
    unfold Settled
    rcases he with hs | hs | hs <;> simp only [hs] <;> exact ⟨fun h => h.1, fun h => ⟨h, hqY⟩⟩
  exact ⟨key X wmax cnt hq1, key X' wmax' cnt' hq2⟩

end Silence

end Vars1
