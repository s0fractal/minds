import Vars1.Grounded
import Vars1.Power

/-!
# Which single act changes a status (`minds_chain.py next`)

`why`, `what-if` and `power` answer about a cell someone names. `next` names the cells: for every act of one roster key
it can find (a new ACCEPT verdict, an INVALID verdict under a verifier id, a seal on a projection) it says which
statuses would change. These theorems are what its in-memory reading rests on; its answers are also held to the gate,
one act at a time (`test_vars1.py` 132).

* `countIn_cons`, `countIn_filter_ne` — a threshold policy counts the distinct members among the keys: one more key
  adds one exactly when it is a member not yet counted, and one fewer takes one exactly when it was.
* `decisive_endorser_iff` — **one endorsement decides a threshold quorum exactly at the margin**: it turns an unmet
  quorum into a met one iff the key is a member, is not yet counted, and the count is one short of the threshold.
* `decisive_withdrawal_iff` — and one withdrawal unmeets it iff the key is counted and the count equals the threshold.
* `decisive_settled_iff`, `decisive_unsettled_iff` — the same for Settled (§4.2 Pass 3), through `settled_iff_keys`:
  when the act changes the keys that count by that one key and nothing else the status reads.
* `grounded_mono` — **Grounded only grows with what counts**: if every live cell stays live, every authorization
  stays, the evaluator policies stay, and the witnesses and the keys they count only grow, every Grounded cell stays
  Grounded. So an endorsement can only add Grounded cells and a withdrawal only remove them (the same theorem, read
  the other way), and `next` reports gains and losses apart.
* `decisive_cascade_grounded` — a cell whose equation holds once `u` and what was Grounded before are given becomes
  Grounded when `u` does: one endorsement of a foundation grounds, at once, every cell that waited only for it.

What is not here: an act that latches an edge (Pass 1), which `next` evaluates through the gate, not in memory, and an
act of a coalition, which is `power`'s (`Power.lean`).
-/

set_option linter.unusedSectionVars false

namespace Vars1

section Count

variable {K : Type} [DecidableEq K]

/-- How many keys of `M` (a policy's members, without repetition) are among `E`. -/
def countIn : List K → List K → Nat
  | [], _ => 0
  | m :: M, E => (if m ∈ E then 1 else 0) + countIn M E

/-- One more key adds one exactly when it is a member not yet among `E`. -/
theorem countIn_cons {M : List K} (hM : M.Nodup) (k : K) (E : List K) :
    countIn M (k :: E) = countIn M E + (if k ∈ M ∧ k ∉ E then 1 else 0) := by
  induction M with
  | nil => simp [countIn]
  | cons m M ih =>
    have hm : m ∉ M := (List.nodup_cons.mp hM).1
    have ih := ih (List.nodup_cons.mp hM).2
    simp only [countIn, ih]
    by_cases hmk : m = k
    · subst hmk
      have h1 : m ∈ m :: E := List.mem_cons_self
      have h2 : m ∈ m :: M := List.mem_cons_self
      have h3 : ¬ (m ∈ M ∧ m ∉ E) := fun h => hm h.1
      rw [if_pos h1, if_neg h3]
      by_cases hE : m ∈ E
      · rw [if_pos hE, if_neg (fun h => h.2 hE)]
        omega
      · rw [if_neg hE, if_pos ⟨h2, hE⟩]
        omega
    · have h1 : (m ∈ k :: E) ↔ m ∈ E := by simp [hmk]
      have h2 : (k ∈ m :: M ∧ k ∉ E) ↔ (k ∈ M ∧ k ∉ E) := by
        have hk' : k ≠ m := fun h => hmk h.symm
        simp [hk']
      simp only [h1, h2]
      omega

/-- One fewer key takes one exactly when it was a member among `E`. -/
theorem countIn_filter_ne {M : List K} (hM : M.Nodup) (k : K) (E : List K) :
    countIn M (E.filter (fun x => x ≠ k)) + (if k ∈ M ∧ k ∈ E then 1 else 0) = countIn M E := by
  induction M with
  | nil => simp [countIn]
  | cons m M ih =>
    have hm : m ∉ M := (List.nodup_cons.mp hM).1
    have ih := ih (List.nodup_cons.mp hM).2
    simp only [countIn]
    by_cases hmk : m = k
    · subst hmk
      have hf : m ∉ E.filter (fun x => x ≠ m) := by simp
      have hz : ¬ (m ∈ M ∧ m ∈ E) := fun h => hm h.1
      rw [if_neg hz, Nat.add_zero] at ih
      rw [if_neg hf, ih]
      by_cases hE : m ∈ E
      · rw [if_pos ⟨List.mem_cons_self, hE⟩, if_pos hE]
        omega
      · rw [if_neg (fun h => hE h.2), if_neg hE]
        omega
    · have h1 : m ∈ E.filter (fun x => x ≠ k) ↔ m ∈ E := by simp [hmk]
      have h2 : (k ∈ m :: M ∧ k ∈ E) ↔ (k ∈ M ∧ k ∈ E) := by
        have hk' : k ≠ m := fun h => hmk h.symm
        simp [hk']
      simp only [h1, h2]
      omega

/-- **One endorsement decides a threshold quorum exactly at the margin.** -/
theorem decisive_endorser_iff {M : List K} (hM : M.Nodup) (thr : Nat) (k : K) (E : List K) :
    (¬ thr ≤ countIn M E ∧ thr ≤ countIn M (k :: E)) ↔ (k ∈ M ∧ k ∉ E ∧ countIn M E + 1 = thr) := by
  rw [countIn_cons hM]
  by_cases h : k ∈ M ∧ k ∉ E
  · rw [if_pos h]
    simp only [h.1, h.2, true_and, not_false_eq_true]
    -- `omega` on the whole iff would rest on Classical.choice; each direction does not
    exact ⟨fun ⟨h1, h2⟩ => by omega, fun h' => ⟨by omega, by omega⟩⟩
  · rw [if_neg h]
    constructor
    · intro ⟨h1, h2⟩; omega
    · intro ⟨h1, h2, _⟩; exact absurd ⟨h1, h2⟩ h

/-- **One withdrawal unmeets a threshold quorum exactly at the margin.** -/
theorem decisive_withdrawal_iff {M : List K} (hM : M.Nodup) (thr : Nat) (k : K) (E : List K) :
    (thr ≤ countIn M E ∧ ¬ thr ≤ countIn M (E.filter (fun x => x ≠ k))) ↔
      (k ∈ M ∧ k ∈ E ∧ countIn M E = thr) := by
  have hc := countIn_filter_ne hM k E
  by_cases h : k ∈ M ∧ k ∈ E
  · rw [if_pos h] at hc
    simp only [h.1, h.2, true_and]
    exact ⟨fun ⟨h1, h2⟩ => by omega, fun h' => ⟨by omega, by omega⟩⟩
  · rw [if_neg h, Nat.add_zero] at hc
    constructor
    · intro ⟨h1, h2⟩; omega
    · intro ⟨h1, h2, _⟩; exact absurd ⟨h1, h2⟩ h

end Count

section Settled

variable {C K P : Type} [DecidableEq C] [DecidableEq K]
variable {W : World C K P} {X X' : Pass3In C K P} {cells cells' : List C} {wmax wmax' : C → List C}
  {cnt cnt' : C → C → List K}

/-- A threshold policy: its quorum is met when at least `thr p` of its members `mem p` (no repetition) are among the
keys. -/
def ThresholdQuorum (W : World C K P) (thr : P → Nat) (mem : P → List K) : Prop :=
  (∀ p, (mem p).Nodup) ∧ ∀ (E : List K) (p : P), W.quorum E p = decide (thr p ≤ countIn (mem p) E)

theorem ThresholdQuorum.ext {thr : P → Nat} {mem : P → List K} (hT : ThresholdQuorum W thr mem) : QuorumExt W := by
  intro E E' p h
  have hc : ∀ M : List K, countIn M E = countIn M E' := by
    intro M
    induction M with
    | nil => rfl
    | cons m M ih => simp only [countIn, ih, h m]
  rw [hT.2, hT.2, hc]

/-- **An endorsement settles a contract or decision exactly at the margin.** If the act leaves the cell's standing and
its evaluator policy as they were, and adds the key `k` to the keys that count and nothing else, it turns the cell
Settled iff the cell is live, `k` is a member of the policy not yet counted, and the count is one short. -/
theorem decisive_settled_iff {thr : P → Nat} {mem : P → List K} (hT : ThresholdQuorum W thr mem)
    (hw : WmaxFaithful W X cells wmax) (hc : CntFaithful W X cells cnt)
    (hw' : WmaxFaithful W X' cells' wmax') (hc' : CntFaithful W X' cells' cnt')
    {v : C} (hs : (W.info v).schema = .contract ∨ (W.info v).schema = .decision)
    (hlive : Live X v ↔ Live X' v) (hpol : evalPol W X v = evalPol W X' v) {k : K} {E : List K}
    (hE : ∀ x, x ∈ E ↔ CountedKey W X cells v x) (hE' : ∀ x, x ∈ k :: E ↔ CountedKey W X' cells' v x) :
    (¬ Settled W X wmax cnt v ∧ Settled W X' wmax' cnt' v) ↔
      (Live X v ∧ k ∈ mem (evalPol W X v) ∧ k ∉ E ∧
        countIn (mem (evalPol W X v)) E + 1 = thr (evalPol W X v)) := by
  rw [settled_iff_keys hT.ext hw hc hs hE, settled_iff_keys hT.ext hw' hc' hs hE', ← hpol, ← hlive, hT.2, hT.2]
  have hd := decisive_endorser_iff (hT.1 (evalPol W X v)) (thr (evalPol W X v)) k E
  -- no case split on `Live X v`: it is a Prop with no decision procedure, and `by_cases` would rest on choice
  constructor
  · intro ⟨hn, hl, hq'⟩
    exact ⟨hl, hd.mp ⟨fun h => hn ⟨hl, decide_eq_true h⟩, of_decide_eq_true hq'⟩⟩
  · intro ⟨hl, hr⟩
    have ⟨hnot, hle⟩ := hd.mpr hr
    exact ⟨fun ⟨_, hq⟩ => hnot (of_decide_eq_true hq), hl, decide_eq_true hle⟩

/-- **A withdrawal unsettles a contract or decision exactly at the margin.** If the act leaves the standing and the
policy and takes the key `k` from the keys that count and nothing else, it turns a Settled cell not Settled iff the
cell is live, `k` is a member of the policy that was counted, and the count equals the threshold. -/
theorem decisive_unsettled_iff {thr : P → Nat} {mem : P → List K} (hT : ThresholdQuorum W thr mem)
    (hw : WmaxFaithful W X cells wmax) (hc : CntFaithful W X cells cnt)
    (hw' : WmaxFaithful W X' cells' wmax') (hc' : CntFaithful W X' cells' cnt')
    {v : C} (hs : (W.info v).schema = .contract ∨ (W.info v).schema = .decision)
    (hlive : Live X v ↔ Live X' v) (hpol : evalPol W X v = evalPol W X' v) {k : K} {E : List K}
    (hE : ∀ x, x ∈ E ↔ CountedKey W X cells v x)
    (hE' : ∀ x, x ∈ E.filter (fun y => y ≠ k) ↔ CountedKey W X' cells' v x) :
    (Settled W X wmax cnt v ∧ ¬ Settled W X' wmax' cnt' v) ↔
      (Live X v ∧ k ∈ mem (evalPol W X v) ∧ k ∈ E ∧ countIn (mem (evalPol W X v)) E = thr (evalPol W X v)) := by
  rw [settled_iff_keys hT.ext hw hc hs hE, settled_iff_keys hT.ext hw' hc' hs hE', ← hpol, ← hlive, hT.2, hT.2]
  have hd := decisive_withdrawal_iff (hT.1 (evalPol W X v)) (thr (evalPol W X v)) k E
  constructor
  · intro ⟨⟨hl, hq⟩, hn⟩
    exact ⟨hl, hd.mp ⟨of_decide_eq_true hq, fun h => hn ⟨hl, decide_eq_true h⟩⟩⟩
  · intro ⟨hl, hr⟩
    have ⟨hle, hnot⟩ := hd.mpr hr
    exact ⟨⟨hl, decide_eq_true hle⟩, fun ⟨_, hq⟩ => hnot (of_decide_eq_true hq)⟩

end Settled

section Grounded

variable {C K P : Type} [DecidableEq C] [DecidableEq K]
variable {W : World C K P} {X X' : Pass3In C K P} {wmax wmax' : C → List C} {cnt cnt' : C → C → List K}

/-- **Grounded only grows with what counts.** Read with the primed and unprimed tips exchanged, it says that an act
which only removes witnesses or counted keys only removes Grounded cells. -/
theorem grounded_mono (hlive : ∀ v, Live X v → Live X' v) (hauth : ∀ v, X.authorized v → X'.authorized v)
    (hpol : ∀ v, evalPol W X v = evalPol W X' v) (hw : ∀ v w, w ∈ wmax v → w ∈ wmax' v)
    (hc : ∀ v w k, k ∈ cnt v w → k ∈ cnt' v w) :
    Sub (Grounded W X wmax cnt) (Grounded W X' wmax' cnt') := by
  refine grounded_least W X wmax cnt _ (fun v ⟨hl, hr, hk⟩ => (grounded_fixed W X' wmax' cnt' v).mp ?_)
  refine ⟨hlive v hl, hr, ?_⟩
  cases hs : (W.info v).schema <;> simp only [hs] at hk ⊢
  case metaSchema => exact hauth v hk
  case scope => exact hauth v hk
  all_goals first
    | trivial
    | (obtain ⟨E, hq, hE⟩ := hk
       refine ⟨E, hpol v ▸ hq, fun k hk' => ?_⟩
       obtain ⟨w, hw', hg, hcw⟩ := hE k hk'
       exact ⟨w, hw v w hw', hg, hc v w k hcw⟩)

/-- **One foundation grounds every cell that waited only for it.** If the act only adds (as in `grounded_mono`), `u`
is Grounded after it, and each cell of `S` satisfies its equation once `u` and what was Grounded before are given,
every cell of `S` is Grounded after the act. -/
theorem decisive_cascade_grounded (hlive : ∀ v, Live X v → Live X' v) (hauth : ∀ v, X.authorized v → X'.authorized v)
    (hpol : ∀ v, evalPol W X v = evalPol W X' v) (hw : ∀ v w, w ∈ wmax v → w ∈ wmax' v)
    (hc : ∀ v w k, k ∈ cnt v w → k ∈ cnt' v w) {u : C} (hu : Grounded W X' wmax' cnt' u) {S : List C}
    (hS : ∀ d ∈ S, GΦ W X' wmax' cnt' (fun c => c = u ∨ Grounded W X wmax cnt c) d) :
    ∀ d ∈ S, Grounded W X' wmax' cnt' d := by
  have hsub : Sub (fun c => c = u ∨ Grounded W X wmax cnt c) (Grounded W X' wmax' cnt') := by
    intro c hc'
    rcases hc' with rfl | hg
    · exact hu
    · exact grounded_mono hlive hauth hpol hw hc c hg
  intro d hd
  exact (grounded_fixed W X' wmax' cnt' d).mp (GΦ_mono W X' wmax' cnt' _ _ hsub d (hS d hd))

end Grounded

end Vars1
