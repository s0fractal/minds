import Vars1.Pass1
import Vars1.Pass2
import Vars1.Pass3

/-!
# A witness checker for `Settled`, and its soundness (roadmap G7)

`experiments/witness/check.py` answers `HELD` for a term (a decision's cone and its endorsements) and argues in
prose that `HELD` implies `Settled`. Here the same positive part is a derivation that a checker written in Lean
checks, with a theorem: if `accepts` holds, the decision is `Settled` in the model of §4.2.

A derivation is a list of lines. Each names its rule, its conclusion and its premises; every premise is the
conclusion of an earlier line (the form of open-ontologies' `OOCert.horn_certificate_sound`).

* `stand c` concludes that `c` stands (`Live`): `c` is a local cell of the store, no cell of the store
  invalidates, retires or supersedes it, it supersedes nothing, and its premises are exactly that each cell it
  relies on stands.
* `endorse w k` concludes that key `k` endorses `w`: a seal of the store on the local cell `w`, under the scope
  cell, by `k`, a key of the scope's admission roster. No premises.
* `settle d` concludes that `d` is `Settled`: `d` is a contract or decision that requires no computation, no
  INVALID verdict of the store judges it, `d` stands, and the endorsements among its premises, each on a standing
  ATTESTED verdict with an empty witness slot that judges and attests `d`, count at least the threshold of `d`'s
  evaluator policy in distinct keys of that policy.

The negative part is read over the whole store (`Store.cells`): no kill edge, no INVALID verdict. That the store
is complete, the scope's admitted chain at the tip, is the reader's pin. It enters `witness_sound` as hypotheses
(`Pin`), with the faithfulness of the decode that read the store from bytes: hashes, cell layout and signatures are
checked by `check.py`, which emits the store and the derivation (`check.py --lean`), not here.
-/

set_option linter.unusedSectionVars false

namespace Vars1.Witness

open Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K] [DecidableEq P]

/-- What the decode read from the store at the tip: every cell of the store, the seals the derivation names
(each one's signature verified), the scope cell, and the policies with their thresholds and keys. -/
structure Store (C K P : Type) where
  cells : List C
  schema : C → Schema
  isLocal : C → Bool
  relies : C → List C
  attests : C → List C
  supersedes : C → List C
  retires : C → List C
  invalidates : C → List C
  payload : C → Option C
  customPol : C → Option P
  verdict : C → VerdictInfo C
  req : C → Option Nat
  seals : List (Seal C K)
  scope : C
  /-- The scope cell's `slots[0]`: the admission roster, and the evaluator policy of a decision with none. -/
  pol0 : P
  pols : List P
  keys : P → List K
  thr : P → Nat

inductive Rule where
  | stand | endorse | settle
  deriving DecidableEq, Repr

inductive Concl (C K : Type) where
  | stands (c : C)
  | endorsed (w : C) (k : K)
  | settled (d : C)
  deriving DecidableEq, Repr

structure Line (C K : Type) where
  rule : Rule
  concl : Concl C K
  prem : List (Concl C K)

variable (S : Store C K P)

/-- Some cell of the store invalidates, retires or supersedes `c`. -/
def killed (c : C) : Bool :=
  S.cells.any fun x => decide (c ∈ S.invalidates x) || decide (c ∈ S.retires x) || decide (c ∈ S.supersedes x)

/-- An INVALID verdict of the store judges `d`. -/
def judgedInvalid (d : C) : Bool :=
  S.cells.any fun b => decide (S.schema b = .verdict) && decide (S.payload b = some d) && (S.verdict b).invalid

/-- `EvalPol(d)` as the store gives it. -/
def evalPol (d : C) : P := (S.customPol d).getD S.pol0

def standOK (c : C) (prem : List (Concl C K)) : Bool :=
  decide (c ∈ S.cells) && S.isLocal c && (S.supersedes c).isEmpty && !killed S c &&
    decide (prem = (S.relies c).map .stands)

def endorseOK (w : C) (k : K) (prem : List (Concl C K)) : Bool :=
  prem.isEmpty && decide (w ∈ S.cells) && S.isLocal w && decide (k ∈ S.keys S.pol0) &&
    S.seals.any fun s => decide (s.target = w) && decide (s.ctx = S.scope) && decide (s.key = k)

/-- An endorsement premise `endorsed w k` of `settle d`: `w` stands among the premises and is an ATTESTED verdict
with an empty witness slot that judges and attests `d`, and `k` is a key of `d`'s evaluator policy. -/
def countsFor (d : C) (prem : List (Concl C K)) (w : C) (k : K) : Bool :=
  decide (Concl.stands w ∈ prem) && decide (S.schema w = .verdict) && decide (S.payload w = some d) &&
    decide (d ∈ S.attests w) && (S.verdict w).attested && decide ((S.verdict w).witness = none) &&
    decide (k ∈ S.keys (evalPol S d))

/-- The keys of the endorsement premises. -/
def endorsedKeys : List (Concl C K) → List K
  | [] => []
  | .endorsed _ k :: ps => k :: endorsedKeys ps
  | _ :: ps => endorsedKeys ps

/-- A list without repeats. -/
def dedup : List K → List K
  | [] => []
  | k :: ks => if k ∈ dedup ks then dedup ks else k :: dedup ks

def settleOK (d : C) (prem : List (Concl C K)) : Bool :=
  decide (d ∈ S.cells) && (decide (S.schema d = .decision) || decide (S.schema d = .contract)) &&
    decide (S.req d = none) && !judgedInvalid S d && decide (Concl.stands d ∈ prem) &&
    decide (evalPol S d ∈ S.pols) &&
    prem.all (fun p => match p with
      | .endorsed w k => countsFor S d prem w k
      | _ => true) &&
    decide (S.thr (evalPol S d) ≤ (dedup (endorsedKeys prem)).length)

def lineOK (done : List (Concl C K)) (l : Line C K) : Bool :=
  l.prem.all (· ∈ done) &&
    match l.rule, l.concl with
    | .stand, .stands c => standOK S c l.prem
    | .endorse, .endorsed w k => endorseOK S w k l.prem
    | .settle, .settled d => settleOK S d l.prem
    | _, _ => false

/-- Check the lines in order; `done` holds the conclusions so far. -/
def run (done : List (Concl C K)) : List (Line C K) → Option (List (Concl C K))
  | [] => some done
  | l :: ls => if lineOK S done l then run (l.concl :: done) ls else none

/-- The checker: every line checks, and one concludes that `d` is settled. -/
def accepts (lines : List (Line C K)) (d : C) : Bool :=
  match run S [] lines with
  | some done => decide (Concl.settled d ∈ done)
  | none => false

/-! ## What a conclusion means in the model -/

/-- The reader's pin and the decode, as hypotheses on the model at the tip. `W`, `AE`, the Pass 1 predicates and
`X` are the model's own reading of the scope's admitted chain; `S` is what the decode read from its bytes.

* The decode is faithful: on every cell of the store, `W` and `X` agree with `S` on the fields the checker reads
  (a payload as far as it names a cell of the store; of a verdict, whether it is ATTESTED, whether INVALID and
  whether its witness slot is empty; of a contract or decision, whether it requires a computation); a cell is
  `Present` exactly when the store holds it; a decoded policy meets its quorum with threshold many distinct keys
  of it.
* The store at the tip is the admitted chain: the Pass 1 equations hold (`IsPass1`); an edge latches only from a
  present cell (`edge_present` proves it of the fold); `X.active` is Pass 1 `Active`; `X.stale` satisfies the
  Pass 2 equation (`stale_pin` proves it of `Stale`); and a verified seal under the scope cell, by a key of the
  admission roster, on a local cell counts among that cell's cumulative endorsers (§4.1). -/
structure Pin (W : World C K P) (AE : C → C → Kind → Bool) (Present isIntrinsic : C → Prop)
    (Auth : C → Bool) (Inv Eff Ret Acc : C → Prop) (X : Pass3In C K P) : Prop where
  schema : ∀ c ∈ S.cells, (W.info c).schema = S.schema c
  isLocal : ∀ c ∈ S.cells, (W.info c).isLocal = S.isLocal c
  relies : ∀ c ∈ S.cells, (W.info c).relies = S.relies c
  attests : ∀ c ∈ S.cells, (W.info c).attests = S.attests c
  supersedes : ∀ c ∈ S.cells, (W.info c).supersedes = S.supersedes c
  retires : ∀ c ∈ S.cells, (W.info c).retires = S.retires c
  invalidates : ∀ c ∈ S.cells, (W.info c).invalidates = S.invalidates c
  payload : ∀ c ∈ S.cells, ∀ d ∈ S.cells, (W.info c).payload = some d ↔ S.payload c = some d
  customPol : ∀ c ∈ S.cells, (W.info c).customPol = S.customPol c
  verdict : ∀ c ∈ S.cells, S.schema c = .verdict → (X.verdict c).attested = (S.verdict c).attested ∧
    (X.verdict c).invalid = (S.verdict c).invalid ∧ ((X.verdict c).witness = none ↔ (S.verdict c).witness = none)
  req : ∀ c ∈ S.cells, (S.schema c = .decision ∨ S.schema c = .contract) → (X.req c = none ↔ S.req c = none)
  scope : X.scopeTip = S.scope
  pol0 : (W.info S.scope).pol0 = S.pol0
  present : ∀ c, Present c ↔ c ∈ S.cells
  quorum : ∀ p ∈ S.pols, ∀ (E ks : List K), (∀ k ∈ ks, k ∈ E) → ks.Nodup → (∀ k ∈ ks, k ∈ S.keys p) →
    S.thr p ≤ ks.length → W.quorum E p = true
  pass1 : IsPass1 W AE Present isIntrinsic Auth Inv Eff Ret Acc
  edgeFrom : ∀ w v k, AE w v k = true → Present w
  active : ∀ c, X.active c ↔ Active W AE Eff Acc Ret c
  stale : ∀ v, X.stale v → (∃ d ∈ (W.info v).relies, ¬ X.active d ∨ X.stale d) ∨ (W.info v).isLocal = false
  cumulative : ∀ s ∈ S.seals, s.ctx = S.scope → S.isLocal s.target = true → s.key ∈ S.keys S.pol0 →
    s.key ∈ X.cumulative s.target

variable (W : World C K P) (X : Pass3In C K P) (wmax : C → List C)

/-- What each conclusion asserts of the model. -/
def Holds : Concl C K → Prop
  | .stands c => c ∈ S.cells ∧ Live X c
  | .endorsed w k => k ∈ witnessEndorsers W X w
  | .settled d => Settled W X wmax d

/-! ## Lemmas on the checker's lists -/

theorem mem_dedup {k : K} : ∀ {ks : List K}, k ∈ dedup ks ↔ k ∈ ks
  | [] => by simp [dedup]
  | j :: ks => by
    have ih := @mem_dedup k ks
    by_cases h : j ∈ dedup ks
    · simp only [dedup, h, if_true, ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | hk)
        · exact ih.mp h
        · exact hk
    · simp [dedup, h, ih]

theorem nodup_dedup : ∀ (ks : List K), (dedup ks).Nodup
  | [] => List.nodup_nil
  | j :: ks => by
    by_cases h : j ∈ dedup ks
    · simp only [dedup, h, if_true]; exact nodup_dedup ks
    · simp only [dedup, h, if_false]; exact List.nodup_cons.mpr ⟨h, nodup_dedup ks⟩

theorem mem_endorsedKeys {k : K} : ∀ {ps : List (Concl C K)}, k ∈ endorsedKeys ps → ∃ w, Concl.endorsed w k ∈ ps
  | [] => by simp [endorsedKeys]
  | .endorsed w j :: ps => by
    intro h
    simp only [endorsedKeys, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨w, List.mem_cons_self⟩
    · obtain ⟨w', hw'⟩ := mem_endorsedKeys h
      exact ⟨w', List.mem_cons_of_mem _ hw'⟩
  | .stands _ :: ps => by
    intro h
    obtain ⟨w', hw'⟩ := mem_endorsedKeys (ps := ps) h
    exact ⟨w', List.mem_cons_of_mem _ hw'⟩
  | .settled _ :: ps => by
    intro h
    obtain ⟨w', hw'⟩ := mem_endorsedKeys (ps := ps) h
    exact ⟨w', List.mem_cons_of_mem _ hw'⟩

/-! ## Soundness, line by line -/

section Sound

variable {S W X wmax}
variable {AE : C → C → Kind → Bool} {Present isIntrinsic : C → Prop} {Auth : C → Bool}
  {Inv Eff Ret Acc : C → Prop}

theorem not_killed {c x : C} (hk : killed S c = false) (hx : x ∈ S.cells) :
    c ∉ S.invalidates x ∧ c ∉ S.retires x ∧ c ∉ S.supersedes x := by
  have := List.any_eq_false.mp hk x hx
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- A `stand` line's checks make its cell `Active`. -/
theorem active_of_stand (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {c : C}
    (hc : c ∈ S.cells) (hl : S.isLocal c = true) (hs : S.supersedes c = []) (hk : killed S c = false) :
    Active W AE Eff Acc Ret c := by
  have h1 := pin.pass1
  have eff_present : ∀ w, Eff w → w ∈ S.cells := fun w hw => (pin.present w).mp ((h1.eff_eq w).mp hw).1
  have hinv : ¬ Inv c := by
    intro hi
    obtain ⟨w, hw, -, hcw, -⟩ := (h1.inv_eq c).mp hi
    have hwc := eff_present w hw
    exact (not_killed hk hwc).1 (pin.invalidates w hwc ▸ hcw)
  refine ⟨(h1.eff_eq c).mpr ⟨(pin.present c).mpr hc, hinv⟩, ?_, ?_, ?_, ?_⟩
  · intro hr
    obtain ⟨w, hw, -, hcw, -⟩ := (h1.ret_eq c).mp hr
    have hwc := eff_present w hw
    exact (not_killed hk hwc).2.1 (pin.retires w hwc ▸ hcw)
  · intro hsup
    cases hsup with
    | direct hcw _ hw _ =>
      have hwc := eff_present _ hw
      exact (not_killed hk hwc).2.2 (pin.supersedes _ hwc ▸ hcw)
    | trans hcw hae _ =>
      have hwc := (pin.present _).mp (pin.edgeFrom _ _ _ hae)
      exact (not_killed hk hwc).2.2 (pin.supersedes _ hwc ▸ hcw)
  · exact (h1.acc_eq c).mpr (Or.inr (Or.inl (pin.isLocal c hc ▸ hl)))
  · intro u hu
    rw [pin.supersedes c hc, hs] at hu
    exact absurd hu (List.not_mem_nil)

/-- A `stand` line whose premises hold concludes a cell that stands. -/
theorem stand_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {c : C}
    {prem : List (Concl C K)} (hok : standOK S c prem = true)
    (hprem : ∀ p ∈ prem, Holds S W X wmax p) : Holds S W X wmax (.stands c) := by
  simp only [standOK, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨hc, hl⟩, hs⟩, hk⟩, hp⟩ := hok
  have hact := active_of_stand pin hc hl hs hk
  refine ⟨hc, (pin.active c).mpr hact, ?_⟩
  intro hst
  rcases pin.stale c hst with ⟨d, hd, hdead⟩ | hnl
  · rw [pin.relies c hc] at hd
    have : Holds S W X wmax (.stands d) := hprem _ (hp ▸ List.mem_map_of_mem hd)
    obtain ⟨-, hda, hds⟩ := this
    rcases hdead with h | h
    · exact h hda
    · exact hds h
  · rw [pin.isLocal c hc, hl] at hnl
    exact Bool.noConfusion hnl

/-- An `endorse` line concludes a key among the verdict's endorsers. -/
theorem endorse_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {w : C} {k : K}
    {prem : List (Concl C K)} (hok : endorseOK S w k prem = true) : Holds S W X wmax (.endorsed w k) := by
  simp only [endorseOK, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hok
  obtain ⟨⟨⟨⟨-, hw⟩, hl⟩, hroster⟩, s, hs, ⟨⟨ht, hctx⟩, hkey⟩⟩ := hok
  show k ∈ witnessEndorsers W X w
  unfold witnessEndorsers
  rw [pin.isLocal w hw, hl, if_pos rfl]
  have := pin.cumulative s hs hctx (ht ▸ hl) (hkey ▸ hroster)
  rw [ht, hkey] at this
  exact this

/-- A `settle` line whose premises hold concludes `Settled`. -/
theorem settle_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X)
    (hwmax : WmaxFaithful W X S.cells wmax) {d : C} {prem : List (Concl C K)}
    (hok : settleOK S d prem = true) (hprem : ∀ p ∈ prem, Holds S W X wmax p) :
    Holds S W X wmax (.settled d) := by
  simp only [settleOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hd, hsch⟩, hreq⟩, hinv⟩, hsd⟩, hpol⟩, hall⟩, hthr⟩ := hok
  have hlive : Live X d := (hprem _ hsd).2
  have hep : Vars1.evalPol W X d = Witness.evalPol S d := by
    unfold Vars1.evalPol Witness.evalPol
    rw [pin.schema d hd, pin.customPol d hd, pin.scope, pin.pol0]
    rcases hsch with h | h <;> rw [h]
  -- every endorsement premise is on a verdict of `W_max(d)`
  have hcount : ∀ w k, Concl.endorsed w k ∈ prem → k ∈ (wmax d).flatMap (witnessEndorsers W X) ∧
      k ∈ S.keys (Witness.evalPol S d) := by
    intro w k hmem
    have hc := hall _ hmem
    simp only [countsFor, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨hsw, hvw⟩, hpw⟩, haw⟩, hatt⟩, hwit⟩, hkey⟩ := hc
    obtain ⟨hw, hlw⟩ := hprem _ hsw
    have hin : InWmax W X S.cells d w := by
      refine ⟨hw, hlw, pin.attests w hw ▸ haw, ?_⟩
      have hctr : ¬ Contradicted W X S.cells d w := by
        rintro ⟨b, hb, -, hbv, hbp, hbi, -⟩
        have : judgedInvalid S d = true := by
          simp only [judgedInvalid, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
          have hbs : S.schema b = .verdict := pin.schema b hb ▸ hbv
          refine ⟨b, hb, ⟨hbs, (pin.payload b hb d hd).mp hbp⟩, ?_⟩
          rw [← (pin.verdict b hb hbs).2.1]
          exact hbi
        rw [hinv] at this
        exact Bool.noConfusion this
      have hrest : (W.info w).schema = .verdict ∧ (W.info w).payload = some d ∧
          (match X.req d with
           | none => (X.verdict w).witness = none ∧ (X.verdict w).attested = true
           | some _ => (X.verdict w).replayed = true ∧
               ∃ c, (X.verdict w).witness = some c ∧ Live X c ∧ X.replayOK c d) := by
        refine ⟨pin.schema w hw ▸ hvw, (pin.payload w hw d hd).mpr hpw, ?_⟩
        rw [(pin.req d hd hsch).mpr hreq]
        exact ⟨(pin.verdict w hw hvw).2.2.mpr hwit, (pin.verdict w hw hvw).1 ▸ hatt⟩
      rw [pin.schema d hd]
      rcases hsch with h | h <;> rw [h] <;> exact ⟨hctr, hrest⟩
    exact ⟨List.mem_flatMap.mpr ⟨w, (hwmax d w).mpr hin, (hprem _ hmem)⟩, hkey⟩
  have hq : W.quorum ((wmax d).flatMap (witnessEndorsers W X)) (Vars1.evalPol W X d) = true := by
    rw [hep]
    refine pin.quorum _ hpol _ (dedup (endorsedKeys prem)) ?_ (nodup_dedup _) ?_ hthr
    · intro k hk
      obtain ⟨w, hw⟩ := mem_endorsedKeys (mem_dedup.mp hk)
      exact (hcount w k hw).1
    · intro k hk
      obtain ⟨w, hw⟩ := mem_endorsedKeys (mem_dedup.mp hk)
      exact (hcount w k hw).2
  show Settled W X wmax d
  refine ⟨hlive, ?_⟩
  rw [pin.schema d hd]
  rcases hsch with h | h <;> rw [h] <;> exact hq

/-- Every conclusion of a checked prefix holds. -/
theorem run_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X)
    (hwmax : WmaxFaithful W X S.cells wmax) :
    ∀ (lines : List (Line C K)) (done out : List (Concl C K)), run S done lines = some out →
      (∀ p ∈ done, Holds S W X wmax p) → ∀ p ∈ out, Holds S W X wmax p
  | [], done, out, h, hd => by
    simp only [run, Option.some.injEq] at h
    exact h ▸ hd
  | l :: ls, done, out, h, hd => by
    simp only [run] at h
    split at h
    · rename_i hl
      apply run_sound pin hwmax ls _ out h
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simp only [lineOK, Bool.and_eq_true, List.all_eq_true] at hl
        obtain ⟨hpre, hrule⟩ := hl
        have hprem : ∀ q ∈ l.prem, Holds S W X wmax q := fun q hq => hd q (by simpa using hpre q hq)
        obtain ⟨rule, concl, prem⟩ := l
        cases rule <;> cases concl <;> simp only at hrule hprem ⊢
        · exact stand_sound pin hrule hprem
        · exact absurd hrule (by decide)
        · exact absurd hrule (by decide)
        · exact absurd hrule (by decide)
        · exact endorse_sound pin hrule
        · exact absurd hrule (by decide)
        · exact absurd hrule (by decide)
        · exact absurd hrule (by decide)
        · exact settle_sound pin hwmax hrule hprem
      · exact hd p hp
    · exact absurd h (by simp)

/-- **Soundness of the witness checker.** If `accepts` holds for a derivation, the decision is `Settled` in the
model of §4.2 at the tip, for every reading `W`, `X` of the scope's admitted chain that the decode `S` agrees
with (`Pin`), and every faithful presentation of `W_max`. -/
theorem witness_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X)
    (hwmax : WmaxFaithful W X S.cells wmax) {lines : List (Line C K)} {d : C}
    (h : accepts S lines d = true) : Settled W X wmax d := by
  unfold accepts at h
  split at h
  · rename_i out hrun
    exact run_sound pin hwmax lines [] out hrun (by simp) _ (by simpa using h)
  · exact absurd h (by decide)

end Sound

/-! ## Two of the pin's hypotheses hold of the model's passes -/

/-- Pass 2 `Stale` satisfies the equation `Pin.stale` asks of `X.stale`. -/
theorem stale_pin {N : Nat} (I : Pass2In N) (v : Fin N) (h : Stale I v) :
    (∃ d ∈ I.relies v, ¬ I.active d ∨ Stale I d) ∨ ¬ I.isLocal v := by
  rcases ((stale_fixed I v).mp h).2 with h | ⟨hl, -⟩
  · exact Or.inl h
  · exact Or.inr hl

/-- An edge latches only from a present cell: true of the fold of §4.1 whenever it is true of its start. -/
theorem edge_present (W : World C K P) :
    ∀ (cs : List (Commit C K)) (s0 : St C K), (∀ w v k, s0.edge w v k = true → w ∈ s0.present) →
      ∀ w v k, (Vars1.run W s0 cs).edge w v k = true → w ∈ (Vars1.run W s0 cs).present
  | [], s0, h0 => by simpa [Vars1.run] using h0
  | cm :: cs, s0, h0 => by
    have h1 : ∀ w v k, (step W s0 cm).edge w v k = true → w ∈ (step W s0 cm).present := by
      intro w v k he
      simp only [step, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at he ⊢
      rcases he with he | ⟨⟨hw, -⟩, -⟩
      · exact List.mem_append_left _ (h0 w v k he)
      · exact hw
    have := edge_present W cs (step W s0 cm) h1
    simpa [Vars1.run, List.foldl] using this

end Vars1.Witness
