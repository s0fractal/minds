import Vars1.Pass1
import Vars1.Pass2
import Vars1.Pass3
import Vars1.Grounded

/-!
# A witness checker for `Settled`, and its soundness (roadmap G7)

`experiments/witness/check.py` answers `HELD` for a term (a decision's cone and its endorsements) and argues in
prose that `HELD` implies `Settled`. Here the same term is a derivation that a checker written in Lean checks, with a
theorem: if `accepts` holds, the decision is `Settled` in the model of §4.2.

A derivation is a list of lines. Each names its rule, its conclusion and its premises; every premise is the
conclusion of an earlier line (the form of open-ontologies' `OOCert.horn_certificate_sound`). The rules come in two
strata. The first reads edges and Pass 1:

* `latch y x k` concludes that the edge `y → x` of kind `k` latched (§4.1 latch 3): a quorum of `Pol(x)`, under one
  of the scope cells that governed, seals `y`. No premises.
* `unlatched y x k` concludes that it did not: under no scope cell that governed do the seals on `y` meet `Pol(x)`,
  and the author clause cannot apply (the edge is an invalidates edge, `x`'s author may not evict it, or no key that
  seals `y` seals `x`). No premises. The author clause reads `InitialEndorsers(x)`, fixed at `x`'s birth, which the
  store at the tip does not show: "no key seals both" over-reads it, so an edge some key of `x` shares with `y` and
  whose quorum fails is neither latched nor unlatched here.
* `dead x` concludes `Invalidated(x)`: an Effective local killer (not a verdict, or an INVALID one) invalidates `x`
  by an edge that latched.
* `eff y` concludes `Effective(y)`: `y` is present, and every cell that invalidates it is a verdict that is not
  INVALID, is `dead`, or its edge is `unlatched`.
* `unsup w` concludes that `w` is not `Superseded`: every cell that supersedes it does so by an `unlatched` edge, or is
  `dead` and itself `unsup`.
* `down b` concludes that `b` is not live (`¬ Active ∨ Stale`): it is `dead`, or it relies on a cell that is `down`.

The second reads Passes 2 and 3:

* `stand c` concludes that `c` stands (`Live`): `c` is a local cell of the store, `eff c`, `unsup c`, every cell that
  retires it is `dead` or retires it by an `unlatched` edge, every supersedes edge of `c` is `latch`ed (a rebinding),
  and each cell it relies on stands.
* `endorse w k` concludes that key `k` endorses `w`: a seal of the store on the local cell `w`, under one of the
  scope cells that governed the chain (`ctxs`: the scope at the tip and each one it supersedes back to the genesis),
  by `k`, a key of that scope's admission roster. No premises.
* `settle d` concludes that `d` is `Settled`: `d` is a contract or decision that requires no computation, `d`
  stands, and the endorsements among its premises, each on a standing ATTESTED verdict with an empty witness slot
  that judges and attests `d`, by a key of `d`'s evaluator policy that no INVALID verdict of the store withdraws,
  count at least the policy's threshold in distinct keys. An INVALID verdict on `d` withdraws a key's endorsement
  through `w` when it is under `w`'s verifier id and the key seals it (`withdraws`), as §4.2 Pass 3 does for a live
  one; it withdraws nothing here when a premise proves it `down`.

What is read over the whole store (`Store.cells`) is what no premise can name: the cells that invalidate, retire or
supersede a cell, the INVALID verdicts on a decision, the seals on a cell. That the store is complete, the scope's
admitted chain at the tip, is the reader's pin. It enters `witness_sound` as hypotheses (`Pin`), with the
faithfulness of the decode that read the store from bytes: hashes, cell layout and signatures are checked by
`check.py`, which emits the store and the derivation (`check.py --lean`), not here. The seals an INVALID verdict
carries and the seals on an edge's source are part of the negative part: the decode writes all of them
(`Pin.invalidSeals`, `Pin.unlatch`).
-/

set_option linter.unusedSectionVars false

namespace Vars1.Witness

open Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K] [DecidableEq P]

/-- What the decode read from the store at the tip: every cell of the store, the seals it wrote (each one's signature
verified), the scope cell governing at the tip, the scope cells that governed before it, and the policies with their
thresholds and keys. -/
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
  /-- A contract or decision whose tier is owner (`slots[0] = H_OWNER`): its `Pol` is the admission policy. -/
  ownerPol : C → Bool
  verdict : C → VerdictInfo C
  req : C → Option Nat
  seals : List (Seal C K)
  scope : C
  /-- The scope cell's `slots[0]`: the admission roster, and the evaluator policy of a decision with none. -/
  pol0 : P
  /-- The scope cells that governed some commit of the chain, the tip's included, each with its admission roster
  (`slots[0]`): a seal under one of them, by a key of its roster, was admitted while it governed. -/
  ctxs : List (C × P)
  pols : List P
  keys : P → List K
  thr : P → Nat

inductive Rule where
  | stand | endorse | settle | latch | unlatch | dead | eff | unsup | down | ground
  deriving DecidableEq, Repr

inductive Concl (C K : Type) where
  | stands (c : C)
  | endorsed (w : C) (k : K)
  | settled (d : C)
  | latch (y x : C) (k : Kind)
  | unlatched (y x : C) (k : Kind)
  | dead (x : C)
  | eff (y : C)
  | unsup (w : C)
  | down (b : C)
  | grounded (d : C)
  deriving DecidableEq, Repr

/-- The rule that draws each kind of conclusion. -/
def Concl.rule {C K : Type} : Concl C K → Rule
  | .stands _ => .stand
  | .endorsed _ _ => .endorse
  | .settled _ => .settle
  | .latch _ _ _ => .latch
  | .unlatched _ _ _ => .unlatch
  | .dead _ => .dead
  | .eff _ => .eff
  | .unsup _ => .unsup
  | .down _ => .down
  | .grounded _ => .ground

structure Line (C K : Type) where
  rule : Rule
  concl : Concl C K
  prem : List (Concl C K)

/-- A list without repeats. -/
def dedup : List K → List K
  | [] => []
  | k :: ks => if k ∈ dedup ks then dedup ks else k :: dedup ks

variable (S : Store C K P)

/-! ## What the rules read from the store -/

/-- The edges of `y` of kind `k`. -/
def edgesOf (y : C) : Kind → List C
  | .supersedes => S.supersedes y
  | .retires => S.retires y
  | .invalidates => S.invalidates y

/-- The keys of the store's seals on `y` under the scope cell `cp.1`, by keys of its admission roster `cp.2`. -/
def sealers (y : C) (cp : C × P) : List K :=
  (S.seals.filter fun s => decide (s.target = y) && decide (s.ctx = cp.1) && decide (s.key ∈ S.keys cp.2)).map
    (·.key)

/-- `Pol(x)` while the scope cell `cp` governed (§4.1's table; the acceptance row is not read here). -/
def polAt (cp : C × P) (x : C) : P :=
  match S.schema x with
  | .contract | .decision => if S.ownerPol x then cp.2 else (S.customPol x).getD cp.2
  | .question => (S.customPol x).getD cp.2
  | _ => cp.2

/-- `AuthorCanEvict(x)` (§4.1's table). -/
def canEvict (x : C) : Bool :=
  match S.schema x with
  | .scope => false
  | .contract | .decision => !S.ownerPol x
  | _ => true

/-- The number of distinct keys of `p` among `ks`. -/
def count (ks : List K) (p : P) : Nat := (dedup (ks.filter fun k => decide (k ∈ S.keys p))).length

/-- The seals on `y` under `cp` meet `Pol(x)`. -/
def meets (y : C) (cp : C × P) (x : C) : Bool :=
  decide (S.thr (polAt S cp x) ≤ count S (sealers S y cp) (polAt S cp x))

/-- The edge `y → x` of kind `k` latched by quorum, under a scope cell that governed. Not read for a scope cell's or a
schema cell's edges, which the gate latches otherwise, nor for an edge to an acceptance cell, counted with the
acceptance roster. -/
def latchOK (y x : C) (k : Kind) : Bool :=
  decide (y ∈ S.cells) && decide (x ∈ edgesOf S y k) && decide (S.schema y ≠ .scope) &&
    decide (S.schema y ≠ .metaSchema) && decide (S.schema x ≠ .acceptance) &&
    S.ctxs.any fun cp => decide (polAt S cp x ∈ S.pols) && meets S y cp x

/-- Some key seals both `y` and `x`, each under a scope cell that governed and as a key of its roster. -/
def shared (y x : C) : Bool :=
  S.ctxs.any fun cp => (sealers S y cp).any fun e => S.ctxs.any fun cq => decide (e ∈ sealers S x cq)

/-- The edge `y → x` of kind `k` did not latch: under no scope cell that governed do the seals on `y` meet `Pol(x)`,
and the author clause cannot apply. -/
def unlatchedOK (y x : C) (k : Kind) : Bool :=
  decide (y ∈ S.cells) && decide (x ∈ S.cells) && decide (S.schema y ≠ .scope) && decide (S.schema x ≠ .acceptance) &&
    (S.ctxs.all fun cp => decide (polAt S cp x ∈ S.pols) && !meets S y cp x) &&
    (decide (k = .invalidates) || !canEvict S x || !S.isLocal x || !shared S y x)

/-- A verdict that is not INVALID: its invalidates edges count for nothing (§4.2 Pass 1). -/
def nonInv (w : C) : Bool := decide (S.schema w = .verdict) && !(S.verdict w).invalid

/-- A seal of the store on `b` by `k`, under a scope cell that governed, by a key of that scope's admission roster. -/
def sealedBy (b : C) (k : K) : Bool :=
  S.ctxs.any fun cp => decide (k ∈ S.keys cp.2) &&
    S.seals.any fun s => decide (s.target = b) && decide (s.ctx = cp.1) && decide (s.key = k)

/-- `b` may withdraw `k`'s endorsement of `d` through `w`: it is an INVALID verdict on `d` under `w`'s verifier id,
and `k` seals it, or it is foreign, whose endorsers the store does not show. -/
def withdraws (d w : C) (k : K) (b : C) : Bool :=
  decide (S.schema b = .verdict) && decide (S.payload b = some d) && (S.verdict b).invalid &&
    decide ((S.verdict b).verifier = (S.verdict w).verifier) && (!S.isLocal b || sealedBy S b k)

/-- `EvalPol(d)` as the store gives it. -/
def evalPol (d : C) : P := (S.customPol d).getD S.pol0

/-! ## The rules -/

def standOK (c : C) (prem : List (Concl C K)) : Bool :=
  decide (c ∈ S.cells) && S.isLocal c && decide (Concl.eff c ∈ prem) && decide (Concl.unsup c ∈ prem) &&
    (S.cells.all fun w => !decide (c ∈ S.retires w) || decide (Concl.dead w ∈ prem) ||
      decide (Concl.unlatched w c .retires ∈ prem)) &&
    ((S.supersedes c).all fun u => decide (Concl.latch c u .supersedes ∈ prem)) &&
    ((S.relies c).all fun r => decide (Concl.stands r ∈ prem))

def endorseOK (w : C) (k : K) (prem : List (Concl C K)) : Bool :=
  prem.isEmpty && decide (w ∈ S.cells) && S.isLocal w &&
    S.ctxs.any fun cp => decide (k ∈ S.keys cp.2) &&
      S.seals.any fun s => decide (s.target = w) && decide (s.ctx = cp.1) && decide (s.key = k)

def effOK (y : C) (prem : List (Concl C K)) : Bool :=
  decide (y ∈ S.cells) && S.cells.all fun w => !decide (y ∈ S.invalidates w) || nonInv S w ||
    decide (Concl.unlatched w y .invalidates ∈ prem) || decide (Concl.dead w ∈ prem)

def deadOK (x : C) (prem : List (Concl C K)) : Bool :=
  S.cells.any fun y => decide (x ∈ S.invalidates y) && S.isLocal y && !nonInv S y &&
    decide (Concl.latch y x .invalidates ∈ prem) && decide (Concl.eff y ∈ prem)

def unsupOK (w : C) (prem : List (Concl C K)) : Bool :=
  S.cells.all fun u => !decide (w ∈ S.supersedes u) || decide (Concl.unlatched u w .supersedes ∈ prem) ||
    (decide (Concl.dead u ∈ prem) && decide (Concl.unsup u ∈ prem))

def downOK (b : C) (prem : List (Concl C K)) : Bool :=
  decide (Concl.dead b ∈ prem) || (decide (b ∈ S.cells) && (S.relies b).any fun r => decide (Concl.down r ∈ prem))

/-- An endorsement premise `endorsed w k` of `settle d`: `w` stands among the premises and is an ATTESTED verdict
with an empty witness slot that judges and attests `d`, `k` is a key of `d`'s evaluator policy, and every INVALID
verdict of the store that may withdraw it (`withdraws`) is proved `down` by a premise. -/
def countsFor (d : C) (prem : List (Concl C K)) (w : C) (k : K) : Bool :=
  decide (Concl.stands w ∈ prem) && decide (S.schema w = .verdict) && decide (S.payload w = some d) &&
    decide (d ∈ S.attests w) && (S.verdict w).attested && decide ((S.verdict w).witness = none) &&
    decide (k ∈ S.keys (evalPol S d)) && S.cells.all fun b => !withdraws S d w k b || decide (Concl.down b ∈ prem)

/-- The keys of the endorsement premises. -/
def endorsedKeys : List (Concl C K) → List K
  | [] => []
  | .endorsed _ k :: ps => k :: endorsedKeys ps
  | _ :: ps => endorsedKeys ps

def settleOK (d : C) (prem : List (Concl C K)) : Bool :=
  decide (d ∈ S.cells) && (decide (S.schema d = .decision) || decide (S.schema d = .contract)) &&
    decide (S.req d = none) && decide (Concl.stands d ∈ prem) &&
    decide (evalPol S d ∈ S.pols) &&
    prem.all (fun p => match p with
      | .endorsed w k => countsFor S d prem w k
      | _ => true) &&
    decide (S.thr (evalPol S d) ≤ (dedup (endorsedKeys prem)).length)

/-- The quorum part of a `ground` line: `settle`'s, with every endorsing verdict Grounded by a premise. -/
def groundQuorum (d : C) (prem : List (Concl C K)) : Bool :=
  decide (S.req d = none) && decide (evalPol S d ∈ S.pols) &&
    prem.all (fun p => match p with
      | .endorsed w k => countsFor S d prem w k && decide (Concl.grounded w ∈ prem)
      | _ => true) &&
    decide (S.thr (evalPol S d) ≤ (dedup (endorsedKeys prem)).length)

/-- `ground d`: `d` stands, every cell it relies on is Grounded by a premise, and, if it is a contract or decision, the
quorum `settle` reads is met by verdicts that are Grounded by premises. A scope, a schema or a question is outside the
rule: the store does not show what authorizes the first two or which schema answers the third. -/
def groundOK (d : C) (prem : List (Concl C K)) : Bool :=
  decide (d ∈ S.cells) && decide (Concl.stands d ∈ prem) &&
    ((S.relies d).all fun r => decide (Concl.grounded r ∈ prem)) &&
    match S.schema d with
    | .scope | .metaSchema | .question => false
    | .contract | .decision => groundQuorum S d prem
    | _ => true

/-- A line's rule is its conclusion's, and the rule's checks hold. -/
def ruleOK (l : Line C K) : Bool :=
  decide (l.rule = l.concl.rule) &&
    match l.concl with
    | .stands c => standOK S c l.prem
    | .endorsed w k => endorseOK S w k l.prem
    | .settled d => settleOK S d l.prem
    | .latch y x k => latchOK S y x k
    | .unlatched y x k => unlatchedOK S y x k
    | .dead x => deadOK S x l.prem
    | .eff y => effOK S y l.prem
    | .unsup w => unsupOK S w l.prem
    | .down b => downOK S b l.prem
    | .grounded d => groundOK S d l.prem

def lineOK (done : List (Concl C K)) (l : Line C K) : Bool :=
  l.prem.all (· ∈ done) && ruleOK S l

/-- Check the lines in order; `done` holds the conclusions so far. -/
def run (done : List (Concl C K)) : List (Line C K) → Option (List (Concl C K))
  | [] => some done
  | l :: ls => if lineOK S done l then run (l.concl :: done) ls else none

/-- The checker: every line checks, and one concludes that `d` is settled. -/
def accepts (lines : List (Line C K)) (d : C) : Bool :=
  match run S [] lines with
  | some done => decide (Concl.settled d ∈ done)
  | none => false

/-- The checker for Grounded: every line checks, and one concludes that `d` is grounded. -/
def acceptsGround (lines : List (Line C K)) (d : C) : Bool :=
  match run S [] lines with
  | some done => decide (Concl.grounded d ∈ done)
  | none => false

/-! ## What a conclusion means in the model -/

/-- The reader's pin and the decode, as hypotheses on the model at the tip. `W`, `AE`, the Pass 1 predicates and
`X` are the model's own reading of the scope's admitted chain; `S` is what the decode read from its bytes.

* The decode is faithful: on every cell of the store, `W` and `X` agree with `S` on the fields the checker reads
  (a payload as far as it names a cell of the store; of a verdict, whether it is ATTESTED, whether INVALID, whether
  its witness slot is empty, and its verifier id; of a contract or decision, whether it requires a computation); a
  cell is `Present` exactly when the store holds it; a decoded policy meets its quorum with threshold many distinct
  keys of it, and only so (`quorum`, `quorumConv`).
* The decode holds every seal of an INVALID verdict: each cumulative endorser of a local INVALID verdict has a seal
  of the store on it, under a scope cell that governed, by a key of that scope's roster.
* Latches are read from the seals (§4.1 latch 3). An edge latches when a quorum of `Pol(x)` seals its source under a
  scope cell that governed (`latch`: latch soundness of the fold). An edge latched only so, or by the author clause
  through a key that seals both ends (`unlatch`): every seal the fold counted for it is in the store, and the decode
  holds every seal on an edge's source and on a retired or superseded cell.
* The store at the tip is the admitted chain: the Pass 1 equations hold (`IsPass1`); an edge latches only from a
  present cell (`edge_present` proves it of the fold); `X.active` is Pass 1 `Active`; `X.stale` satisfies the
  Pass 2 equation, both ways for a local active cell (`stale_pin`, `stale_complete` prove it of `Stale`); and a
  verified seal under a scope cell that governed, by a key of its admission roster, on a local cell counts among
  that cell's cumulative endorsers (§4.1: each seal is checked under the scope of its own commit, and the gate admits
  a seal on a local cell only under the scope governing it). -/
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
  verdictInvalid : ∀ c ∈ S.cells, S.schema c = .verdict → (W.info c).verdictInvalid = (S.verdict c).invalid
  verdict : ∀ c ∈ S.cells, S.schema c = .verdict → (X.verdict c).attested = (S.verdict c).attested ∧
    (X.verdict c).invalid = (S.verdict c).invalid ∧ ((X.verdict c).witness = none ↔ (S.verdict c).witness = none) ∧
    (X.verdict c).verifier = (S.verdict c).verifier
  req : ∀ c ∈ S.cells, (S.schema c = .decision ∨ S.schema c = .contract) → (X.req c = none ↔ S.req c = none)
  scope : X.scopeTip = S.scope
  pol0 : (W.info S.scope).pol0 = S.pol0
  present : ∀ c, Present c ↔ c ∈ S.cells
  quorum : ∀ p ∈ S.pols, ∀ (E ks : List K), (∀ k ∈ ks, k ∈ E) → ks.Nodup → (∀ k ∈ ks, k ∈ S.keys p) →
    S.thr p ≤ ks.length → W.quorum E p = true
  quorumConv : ∀ p ∈ S.pols, ∀ E, W.quorum E p = true →
    ∃ ks : List K, ks.Nodup ∧ (∀ k ∈ ks, k ∈ E) ∧ (∀ k ∈ ks, k ∈ S.keys p) ∧ S.thr p ≤ ks.length
  pass1 : IsPass1 W AE Present isIntrinsic Auth Inv Eff Ret Acc
  edgeFrom : ∀ w v k, AE w v k = true → Present w
  latch : ∀ y ∈ S.cells, ∀ (x : C) (k : Kind), x ∈ edgesOf S y k → S.schema y ≠ .scope →
    S.schema y ≠ .metaSchema → S.schema x ≠ .acceptance → ∀ cp ∈ S.ctxs, ∀ E : List K,
    (∀ e ∈ E, e ∈ sealers S y cp) → W.quorum E (polAt S cp x) = true → AE y x k = true
  unlatch : ∀ y ∈ S.cells, ∀ x ∈ S.cells, ∀ k : Kind, S.schema y ≠ .scope → S.schema x ≠ .acceptance →
    AE y x k = true →
    (∃ cp ∈ S.ctxs, ∃ E : List K, (∀ e ∈ E, e ∈ sealers S y cp) ∧ W.quorum E (polAt S cp x) = true) ∨
    (k ≠ .invalidates ∧ canEvict S x = true ∧ S.isLocal x = true ∧
      ∃ cp ∈ S.ctxs, ∃ e ∈ sealers S y cp, ∃ cq ∈ S.ctxs, e ∈ sealers S x cq)
  active : ∀ c, X.active c ↔ Active W AE Eff Acc Ret c
  stale : ∀ v, X.stale v → (∃ d ∈ (W.info v).relies, ¬ X.active d ∨ X.stale d) ∨ (W.info v).isLocal = false
  reliesLive : ∀ v d, X.active v → ¬ X.stale v → d ∈ (W.info v).relies → X.active d ∧ ¬ X.stale d
  cumulative : ∀ s ∈ S.seals, ∀ cp ∈ S.ctxs, s.ctx = cp.1 → S.isLocal s.target = true → s.key ∈ S.keys cp.2 →
    s.key ∈ X.cumulative s.target
  invalidSeals : ∀ b ∈ S.cells, S.schema b = .verdict → (S.verdict b).invalid = true → S.isLocal b = true →
    ∀ k ∈ X.cumulative b, ∃ cp ∈ S.ctxs, k ∈ S.keys cp.2 ∧ ∃ s ∈ S.seals, s.target = b ∧ s.ctx = cp.1 ∧ s.key = k

variable (W : World C K P) (X : Pass3In C K P) (wmax : C → List C) (cnt : C → C → List K)
variable (AE : C → C → Kind → Bool) (Inv Eff Acc : C → Prop)

/-- What each conclusion asserts of the model. -/
def Holds : Concl C K → Prop
  | .stands c => c ∈ S.cells ∧ Live X c
  | .endorsed w k => k ∈ witnessEndorsers W X w
  | .settled d => Settled W X wmax cnt d
  | .latch y x k => AE y x k = true
  | .unlatched y x k => AE y x k = false
  | .dead x => Inv x
  | .eff y => Eff y
  | .unsup w => ¬ Superseded W AE Eff Acc w
  | .down b => ¬ Live X b
  | .grounded d => Grounded W X wmax cnt d

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
  | .stands _ :: ps | .settled _ :: ps | .latch _ _ _ :: ps | .unlatched _ _ _ :: ps | .dead _ :: ps
  | .eff _ :: ps | .unsup _ :: ps | .down _ :: ps | .grounded _ :: ps => by
    intro h
    obtain ⟨w', hw'⟩ := mem_endorsedKeys (ps := ps) h
    exact ⟨w', List.mem_cons_of_mem _ hw'⟩

/-- `M` without the first `k` (written here, not `List.erase`, whose lemmas rest on `Classical.choice`). -/
def drop1 (k : K) : List K → List K
  | [] => []
  | j :: js => if j = k then js else j :: drop1 k js

theorem length_drop1 {k : K} : ∀ {M : List K}, k ∈ M → (drop1 k M).length + 1 = M.length
  | [], h => absurd h List.not_mem_nil
  | j :: js, h => by
    unfold drop1
    split
    · rfl
    · rename_i hjk
      have hk : k ∈ js := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hjk
        · exact h
      simp only [List.length_cons, length_drop1 hk]

theorem mem_drop1 {k a : K} (hak : a ≠ k) : ∀ {M : List K}, a ∈ M → a ∈ drop1 k M
  | [], h => absurd h List.not_mem_nil
  | j :: js, h => by
    unfold drop1
    split
    · rename_i hjk
      rcases List.mem_cons.mp h with h | h
      · exact absurd (h.trans hjk) hak
      · exact h
    · rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_drop1 hak h)

/-- A list without repeats, every member of which is in `M`, is no longer than `M`. -/
theorem nodup_length_le : ∀ {ks : List K} {M : List K}, ks.Nodup → (∀ k ∈ ks, k ∈ M) → ks.length ≤ M.length
  | [], _, _, _ => Nat.zero_le _
  | k :: ks, M, hnd, hsub => by
    obtain ⟨hk, hnd'⟩ := List.nodup_cons.mp hnd
    have hkM : k ∈ M := hsub k List.mem_cons_self
    have hsub' : ∀ j ∈ ks, j ∈ drop1 k M := by
      intro j hj
      have hjk : j ≠ k := fun h => hk (h ▸ hj)
      exact mem_drop1 hjk (hsub j (List.mem_cons_of_mem _ hj))
    have ih := nodup_length_le hnd' hsub'
    have := length_drop1 hkM
    simp only [List.length_cons]
    omega

theorem mem_count_list {ks : List K} {p : P} {k : K} :
    k ∈ dedup (ks.filter fun k => decide (k ∈ S.keys p)) ↔ k ∈ ks ∧ k ∈ S.keys p := by
  rw [mem_dedup, List.mem_filter, decide_eq_true_eq]

/-- Distinct keys of `p` among `ks` number at most `count`. -/
theorem le_count {ks E : List K} {p : P} (hnd : ks.Nodup) (h : ∀ k ∈ ks, k ∈ E ∧ k ∈ S.keys p) :
    ks.length ≤ count S E p :=
  nodup_length_le hnd fun k hk => (mem_count_list S).mpr (h k hk)

theorem mem_edgesOf {W : World C K P} {y : C} (hs : (W.info y).supersedes = S.supersedes y)
    (hr : (W.info y).retires = S.retires y) (hi : (W.info y).invalidates = S.invalidates y) (k : Kind) :
    (W.info y).edges k = edgesOf S y k := by
  cases k <;> simp [CellInfo.edges, edgesOf, hs, hr, hi]

/-! ## Soundness, line by line -/

section Sound

variable {S W X wmax cnt AE Inv Eff Acc}
variable {Present isIntrinsic : C → Prop} {Auth : C → Bool} {Ret : C → Prop}

theorem eff_present (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {w : C} (h : Eff w) :
    w ∈ S.cells :=
  (pin.present w).mp ((pin.pass1.eff_eq w).mp h).1

theorem acc_of_local (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {c : C} (hc : c ∈ S.cells)
    (hl : S.isLocal c = true) : Acc c :=
  (pin.pass1.acc_eq c).mpr (Or.inr (Or.inl (pin.isLocal c hc ▸ hl)))

theorem not_eff_of_inv (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {c : C} (h : Inv c) : ¬ Eff c :=
  fun he => ((pin.pass1.eff_eq c).mp he).2 h

/-- A killer of the model: not a verdict, or an INVALID one. -/
theorem killer_of_nonInv (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {y : C} (hy : y ∈ S.cells)
    (h : nonInv S y = false) : (W.info y).schema ≠ .verdict ∨ (W.info y).verdictInvalid = true := by
  rw [pin.schema y hy]
  by_cases hv : S.schema y = .verdict
  · refine Or.inr ?_
    rw [pin.verdictInvalid y hy hv]
    simp only [nonInv, hv, decide_true, Bool.true_and, Bool.not_eq_false'] at h
    exact h
  · exact Or.inl hv

theorem nonInv_of_killer (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {y : C} (hy : y ∈ S.cells)
    (h : (W.info y).schema ≠ .verdict ∨ (W.info y).verdictInvalid = true) : nonInv S y = false := by
  rw [pin.schema y hy] at h
  unfold nonInv
  by_cases hv : S.schema y = .verdict
  · rw [pin.verdictInvalid y hy hv] at h
    rcases h with h | h
    · exact absurd hv h
    · simp [hv, h]
  · simp [hv]

/-- A `latch` line: a quorum of `Pol(x)` seals `y` under a scope cell that governed, so the edge latched. -/
theorem latch_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {y x : C} {k : Kind}
    (h : latchOK S y x k = true) : AE y x k = true := by
  simp only [latchOK, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hy, hx⟩, hs⟩, hm⟩, ha⟩, cp, hcp, hpol, hmeet⟩ := h
  simp only [meets, count, decide_eq_true_eq] at hmeet
  have hq := pin.quorum _ hpol _ _ (fun _ h => h) (nodup_dedup _)
    (fun k hk => ((mem_count_list S).mp hk).2) hmeet
  exact pin.latch y hy x k hx hs hm ha cp hcp _ (fun e he => ((mem_count_list S).mp he).1) hq

/-- An `unlatched` line: under no scope cell do the seals on `y` meet `Pol(x)`, and the author clause cannot apply,
so the edge did not latch. -/
theorem unlatched_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {y x : C} {k : Kind}
    (h : unlatchedOK S y x k = true) : AE y x k = false := by
  simp only [unlatchedOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨hy, hx⟩, hs⟩, ha⟩, hall⟩, hauth⟩ := h
  cases hae : AE y x k with
  | false => rfl
  | true =>
    exfalso
    rcases pin.unlatch y hy x hx k hs ha hae with ⟨cp, hcp, E, hE, hq⟩ | ⟨hk, hev, hloc, hsh⟩
    · obtain ⟨hpol, hnm⟩ := hall cp hcp
      obtain ⟨ks, hnd, hkE, hkK, hthr⟩ := pin.quorumConv _ hpol E hq
      have hle := le_count S hnd fun k hk => ⟨hE k (hkE k hk), hkK k hk⟩
      simp only [meets, decide_eq_false_iff_not] at hnm
      exact hnm (Nat.le_trans hthr hle)
    · have hsh' : shared S y x = true := by
        obtain ⟨cp, hcp, e, he, cq, hcq, hex⟩ := hsh
        simp only [shared, List.any_eq_true, decide_eq_true_eq]
        exact ⟨cp, hcp, e, he, cq, hcq, hex⟩
      rcases hauth with ((h | h) | h) | h
      · exact hk h
      · rw [hev] at h; exact Bool.noConfusion h
      · rw [hloc] at h; exact Bool.noConfusion h
      · rw [hsh'] at h; exact Bool.noConfusion h

/-- A `dead` line: an Effective local killer invalidates `x` by an edge that latched. -/
theorem dead_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {x : C} {prem : List (Concl C K)}
    (h : deadOK S x prem = true) (hprem : ∀ p ∈ prem, Holds S W X wmax cnt AE Inv Eff Acc p) : Inv x := by
  simp only [deadOK, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨y, hy, ⟨⟨⟨⟨hxy, hl⟩, hk⟩, hlat⟩, heff⟩⟩ := h
  have hae : AE y x .invalidates = true := hprem _ hlat
  have hE : Eff y := hprem _ heff
  exact (pin.pass1.inv_eq x).mpr ⟨y, hE, acc_of_local pin hy hl, (pin.invalidates y hy).symm ▸ hxy, hae,
    killer_of_nonInv pin hy hk⟩

/-- An `eff` line: no cell invalidates `y` by an edge that counts, so it is Effective. -/
theorem eff_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {y : C} {prem : List (Concl C K)}
    (h : effOK S y prem = true) (hprem : ∀ p ∈ prem, Holds S W X wmax cnt AE Inv Eff Acc p) : Eff y := by
  simp only [effOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  obtain ⟨hy, hall⟩ := h
  refine (pin.pass1.eff_eq y).mpr ⟨(pin.present y).mpr hy, ?_⟩
  intro hinv
  obtain ⟨w, hw, -, hyw, hae, hkill⟩ := (pin.pass1.inv_eq y).mp hinv
  have hwc := eff_present pin hw
  rcases hall w hwc with ((h | h) | h) | h
  · exact h ((pin.invalidates w hwc) ▸ hyw)
  · rw [nonInv_of_killer pin hwc hkill] at h; exact Bool.noConfusion h
  · have : AE w y .invalidates = false := hprem _ h
    rw [hae] at this; exact Bool.noConfusion this
  · exact not_eff_of_inv pin (hprem _ h) hw

/-- An `unsup` line: no cell supersedes `w` by an edge that counts, so it is not Superseded. -/
theorem unsup_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {w : C} {prem : List (Concl C K)}
    (h : unsupOK S w prem = true) (hprem : ∀ p ∈ prem, Holds S W X wmax cnt AE Inv Eff Acc p) :
    ¬ Superseded W AE Eff Acc w := by
  simp only [unsupOK, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, Bool.and_eq_true] at h
  intro hs
  cases hs with
  | direct hwu hae hu _ =>
    have huc := eff_present pin hu
    rcases h _ huc with (hn | hn) | ⟨hd, -⟩
    · exact hn ((pin.supersedes _ huc) ▸ hwu)
    · have : AE _ w .supersedes = false := hprem _ hn
      rw [hae] at this; exact Bool.noConfusion this
    · exact not_eff_of_inv pin (hprem _ hd) hu
  | trans hwu hae hsu =>
    have huc := (pin.present _).mp (pin.edgeFrom _ _ _ hae)
    rcases h _ huc with (hn | hn) | ⟨-, hus⟩
    · exact hn ((pin.supersedes _ huc) ▸ hwu)
    · have : AE _ w .supersedes = false := hprem _ hn
      rw [hae] at this; exact Bool.noConfusion this
    · exact (hprem _ hus) hsu

/-- A `down` line: `b` is Invalidated, or relies on a cell that is not live, so it is not live. -/
theorem down_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {b : C} {prem : List (Concl C K)}
    (h : downOK S b prem = true) (hprem : ∀ p ∈ prem, Holds S W X wmax cnt AE Inv Eff Acc p) : ¬ Live X b := by
  simp only [downOK, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  intro hl
  rcases h with hd | ⟨hb, r, hr, hdr⟩
  · exact not_eff_of_inv pin (hprem _ hd) ((pin.active b).mp hl.1).1
  · have := pin.reliesLive b r hl.1 hl.2 ((pin.relies b hb).symm ▸ hr)
    exact hprem _ hdr this

/-- A `stand` line's checks make its cell `Active`. -/
theorem active_of_stand (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {c : C}
    (hc : c ∈ S.cells) (hl : S.isLocal c = true) (heff : Eff c) (hns : ¬ Superseded W AE Eff Acc c)
    (hret : ∀ w ∈ S.cells, c ∈ S.retires w → Inv w ∨ AE w c .retires = false)
    (hout : ∀ u ∈ S.supersedes c, AE c u .supersedes = true) : Active W AE Eff Acc Ret c := by
  refine ⟨heff, ?_, hns, acc_of_local pin hc hl, ?_⟩
  · intro hr
    obtain ⟨w, hw, -, hcw, hae⟩ := (pin.pass1.ret_eq c).mp hr
    have hwc := eff_present pin hw
    rcases hret w hwc ((pin.retires w hwc) ▸ hcw) with h | h
    · exact not_eff_of_inv pin h hw
    · rw [hae] at h; exact Bool.noConfusion h
  · intro u hu
    exact hout u ((pin.supersedes c hc) ▸ hu)

/-- A `stand` line whose premises hold concludes a cell that stands. -/
theorem stand_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {c : C}
    {prem : List (Concl C K)} (hok : standOK S c prem = true)
    (hprem : ∀ p ∈ prem, Holds S W X wmax cnt AE Inv Eff Acc p) : Holds S W X wmax cnt AE Inv Eff Acc (.stands c) := by
  simp only [standOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at hok
  obtain ⟨⟨⟨⟨⟨⟨hc, hl⟩, he⟩, hu⟩, hr⟩, ho⟩, hp⟩ := hok
  have hact := active_of_stand pin hc hl (hprem _ he) (hprem _ hu)
    (fun w hw hcw => by
      rcases hr w hw with (h | h) | h
      · exact absurd hcw h
      · exact Or.inl (hprem _ h)
      · exact Or.inr (hprem _ h))
    (fun u hu => hprem _ (ho u hu))
  refine ⟨hc, (pin.active c).mpr hact, ?_⟩
  intro hst
  rcases pin.stale c hst with ⟨d, hd, hdead⟩ | hnl
  · rw [pin.relies c hc] at hd
    obtain ⟨-, hda, hds⟩ := (hprem _ (hp d hd) : Holds S W X wmax cnt AE Inv Eff Acc (.stands d))
    rcases hdead with h | h
    · exact h hda
    · exact hds h
  · rw [pin.isLocal c hc, hl] at hnl
    exact Bool.noConfusion hnl

/-- An `endorse` line concludes a key among the verdict's endorsers. -/
theorem endorse_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {w : C} {k : K}
    {prem : List (Concl C K)} (hok : endorseOK S w k prem = true) :
    Holds S W X wmax cnt AE Inv Eff Acc (.endorsed w k) := by
  simp only [endorseOK, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hok
  obtain ⟨⟨⟨-, hw⟩, hl⟩, cp, hcp, hroster, s, hs, ⟨⟨ht, hctx⟩, hkey⟩⟩ := hok
  show k ∈ witnessEndorsers W X w
  unfold witnessEndorsers
  rw [pin.isLocal w hw, hl, if_pos rfl]
  have := pin.cumulative s hs cp hcp hctx (ht ▸ hl) (hkey ▸ hroster)
  rw [ht, hkey] at this
  exact this

/-- An endorsement premise that `countsFor` admits names a verdict of `W_max(d)` and a key of `d`'s evaluator policy
that counts through it. -/
theorem counts_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt) {d : C} {prem : List (Concl C K)}
    (hd : d ∈ S.cells) (hsch : S.schema d = .decision ∨ S.schema d = .contract) (hreq : S.req d = none)
    (hprem : ∀ p ∈ prem, Holds S W X wmax cnt AE Inv Eff Acc p) {w : C} {k : K}
    (hmem : Concl.endorsed w k ∈ prem) (hc : countsFor S d prem w k = true) :
    w ∈ wmax d ∧ k ∈ cnt d w ∧ k ∈ S.keys (Witness.evalPol S d) := by
  simp only [countsFor, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨hsw, hvw⟩, hpw⟩, haw⟩, hatt⟩, hwit⟩, hkey⟩, hnot⟩ := hc
  obtain ⟨hw, hlw⟩ := (hprem _ hsw : Holds S W X wmax cnt AE Inv Eff Acc (.stands w))
  have hin : InWmax W X S.cells d w := by
    refine ⟨hw, hlw, pin.attests w hw ▸ haw, ?_⟩
    have hrest : (W.info w).schema = .verdict ∧ (W.info w).payload = some d ∧
        (match X.req d with
         | none => (X.verdict w).witness = none ∧ (X.verdict w).attested = true
         | some _ => (X.verdict w).replayed = true ∧
             ∃ c, (X.verdict w).witness = some c ∧ Live X c ∧ X.replayOK c d) := by
      refine ⟨pin.schema w hw ▸ hvw, (pin.payload w hw d hd).mpr hpw, ?_⟩
      rw [(pin.req d hd hsch).mpr hreq]
      exact ⟨(pin.verdict w hw hvw).2.2.1.mpr hwit, (pin.verdict w hw hvw).1 ▸ hatt⟩
    rw [pin.schema d hd]
    rcases hsch with h | h <;> rw [h] <;> exact hrest
  -- an INVALID verdict on `d` under `w`'s verifier id that `k` endorses is one the checker found `withdraws`, and
  -- a premise proves it not live; and `w` names no witness: nothing withdraws `k`
  have hnw : ¬ Withdrawn W X S.cells d w k := by
    rintro ⟨b, hb, hbl, hbv, hbp, hbi, hbver, hbk⟩
    rcases hbp with hbp | ⟨hwn, -⟩
    · have hbs : S.schema b = .verdict := pin.schema b hb ▸ hbv
      have hbi' : (S.verdict b).invalid = true := by
        rw [← (pin.verdict b hb hbs).2.1]
        exact hbi
      have hwd : withdraws S d w k b = true := by
        simp only [withdraws, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true']
        refine ⟨⟨⟨⟨hbs, (pin.payload b hb d hd).mp hbp⟩, hbi'⟩, ?_⟩, ?_⟩
        · rw [← (pin.verdict b hb hbs).2.2.2, ← (pin.verdict w hw hvw).2.2.2]
          exact hbver
        · cases hlb : S.isLocal b with
          | false => exact Or.inl rfl
          | true =>
            refine Or.inr ?_
            have hk : k ∈ X.cumulative b := by
              unfold witnessEndorsers at hbk
              rw [pin.isLocal b hb, hlb, if_pos rfl] at hbk
              exact hbk
            obtain ⟨cp, hcp, hroster, s, hs, ht, hctx, hks⟩ := pin.invalidSeals b hb hbs hbi' hlb k hk
            simp only [sealedBy, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨cp, hcp, hroster, s, hs, ⟨ht, hctx⟩, hks⟩
      rcases hnot b hb with h | h
      · rw [hwd] at h; exact Bool.noConfusion h
      · exact (hprem _ h : Holds S W X wmax cnt AE Inv Eff Acc (.down b)) hbl
    · exact hwn ((pin.verdict w hw hvw).2.2.1.mpr hwit)
  have hcounts : Counts W X S.cells d w k := by
    refine ⟨hprem _ hmem, ?_⟩
    rw [pin.schema d hd]
    rcases hsch with h | h <;> rw [h] <;> exact hnw
  exact ⟨(hwmax d w).mpr hin, (hcnt d w k).mpr hcounts, hkey⟩

/-- A `settle` line whose premises hold concludes `Settled`. -/
theorem settle_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt) {d : C} {prem : List (Concl C K)}
    (hok : settleOK S d prem = true) (hprem : ∀ p ∈ prem, Holds S W X wmax cnt AE Inv Eff Acc p) :
    Holds S W X wmax cnt AE Inv Eff Acc (.settled d) := by
  simp only [settleOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨hd, hsch⟩, hreq⟩, hsd⟩, hpol⟩, hall⟩, hthr⟩ := hok
  have hlive : Live X d := (hprem _ hsd).2
  have hep : Vars1.evalPol W X d = Witness.evalPol S d := by
    unfold Vars1.evalPol Witness.evalPol
    rw [pin.schema d hd, pin.customPol d hd, pin.scope, pin.pol0]
    rcases hsch with h | h <;> rw [h]
  -- every endorsement premise is on a verdict of `W_max(d)`
  have hcount : ∀ w k, Concl.endorsed w k ∈ prem → k ∈ (wmax d).flatMap (cnt d) ∧
      k ∈ S.keys (Witness.evalPol S d) := by
    intro w k hmem
    obtain ⟨hw, hk, hkey⟩ := counts_sound pin hwmax hcnt hd hsch hreq hprem hmem (hall _ hmem)
    exact ⟨List.mem_flatMap.mpr ⟨w, hw, hk⟩, hkey⟩
  have hq : W.quorum ((wmax d).flatMap (cnt d)) (Vars1.evalPol W X d) = true := by
    rw [hep]
    refine pin.quorum _ hpol _ (dedup (endorsedKeys prem)) ?_ (nodup_dedup _) ?_ hthr
    · intro k hk
      obtain ⟨w, hw⟩ := mem_endorsedKeys (mem_dedup.mp hk)
      exact (hcount w k hw).1
    · intro k hk
      obtain ⟨w, hw⟩ := mem_endorsedKeys (mem_dedup.mp hk)
      exact (hcount w k hw).2
  show Settled W X wmax cnt d
  refine ⟨hlive, ?_⟩
  rw [pin.schema d hd]
  rcases hsch with h | h <;> rw [h] <;> exact hq

/-- A `ground` line whose premises hold concludes `Grounded`: it meets Grounded's equation over the cells the
premises prove Grounded, so it meets it over `Grounded` (`grounded_fixed`). -/
theorem ground_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt) {d : C} {prem : List (Concl C K)}
    (hok : groundOK S d prem = true) (hprem : ∀ p ∈ prem, Holds S W X wmax cnt AE Inv Eff Acc p) :
    Holds S W X wmax cnt AE Inv Eff Acc (.grounded d) := by
  unfold groundOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨⟨⟨hd, hsd⟩, hrel⟩, hsch⟩ := hok
  show Grounded W X wmax cnt d
  rw [← grounded_fixed]
  refine ⟨(hprem _ hsd).2, fun r hr => hprem _ (hrel r ((pin.relies d hd) ▸ hr)), ?_⟩
  rw [pin.schema d hd]
  -- the quorum, for a contract or a decision
  have quorum : (S.schema d = .decision ∨ S.schema d = .contract) → groundQuorum S d prem = true →
      ∃ E : List K, W.quorum E (Vars1.evalPol W X d) = true ∧
        ∀ k ∈ E, ∃ w ∈ wmax d, Grounded W X wmax cnt w ∧ k ∈ cnt d w := by
    intro hs hq
    simp only [groundQuorum, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hq
    obtain ⟨⟨⟨hreq, hpol⟩, hall⟩, hthr⟩ := hq
    have hep : Vars1.evalPol W X d = Witness.evalPol S d := by
      unfold Vars1.evalPol Witness.evalPol
      rw [pin.schema d hd, pin.customPol d hd, pin.scope, pin.pol0]
      rcases hs with h | h <;> rw [h]
    have each : ∀ k ∈ dedup (endorsedKeys prem), ∃ w, w ∈ wmax d ∧ k ∈ cnt d w ∧
        k ∈ S.keys (Witness.evalPol S d) ∧ Grounded W X wmax cnt w := by
      intro k hk
      obtain ⟨w, hmem⟩ := mem_endorsedKeys (mem_dedup.mp hk)
      have hc := hall _ hmem
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hw, hkc, hkey⟩ := counts_sound pin hwmax hcnt hd hs hreq hprem hmem hc.1
      exact ⟨w, hw, hkc, hkey, hprem _ hc.2⟩
    refine ⟨dedup (endorsedKeys prem), ?_, fun k hk => ?_⟩
    · rw [hep]
      refine pin.quorum _ hpol _ _ (fun k hk => hk) (nodup_dedup _) (fun k hk => ?_) hthr
      obtain ⟨w, -, -, hkey, -⟩ := each k hk
      exact hkey
    · obtain ⟨w, hw, hkc, -, hg⟩ := each k hk
      exact ⟨w, hw, hg, hkc⟩
  cases hs : S.schema d <;> simp only [hs] at hsch ⊢
  case decision => exact quorum (Or.inl hs) hsch
  case contract => exact quorum (Or.inr hs) hsch
  all_goals first | exact Bool.noConfusion hsch | trivial

/-- A line whose rule checks and whose premises hold concludes what holds. -/
theorem line_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt) {l : Line C K}
    (h : ruleOK S l = true) (hprem : ∀ p ∈ l.prem, Holds S W X wmax cnt AE Inv Eff Acc p) :
    Holds S W X wmax cnt AE Inv Eff Acc l.concl := by
  obtain ⟨rule, concl, prem⟩ := l
  simp only [ruleOK, Bool.and_eq_true] at h
  obtain ⟨-, h⟩ := h
  cases concl with
  | stands c => exact stand_sound pin h hprem
  | endorsed w k => exact endorse_sound pin h
  | settled d => exact settle_sound pin hwmax hcnt h hprem
  | latch y x k => exact latch_sound pin h
  | unlatched y x k => exact unlatched_sound pin h
  | dead x => exact dead_sound pin h hprem
  | eff y => exact eff_sound pin h hprem
  | unsup w => exact unsup_sound pin h hprem
  | down b => exact down_sound pin h hprem
  | grounded d => exact ground_sound pin hwmax hcnt h hprem

/-- Every conclusion of a checked prefix holds. -/
theorem run_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt) :
    ∀ (lines : List (Line C K)) (done out : List (Concl C K)), run S done lines = some out →
      (∀ p ∈ done, Holds S W X wmax cnt AE Inv Eff Acc p) → ∀ p ∈ out, Holds S W X wmax cnt AE Inv Eff Acc p
  | [], done, out, h, hd => by
    simp only [run, Option.some.injEq] at h
    exact h ▸ hd
  | l :: ls, done, out, h, hd => by
    simp only [run] at h
    split at h
    · rename_i hl
      apply run_sound pin hwmax hcnt ls _ out h
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · simp only [lineOK, Bool.and_eq_true, List.all_eq_true] at hl
        obtain ⟨hpre, hrule⟩ := hl
        exact line_sound pin hwmax hcnt hrule fun q hq => hd q (by simpa using hpre q hq)
      · exact hd p hp
    · exact absurd h (by simp)

/-- **Soundness of the witness checker.** If `accepts` holds for a derivation, the decision is `Settled` in the
model of §4.2 at the tip, for every reading `W`, `X` of the scope's admitted chain that the decode `S` agrees
with (`Pin`), and every faithful presentation of `W_max`. -/
theorem witness_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt) {lines : List (Line C K)} {d : C}
    (h : accepts S lines d = true) : Settled W X wmax cnt d := by
  unfold accepts at h
  split at h
  · rename_i out hrun
    exact (run_sound (AE := AE) (Inv := Inv) (Eff := Eff) (Acc := Acc) pin hwmax hcnt lines [] out hrun (by simp)
      _ (by simpa using h) : Holds S W X wmax cnt AE Inv Eff Acc (.settled d))
  · exact absurd h (by decide)

/-- **Soundness of the checker for Grounded.** If `acceptsGround` holds for a derivation, the cell is `Grounded` in the
model of §4.2 at the tip, under the hypotheses of `witness_sound`. -/
theorem witness_ground_sound (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt) {lines : List (Line C K)} {d : C}
    (h : acceptsGround S lines d = true) : Grounded W X wmax cnt d := by
  unfold acceptsGround at h
  split at h
  · rename_i out hrun
    exact (run_sound (AE := AE) (Inv := Inv) (Eff := Eff) (Acc := Acc) pin hwmax hcnt lines [] out hrun (by simp)
      _ (by simpa using h) : Holds S W X wmax cnt AE Inv Eff Acc (.grounded d))
  · exact absurd h (by decide)

end Sound

/-! ## Two of the pin's hypotheses hold of the model's passes -/

/-- Pass 2 `Stale` satisfies the equation `Pin.stale` asks of `X.stale`. -/
theorem stale_pin {N : Nat} (I : Pass2In N) (v : Fin N) (h : Stale I v) :
    (∃ d ∈ I.relies v, ¬ I.active d ∨ Stale I d) ∨ ¬ I.isLocal v := by
  rcases ((stale_fixed I v).mp h).2 with h | ⟨hl, -⟩
  · exact Or.inl h
  · exact Or.inr hl

/-- Pass 2 `Stale` satisfies what `Pin.reliesLive` asks of `X.stale`: what an active cell that is not stale relies
on is active and not stale. -/
theorem stale_complete {N : Nat} (I : Pass2In N) [DecidablePred I.active] (v d : Fin N) (ha : I.active v)
    (hns : ¬ Stale I v) (hd : d ∈ I.relies v) : I.active d ∧ ¬ Stale I d := by
  refine ⟨?_, fun hs => hns ((stale_fixed I v).mpr ⟨ha, Or.inl ⟨d, hd, Or.inr hs⟩⟩)⟩
  match (inferInstance : Decidable (I.active d)) with
  | isTrue h => exact h
  | isFalse h => exact absurd ((stale_fixed I v).mpr ⟨ha, Or.inl ⟨d, hd, Or.inl h⟩⟩) hns

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
