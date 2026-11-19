/-!
# Metered Portable Agent Spores — Formal Conservation & Partiality Theorems (AS-1..AS-6)

Formalizes the core algebraic invariants of `AGENT-SPORE-DIRECTION.md` and `spore.py`:
1. **Budget Conservation & Bounded Recursion (`AS-2`)**:
   Partitioning a parent's budget to spawn child spores strictly conserves ATP and fetch
   budgets across an arbitrary recursive execution tree (`tree_conserves_atp`,
   `tree_conserves_fetches`), strictly decreases recursion depth (`spawn_depth_strictly_decreases`),
   and bounds total spawned nodes (`tree_nodes_bounded`).
2. **Exact Partiality Lattice & No Verification Inflation by Retelling (`AS-4`, `AS-5`)**:
   A 6-dimensional partiality vector forms a meet-semilattice; forwarding a result across
   agents (`retell`) can never raise any dimension (`retell_never_inflates`), never preserves
   `verifiedHere` (`retell_never_verified_here`), is idempotent (`retell_idempotent`), and
   composing a parent with a child via `meet` can never exceed either operand (`meet_le_left`,
   `meet_le_right`).
3. **Counterexample-Driven Revision Monotonicity (`AS-6`)**:
   Any counterexample invalidating a dependency forces revision of every dependent result
   carrying the transitive dependency closure (`revision_trans`).

Every theorem here uses only Lean core (`propext` and `Quot.sound`, no `Classical.choice`, no `sorry`).
-/

namespace Vars1.Spore

/-! ## 1. Budget Conservation & Bounded Recursion (AS-2) -/

structure Budget where
  atp     : Nat
  fetches : Nat
  spawns  : Nat
  depth   : Nat
  deriving DecidableEq, Repr

/-- Valid local spending of `(dAtp, dFetch)` from budget `b`. -/
def CanSpend (b : Budget) (dAtp dFetch : Nat) : Prop :=
  dAtp ≤ b.atp ∧ dFetch ≤ b.fetches

/-- Remaining budget after spending `(dAtp, dFetch)`. -/
def spend (b : Budget) (dAtp dFetch : Nat) : Budget :=
  { atp := b.atp - dAtp
    fetches := b.fetches - dFetch
    spawns := b.spawns
    depth := b.depth }

theorem spend_conserves_atp (b : Budget) (dAtp dFetch : Nat) (h : CanSpend b dAtp dFetch) :
    (spend b dAtp dFetch).atp + dAtp = b.atp := by
  simp only [spend]
  exact Nat.sub_add_cancel h.1

theorem spend_conserves_fetches (b : Budget) (dAtp dFetch : Nat) (h : CanSpend b dAtp dFetch) :
    (spend b dAtp dFetch).fetches + dFetch = b.fetches := by
  simp only [spend]
  exact Nat.sub_add_cancel h.2

/-- Valid budget partition when spawning a child spore with budget `child` from `parent`. -/
def ValidSpawn (parent child : Budget) : Prop :=
  1 ≤ parent.spawns ∧
  1 ≤ parent.depth ∧
  child.atp ≤ parent.atp ∧
  child.fetches ≤ parent.fetches ∧
  child.spawns ≤ parent.spawns - 1 ∧
  child.depth ≤ parent.depth - 1

/-- Parent budget remaining after carving out `child` (also pays 1 spawn slot). -/
def afterSpawn (parent child : Budget) : Budget :=
  { atp := parent.atp - child.atp
    fetches := parent.fetches - child.fetches
    spawns := parent.spawns - 1 - child.spawns
    depth := parent.depth }

theorem spawn_conserves_atp (p c : Budget) (h : ValidSpawn p c) :
    (afterSpawn p c).atp + c.atp = p.atp := by
  simp only [afterSpawn]
  exact Nat.sub_add_cancel h.2.2.1

theorem spawn_conserves_fetches (p c : Budget) (h : ValidSpawn p c) :
    (afterSpawn p c).fetches + c.fetches = p.fetches := by
  simp only [afterSpawn]
  exact Nat.sub_add_cancel h.2.2.2.1

theorem spawn_conserves_spawns (p c : Budget) (h : ValidSpawn p c) :
    (afterSpawn p c).spawns + c.spawns + 1 = p.spawns := by
  simp only [afterSpawn]
  have h1 : p.spawns - 1 - c.spawns + c.spawns = p.spawns - 1 :=
    Nat.sub_add_cancel h.2.2.2.2.1
  rw [h1]
  exact Nat.sub_add_cancel h.1

theorem spawn_depth_strictly_decreases (p c : Budget) (h : ValidSpawn p c) :
    c.depth < p.depth := by
  have hd : 1 ≤ p.depth := h.2.1
  have hc : c.depth ≤ p.depth - 1 := h.2.2.2.2.2
  omega

/-- A recursive spore execution tree: local steps + child spores spawned from partitioned sub-budgets. -/
inductive SporeExec : Budget → Nat → Nat → Nat → Nat → Nat → Prop where
  /-- Leaf execution: spend `(sAtp, sFetch)` locally and stop with remaining budget `rem`. -/
  | finish (b : Budget) (sAtp sFetch : Nat) (h : CanSpend b sAtp sFetch) :
      SporeExec b sAtp (b.atp - sAtp) sFetch (b.fetches - sFetch) 1
  /-- Recursive execution: carve out child budget `c`, execute child tree and continue parent on `afterSpawn b c`. -/
  | spawn (b c : Budget) (h : ValidSpawn b c)
      (cSAtp cRAtp cSFet cRFet cNodes : Nat)
      (pSAtp pRAtp pSFet pRFet pNodes : Nat)
      (hc : SporeExec c cSAtp cRAtp cSFet cRFet cNodes)
      (hp : SporeExec (afterSpawn b c) pSAtp pRAtp pSFet pRFet pNodes) :
      SporeExec b (cSAtp + pSAtp) (cRAtp + pRAtp) (cSFet + pSFet) (cRFet + pRFet) (cNodes + pNodes)

/-- **Global ATP Conservation Theorem**: across any recursive tree of spawned child spores,
    total spent ATP plus total remaining ATP equals the root's initial ATP budget. -/
theorem tree_conserves_atp {b : Budget} {sAtp rAtp sFet rFet nodes : Nat}
    (h : SporeExec b sAtp rAtp sFet rFet nodes) :
    sAtp + rAtp = b.atp := by
  induction h with
  | finish b sAtp sFetch hs =>
    have hc := Nat.sub_add_cancel hs.1
    omega
  | spawn b c hv _ _ _ _ _ _ _ _ _ _ _ _ ihc ihp =>
    have hsp := spawn_conserves_atp b c hv
    omega

/-- **Global Fetch Conservation Theorem**: total fetches performed plus remaining equals initial fetch budget. -/
theorem tree_conserves_fetches {b : Budget} {sAtp rAtp sFet rFet nodes : Nat}
    (h : SporeExec b sAtp rAtp sFet rFet nodes) :
    sFet + rFet = b.fetches := by
  induction h with
  | finish b sAtp sFetch hs =>
    have hc := Nat.sub_add_cancel hs.2
    omega
  | spawn b c hv _ _ _ _ _ _ _ _ _ _ _ _ ihc ihp =>
    have hsp := spawn_conserves_fetches b c hv
    omega

/-- **Bounded Spawn Tree Theorem**: total leaf/continuation executions never exceed `initial.spawns + 1`. -/
theorem tree_nodes_bounded {b : Budget} {sAtp rAtp sFet rFet nodes : Nat}
    (h : SporeExec b sAtp rAtp sFet rFet nodes) :
    nodes ≤ b.spawns + 1 := by
  induction h with
  | finish b _ _ _ =>
    omega
  | spawn b c hv _ _ _ _ _ _ _ _ _ _ _ _ ihc ihp =>
    have hsp := spawn_conserves_spawns b c hv
    omega

/-! ## 2. Exact 6-Dimensional Partiality Lattice & No Retelling Inflation (AS-4, AS-5) -/

inductive Integrity where
  | failed
  | verified
  deriving DecidableEq, Repr

inductive Authenticity where
  | failed
  | unsigned
  | untrusted
  | verified
  deriving DecidableEq, Repr

inductive SliceCompleteness where
  | partialSlice
  | completeSlice
  deriving DecidableEq, Repr

inductive ExecutionStatus where
  | refused
  | checkpointed
  | completed
  deriving DecidableEq, Repr

inductive HistoryLink where
  | unlinked
  | witnessed
  | verifiedHere
  deriving DecidableEq, Repr

inductive Reliance where
  | unreliable
  | conditional
  | reliable
  deriving DecidableEq, Repr

def Integrity.rank : Integrity → Nat
  | .failed => 0 | .verified => 1

def Authenticity.rank : Authenticity → Nat
  | .failed => 0 | .unsigned => 1 | .untrusted => 2 | .verified => 3

def SliceCompleteness.rank : SliceCompleteness → Nat
  | .partialSlice => 0 | .completeSlice => 1

def ExecutionStatus.rank : ExecutionStatus → Nat
  | .refused => 0 | .checkpointed => 1 | .completed => 2

def HistoryLink.rank : HistoryLink → Nat
  | .unlinked => 0 | .witnessed => 1 | .verifiedHere => 2

def Reliance.rank : Reliance → Nat
  | .unreliable => 0 | .conditional => 1 | .reliable => 2

def Integrity.meet (a b : Integrity) : Integrity :=
  if a.rank ≤ b.rank then a else b

def Authenticity.meet (a b : Authenticity) : Authenticity :=
  if a.rank ≤ b.rank then a else b

def SliceCompleteness.meet (a b : SliceCompleteness) : SliceCompleteness :=
  if a.rank ≤ b.rank then a else b

def ExecutionStatus.meet (a b : ExecutionStatus) : ExecutionStatus :=
  if a.rank ≤ b.rank then a else b

def HistoryLink.meet (a b : HistoryLink) : HistoryLink :=
  if a.rank ≤ b.rank then a else b

def Reliance.meet (a b : Reliance) : Reliance :=
  if a.rank ≤ b.rank then a else b

structure Partiality where
  integrity    : Integrity
  authenticity : Authenticity
  slice        : SliceCompleteness
  execution    : ExecutionStatus
  historyLink  : HistoryLink
  reliance     : Reliance
  deriving DecidableEq, Repr

/-- Componentwise order: `a ≤ b` iff `a` claims no stronger verification than `b` in any dimension. -/
def Partiality.le (a b : Partiality) : Prop :=
  a.integrity.rank ≤ b.integrity.rank ∧
  a.authenticity.rank ≤ b.authenticity.rank ∧
  a.slice.rank ≤ b.slice.rank ∧
  a.execution.rank ≤ b.execution.rank ∧
  a.historyLink.rank ≤ b.historyLink.rank ∧
  a.reliance.rank ≤ b.reliance.rank

/-- Componentwise meet (greatest lower bound) when combining parent and child evidence. -/
def Partiality.meet (a b : Partiality) : Partiality :=
  { integrity := a.integrity.meet b.integrity
    authenticity := a.authenticity.meet b.authenticity
    slice := a.slice.meet b.slice
    execution := a.execution.meet b.execution
    historyLink := a.historyLink.meet b.historyLink
    reliance := a.reliance.meet b.reliance }

/-- Passing a result from Agent B to Agent C without C re-verifying history downgrades
    `verifiedHere` to `witnessed` and never raises reliance above `conditional` when not locally verified. -/
def retellHistory : HistoryLink → HistoryLink
  | .verifiedHere => .witnessed
  | .witnessed    => .witnessed
  | .unlinked     => .unlinked

def retellReliance : Reliance → Reliance
  | .reliable    => .conditional
  | .conditional => .conditional
  | .unreliable  => .unreliable

def retell (p : Partiality) : Partiality :=
  { p with
    historyLink := retellHistory p.historyLink
    reliance := retellReliance p.reliance }

theorem retell_never_inflates (p : Partiality) : Partiality.le (retell p) p := by
  cases p with
  | mk i a s e h r =>
    refine ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, ?_, ?_⟩
    · cases h <;> simp [retell, retellHistory, HistoryLink.rank]
    · cases r <;> simp [retell, retellReliance, Reliance.rank]

theorem retell_never_verified_here (p : Partiality) : (retell p).historyLink ≠ .verifiedHere := by
  cases p with
  | mk i a s e h r =>
    cases h <;> simp [retell, retellHistory]

theorem retell_idempotent (p : Partiality) : retell (retell p) = retell p := by
  cases p with
  | mk i a s e h r =>
    cases h <;> cases r <;> rfl

private theorem rank_meet_le_left {α : Type} (rk : α → Nat) (x y : α) :
    rk (if rk x ≤ rk y then x else y) ≤ rk x := by
  split
  · exact Nat.le_refl _
  · omega

private theorem rank_meet_le_right {α : Type} (rk : α → Nat) (x y : α) :
    rk (if rk x ≤ rk y then x else y) ≤ rk y := by
  split
  · assumption
  · exact Nat.le_refl _

theorem meet_le_left (a b : Partiality) : Partiality.le (a.meet b) a :=
  ⟨rank_meet_le_left Integrity.rank _ _,
   rank_meet_le_left Authenticity.rank _ _,
   rank_meet_le_left SliceCompleteness.rank _ _,
   rank_meet_le_left ExecutionStatus.rank _ _,
   rank_meet_le_left HistoryLink.rank _ _,
   rank_meet_le_left Reliance.rank _ _⟩

theorem meet_le_right (a b : Partiality) : Partiality.le (a.meet b) b :=
  ⟨rank_meet_le_right Integrity.rank _ _,
   rank_meet_le_right Authenticity.rank _ _,
   rank_meet_le_right SliceCompleteness.rank _ _,
   rank_meet_le_right ExecutionStatus.rank _ _,
   rank_meet_le_right HistoryLink.rank _ _,
   rank_meet_le_right Reliance.rank _ _⟩

/-! ## 3. Counterexample-Driven Revision Monotonicity (AS-6) -/

/-- A result with recorded dependency closure `deps` requires reassessment when a counterexample hits `bad`. -/
def NeedsRevision {C : Type} (deps : List C) (bad : C) : Prop :=
  bad ∈ deps

/-- If `r2` carries the transitive dependencies of `r1` (`deps1 ⊆ deps2`), any counterexample
    requiring revision of `r1` necessarily requires revision of `r2`. -/
theorem revision_trans {C : Type} (deps1 deps2 : List C) (bad : C)
    (hsub : ∀ x, x ∈ deps1 → x ∈ deps2) (h1 : NeedsRevision deps1 bad) :
    NeedsRevision deps2 bad :=
  hsub bad h1

end Vars1.Spore
