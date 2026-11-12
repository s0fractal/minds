import Vars1.Witness

/-!
# The witness checker is complete on its fragment

`witness_sound` (`Witness.lean`) proves that `accepts` implies `Settled`. Here is the converse, where the checker's
rules read as the model's. `prove` builds a derivation from the store alone, and when the model holds a decision
`Settled`, `accepts` takes it (`witness_complete`). With soundness, `accepts S (prove S n d) d` is exactly `Settled`
there (`accepts_iff_settled`).

The prover decides Pass 1 by recursion over a rank (`effB`, `deadB`, `unsupB`): cells are named by the hash of their
contents, so a cell invalidates or supersedes only cells that do not name it, and a rank exists that every such edge
climbs. On it the Pass 1 equations have exactly one solution (`pass1_kernel_unique` in `Pass1.lean`), and the
prover's is it (`kernel_iff`): this is the stratified negation the derivation needs, each `eff` and `dead` drawn from
the stratum above.

The fragment (`Fragment`) is where every edge the derivation must read is decided by the store at the tip:
* the decision requires no computation, and every cell of the store is local (the model counts an edge only from an
  Accepted cell; every local cell is Accepted);
* every invalidates edge latched or not by quorum, which the store decides (§4.1 counts every seal on an edge's
  source under the governing scope, cumulatively); and every retires or supersedes edge into the decision's
  relevant cells (`Rel`: its live cone and what supersedes them, upward), and every supersedes edge out of its cone,
  is decided too: the author clause reads `InitialEndorsers`, fixed at the target's birth, so an edge whose quorum
  fails and one of whose target's keys seals its source is left out;
* every INVALID verdict on the decision is live, or not live because it is Invalidated or rests along `relies` on
  an Invalidated cell (`DownByInv`): a retired or superseded INVALID verdict is left out.

Completeness needs the decode to be complete as well as faithful (`PinComplete`): the store holds a seal for every
cumulative endorser of a local cell, under a scope of the chain and by a key of its roster, and every decision's
evaluator policy is among the decoded ones. It also needs ranks (`Ranked`): `rank` for `relies`, `ht` for
invalidates and supersedes, both below the prover's depth `n`.
-/

set_option linter.unusedSectionVars false

namespace Vars1.Witness

open Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K] [DecidableEq P]
variable (S : Store C K P)

/-! ## The prover's decisions -/

/-- `y` kills `x` as `deadB` reads it: an invalidates edge that latched, from a local killer that `eff` holds. -/
def killerOf (eff : C → Bool) (x y : C) : Bool :=
  decide (x ∈ S.invalidates y) && S.isLocal y && !nonInv S y && latchOK S y x .invalidates && eff y

/-- `w` invalidates `y` by an edge that may count: a killer, whose edge is not proved unlatched. -/
def attacker (y w : C) : Bool :=
  decide (y ∈ S.invalidates w) && !nonInv S w && !unlatchedOK S w y .invalidates

/-- `Effective` to depth `n` (over the invalidates rank). -/
def effB : Nat → C → Bool
  | 0, _ => false
  | n + 1, y => decide (y ∈ S.cells) && S.cells.all fun w => !attacker S y w || S.cells.any (killerOf S (effB n) w)

/-- `Invalidated` to depth `n`. -/
def deadB (n : Nat) (x : C) : Bool := S.cells.any (killerOf S (effB S n) x)

/-- `u` supersedes `w` by an edge that may count. -/
def supAttacker (w u : C) : Bool := decide (w ∈ S.supersedes u) && !unlatchedOK S u w .supersedes

/-- Not `Superseded`, to depth `n` (over the supersedes rank). -/
def unsupB (S : Store C K P) : Nat → C → Bool
  | 0, _ => false
  | n + 1, w => S.cells.all fun u => !supAttacker S w u || (deadB S n u && unsupB S n u)

/-- `w` retires `c` by an edge that may count. -/
def retAttacker (c w : C) : Bool := decide (c ∈ S.retires w) && !unlatchedOK S w c .retires

/-- Not `Retired`. -/
def retB (n : Nat) (c : C) : Bool := S.cells.all fun w => !retAttacker S c w || deadB S n w

/-- Every supersedes edge of `c` latched. -/
def outB (c : C) : Bool := (S.supersedes c).all fun u => latchOK S c u .supersedes

/-- The checker's `stand` conditions, with Pass 1 decided to depth `n`, closed under `relies` to depth `m`. -/
def standsB (S : Store C K P) (n : Nat) : Nat → C → Bool
  | 0, _ => false
  | m + 1, c => decide (c ∈ S.cells) && S.isLocal c && effB S n c && unsupB S n c && retB S n c && outB S c &&
      (S.relies c).all (standsB S n m)

/-- Not live, as `down` proves it: Invalidated, or relying on such a cell, to depth `m`. -/
def downB (S : Store C K P) (n : Nat) : Nat → C → Bool
  | 0, _ => false
  | m + 1, b => deadB S n b || (decide (b ∈ S.cells) && (S.relies b).any (downB S n m))

/-! ## The prover's lines -/

/-- A `latch` line for every edge of the store that latched by quorum, an `unlatched` line for every one that did not. -/
def edgeLines : List (Line C K) :=
  S.cells.flatMap fun y => [Kind.supersedes, Kind.retires, Kind.invalidates].flatMap fun k =>
    (edgesOf S y k).flatMap fun x =>
      (if latchOK S y x k then [⟨.latch, .latch y x k, []⟩] else []) ++
        (if unlatchedOK S y x k then [⟨.unlatch, .unlatched y x k, []⟩] else [])

def deadLine (n : Nat) (x : C) : Line C K :=
  ⟨.dead, .dead x, (S.cells.filter (killerOf S (effB S n) x)).flatMap fun y => [.latch y x .invalidates, .eff y]⟩

def effLine (y : C) : Line C K :=
  ⟨.eff, .eff y, (S.cells.filter fun w => decide (y ∈ S.invalidates w) && !nonInv S w).map fun w =>
    if unlatchedOK S w y .invalidates then .unlatched w y .invalidates else .dead w⟩

/-- Lines concluding `eff y`, after `dead w` for each cell that may count against it. -/
def effLines (S : Store C K P) : Nat → C → List (Line C K)
  | 0, _ => []
  | n + 1, y => (S.cells.filter (attacker S y)).flatMap
      (fun w => (S.cells.filter (killerOf S (effB S n) w)).flatMap (effLines S n) ++ [deadLine S n w]) ++
      [effLine S y]

/-- Lines concluding `dead x`, after `eff y` for each of its killers. -/
def deadLines (n : Nat) (x : C) : List (Line C K) :=
  (S.cells.filter (killerOf S (effB S n) x)).flatMap (effLines S n) ++ [deadLine S n x]

theorem effLines_succ (n : Nat) (y : C) :
    effLines S (n + 1) y = (S.cells.filter (attacker S y)).flatMap (deadLines S n) ++ [effLine S y] := rfl

def unsupLine (w : C) : Line C K :=
  ⟨.unsup, .unsup w, (S.cells.filter fun u => decide (w ∈ S.supersedes u)).flatMap fun u =>
    if unlatchedOK S u w .supersedes then [.unlatched u w .supersedes] else [.dead u, .unsup u]⟩

def unsupLines (S : Store C K P) : Nat → C → List (Line C K)
  | 0, _ => []
  | n + 1, w => (S.cells.filter (supAttacker S w)).flatMap (fun u => deadLines S n u ++ unsupLines S n u) ++
      [unsupLine S w]

def standLine (c : C) : Line C K :=
  ⟨.stand, .stands c, .eff c :: .unsup c ::
    (((S.cells.filter fun w => decide (c ∈ S.retires w)).map fun w =>
      if unlatchedOK S w c .retires then .unlatched w c .retires else .dead w) ++
    ((S.supersedes c).map fun u => .latch c u .supersedes) ++ (S.relies c).map .stands)⟩

/-- Stand lines for `c`, after its Pass 1 lines and those for what it relies on, to depth `m`. -/
def standLines (S : Store C K P) (n : Nat) : Nat → C → List (Line C K)
  | 0, _ => []
  | m + 1, c => effLines S n c ++ unsupLines S n c ++ (S.cells.filter (retAttacker S c)).flatMap (deadLines S n) ++
      (S.relies c).flatMap (standLines S n m) ++ [standLine S c]

def downLine (n m : Nat) (b : C) : Line C K :=
  ⟨.down, .down b, if deadB S n b then [.dead b] else ((S.relies b).filter (downB S n m)).map .down⟩

def downLines (S : Store C K P) (n : Nat) : Nat → C → List (Line C K)
  | 0, _ => []
  | m + 1, b => (if deadB S n b then deadLines S n b
      else ((S.relies b).filter (downB S n m)).flatMap (downLines S n m)) ++ [downLine S n m b]

/-- A verdict the prover counts for `d`: an ATTESTED verdict with an empty witness slot that judges and attests `d`,
and stands to depth `n`. -/
def countable (n : Nat) (d w : C) : Bool :=
  decide (S.schema w = .verdict) && decide (S.payload w = some d) && decide (d ∈ S.attests w) &&
    (S.verdict w).attested && decide ((S.verdict w).witness = none) && standsB S n n w

/-- The verdicts the prover counts for `d`. -/
def counted (n : Nat) (d : C) : List C := S.cells.filter (countable S n d)

/-- An INVALID verdict on `d`. -/
def invalidOn (d b : C) : Bool :=
  decide (S.schema b = .verdict) && decide (S.payload b = some d) && (S.verdict b).invalid

/-- The INVALID verdicts on `d` the prover proves not live. -/
def downs (n : Nat) (d : C) : List C := S.cells.filter fun b => invalidOn S d b && downB S n n b

/-- The endorsements the prover names: a key of `d`'s evaluator policy that seals a counted verdict under a scope of
the chain, as a key of that scope's roster, and that every INVALID verdict of the store that may withdraw it is proved
not live. -/
def pairs (n : Nat) (d : C) : List (C × K) :=
  (counted S n d).flatMap fun w =>
    ((S.keys (evalPol S d)).filter fun k => endorseOK S w k [] &&
      S.cells.all fun b => !withdraws S d w k b || downB S n n b).map fun k => (w, k)

def endorseLine (p : C × K) : Line C K := ⟨.endorse, .endorsed p.1 p.2, []⟩

def settlePrem (n : Nat) (d : C) : List (Concl C K) :=
  .stands d :: ((counted S n d).map .stands ++ (pairs S n d).map (fun p => .endorsed p.1 p.2) ++
    (downs S n d).map .down)

/-- **The prover.** A derivation that `d` is settled, built from the store alone: the edge lines, stand lines for `d`
and each counted verdict, down lines for the INVALID verdicts on `d` it proves not live, an endorse line for each
named endorsement, then the settle line. -/
def prove (n : Nat) (d : C) : List (Line C K) :=
  edgeLines S ++ standLines S n n d ++ (counted S n d).flatMap (standLines S n n) ++
    (downs S n d).flatMap (downLines S n n) ++ (pairs S n d).flatMap (fun p => [endorseLine p]) ++
    [⟨.settle, .settled d, settlePrem S n d⟩]

theorem mem_pairs {n : Nat} {d w : C} {k : K} (h : (w, k) ∈ pairs S n d) :
    w ∈ counted S n d ∧ k ∈ S.keys (evalPol S d) ∧ endorseOK S w k [] = true ∧
      (S.cells.all fun b => !withdraws S d w k b || downB S n n b) = true := by
  obtain ⟨w', hw', hm⟩ := List.mem_flatMap.mp h
  obtain ⟨k', hk', he⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hf := (List.mem_filter.mp hk').2
  simp only [Bool.and_eq_true] at hf
  exact ⟨hw', (List.mem_filter.mp hk').1, hf.1, hf.2⟩

/-! ## Running the checker over pieces of a derivation -/

theorem run_append (done : List (Concl C K)) (l₁ l₂ : List (Line C K)) :
    run S done (l₁ ++ l₂) = (run S done l₁).bind (fun o => run S o l₂) := by
  induction l₁ generalizing done with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.cons_append, run]
    split
    · exact ih _
    · rfl

theorem run_single {done : List (Concl C K)} {l : Line C K} (h : lineOK S done l = true) :
    run S done [l] = some (l.concl :: done) := by
  simp only [run, h, if_true]

/-- A line whose premises are among `done` and whose rule checks, checks. -/
theorem lineOK_of {done : List (Concl C K)} {l : Line C K} (hp : ∀ p ∈ l.prem, p ∈ done) (hr : ruleOK S l = true) :
    lineOK S done l = true := by
  simp only [lineOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨hp, hr⟩

/-- What the pieces of a derivation conclude: the conclusions in `out`, which keeps what `done` held. -/
def Reaches (done : List (Concl C K)) (ls : List (Line C K)) (gs : List (Concl C K)) : Prop :=
  ∃ out, run S done ls = some out ∧ (∀ q ∈ gs, q ∈ out) ∧ ∀ p ∈ done, p ∈ out

theorem Reaches.weaken {done : List (Concl C K)} {ls : List (Line C K)} {gs gs' : List (Concl C K)}
    (h : Reaches S done ls gs) (hg : ∀ q ∈ gs', q ∈ gs) : Reaches S done ls gs' := by
  obtain ⟨out, r, hgs, hs⟩ := h
  exact ⟨out, r, fun q hq => hgs q (hg q hq), hs⟩

theorem reaches_single {done : List (Concl C K)} {l : Line C K} (h : lineOK S done l = true) :
    Reaches S done [l] [l.concl] :=
  ⟨_, run_single S h, by simp, fun _ hp => List.mem_cons_of_mem _ hp⟩

theorem reaches_append {done : List (Concl C K)} {l₁ l₂ : List (Line C K)} {g₁ g₂ : List (Concl C K)}
    (h₁ : Reaches S done l₁ g₁) (h₂ : ∀ o, (∀ q ∈ g₁, q ∈ o) → (∀ p ∈ done, p ∈ o) → Reaches S o l₂ g₂) :
    Reaches S done (l₁ ++ l₂) (g₁ ++ g₂) := by
  obtain ⟨o1, r1, hg1, hs1⟩ := h₁
  obtain ⟨o2, r2, hg2, hs2⟩ := h₂ o1 hg1 hs1
  refine ⟨o2, ?_, ?_, fun p hp => hs2 p (hs1 p hp)⟩
  · rw [run_append, r1]; exact r2
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hs2 q (hg1 q hq)
    · exact hg2 q hq

/-- Running the pieces `f a` one after another reaches every `g a`, when each piece reaches its own from any start that
an invariant `Q`, which grows with `done`, holds of. -/
theorem reaches_flatMap {α : Type} (Q : List (Concl C K) → Prop) (hQ : ∀ a b, Q a → (∀ p ∈ a, p ∈ b) → Q b)
    (f : α → List (Line C K)) (g : α → List (Concl C K)) :
    ∀ (as : List α), (∀ a ∈ as, ∀ done, Q done → Reaches S done (f a) (g a)) →
    ∀ done, Q done → Reaches S done (as.flatMap f) (as.flatMap g)
  | [], _, done, _ => ⟨done, rfl, by simp, fun _ hp => hp⟩
  | a :: as, h, done, hq => by
    rw [List.flatMap_cons, List.flatMap_cons]
    refine reaches_append S (h a List.mem_cons_self done hq) fun o _ hs => ?_
    exact reaches_flatMap Q hQ f g as (fun b hb => h b (List.mem_cons_of_mem _ hb)) o (hQ _ _ hq hs)

/-- Lines with no premises whose rules check run from any start. -/
theorem reaches_free : ∀ (ls : List (Line C K)), (∀ l ∈ ls, l.prem = [] ∧ ruleOK S l = true) →
    ∀ done, Reaches S done ls (ls.map (·.concl))
  | [], _, done => ⟨done, rfl, by simp, fun _ h => h⟩
  | l :: ls, h, done => by
    have hl : lineOK S done l = true := by
      obtain ⟨hp, hr⟩ := h l List.mem_cons_self
      exact lineOK_of S (by simp [hp]) hr
    have := reaches_append S (l₁ := [l]) (reaches_single S hl) fun o _ _ =>
      reaches_free ls (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')) o
    simpa using this

/-- The latch facts a set of conclusions holds. -/
def EdgeFacts (done : List (Concl C K)) : Prop :=
  ∀ y ∈ S.cells, ∀ (k : Kind) (x : C), x ∈ edgesOf S y k →
    (latchOK S y x k = true → Concl.latch y x k ∈ done) ∧ (unlatchedOK S y x k = true → Concl.unlatched y x k ∈ done)

theorem EdgeFacts.mono {a b : List (Concl C K)} (h : EdgeFacts S a) (hab : ∀ p ∈ a, p ∈ b) : EdgeFacts S b :=
  fun y hy k x hx => ⟨fun hl => hab _ ((h y hy k x hx).1 hl), fun hu => hab _ ((h y hy k x hx).2 hu)⟩

theorem edgeFacts_mono : ∀ a b : List (Concl C K), EdgeFacts S a → (∀ p ∈ a, p ∈ b) → EdgeFacts S b :=
  fun _ _ h hab => h.mono S hab

theorem mem_kinds (k : Kind) : k ∈ [Kind.supersedes, Kind.retires, Kind.invalidates] := by
  cases k <;> simp

/-- The edge lines run from any start and leave the latch facts of every edge. -/
theorem edge_run (done : List (Concl C K)) :
    ∃ out, run S done (edgeLines S) = some out ∧ EdgeFacts S out ∧ ∀ p ∈ done, p ∈ out := by
  have hfree : ∀ l ∈ edgeLines S, l.prem = [] ∧ ruleOK S l = true := by
    intro l hl
    simp only [edgeLines, List.mem_flatMap, List.mem_append] at hl
    obtain ⟨y, -, k, -, x, -, hl⟩ := hl
    rcases hl with hl | hl
    · cases hlk : latchOK S y x k <;> simp only [hlk, Bool.false_eq_true, if_false, if_true,
        List.not_mem_nil, List.mem_singleton] at hl
      subst hl
      simp [ruleOK, Concl.rule, hlk]
    · cases hlk : unlatchedOK S y x k <;> simp only [hlk, Bool.false_eq_true, if_false, if_true,
        List.not_mem_nil, List.mem_singleton] at hl
      subst hl
      simp [ruleOK, Concl.rule, hlk]
  obtain ⟨out, ho, hc, hs⟩ := reaches_free S (edgeLines S) hfree done
  refine ⟨out, ho, ?_, hs⟩
  intro y hy k x hx
  constructor
  · intro hl
    apply hc
    simp only [List.mem_map, edgeLines, List.mem_flatMap, List.mem_append]
    exact ⟨⟨.latch, .latch y x k, []⟩, ⟨y, hy, k, mem_kinds k, x, hx, Or.inl (by simp [hl])⟩, rfl⟩
  · intro hu
    apply hc
    simp only [List.mem_map, edgeLines, List.mem_flatMap, List.mem_append]
    exact ⟨⟨.unlatch, .unlatched y x k, []⟩, ⟨y, hy, k, mem_kinds k, x, hx, Or.inr (by simp [hu])⟩, rfl⟩

/-! ## The prover's lines reach what its decisions say -/

/-- The `eff` and `dead` lines run wherever `effB` and `deadB` hold. -/
theorem kernel_run : ∀ n : Nat,
    (∀ y, effB S n y = true → ∀ done, EdgeFacts S done → Reaches S done (effLines S n y) [.eff y]) ∧
    (∀ x, deadB S n x = true → ∀ done, EdgeFacts S done → Reaches S done (deadLines S n x) [.dead x]) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun y h => by simp [effB] at h, fun x h => ?_⟩
    simp [deadB, killerOf, effB] at h
  | succ n ih =>
    have heff : ∀ y, effB S (n + 1) y = true → ∀ done, EdgeFacts S done →
        Reaches S done (effLines S (n + 1) y) [.eff y] := by
      intro y hy done hd
      simp only [effB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
        Bool.not_eq_true'] at hy
      obtain ⟨hyc, hall⟩ := hy
      rw [effLines_succ]
      have h1 := reaches_flatMap S (EdgeFacts S) (edgeFacts_mono S) (deadLines S n) (fun w => [.dead w])
        (S.cells.filter (attacker S y)) (fun w hw o ho => by
          have hwc := (List.mem_filter.mp hw).1
          have ha := (List.mem_filter.mp hw).2
          rcases hall w hwc with h | h
          · rw [ha] at h; exact Bool.noConfusion h
          · exact ih.2 w h o ho) done hd
      have := reaches_append S (l₂ := [effLine S y]) (g₂ := [.eff y]) h1 fun o hg hs => by
        refine reaches_single S (lineOK_of S ?_ ?_)
        · intro p hp
          simp only [effLine, List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
            Bool.not_eq_true'] at hp
          obtain ⟨w, ⟨hwc, hyw, hnw⟩, rfl⟩ := hp
          cases hu : unlatchedOK S w y .invalidates with
          | true =>
            simp only [hu, if_true]
            exact ((hd.mono S hs) w hwc .invalidates y hyw).2 hu
          | false =>
            simp only [hu, Bool.false_eq_true, if_false]
            apply hg
            simp only [List.mem_flatMap, List.mem_filter, List.mem_singleton]
            refine ⟨w, ⟨hwc, ?_⟩, rfl⟩
            simp [attacker, hyw, hnw, hu]
        · simp only [ruleOK, effLine, Concl.rule, decide_true, Bool.true_and, effOK, Bool.and_eq_true,
            decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
          refine ⟨hyc, fun w hwc => ?_⟩
          by_cases hyw : y ∈ S.invalidates w
          · cases hn : nonInv S w with
            | true => exact Or.inl (Or.inl (Or.inr rfl))
            | false =>
              cases hu : unlatchedOK S w y .invalidates with
              | true =>
                refine Or.inl (Or.inr ?_)
                simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
                exact ⟨w, ⟨hwc, hyw, by simp [hn]⟩, by simp [hu]⟩
              | false =>
                refine Or.inr ?_
                simp only [List.mem_map, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
                exact ⟨w, ⟨hwc, hyw, by simp [hn]⟩, by simp [hu]⟩
          · exact Or.inl (Or.inl (Or.inl hyw))
      exact this.weaken S (by simp)
    refine ⟨heff, fun x hx done hd => ?_⟩
    have h1 := reaches_flatMap S (EdgeFacts S) (edgeFacts_mono S) (effLines S (n + 1)) (fun y => [.eff y])
      (S.cells.filter (killerOf S (effB S (n + 1)) x)) (fun y hy o ho => by
        have hk := (List.mem_filter.mp hy).2
        simp only [killerOf, Bool.and_eq_true] at hk
        exact heff y hk.2 o ho) done hd
    have := reaches_append S (l₂ := [deadLine S (n + 1) x]) (g₂ := [.dead x]) h1 fun o hg hs => by
      refine reaches_single S (lineOK_of S ?_ ?_)
      · intro p hp
        simp only [deadLine, List.mem_flatMap, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
        obtain ⟨y, hy, hp⟩ := hp
        have hyc := (List.mem_filter.mp hy).1
        have hk := (List.mem_filter.mp hy).2
        simp only [killerOf, Bool.and_eq_true, decide_eq_true_eq] at hk
        rcases hp with rfl | rfl
        · exact ((hd.mono S hs) y hyc .invalidates x hk.1.1.1.1).1 hk.1.2
        · apply hg
          simp only [List.mem_flatMap, List.mem_singleton]
          exact ⟨y, hy, rfl⟩
      · simp only [ruleOK, deadLine, Concl.rule, decide_true, Bool.true_and, deadOK, List.any_eq_true,
          Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
        simp only [deadB, List.any_eq_true] at hx
        obtain ⟨y, hyc, hk⟩ := hx
        have hyf : y ∈ S.cells.filter (killerOf S (effB S (n + 1)) x) := List.mem_filter.mpr ⟨hyc, hk⟩
        simp only [killerOf, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hk
        refine ⟨y, hyc, ⟨⟨⟨⟨hk.1.1.1.1, hk.1.1.1.2⟩, hk.1.1.2⟩, ?_⟩, ?_⟩⟩
        · simp only [List.mem_flatMap, List.mem_cons, List.mem_singleton]
          exact ⟨y, hyf, Or.inl rfl⟩
        · simp only [List.mem_flatMap, List.mem_cons, List.mem_singleton]
          exact ⟨y, hyf, Or.inr (Or.inl rfl)⟩
    exact this.weaken S (by simp)

/-- The `unsup` lines run wherever `unsupB` holds. -/
theorem unsup_run : ∀ n w, unsupB S n w = true → ∀ done, EdgeFacts S done → Reaches S done (unsupLines S n w) [.unsup w]
  | 0, _, h, _, _ => by simp [unsupB] at h
  | n + 1, w, h, done, hd => by
    simp only [unsupB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at h
    have h1 := reaches_flatMap S (EdgeFacts S) (edgeFacts_mono S) (fun u => deadLines S n u ++ unsupLines S n u)
      (fun u => [.dead u, .unsup u]) (S.cells.filter (supAttacker S w)) (fun u hu o ho => by
        have huc := (List.mem_filter.mp hu).1
        have ha := (List.mem_filter.mp hu).2
        rcases h u huc with h' | ⟨hdu, huu⟩
        · rw [ha] at h'; exact Bool.noConfusion h'
        · have := reaches_append S ((kernel_run S n).2 u hdu o ho) fun o' _ hs =>
            unsup_run n u huu o' ((ho.mono S) hs)
          simpa using this) done hd
    have := reaches_append S (l₂ := [unsupLine S w]) (g₂ := [.unsup w]) h1 fun o hg hs => by
      refine reaches_single S (lineOK_of S ?_ ?_)
      · intro p hp
        simp only [unsupLine, List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hp
        obtain ⟨u, ⟨huc, hwu⟩, hp⟩ := hp
        cases hu : unlatchedOK S u w .supersedes with
        | true =>
          simp only [hu, if_true, List.mem_singleton] at hp
          subst hp
          exact ((hd.mono S hs) u huc .supersedes w hwu).2 hu
        | false =>
          simp only [hu, Bool.false_eq_true, if_false, List.mem_cons, List.mem_singleton, List.not_mem_nil,
            or_false] at hp
          have hf : u ∈ S.cells.filter (supAttacker S w) := List.mem_filter.mpr ⟨huc, by simp [supAttacker, hwu, hu]⟩
          rcases hp with rfl | rfl
          · exact hg _ (List.mem_flatMap.mpr ⟨u, hf, by simp⟩)
          · exact hg _ (List.mem_flatMap.mpr ⟨u, hf, by simp⟩)
      · simp only [ruleOK, unsupLine, Concl.rule, decide_true, Bool.true_and, unsupOK, List.all_eq_true,
          Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, Bool.and_eq_true]
        intro u huc
        by_cases hwu : w ∈ S.supersedes u
        · have hfu : u ∈ S.cells.filter fun u => decide (w ∈ S.supersedes u) :=
            List.mem_filter.mpr ⟨huc, by simp [hwu]⟩
          cases hu : unlatchedOK S u w .supersedes with
          | true => exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨u, hfu, by simp [hu]⟩))
          | false =>
            exact Or.inr ⟨List.mem_flatMap.mpr ⟨u, hfu, by simp [hu]⟩, List.mem_flatMap.mpr ⟨u, hfu, by simp [hu]⟩⟩
        · exact Or.inl (Or.inl hwu)
    simpa [unsupLines] using this.weaken S (gs' := [.unsup w]) (by simp)

/-- The stand lines of a cell whose stand conditions hold to depth `m` run and conclude that it stands. -/
theorem stand_run (n : Nat) : ∀ (m : Nat) (c : C), standsB S n m c = true →
    ∀ done, EdgeFacts S done → Reaches S done (standLines S n m c) [.stands c]
  | 0, c, h, _, _ => by simp [standsB] at h
  | m + 1, c, h, done, hd => by
    simp only [standsB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨hc, hl⟩, he⟩, hu⟩, hr⟩, ho⟩, hrel⟩ := h
    have r1 := (kernel_run S n).1 c he done hd
    have r2 := reaches_append S r1 fun o _ hs => unsup_run S n c hu o ((hd.mono S) hs)
    have r3 := reaches_append S r2 fun o _ hs =>
      reaches_flatMap S (EdgeFacts S) (edgeFacts_mono S) (deadLines S n) (fun w => [.dead w])
        (S.cells.filter (retAttacker S c)) (fun w hw o' ho' => by
          have hwc := (List.mem_filter.mp hw).1
          have ha := (List.mem_filter.mp hw).2
          simp only [retB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hr
          rcases hr w hwc with h' | h'
          · rw [ha] at h'; exact Bool.noConfusion h'
          · exact (kernel_run S n).2 w h' o' ho') o ((hd.mono S) hs)
    have r4 := reaches_append S r3 fun o _ hs =>
      reaches_flatMap S (EdgeFacts S) (edgeFacts_mono S) (standLines S n m) (fun r => [.stands r])
        (S.relies c) (fun r hr' o' ho' => stand_run n m r (hrel r hr') o' ho') o ((hd.mono S) hs)
    have := reaches_append S (l₂ := [standLine S c]) (g₂ := [.stands c]) r4 fun o hg hs => by
      refine reaches_single S (lineOK_of S ?_ ?_)
      · intro p hp
        simp only [standLine, List.mem_cons, List.mem_append, List.mem_map, List.mem_filter,
          decide_eq_true_eq] at hp
        rcases hp with rfl | rfl | ((⟨w, ⟨hwc, hcw⟩, rfl⟩ | ⟨u, hu', rfl⟩) | ⟨r, hr', rfl⟩)
        · exact hg _ (by simp)
        · exact hg _ (by simp)
        · cases hun : unlatchedOK S w c .retires with
          | true =>
            simp only [hun, if_true]
            exact ((hd.mono S hs) w hwc .retires c hcw).2 hun
          | false =>
            simp only [hun, Bool.false_eq_true, if_false]
            apply hg
            simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_singleton, List.mem_cons]
            exact Or.inl (Or.inr ⟨w, ⟨hwc, by simp [retAttacker, hcw, hun]⟩, by simp⟩)
        · simp only [outB, List.all_eq_true] at ho
          exact ((hd.mono S hs) c hc .supersedes u hu').1 (ho u hu')
        · apply hg
          simp only [List.mem_append, List.mem_flatMap, List.mem_singleton]
          exact Or.inr ⟨r, hr', rfl⟩
      · have hA : ∀ q ∈ ((S.cells.filter fun w => decide (c ∈ S.retires w)).map fun w =>
            if unlatchedOK S w c .retires then Concl.unlatched w c .retires else .dead w),
            q ∈ (standLine S c).prem := fun q hq =>
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_left _ hq)))
        have hB : ∀ q ∈ ((S.supersedes c).map fun u => Concl.latch c u .supersedes), q ∈ (standLine S c).prem :=
          fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
            (List.mem_append_right _ hq)))
        have hC : ∀ q ∈ ((S.relies c).map Concl.stands), q ∈ (standLine S c).prem :=
          fun q hq => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hq))
        show (decide (Rule.stand = Rule.stand) && standOK S c (standLine S c).prem) = true
        simp only [decide_true, Bool.true_and, standOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
          Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
        refine ⟨⟨⟨⟨⟨⟨hc, hl⟩, List.mem_cons_self⟩, List.mem_cons_of_mem _ List.mem_cons_self⟩, ?_⟩, ?_⟩, ?_⟩
        · intro w hwc
          by_cases hcw : c ∈ S.retires w
          · have hwf : w ∈ S.cells.filter fun w => decide (c ∈ S.retires w) := List.mem_filter.mpr ⟨hwc, by simp [hcw]⟩
            cases hun : unlatchedOK S w c .retires with
            | true => exact Or.inr (hA _ (List.mem_map.mpr ⟨w, hwf, by simp [hun]⟩))
            | false => exact Or.inl (Or.inr (hA _ (List.mem_map.mpr ⟨w, hwf, by simp [hun]⟩)))
          · exact Or.inl (Or.inl hcw)
        · intro u hu'
          exact hB _ (List.mem_map.mpr ⟨u, hu', rfl⟩)
        · intro r hr'
          exact hC _ (List.mem_map.mpr ⟨r, hr', rfl⟩)
    simpa [standLines] using this.weaken S (gs' := [.stands c]) (by simp)

/-- The down lines run wherever `downB` holds. -/
theorem down_run (n : Nat) : ∀ (m : Nat) (b : C), downB S n m b = true →
    ∀ done, EdgeFacts S done → Reaches S done (downLines S n m b) [.down b]
  | 0, _, h, _, _ => by simp [downB] at h
  | m + 1, b, h, done, hd => by
    cases hdb : deadB S n b with
    | true =>
      have := reaches_append S (l₂ := [downLine S n m b]) (g₂ := [.down b]) ((kernel_run S n).2 b hdb done hd)
        fun o hg _ => by
        refine reaches_single S (lineOK_of S ?_ ?_)
        · intro p hp
          simp only [downLine, hdb, if_true, List.mem_singleton] at hp
          subst hp
          exact hg _ (by simp)
        · simp [ruleOK, downLine, Concl.rule, downOK, hdb]
      simpa [downLines, hdb] using this.weaken S (gs' := [.down b]) (by simp)
    | false =>
      simp only [downB, hdb, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
      obtain ⟨hb, r, hr, hdr⟩ := h
      have h1 := reaches_flatMap S (EdgeFacts S) (edgeFacts_mono S) (downLines S n m) (fun r => [.down r])
        ((S.relies b).filter (downB S n m)) (fun r' hr' o ho =>
          down_run n m r' (List.mem_filter.mp hr').2 o ho) done hd
      have := reaches_append S (l₂ := [downLine S n m b]) (g₂ := [.down b]) h1 fun o hg _ => by
        refine reaches_single S (lineOK_of S ?_ ?_)
        · intro p hp
          simp only [downLine, hdb, Bool.false_eq_true, if_false, List.mem_map] at hp
          obtain ⟨r', hr', rfl⟩ := hp
          exact hg _ (List.mem_flatMap.mpr ⟨r', hr', by simp⟩)
        · simp only [ruleOK, downLine, hdb, Bool.false_eq_true, if_false, Concl.rule, decide_true, Bool.true_and,
            downOK, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, List.any_eq_true, List.mem_map,
            List.mem_filter]
          exact Or.inr ⟨hb, r, hr, r, ⟨hr, hdr⟩, rfl⟩
      simpa [downLines, hdb] using this.weaken S (gs' := [.down b]) (by simp)

/-! ## Lemmas on keys -/

theorem endorsedKeys_of_mem {k : K} {w : C} : ∀ {ps : List (Concl C K)}, Concl.endorsed w k ∈ ps → k ∈ endorsedKeys ps
  | [], h => absurd h List.not_mem_nil
  | .endorsed w' j :: ps, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (endorsedKeys_of_mem h)
  | .stands _ :: ps, h | .settled _ :: ps, h | .latch _ _ _ :: ps, h | .unlatched _ _ _ :: ps, h
  | .dead _ :: ps, h | .eff _ :: ps, h | .unsup _ :: ps, h | .down _ :: ps, h | .grounded _ :: ps, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h
    · exact endorsedKeys_of_mem (ps := ps) h

/-! ## What completeness asks of the store and the model -/

/-- What completeness asks of the decode beyond `Pin`: that it holds every seal and policy the model counts. -/
structure PinComplete (W : World C K P) (X : Pass3In C K P) : Prop where
  seals : ∀ w ∈ S.cells, S.isLocal w = true → ∀ k ∈ X.cumulative w,
    ∃ cp ∈ S.ctxs, k ∈ S.keys cp.2 ∧ ∃ s ∈ S.seals, s.target = w ∧ s.ctx = cp.1 ∧ s.key = k
  pols : ∀ d ∈ S.cells, (S.schema d = .decision ∨ S.schema d = .contract) → evalPol S d ∈ S.pols

/-- A decision's live cone: the decision, the verdicts of `W_max`, and what they rely on. -/
inductive Cone (W : World C K P) (X : Pass3In C K P) (cells : List C) (d : C) : C → Prop where
  | self : Cone W X cells d d
  | verdict {w : C} : InWmax W X cells d w → Cone W X cells d w
  | relies {c r : C} : Cone W X cells d c → r ∈ (W.info c).relies → Cone W X cells d r

/-- The cells whose not being superseded the derivation reads: the live cone, and upward along supersedes. -/
inductive Rel (S : Store C K P) (W : World C K P) (X : Pass3In C K P) (d : C) : C → Prop where
  | cone {c : C} : Cone W X S.cells d c → Rel S W X d c
  | up {w u : C} : Rel S W X d w → u ∈ S.cells → w ∈ S.supersedes u → Rel S W X d u

/-- Not live because Invalidated, or resting along `relies` on an Invalidated cell. -/
inductive DownByInv (S : Store C K P) (Inv : C → Prop) : C → Prop where
  | dead {b : C} : b ∈ S.cells → Inv b → DownByInv S Inv b
  | relies {b r : C} : b ∈ S.cells → r ∈ S.relies b → DownByInv S Inv r → DownByInv S Inv b

/-- The store decides whether the edge `y → x` of kind `k` latched. -/
def decided (y x : C) (k : Kind) : Bool := latchOK S y x k || unlatchedOK S y x k

/-- The fragment of `d`: no computation, only local cells, every edge the derivation reads decided by the store, and
every INVALID verdict on `d` live or not live through an Invalidated cell. -/
structure Fragment (W : World C K P) (X : Pass3In C K P) (Inv : C → Prop) (d : C) : Prop where
  req : S.req d = none
  isLocal : ∀ c ∈ S.cells, S.isLocal c = true
  invDecided : ∀ y ∈ S.cells, ∀ x ∈ S.cells, x ∈ S.invalidates y → decided S y x .invalidates = true
  evictDecided : ∀ y ∈ S.cells, ∀ (x : C) (k : Kind), k ≠ .invalidates → x ∈ edgesOf S y k →
    (Rel S W X d x ∨ Cone W X S.cells d y) → decided S y x k = true
  invalid : ∀ b ∈ S.cells, S.schema b = .verdict → S.payload b = some d → (S.verdict b).invalid = true →
    Live X b ∨ DownByInv S Inv b

/-- Ranks the prover's recursions descend, below its depth `n`: `relies` descends `rank`; invalidates and supersedes
edges climb `ht`. Cells are named by the hash of their contents, so both exist. -/
structure Ranked (rank ht : C → Nat) (n : Nat) : Prop where
  relies : ∀ c ∈ S.cells, ∀ r ∈ S.relies c, rank r < rank c
  invalidates : ∀ y ∈ S.cells, ∀ x ∈ S.invalidates y, ht y < ht x
  supersedes : ∀ y ∈ S.cells, ∀ x ∈ S.supersedes y, ht y < ht x
  bound : ∀ c ∈ S.cells, rank c < n ∧ ht c < n

/-! ## Completeness -/

section Complete

variable {S}
variable {W : World C K P} {X : Pass3In C K P} {wmax : C → List C} {cnt : C → C → List K}
variable {AE : C → C → Kind → Bool} {Present isIntrinsic : C → Prop} {Auth : C → Bool} {Inv Eff Ret Acc : C → Prop}

theorem latchOK_of_decided (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {y x : C} {k : Kind}
    (hd : decided S y x k = true) (hae : AE y x k = true) : latchOK S y x k = true := by
  simp only [decided, Bool.or_eq_true] at hd
  rcases hd with h | h
  · exact h
  · rw [unlatched_sound pin h] at hae; exact Bool.noConfusion hae

theorem latchOK_of_not_unlatched {y x : C} {k : Kind} (hd : decided S y x k = true)
    (hu : unlatchedOK S y x k = false) : latchOK S y x k = true := by
  simp only [decided, Bool.or_eq_true, hu, Bool.false_eq_true, or_false] at hd
  exact hd

/-- **The prover's Pass 1 is the model's.** On a store of local cells whose invalidates edges the store decides, and
that climb a rank, `effB` and `deadB` are `Effective` and `Invalidated` above the rank: the unique solution of the
Pass 1 equations (`pass1_kernel_unique`), computed. -/
theorem kernel_iff (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X)
    (hloc : ∀ c ∈ S.cells, S.isLocal c = true)
    (hdec : ∀ y ∈ S.cells, ∀ x ∈ S.cells, x ∈ S.invalidates y → decided S y x .invalidates = true)
    (ht : C → Nat) (hht : ∀ y ∈ S.cells, ∀ x ∈ S.invalidates y, ht y < ht x) :
    ∀ m, (∀ c ∈ S.cells, ht c < m → (effB S m c = true ↔ Eff c)) ∧
      (∀ c ∈ S.cells, ht c < m → (deadB S m c = true ↔ Inv c)) := by
  have dOfE : ∀ m, (∀ c ∈ S.cells, ht c < m → (effB S m c = true ↔ Eff c)) →
      ∀ c ∈ S.cells, ht c < m → (deadB S m c = true ↔ Inv c) := by
    intro m hE c hc hcm
    constructor
    · intro h
      simp only [deadB, killerOf, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
      obtain ⟨z, hz, ⟨⟨⟨⟨hcz, hl⟩, hk⟩, hlat⟩, heff⟩⟩ := h
      have hzc : ht z < m := Nat.lt_trans (hht z hz c hcz) hcm
      exact (pin.pass1.inv_eq c).mpr ⟨z, (hE z hz hzc).mp heff, acc_of_local pin hz hl,
        (pin.invalidates z hz).symm ▸ hcz, latch_sound pin hlat, killer_of_nonInv pin hz hk⟩
    · intro h
      obtain ⟨w, hw, -, hcw, hae, hkill⟩ := (pin.pass1.inv_eq c).mp h
      have hwc := eff_present pin hw
      have hcw' : c ∈ S.invalidates w := (pin.invalidates w hwc) ▸ hcw
      have hwm : ht w < m := Nat.lt_trans (hht w hwc c hcw') hcm
      simp only [deadB, List.any_eq_true]
      refine ⟨w, hwc, ?_⟩
      simp only [killerOf, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
      exact ⟨⟨⟨⟨hcw', hloc w hwc⟩, nonInv_of_killer pin hwc hkill⟩,
        latchOK_of_decided pin (hdec w hwc c hc hcw') hae⟩, (hE w hwc hwm).mpr hw⟩
  have eOfD : ∀ m, (∀ c ∈ S.cells, ht c < m → (deadB S m c = true ↔ Inv c)) →
      ∀ c ∈ S.cells, ht c < m + 1 → (effB S (m + 1) c = true ↔ Eff c) := by
    intro m hD c hc hcm
    constructor
    · intro h
      simp only [effB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
        Bool.not_eq_true'] at h
      obtain ⟨-, hall⟩ := h
      refine (pin.pass1.eff_eq c).mpr ⟨(pin.present c).mpr hc, ?_⟩
      intro hinv
      obtain ⟨w, hw, -, hcw, hae, hkill⟩ := (pin.pass1.inv_eq c).mp hinv
      have hwc := eff_present pin hw
      have hcw' : c ∈ S.invalidates w := (pin.invalidates w hwc) ▸ hcw
      have hwm : ht w < m := by have := hht w hwc c hcw'; omega
      rcases hall w hwc with h | h
      · have ha : attacker S c w = true := by
          simp only [attacker, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true']
          refine ⟨⟨hcw', nonInv_of_killer pin hwc hkill⟩, ?_⟩
          cases hu : unlatchedOK S w c .invalidates with
          | false => rfl
          | true => rw [unlatched_sound pin hu] at hae; exact Bool.noConfusion hae
        rw [ha] at h; exact Bool.noConfusion h
      · exact not_eff_of_inv pin ((hD w hwc hwm).mp h) hw
    · intro he
      simp only [effB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
        Bool.not_eq_true']
      refine ⟨hc, fun w hwc => ?_⟩
      cases ha : attacker S c w with
      | false => exact Or.inl rfl
      | true =>
        refine Or.inr (?_ : deadB S m w = true)
        simp only [attacker, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at ha
        obtain ⟨⟨hcw, hk⟩, hu⟩ := ha
        have hwm : ht w < m := by have := hht w hwc c hcw; omega
        cases hdw : deadB S m w with
        | true => rfl
        | false =>
          exfalso
          have hni : ¬ Inv w := fun hi => by rw [(hD w hwc hwm).mpr hi] at hdw; exact Bool.noConfusion hdw
          have hEw : Eff w := (pin.pass1.eff_eq w).mpr ⟨(pin.present w).mpr hwc, hni⟩
          have hae := latch_sound pin (latchOK_of_not_unlatched (hdec w hwc c hc hcw) hu)
          exact ((pin.pass1.eff_eq c).mp he).2 ((pin.pass1.inv_eq c).mpr ⟨w, hEw, acc_of_local pin hwc (hloc w hwc),
            (pin.invalidates w hwc).symm ▸ hcw, hae, killer_of_nonInv pin hwc hk⟩)
  intro m
  induction m with
  | zero =>
    have hE : ∀ c ∈ S.cells, ht c < 0 → (effB S 0 c = true ↔ Eff c) := fun _ _ h => absurd h (Nat.not_lt_zero _)
    exact ⟨hE, dOfE 0 hE⟩
  | succ m ih =>
    have hE := eOfD m ih.2
    exact ⟨hE, dOfE (m + 1) hE⟩

theorem live_mem (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {c : C} (h : Live X c) :
    c ∈ S.cells :=
  eff_present pin ((pin.active c).mp h.1).1

theorem cone_live (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {d c : C} (hd : Live X d)
    (hc : Cone W X S.cells d c) : Live X c := by
  induction hc with
  | self => exact hd
  | verdict hw => exact hw.2.1
  | relies _ hr ih => exact pin.reliesLive _ _ ih.1 ih.2 hr

section Frag

variable {d : C} {rank ht : C → Nat} {n : Nat}

/-- A cell of `Rel` that is not Superseded passes `unsupB` above its rank. -/
theorem unsupB_of (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) (hf : Fragment S W X Inv d)
    (hr : Ranked S rank ht n) : ∀ m, ∀ w ∈ S.cells, Rel S W X d w → ht w < m →
      ¬ Superseded W AE Eff Acc w → unsupB S m w = true
  | 0, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | m + 1, w, hw, hrel, hwm, hns => by
    have hK := kernel_iff pin hf.isLocal hf.invDecided ht hr.invalidates m
    simp only [unsupB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true]
    intro u hu
    cases hsa : supAttacker S w u with
    | false => exact Or.inl rfl
    | true =>
      simp only [supAttacker, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hsa
      obtain ⟨hwu, hun⟩ := hsa
      have hae := latch_sound pin (latchOK_of_not_unlatched
        (hf.evictDecided u hu w .supersedes (by decide) hwu (Or.inl hrel)) hun)
      have hum : ht u < m := by have := hr.supersedes u hu w hwu; omega
      have hwu' : w ∈ (W.info u).supersedes := (pin.supersedes u hu).symm ▸ hwu
      refine Or.inr ⟨?_, ?_⟩
      · cases hdu : deadB S m u with
        | true => rfl
        | false =>
          exfalso
          have hni : ¬ Inv u := fun hi => by rw [(hK.2 u hu hum).mpr hi] at hdu; exact Bool.noConfusion hdu
          have hEu : Eff u := (pin.pass1.eff_eq u).mpr ⟨(pin.present u).mpr hu, hni⟩
          exact hns (Superseded.direct hwu' hae hEu (acc_of_local pin hu (hf.isLocal u hu)))
      · exact unsupB_of pin hf hr m u hu (Rel.up hrel hu hwu) hum
          (fun hsu => hns (Superseded.trans hwu' hae hsu))

/-- A live cell of the cone meets the checker's stand conditions to any depth above its rank. -/
theorem stands_of_cone (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) (hf : Fragment S W X Inv d)
    (hr : Ranked S rank ht n) (hd : Live X d) :
    ∀ (m : Nat) (c : C), rank c < m → Cone W X S.cells d c → standsB S n m c = true
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | m + 1, c, hm, hcone => by
    have hlive := cone_live pin hd hcone
    have hc := live_mem pin hlive
    have hact := (pin.active c).mp hlive.1
    have hK := kernel_iff pin hf.isLocal hf.invDecided ht hr.invalidates n
    have hcn := (hr.bound c hc).2
    simp only [standsB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    refine ⟨⟨⟨⟨⟨⟨hc, hf.isLocal c hc⟩, (hK.1 c hc hcn).mpr hact.1⟩,
      unsupB_of pin hf hr n c hc (Rel.cone hcone) hcn hact.2.2.1⟩, ?_⟩, ?_⟩, ?_⟩
    · simp only [retB, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
      intro w hw
      cases hra : retAttacker S c w with
      | false => exact Or.inl rfl
      | true =>
        refine Or.inr ?_
        simp only [retAttacker, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hra
        obtain ⟨hcw, hun⟩ := hra
        have hae := latch_sound pin (latchOK_of_not_unlatched
          (hf.evictDecided w hw c .retires (by decide) hcw (Or.inl (Rel.cone hcone))) hun)
        cases hdw : deadB S n w with
        | true => rfl
        | false =>
          exfalso
          have hni : ¬ Inv w := fun hi => by
            rw [(hK.2 w hw (hr.bound w hw).2).mpr hi] at hdw; exact Bool.noConfusion hdw
          have hEw : Eff w := (pin.pass1.eff_eq w).mpr ⟨(pin.present w).mpr hw, hni⟩
          exact hact.2.1 ((pin.pass1.ret_eq c).mpr ⟨w, hEw, acc_of_local pin hw (hf.isLocal w hw),
            (pin.retires w hw).symm ▸ hcw, hae⟩)
    · simp only [outB, List.all_eq_true]
      intro u hu
      exact latchOK_of_decided pin (hf.evictDecided c hc u .supersedes (by decide) hu (Or.inr hcone))
        (hact.2.2.2.2 u ((pin.supersedes c hc).symm ▸ hu))
    · intro r hr'
      have hr'' : r ∈ (W.info c).relies := (pin.relies c hc).symm ▸ hr'
      exact stands_of_cone pin hf hr hd m r (by have := hr.relies c hc r hr'; omega) (Cone.relies hcone hr'')

/-- An INVALID verdict that is not live through an Invalidated cell passes `downB` above its rank. -/
theorem downB_of (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) (hf : Fragment S W X Inv d)
    (hr : Ranked S rank ht n) : ∀ (m : Nat) (b : C), rank b < m → DownByInv S Inv b → downB S n m b = true
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | m + 1, b, hbm, hdb => by
    have hK := kernel_iff pin hf.isLocal hf.invDecided ht hr.invalidates n
    cases hdb with
    | dead hb hinv =>
      simp only [downB, Bool.or_eq_true]
      exact Or.inl ((hK.2 b hb (hr.bound b hb).2).mpr hinv)
    | relies hb hrb hdr =>
      simp only [downB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
      exact Or.inr ⟨hb, _, hrb, downB_of pin hf hr m _ (by have := hr.relies b hb _ hrb; omega) hdr⟩

end Frag

/-- **A key that counts is a pair the prover names.** On the fragment of a live decision, a key of its evaluator policy
that counts through a verdict of `W_max` is among the endorsements `pairs` names. -/
theorem pair_of_counts (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) (pc : PinComplete S W X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt)
    {rank ht : C → Nat} {n : Nat} (hr : Ranked S rank ht n)
    {d : C} (hsch : S.schema d = .decision ∨ S.schema d = .contract) (hf : Fragment S W X Inv d) (hl : Live X d)
    {w : C} {k : K} (hw : w ∈ wmax d) (hkw : k ∈ cnt d w) (hkK : k ∈ S.keys (evalPol S d)) :
    (w, k) ∈ pairs S n d := by
  have hd : d ∈ S.cells := live_mem pin hl
  have stands : ∀ c, Cone W X S.cells d c → c ∈ S.cells → standsB S n n c = true :=
    fun c hc hmem => stands_of_cone pin hf hr hl n c (hr.bound c hmem).1 hc
  have hin : InWmax W X S.cells d w := (hwmax d w).mp hw
  have hcnt' : Counts W X S.cells d w k := (hcnt d w k).mp hkw
  obtain ⟨hwc, hwl, hatt, hrest⟩ := hin
  rw [pin.schema d hd] at hrest
  have hrest' : (W.info w).schema = .verdict ∧ (W.info w).payload = some d ∧
      (X.verdict w).witness = none ∧ (X.verdict w).attested = true := by
    have hreq : X.req d = none := (pin.req d hd hsch).mpr hf.req
    rcases hsch with h | h <;> rw [h] at hrest <;> rw [hreq] at hrest <;>
      exact ⟨hrest.1, hrest.2.1, hrest.2.2.1, hrest.2.2.2⟩
  obtain ⟨hvs, hvp, hvw, hva⟩ := hrest'
  have hconew : Cone W X S.cells d w := Cone.verdict ((hwmax d w).mp hw)
  have hvs' : S.schema w = .verdict := pin.schema w hwc ▸ hvs
  have hcountable : countable S n d w = true := by
    simp only [countable, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨hvs', (pin.payload w hwc d hd).mp hvp⟩, pin.attests w hwc ▸ hatt⟩, ?_⟩, ?_⟩,
      stands w hconew hwc⟩
    · exact (pin.verdict w hwc hvs').1 ▸ hva
    · exact (pin.verdict w hwc hvs').2.2.1.mp hvw
  have hlocal := hf.isLocal w hwc
  have hend : k ∈ X.cumulative w := by
    have := hcnt'.1
    unfold witnessEndorsers at this
    rw [pin.isLocal w hwc, hlocal, if_pos rfl] at this
    exact this
  obtain ⟨cp, hcp, hroster, s, hs, ht', hctx, hkey⟩ := pc.seals w hwc hlocal k hend
  have hseal : endorseOK S w k [] = true := by
    simp only [endorseOK, List.isEmpty_nil, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    exact ⟨⟨hwc, hlocal⟩, cp, hcp, hroster, s, hs, ⟨ht', hctx⟩, hkey⟩
  -- an INVALID verdict the checker finds `withdraws` is live, and then the model withdraws `k` too, or the prover
  -- proves it not live
  have hnot : ¬ Withdrawn W X S.cells d w k := by
    have := hcnt'.2
    rw [pin.schema d hd] at this
    rcases hsch with h | h <;> rw [h] at this <;> exact this
  have hnw : (S.cells.all fun b => !withdraws S d w k b || downB S n n b) = true := by
    simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
    intro b hb
    cases hwd : withdraws S d w k b with
    | false => exact Or.inl rfl
    | true =>
      refine Or.inr ?_
      simp only [withdraws, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hwd
      obtain ⟨⟨⟨⟨hbs, hbp⟩, hbi⟩, hbver⟩, hloc⟩ := hwd
      rcases hf.invalid b hb hbs hbp hbi with hblive | hdown
      · exfalso
        have hbl := hf.isLocal b hb
        have hsb : sealedBy S b k = true := by
          rcases hloc with h | h
          · rw [hbl] at h; exact Bool.noConfusion h
          · exact h
        simp only [sealedBy, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hsb
        obtain ⟨cp', hcp', hroster', s', hs', ⟨ht'', hctx'⟩, hks'⟩ := hsb
        have hcum : k ∈ X.cumulative b := by
          have := pin.cumulative s' hs' cp' hcp' hctx' (ht'' ▸ hbl) (hks' ▸ hroster')
          rw [ht'', hks'] at this
          exact this
        apply hnot
        refine ⟨b, hb, hblive, (pin.schema b hb).trans hbs, Or.inl ((pin.payload b hb d hd).mpr hbp), ?_, ?_, ?_⟩
        · rw [(pin.verdict b hb hbs).2.1]
          exact hbi
        · rw [(pin.verdict b hb hbs).2.2.2, (pin.verdict w hwc hvs').2.2.2]
          exact hbver
        · unfold witnessEndorsers
          rw [pin.isLocal b hb, hbl, if_pos rfl]
          exact hcum
      · exact downB_of pin hf hr n b (hr.bound b hb).1 hdown
  refine List.mem_flatMap.mpr ⟨w, List.mem_filter.mpr ⟨hwc, hcountable⟩, ?_⟩
  exact List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hkK, by simp only [Bool.and_eq_true]; exact ⟨hseal, hnw⟩⟩, rfl⟩

/-- **Completeness of the witness checker on its fragment.** If the model of §4.2 holds a decision `Settled` at the
tip, the checker accepts the derivation `prove` builds from the store, for every reading `W`, `X` of the scope's
admitted chain that the decode `S` agrees with and is complete for (`Pin`, `PinComplete`), every faithful
presentation of `W_max`, and every depth above the ranks of `relies` and of the kill edges (`Ranked`). -/
theorem witness_complete (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) (pc : PinComplete S W X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt)
    {rank ht : C → Nat} {n : Nat} (hr : Ranked S rank ht n)
    {d : C} (hsch : S.schema d = .decision ∨ S.schema d = .contract) (hf : Fragment S W X Inv d)
    (hs : Settled W X wmax cnt d) : accepts S (prove S n d) d = true := by
  have hd : d ∈ S.cells := live_mem pin hs.1
  have stands : ∀ c, Cone W X S.cells d c → c ∈ S.cells → standsB S n n c = true :=
    fun c hc hmem => stands_of_cone pin hf hr hs.1 n c (hr.bound c hmem).1 hc
  -- the blocks of `prove` run, one after another
  obtain ⟨o0, h0, he0, -⟩ := edge_run S []
  obtain ⟨o1, h1, hg1, hs1⟩ := stand_run S n n d (stands d Cone.self hd) o0 he0
  have he1 := he0.mono S hs1
  obtain ⟨o2, h2, hg2, hs2⟩ := reaches_flatMap S (EdgeFacts S) (edgeFacts_mono S) (standLines S n n)
    (fun w => [.stands w]) (counted S n d)
    (fun w hw o ho => by
      have := (List.mem_filter.mp hw).2
      simp only [countable, Bool.and_eq_true] at this
      exact stand_run S n n w this.2 o ho) o1 he1
  have he2 := he1.mono S hs2
  obtain ⟨o3, h3, hg3, hs3⟩ := reaches_flatMap S (EdgeFacts S) (edgeFacts_mono S) (downLines S n n)
    (fun b => [.down b]) (downs S n d)
    (fun b hb o ho => by
      have := (List.mem_filter.mp hb).2
      simp only [Bool.and_eq_true] at this
      exact down_run S n n b this.2 o ho) o2 he2
  obtain ⟨o4, h4, hg4, hs4⟩ := reaches_flatMap S (fun _ => True) (fun _ _ _ _ => trivial) (fun p => [endorseLine p])
    (fun p => [Concl.endorsed p.1 p.2]) (pairs S n d)
    (fun p hp done _ => by
      obtain ⟨w, k⟩ := p
      have hok : lineOK S done (endorseLine (w, k)) = true :=
        lineOK_of S (by simp [endorseLine]) (by simp [ruleOK, endorseLine, Concl.rule, (mem_pairs S hp).2.2.1])
      exact reaches_single S hok) o3 trivial
  -- the settle line
  have hep : Vars1.evalPol W X d = Witness.evalPol S d := by
    unfold Vars1.evalPol Witness.evalPol
    rw [pin.schema d hd, pin.customPol d hd, pin.scope, pin.pol0]
    rcases hsch with h | h <;> rw [h]
  have hq : W.quorum ((wmax d).flatMap (cnt d)) (Witness.evalPol S d) = true := by
    have := hs.2
    rw [pin.schema d hd] at this
    rw [← hep]
    rcases hsch with h | h <;> rw [h] at this <;> exact this
  have hpol := pc.pols d hd hsch
  obtain ⟨ks, hnd, hkE, hkK, hthr⟩ := pin.quorumConv _ hpol _ hq
  -- every key of the quorum is named by an endorsement of a counted verdict
  have hnamed : ∀ k ∈ ks, ∃ w, (w, k) ∈ pairs S n d := by
    intro k hk
    obtain ⟨w, hw, hkw⟩ := List.mem_flatMap.mp (hkE k hk)
    exact ⟨w, pair_of_counts pin pc hwmax hcnt hr hsch hf hs.1 hw hkw (hkK k hk)⟩
  have hsettle : lineOK S o4 ⟨.settle, .settled d, settlePrem S n d⟩ = true := by
    refine lineOK_of S ?_ ?_
    · intro p hp
      simp only [settlePrem, List.mem_cons, List.mem_append, List.mem_map] at hp
      rcases hp with rfl | ((⟨w, hw, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨b, hb, rfl⟩)
      · exact hs4 _ (hs3 _ (hs2 _ (hg1 _ (by simp))))
      · exact hs4 _ (hs3 _ (hg2 _ (List.mem_flatMap.mpr ⟨w, hw, by simp⟩)))
      · exact hg4 _ (List.mem_flatMap.mpr ⟨q, hq, by simp⟩)
      · exact hs4 _ (hg3 _ (List.mem_flatMap.mpr ⟨b, hb, by simp⟩))
    · simp only [ruleOK, Concl.rule, decide_true, Bool.true_and, settleOK, Bool.and_eq_true, Bool.or_eq_true,
        decide_eq_true_eq, List.all_eq_true]
      refine ⟨⟨⟨⟨⟨⟨hd, hsch⟩, hf.req⟩, List.mem_cons_self⟩, hpol⟩, ?_⟩, ?_⟩
      · intro p hp
        simp only [settlePrem, List.mem_cons, List.mem_append, List.mem_map] at hp
        rcases hp with rfl | ((⟨w, hw, rfl⟩ | ⟨⟨w, k⟩, hwk, rfl⟩) | ⟨b, hb, rfl⟩)
        · rfl
        · rfl
        · obtain ⟨hw', hkK', -, hnw'⟩ := mem_pairs S hwk
          have hc := (List.mem_filter.mp hw').2
          simp only [countable, Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨⟨⟨⟨⟨hvs, hvp⟩, hva⟩, hvt⟩, hvw⟩, -⟩ := hc
          simp only [countsFor, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
            Bool.not_eq_true']
          refine ⟨⟨⟨⟨⟨⟨⟨?_, hvs⟩, hvp⟩, hva⟩, hvt⟩, hvw⟩, hkK'⟩, ?_⟩
          · simp only [settlePrem, List.mem_cons, List.mem_append, List.mem_map]
            exact Or.inr (Or.inl (Or.inl ⟨w, hw', rfl⟩))
          · intro b hb
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
                simp only [settlePrem, List.mem_cons, List.mem_append, List.mem_map]
                refine Or.inr (Or.inr ⟨b, List.mem_filter.mpr ⟨hb, ?_⟩, rfl⟩)
                simp [hinv, h]
        · rfl
      · refine Nat.le_trans hthr (nodup_length_le hnd ?_)
        intro k hk
        obtain ⟨w, hwk⟩ := hnamed k hk
        apply mem_dedup.mpr
        apply endorsedKeys_of_mem (w := w)
        simp only [settlePrem, List.mem_cons, List.mem_append, List.mem_map]
        exact Or.inr (Or.inl (Or.inr ⟨(w, k), hwk, rfl⟩))
  -- the whole derivation
  unfold accepts prove
  rw [run_append, run_append, run_append, run_append, run_append, h0]
  simp only [Option.bind_some]
  rw [h1]
  simp only [Option.bind_some]
  rw [h2]
  simp only [Option.bind_some]
  rw [h3]
  simp only [Option.bind_some]
  rw [h4]
  simp only [Option.bind_some]
  rw [run_single S hsettle]
  simp

/-- **The checker decides `Settled` on its fragment.** Under the hypotheses of soundness and completeness, the checker
accepts the prover's derivation exactly when the model holds the decision `Settled`. -/
theorem accepts_iff_settled (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) (pc : PinComplete S W X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt)
    {rank ht : C → Nat} {n : Nat} (hr : Ranked S rank ht n)
    {d : C} (hsch : S.schema d = .decision ∨ S.schema d = .contract) (hf : Fragment S W X Inv d) :
    accepts S (prove S n d) d = true ↔ Settled W X wmax cnt d :=
  ⟨witness_sound pin hwmax hcnt, witness_complete pin pc hwmax hcnt hr hsch hf⟩

end Complete

end Vars1.Witness
