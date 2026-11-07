import Vars1.Witness

/-!
# The witness checker is complete on its fragment

`witness_sound` (`Witness.lean`) proves that `accepts` implies `Settled`. Here is the converse, where the checker's
rules read as the model's. `prove` builds a derivation from the store alone, and when the model holds a decision
`Settled`, `accepts` takes it (`witness_complete`). With soundness, `accepts S (prove S n d) d` is exactly `Settled`
there (`accepts_iff_settled`).

The fragment (`Fragment`) is where the checker's syntactic rules and the model's read the same:
* the decision requires no computation, and no INVALID verdict of the store judges it (the model withdraws only the
  keys that seal one under the verifier id of the verdict it withdraws; the checker refuses any);
* every cell of the decision's live cone (`Cone`: the decision, the verdicts of `W_max`, and what they rely on) is
  local, supersedes nothing, and no cell of the store invalidates, retires or supersedes it (the model counts only an
  authorized edge from an Effective cell; the checker refuses any).

Completeness needs the decode to be complete, where soundness needs it faithful (`PinComplete`):
* what a live cell relies on is live, the other direction of the Pass 2 equation (`stale_complete` proves it of
  `Stale` where `active` is decidable, as the lens's bits are);
* the store holds a seal for every cumulative endorser of a local cell, under a scope of the chain and by a key of
  that scope's roster;
* a policy that meets its quorum does so with threshold many distinct keys of it;
* every decision's evaluator policy is among the decoded ones.

`relies` has a rank on the store (cells are named by the hash of their contents, so none relies on one that names it),
and `n` bounds it: the prover's depth.
-/

set_option linter.unusedSectionVars false

namespace Vars1.Witness

open Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K] [DecidableEq P]
variable (S : Store C K P)

/-! ## The prover -/

/-- The checker's `stand` conditions, closed under `relies` to depth `n`. -/
def standsB : Nat → C → Bool
  | 0, _ => false
  | n + 1, c => decide (c ∈ S.cells) && S.isLocal c && (S.supersedes c).isEmpty && !killed S c &&
      (S.relies c).all (standsB n)

/-- Stand lines for `c`, after those for what it relies on, to depth `n`. -/
def standLines : Nat → C → List (Line C K)
  | 0, _ => []
  | n + 1, c => (S.relies c).flatMap (standLines n) ++ [⟨.stand, .stands c, (S.relies c).map .stands⟩]

/-- A verdict the prover counts for `d`: it stands to depth `n`, and it is an ATTESTED verdict with an empty witness
slot that judges and attests `d`. -/
def countable (n : Nat) (d w : C) : Bool :=
  standsB S n w && decide (S.schema w = .verdict) && decide (S.payload w = some d) && decide (d ∈ S.attests w) &&
    (S.verdict w).attested && decide ((S.verdict w).witness = none)

/-- The verdicts the prover counts for `d`. -/
def counted (n : Nat) (d : C) : List C := S.cells.filter (countable S n d)

/-- The endorsements the prover names: a key of `d`'s evaluator policy that seals a counted verdict under a scope of
the chain, as a key of that scope's roster. -/
def pairs (n : Nat) (d : C) : List (C × K) :=
  (counted S n d).flatMap fun w => ((S.keys (evalPol S d)).filter fun k => endorseOK S w k []).map fun k => (w, k)

def endorseLine (p : C × K) : Line C K := ⟨.endorse, .endorsed p.1 p.2, []⟩

theorem mem_pairs {n : Nat} {d w : C} {k : K} (h : (w, k) ∈ pairs S n d) :
    w ∈ counted S n d ∧ k ∈ S.keys (evalPol S d) ∧ endorseOK S w k [] = true := by
  obtain ⟨w', hw', hm⟩ := List.mem_flatMap.mp h
  obtain ⟨k', hk', he⟩ := List.mem_map.mp hm
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨hw', (List.mem_filter.mp hk').1, (List.mem_filter.mp hk').2⟩

def settlePrem (n : Nat) (d : C) : List (Concl C K) :=
  .stands d :: ((counted S n d).map .stands ++ (pairs S n d).map fun p => .endorsed p.1 p.2)

/-- **The prover.** A derivation that `d` is settled, built from the store alone: stand lines for `d` and for each
counted verdict, an endorse line for each named endorsement, then the settle line. -/
def prove (n : Nat) (d : C) : List (Line C K) :=
  standLines S n d ++ (counted S n d).flatMap (standLines S n) ++ (pairs S n d).flatMap (fun p => [endorseLine p]) ++
    [⟨.settle, .settled d, settlePrem S n d⟩]

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

theorem lineOK_mono {done done' : List (Concl C K)} (hsub : ∀ p ∈ done, p ∈ done') {l : Line C K}
    (h : lineOK S done l = true) : lineOK S done' l = true := by
  unfold lineOK at h ⊢
  rw [Bool.and_eq_true] at h ⊢
  refine ⟨?_, h.2⟩
  rw [List.all_eq_true] at h ⊢
  intro p hp
  have := h.1 p hp
  simp only [decide_eq_true_eq] at this ⊢
  exact hsub p this

theorem run_single {done : List (Concl C K)} {l : Line C K} (h : lineOK S done l = true) :
    run S done [l] = some (l.concl :: done) := by
  simp only [run, h, if_true]

/-- A run that a set of conclusions lets through, a larger set lets through, to a larger set. -/
theorem run_mono : ∀ (ls : List (Line C K)) (done done' out : List (Concl C K)), run S done ls = some out →
    (∀ p ∈ done, p ∈ done') → ∃ out', run S done' ls = some out' ∧ ∀ p ∈ out, p ∈ out'
  | [], done, done', out, h, hsub => by
    simp only [run, Option.some.injEq] at h
    subst h
    exact ⟨done', rfl, hsub⟩
  | l :: ls, done, done', out, h, hsub => by
    simp only [run] at h ⊢
    split at h
    · rename_i hl
      rw [if_pos (lineOK_mono S hsub hl)]
      refine run_mono ls _ _ out h ?_
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub p hp)
    · exact absurd h (by simp)

/-- Running the pieces `f a` one after another reaches every `g a`, when each piece reaches its own from any start. -/
theorem run_flatMap {α : Type} (f : α → List (Line C K)) (g : α → Concl C K) :
    ∀ (as : List α), (∀ a ∈ as, ∀ done, ∃ out, run S done (f a) = some out ∧ g a ∈ out ∧ ∀ p ∈ done, p ∈ out) →
    ∀ done, ∃ out, run S done (as.flatMap f) = some out ∧ (∀ a ∈ as, g a ∈ out) ∧ ∀ p ∈ done, p ∈ out
  | [], _, done => ⟨done, rfl, by simp, fun _ hp => hp⟩
  | a :: as, h, done => by
    obtain ⟨o1, h1, hg1, hs1⟩ := h a List.mem_cons_self done
    obtain ⟨o2, h2, hg2, hs2⟩ := run_flatMap f g as (fun b hb => h b (List.mem_cons_of_mem _ hb)) o1
    refine ⟨o2, ?_, ?_, fun p hp => hs2 p (hs1 p hp)⟩
    · rw [List.flatMap_cons, run_append, h1]
      exact h2
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hs2 _ hg1
      · exact hg2 b hb

/-- The stand lines of a cell whose stand conditions hold to depth `n` run from any start and conclude that it stands. -/
theorem stand_run : ∀ (n : Nat) (c : C), standsB S n c = true →
    ∀ done, ∃ out, run S done (standLines S n c) = some out ∧ Concl.stands c ∈ out ∧ ∀ p ∈ done, p ∈ out
  | 0, c, h, _ => by simp [standsB] at h
  | n + 1, c, h, done => by
    simp only [standsB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true] at h
    obtain ⟨⟨⟨⟨hc, hl⟩, hs⟩, hk⟩, hr⟩ := h
    obtain ⟨o1, h1, hg1, hs1⟩ := run_flatMap S (standLines S n) Concl.stands (S.relies c)
      (fun r hr' => stand_run n r (hr r hr')) done
    have hok : lineOK S o1 ⟨.stand, .stands c, (S.relies c).map .stands⟩ = true := by
      simp only [lineOK, standOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, hc, hl, hs, hk,
        Bool.not_false, and_true]
      intro p hp
      obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hp
      exact hg1 r hr'
    refine ⟨Concl.stands c :: o1, ?_, List.mem_cons_self, fun p hp => List.mem_cons_of_mem _ (hs1 p hp)⟩
    simp only [standLines]
    rw [run_append, h1]
    exact run_single S hok

/-! ## Lemmas on keys -/

theorem endorsedKeys_of_mem {k : K} {w : C} : ∀ {ps : List (Concl C K)}, Concl.endorsed w k ∈ ps → k ∈ endorsedKeys ps
  | [], h => absurd h List.not_mem_nil
  | .endorsed w' j :: ps, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (endorsedKeys_of_mem h)
  | .stands _ :: ps, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h
    · exact endorsedKeys_of_mem (ps := ps) h
  | .settled _ :: ps, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h
    · exact endorsedKeys_of_mem (ps := ps) h

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

/-! ## What completeness asks of the store and the model -/

/-- What completeness asks of the decode beyond `Pin`: that it holds every seal, policy and stale cell the model
counts. -/
structure PinComplete (W : World C K P) (X : Pass3In C K P) : Prop where
  reliesLive : ∀ v d, X.active v → ¬ X.stale v → d ∈ (W.info v).relies → X.active d ∧ ¬ X.stale d
  seals : ∀ w ∈ S.cells, S.isLocal w = true → ∀ k ∈ X.cumulative w,
    ∃ cp ∈ S.ctxs, k ∈ S.keys cp.2 ∧ ∃ s ∈ S.seals, s.target = w ∧ s.ctx = cp.1 ∧ s.key = k
  quorum : ∀ p ∈ S.pols, ∀ E, W.quorum E p = true →
    ∃ ks : List K, ks.Nodup ∧ (∀ k ∈ ks, k ∈ E) ∧ (∀ k ∈ ks, k ∈ S.keys p) ∧ S.thr p ≤ ks.length
  pols : ∀ d ∈ S.cells, (S.schema d = .decision ∨ S.schema d = .contract) → evalPol S d ∈ S.pols

/-- A decision's live cone: the decision, the verdicts of `W_max`, and what they rely on. -/
inductive Cone (W : World C K P) (X : Pass3In C K P) (cells : List C) (d : C) : C → Prop where
  | self : Cone W X cells d d
  | verdict {w : C} : InWmax W X cells d w → Cone W X cells d w
  | relies {c r : C} : Cone W X cells d c → r ∈ (W.info c).relies → Cone W X cells d r

/-- The fragment of `d`: no computation, no INVALID verdict on `d`, and a cone of local cells that supersede nothing
and that no cell of the store invalidates, retires or supersedes. -/
structure Fragment (W : World C K P) (X : Pass3In C K P) (d : C) : Prop where
  req : S.req d = none
  noInvalid : judgedInvalid S d = false
  cone : ∀ c, Cone W X S.cells d c → S.isLocal c = true ∧ S.supersedes c = [] ∧ killed S c = false

/-- Pass 2 `Stale` satisfies what `PinComplete.reliesLive` asks of `X.stale`: what an active cell that is not stale
relies on is active and not stale. -/
theorem stale_complete {N : Nat} (I : Pass2In N) [DecidablePred I.active] (v d : Fin N) (ha : I.active v)
    (hns : ¬ Stale I v) (hd : d ∈ I.relies v) : I.active d ∧ ¬ Stale I d := by
  refine ⟨?_, fun hs => hns ((stale_fixed I v).mpr ⟨ha, Or.inl ⟨d, hd, Or.inr hs⟩⟩)⟩
  match (inferInstance : Decidable (I.active d)) with
  | isTrue h => exact h
  | isFalse h => exact absurd ((stale_fixed I v).mpr ⟨ha, Or.inl ⟨d, hd, Or.inl h⟩⟩) hns

/-! ## Completeness -/

section Complete

variable {S}
variable {W : World C K P} {X : Pass3In C K P} {wmax : C → List C} {cnt : C → C → List K}
variable {AE : C → C → Kind → Bool} {Present isIntrinsic : C → Prop} {Auth : C → Bool} {Inv Eff Ret Acc : C → Prop}

theorem live_mem (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) {c : C} (h : Live X c) :
    c ∈ S.cells :=
  (pin.present c).mp ((pin.pass1.eff_eq c).mp ((pin.active c).mp h.1).1).1

theorem live_relies (pc : PinComplete S W X) {c r : C} (h : Live X c) (hr : r ∈ (W.info c).relies) : Live X r :=
  pc.reliesLive c r h.1 h.2 hr

theorem cone_live (pc : PinComplete S W X) {d c : C} (hd : Live X d) (hc : Cone W X S.cells d c) : Live X c := by
  induction hc with
  | self => exact hd
  | verdict hw => exact hw.2.1
  | relies _ hr ih => exact live_relies pc ih hr

/-- A live cell of the cone meets the checker's stand conditions to any depth above its rank. -/
theorem stands_of_cone (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) (pc : PinComplete S W X)
    (rank : C → Nat) (hrank : ∀ c ∈ S.cells, ∀ r ∈ S.relies c, rank r < rank c) {d : C} (hf : Fragment S W X d)
    (hd : Live X d) : ∀ (n : Nat) (c : C), rank c < n → Cone W X S.cells d c → standsB S n c = true
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, c, hn, hcone => by
    have hlive := cone_live pc hd hcone
    have hc := live_mem pin hlive
    obtain ⟨hl, hs, hk⟩ := hf.cone c hcone
    simp only [standsB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true, hc, hl, hs, hk,
      List.isEmpty_nil, and_self, true_and]
    intro r hr
    have hr' : r ∈ (W.info c).relies := (pin.relies c hc).symm ▸ hr
    exact stands_of_cone pin pc rank hrank hf hd n r (by have := hrank c hc r hr; omega) (Cone.relies hcone hr')

/-- **Completeness of the witness checker on its fragment.** If the model of §4.2 holds a decision `Settled` at the
tip, the checker accepts the derivation `prove` builds from the store, for every reading `W`, `X` of the scope's
admitted chain that the decode `S` agrees with and is complete for (`Pin`, `PinComplete`), every faithful
presentation of `W_max`, and every depth above the rank of `relies`. -/
theorem witness_complete (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) (pc : PinComplete S W X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt)
    (rank : C → Nat) (hrank : ∀ c ∈ S.cells, ∀ r ∈ S.relies c, rank r < rank c)
    {n : Nat} (hn : ∀ c ∈ S.cells, rank c < n)
    {d : C} (hsch : S.schema d = .decision ∨ S.schema d = .contract) (hf : Fragment S W X d)
    (hs : Settled W X wmax cnt d) : accepts S (prove S n d) d = true := by
  have hd : d ∈ S.cells := live_mem pin hs.1
  have stands : ∀ c, Cone W X S.cells d c → c ∈ S.cells → standsB S n c = true :=
    fun c hc hmem => stands_of_cone pin pc rank hrank hf hs.1 n c (hn c hmem) hc
  -- the four blocks of `prove` run, one after another
  obtain ⟨o1, h1, hg1, -⟩ := stand_run S n d (stands d Cone.self hd) []
  obtain ⟨o2, h2, hg2, hs2⟩ := run_flatMap S (standLines S n) Concl.stands (counted S n d)
    (fun w hw => by
      have := (List.mem_filter.mp hw).2
      simp only [countable, Bool.and_eq_true] at this
      exact stand_run S n w this.1.1.1.1.1) o1
  obtain ⟨o3, h3, hg3, hs3⟩ := run_flatMap S (fun p => [endorseLine p]) (fun p => Concl.endorsed p.1 p.2)
    (pairs S n d)
    (fun p hp done => by
      obtain ⟨w, k⟩ := p
      have hok : lineOK S done (endorseLine (w, k)) = true := by
        simp only [lineOK, endorseLine, List.all_nil, Bool.true_and]
        exact (mem_pairs S hp).2.2
      exact ⟨_, run_single S hok, List.mem_cons_self, fun q hq => List.mem_cons_of_mem _ hq⟩) o2
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
  obtain ⟨ks, hnd, hkE, hkK, hthr⟩ := pc.quorum _ hpol _ hq
  -- every key of the quorum is named by an endorsement of a counted verdict
  have hnamed : ∀ k ∈ ks, ∃ w, (w, k) ∈ pairs S n d := by
    intro k hk
    obtain ⟨w, hw, hkw⟩ := List.mem_flatMap.mp (hkE k hk)
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
      refine ⟨⟨⟨⟨⟨stands w hconew hwc, hvs'⟩, (pin.payload w hwc d hd).mp hvp⟩, pin.attests w hwc ▸ hatt⟩, ?_⟩, ?_⟩
      · exact (pin.verdict w hwc hvs').1 ▸ hva
      · exact (pin.verdict w hwc hvs').2.2.mp hvw
    have hlocal := (hf.cone w hconew).1
    have hend : k ∈ X.cumulative w := by
      have := hcnt'.1
      unfold witnessEndorsers at this
      rw [pin.isLocal w hwc, hlocal, if_pos rfl] at this
      exact this
    obtain ⟨cp, hcp, hroster, s, hs, ht, hctx, hkey⟩ := pc.seals w hwc hlocal k hend
    have hseal : endorseOK S w k [] = true := by
      simp only [endorseOK, List.isEmpty_nil, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
      exact ⟨⟨hwc, hlocal⟩, cp, hcp, hroster, s, hs, ⟨ht, hctx⟩, hkey⟩
    refine ⟨w, List.mem_flatMap.mpr ⟨w, List.mem_filter.mpr ⟨hwc, hcountable⟩, ?_⟩⟩
    exact List.mem_map.mpr ⟨k, List.mem_filter.mpr ⟨hkK k hk, hseal⟩, rfl⟩
  have hsettle : lineOK S o3 ⟨.settle, .settled d, settlePrem S n d⟩ = true := by
    simp only [lineOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · intro p hp
      simp only [settlePrem, List.mem_cons, List.mem_append, List.mem_map] at hp
      rcases hp with rfl | ⟨w, hw, rfl⟩ | ⟨q, hq, rfl⟩
      · exact hs3 _ (hs2 _ hg1)
      · exact hs3 _ (hg2 w hw)
      · exact hg3 q hq
    · simp only [settleOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        List.all_eq_true]
      refine ⟨⟨⟨⟨⟨⟨⟨hd, hsch⟩, hf.req⟩, hf.noInvalid⟩, List.mem_cons_self⟩, hpol⟩, ?_⟩, ?_⟩
      · intro p hp
        simp only [settlePrem, List.mem_cons, List.mem_append, List.mem_map] at hp
        rcases hp with rfl | ⟨w, hw, rfl⟩ | ⟨⟨w, k⟩, hwk, rfl⟩
        · rfl
        · rfl
        · obtain ⟨hw', hkK', -⟩ := mem_pairs S hwk
          have hc := (List.mem_filter.mp hw').2
          simp only [countable, Bool.and_eq_true, decide_eq_true_eq] at hc
          obtain ⟨⟨⟨⟨⟨-, hvs⟩, hvp⟩, hva⟩, hvt⟩, hvw⟩ := hc
          simp only [countsFor, Bool.and_eq_true, decide_eq_true_eq]
          refine ⟨⟨⟨⟨⟨⟨?_, hvs⟩, hvp⟩, hva⟩, hvt⟩, hvw⟩, hkK'⟩
          simp only [settlePrem, List.mem_cons, List.mem_append, List.mem_map]
          exact Or.inr (Or.inl ⟨w, hw', rfl⟩)
      · refine Nat.le_trans hthr (nodup_length_le hnd ?_)
        intro k hk
        obtain ⟨w, hwk⟩ := hnamed k hk
        apply mem_dedup.mpr
        apply endorsedKeys_of_mem (w := w)
        simp only [settlePrem, List.mem_cons, List.mem_append, List.mem_map]
        exact Or.inr (Or.inr ⟨(w, k), hwk, rfl⟩)
  -- the whole derivation
  unfold accepts prove
  rw [run_append, run_append, run_append, h1]
  simp only [Option.bind_some]
  rw [h2]
  simp only [Option.bind_some]
  rw [h3]
  simp only [Option.bind_some]
  rw [run_single S hsettle]
  simp

/-- **The checker decides `Settled` on its fragment.** Under the hypotheses of soundness and completeness, the checker
accepts the prover's derivation exactly when the model holds the decision `Settled`. -/
theorem accepts_iff_settled (pin : Pin S W AE Present isIntrinsic Auth Inv Eff Ret Acc X) (pc : PinComplete S W X)
    (hwmax : WmaxFaithful W X S.cells wmax) (hcnt : CntFaithful W X S.cells cnt)
    (rank : C → Nat) (hrank : ∀ c ∈ S.cells, ∀ r ∈ S.relies c, rank r < rank c)
    {n : Nat} (hn : ∀ c ∈ S.cells, rank c < n)
    {d : C} (hsch : S.schema d = .decision ∨ S.schema d = .contract) (hf : Fragment S W X d) :
    accepts S (prove S n d) d = true ↔ Settled W X wmax cnt d :=
  ⟨witness_sound pin hwmax hcnt, witness_complete pin pc hwmax hcnt rank hrank hn hsch hf⟩

end Complete

end Vars1.Witness
