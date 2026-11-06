import Vars1.Fold2
import Vars1.Pass1
import Vars1.Pass2

/-!
# Two scopes: when does an import read as its source does?

Every other theorem here speaks of one scope. A cell of scope `B` imported into scope `A` is the same bytes under two folds:
its edges latch in `B` under `B`'s policies, and in `A` only by `A`'s own keys' cross-seals. So the plain statement, that `A`'s
statuses on what it imported are `B`'s, is false, and `test_vars1.py` 127 shows it through the gate three ways. Here:

* `cross_seal_uniform`, `run_uniform`, `run2_uniform` — **a cross-seal is on a cell, not on an edge.** For two foreign targets of
  one policy under `A`, a source's edges latch in `A` together or not at all. `B` can separate them: there the author clause
  may latch one and not the other.
* `no_faithful_import` — **so some cells have no faithful import**, whatever `A` seals: an edge `B` latched and an edge of the
  same source and kind `B` did not, into two such targets, cannot both read in `A` as in `B`. No seal `A` can make helps; only a
  new form of import could.
* `edgeCond_out_of_reach` — **and some edges cannot be followed at all.** Into a foreign target whose policy no keys of `A`'s roster
  meet, such as a decision with an evaluator policy of `B`'s keys, no seal of `A` latches an edge.
* `import_faithful`, `stale_faithful` — **the exact condition.** On a set closed under who attacks it and what it supersedes, pinned
  or local on each side, if the latched edges into it agree, `Active` and `Stale` agree. The cell's own bytes give the rest.
* `pinned_active`, `unpinned_not_active` — **what `A` can do instead.** With no cross-seal and no supersedes edge, a foreign cell of
  `A` stands exactly while `A` pins it: `A` can follow `B`'s verdict on whether a cell stands, by its own acceptance alone.
-/

set_option linter.unusedSectionVars false

namespace Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K]

/-! ## A cross-seal is on a cell -/

section Uniform

variable (W : World C K P)

/-- Into a foreign target the author clause of §4.1 latch 3 never applies: only a quorum of the policy, read from the source's
endorsers. -/
theorem edgeCond_foreign (cm : Commit C K) (S w v : C) (k : Kind) (init : C → List K) (hf : (W.info v).isLocal = false) :
    edgeCond W cm S w v k init = W.quorum (endorsers W cm S w (roster W S v)) (pol W S v).1 := by
  simp [edgeCond, hf]

/-- **A cross-seal is on a cell, not on an edge.** Two foreign targets of one roster and one policy under the scope: an edge into
one latches at a commit exactly when an edge from the same source into the other does, of any kinds. -/
theorem cross_seal_uniform (cm : Commit C K) (S w v₁ v₂ : C) (k₁ k₂ : Kind) (init₁ init₂ : C → List K)
    (hf₁ : (W.info v₁).isLocal = false) (hf₂ : (W.info v₂).isLocal = false)
    (hr : roster W S v₁ = roster W S v₂) (hp : (pol W S v₁).1 = (pol W S v₂).1) :
    edgeCond W cm S w v₁ k₁ init₁ = edgeCond W cm S w v₂ k₂ init₂ := by
  rw [edgeCond_foreign W cm S w v₁ k₁ init₁ hf₁, edgeCond_foreign W cm S w v₂ k₂ init₂ hf₂, hr, hp]

/-- Along a chain under v1: the two edges latch together, whatever the commits. -/
theorem run_uniform {w v₁ v₂ : C} {k₁ k₂ : Kind} (hm₁ : v₁ ∈ (W.info w).edges k₁) (hm₂ : v₂ ∈ (W.info w).edges k₂)
    (hf₁ : (W.info v₁).isLocal = false) (hf₂ : (W.info v₂).isLocal = false)
    (hr : ∀ S, roster W S v₁ = roster W S v₂) (hp : ∀ S, (pol W S v₁).1 = (pol W S v₂).1) :
    ∀ (cs : List (Commit C K)) (st : St C K), st.edge w v₁ k₁ = st.edge w v₂ k₂ →
      (run W st cs).edge w v₁ k₁ = (run W st cs).edge w v₂ k₂
  | [], _, h => h
  | cm :: cs, st, h => by
    apply run_uniform hm₁ hm₂ hf₁ hf₂ hr hp cs (step W st cm)
    have hc := cross_seal_uniform W cm st.scope w v₁ v₂ k₁ k₂ (initAfter W st cm) (initAfter W st cm) hf₁ hf₂
      (hr _) (hp _)
    simp only [step, hm₁, hm₂, decide_true, Bool.and_true, h, hc]

end Uniform

section Uniform2

variable (W : World2 C K P)

theorem settle2_edge_uniform {w v₁ v₂ : C} {k : Kind} (hm₁ : v₁ ∈ (W.info w).edges k) (hm₂ : v₂ ∈ (W.info w).edges k)
    (cm : Commit C K) (now : Nat) (st : St2 C K) (h : st.edge w v₁ k = st.edge w v₂ k) :
    (settle2 W cm now st).edge w v₁ k = (settle2 W cm now st).edge w v₂ k := by
  cases hw : st.waiting with
  | none => simp only [settle2, hw]; exact h
  | some x =>
    obtain ⟨s, t, ch⟩ := x
    simp only [settle2, hw]
    split
    · exact h
    · split
      · show (st.edge w v₁ k || (decide (w = s) && decide (k = .supersedes) && decide (v₁ ∈ (W.info s).supersedes))) =
          (st.edge w v₂ k || (decide (w = s) && decide (k = .supersedes) && decide (v₂ ∈ (W.info s).supersedes)))
        by_cases hs : w = s
        · subst hs
          by_cases hk : k = .supersedes
          · subst hk
            have h₁ : v₁ ∈ (W.info w).supersedes := hm₁
            have h₂ : v₂ ∈ (W.info w).supersedes := hm₂
            simp [h, h₁, h₂]
          · simp [h, hk]
        · simp [h, hs]
      · exact h

/-- Along a chain under v2: the same, for edges of one kind. -/
theorem run2_uniform {w v₁ v₂ : C} {k : Kind} (hm₁ : v₁ ∈ (W.info w).edges k) (hm₂ : v₂ ∈ (W.info w).edges k)
    (hf₁ : (W.info v₁).isLocal = false) (hf₂ : (W.info v₂).isLocal = false)
    (hr : ∀ S, roster W.toWorld S v₁ = roster W.toWorld S v₂) (hp : ∀ S, (pol W.toWorld S v₁).1 = (pol W.toWorld S v₂).1) :
    ∀ (cs : List (Commit C K)) (st : St2 C K), st.edge w v₁ k = st.edge w v₂ k →
      (run2 W st cs).edge w v₁ k = (run2 W st cs).edge w v₂ k
  | [], _, h => h
  | cm :: cs, st, h => by
    apply run2_uniform hm₁ hm₂ hf₁ hf₂ hr hp cs (step2 W st cm)
    apply settle2_edge_uniform W hm₁ hm₂
    have hc := cross_seal_uniform W.toWorld cm st.scope w v₁ v₂ k k (initAfter W.toWorld st.toSt cm)
      (initAfter W.toWorld st.toSt cm) hf₁ hf₂ (hr _) (hp _)
    simp only [latch2, hm₁, hm₂, decide_true, Bool.and_true, h, hc]

/-- **No faithful import.** Let `B`'s latches separate two edges of one source and one kind into two foreign targets of one policy
under `A`, as `B`'s author clause can. Then no chain of `A`'s, with whatever seals, reads both edges as `B` does. -/
theorem no_faithful_import {w v₁ v₂ : C} {k : Kind} (hm₁ : v₁ ∈ (W.info w).edges k) (hm₂ : v₂ ∈ (W.info w).edges k)
    (hf₁ : (W.info v₁).isLocal = false) (hf₂ : (W.info v₂).isLocal = false)
    (hr : ∀ S, roster W.toWorld S v₁ = roster W.toWorld S v₂) (hp : ∀ S, (pol W.toWorld S v₁).1 = (pol W.toWorld S v₂).1)
    (cs : List (Commit C K)) (st : St2 C K) (h0 : st.edge w v₁ k = st.edge w v₂ k)
    (AEB : C → C → Kind → Bool) (hB₁ : AEB w v₁ k = true) (hB₂ : AEB w v₂ k = false) :
    ¬ ((run2 W st cs).edge w v₁ k = AEB w v₁ k ∧ (run2 W st cs).edge w v₂ k = AEB w v₂ k) := by
  rintro ⟨h₁, h₂⟩
  have := run2_uniform W hm₁ hm₂ hf₁ hf₂ hr hp cs st h0
  rw [h₁, h₂, hB₁, hB₂] at this
  exact Bool.noConfusion this

end Uniform2

/-- **Out of reach.** Into a foreign target whose policy no list of the roster's keys meets, no seal of this scope latches an edge:
the source's endorsers are read through the scope's roster. -/
theorem edgeCond_out_of_reach (W : World C K P) (cm : Commit C K) (S w v : C) (k : Kind) (init : C → List K)
    (hf : (W.info v).isLocal = false)
    (hq : ∀ E : List K, (∀ e ∈ E, W.member (roster W S v) e = true) → W.quorum E (pol W S v).1 = false) :
    edgeCond W cm S w v k init = false := by
  rw [edgeCond_foreign W cm S w v k init hf]
  apply hq
  intro e he
  simp only [endorsers, List.mem_map, List.mem_filter, sealCounts, Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨s, ⟨-, ⟨-, -⟩, hm⟩, rfl⟩ := he
  exact hm

/-! ## The exact condition -/

section Faithful

/-- Two scopes' readings of one set of cells: the bytes of a cell are the same on both sides, so all but its locality agree. -/
structure SameBytes (W₁ W₂ : World C K P) : Prop where
  invalidates : ∀ c, (W₁.info c).invalidates = (W₂.info c).invalidates
  retires : ∀ c, (W₁.info c).retires = (W₂.info c).retires
  supersedes : ∀ c, (W₁.info c).supersedes = (W₂.info c).supersedes
  schema : ∀ c, (W₁.info c).schema = (W₂.info c).schema
  verdictInvalid : ∀ c, (W₁.info c).verdictInvalid = (W₂.info c).verdictInvalid

/-- A set closed under who attacks it and what it supersedes, present alike, whose latched edges into it agree, and every cell of
which is accepted on each side: pinned where it is foreign, by being local where it is not. -/
structure Faithful (W₁ W₂ : World C K P) (AE₁ AE₂ : C → C → Kind → Bool) (Present₁ Present₂ Acc₁ Acc₂ : C → Prop) (Pr : C → Prop) :
    Prop where
  present : ∀ v, Pr v → (Present₁ v ↔ Present₂ v)
  edges : ∀ v, Pr v → ∀ w k, AE₁ w v k = AE₂ w v k
  attackers₁ : ∀ v, Pr v → ∀ w k, v ∈ (W₁.info w).edges k → AE₁ w v k = true → Pr w
  supers : ∀ v, Pr v → ∀ u ∈ (W₁.info v).supersedes, Pr u
  acc₁ : ∀ v, Pr v → Acc₁ v
  acc₂ : ∀ v, Pr v → Acc₂ v

variable {W₁ W₂ : World C K P} {AE₁ AE₂ : C → C → Kind → Bool} {Present₁ Present₂ isI₁ isI₂ : C → Prop} {Auth₁ Auth₂ : C → Bool}
  {Inv₁ Eff₁ Ret₁ Acc₁ Inv₂ Eff₂ Ret₂ Acc₂ : C → Prop} {Pr : C → Prop}

theorem Faithful.symm (hs : SameBytes W₁ W₂) (h : Faithful W₁ W₂ AE₁ AE₂ Present₁ Present₂ Acc₁ Acc₂ Pr) :
    Faithful W₂ W₁ AE₂ AE₁ Present₂ Present₁ Acc₂ Acc₁ Pr where
  present := fun v hv => (h.present v hv).symm
  edges := fun v hv w k => (h.edges v hv w k).symm
  attackers₁ := fun v hv w k hm he => by
    have hm₁ : v ∈ (W₁.info w).edges k := by
      cases k
      · simpa [CellInfo.edges, hs.supersedes w] using hm
      · simpa [CellInfo.edges, hs.retires w] using hm
      · simpa [CellInfo.edges, hs.invalidates w] using hm
    exact h.attackers₁ v hv w k hm₁ (by rw [h.edges v hv w k]; exact he)
  supers := fun v hv u hu => h.supers v hv u (by rw [hs.supersedes v]; exact hu)
  acc₁ := h.acc₂
  acc₂ := h.acc₁

/-- `Effective` agrees on the set. -/
theorem eff_faithful (hs : SameBytes W₁ W₂) (hp : Faithful W₁ W₂ AE₁ AE₂ Present₁ Present₂ Acc₁ Acc₂ Pr)
    (h1 : IsPass1 W₁ AE₁ Present₁ isI₁ Auth₁ Inv₁ Eff₁ Ret₁ Acc₁) (h2 : IsPass1 W₂ AE₂ Present₂ isI₂ Auth₂ Inv₂ Eff₂ Ret₂ Acc₂)
    (rank : C → Nat) (hr : ∀ w v k, v ∈ (W₁.info w).edges k → rank v < rank w)
    (N : Nat) (hb : ∀ w, Pr w → Present₁ w → rank w < N) :
    ∀ n v, Pr v → N - rank v ≤ n → (Eff₁ v ↔ Eff₂ v) := by
  intro n
  induction n with
  | zero =>
    intro v hv hn
    have hnp : ¬ Present₁ v := fun hpv => by have := hb v hv hpv; omega
    have hnp' : ¬ Present₂ v := fun h => hnp ((hp.present v hv).mpr h)
    constructor
    · intro h; exact absurd ((h1.eff_eq v).mp h).1 hnp
    · intro h; exact absurd ((h2.eff_eq v).mp h).1 hnp'
  | succ n ih =>
    intro v hv hn
    have hage : ∀ w, v ∈ (W₁.info w).invalidates → Pr w → Present₁ w → (Eff₁ w ↔ Eff₂ w) := by
      intro w hm hw hpw
      have hlt := hr w v .invalidates hm
      have hbw := hb w hw hpw
      exact ih w hw (by omega)
    have hinv : Inv₁ v → Inv₂ v := by
      intro hi
      obtain ⟨w, he, -, hm, hae, hsc⟩ := (h1.inv_eq v).mp hi
      have hw : Pr w := hp.attackers₁ v hv w .invalidates hm hae
      refine (h2.inv_eq v).mpr ⟨w, (hage w hm hw ((h1.eff_eq w).mp he).1).mp he, hp.acc₂ w hw, ?_, ?_, ?_⟩
      · rw [← hs.invalidates w]; exact hm
      · rw [← hp.edges v hv w .invalidates]; exact hae
      · rwa [← hs.schema w, ← hs.verdictInvalid w]
    have hinv' : Inv₂ v → Inv₁ v := by
      intro hi
      obtain ⟨w, he, -, hm, hae, hsc⟩ := (h2.inv_eq v).mp hi
      have hm₁ : v ∈ (W₁.info w).invalidates := by rw [hs.invalidates w]; exact hm
      have hae' : AE₁ w v .invalidates = true := by rw [hp.edges v hv w .invalidates]; exact hae
      have hw : Pr w := hp.attackers₁ v hv w .invalidates hm₁ hae'
      have hpw : Present₁ w := (hp.present w hw).mpr ((h2.eff_eq w).mp he).1
      refine (h1.inv_eq v).mpr ⟨w, (hage w hm₁ hw hpw).mpr he, hp.acc₁ w hw, hm₁, hae', ?_⟩
      rwa [hs.schema w, hs.verdictInvalid w]
    constructor
    · intro h
      obtain ⟨hpv, hni⟩ := (h1.eff_eq v).mp h
      exact (h2.eff_eq v).mpr ⟨(hp.present v hv).mp hpv, fun hi => hni (hinv' hi)⟩
    · intro h
      obtain ⟨hpv, hni⟩ := (h2.eff_eq v).mp h
      exact (h1.eff_eq v).mpr ⟨(hp.present v hv).mpr hpv, fun hi => hni (hinv hi)⟩

theorem ret_faithful (hs : SameBytes W₁ W₂) (hp : Faithful W₁ W₂ AE₁ AE₂ Present₁ Present₂ Acc₁ Acc₂ Pr)
    (h1 : IsPass1 W₁ AE₁ Present₁ isI₁ Auth₁ Inv₁ Eff₁ Ret₁ Acc₁) (h2 : IsPass1 W₂ AE₂ Present₂ isI₂ Auth₂ Inv₂ Eff₂ Ret₂ Acc₂)
    (heff : ∀ w, Pr w → Eff₁ w → Eff₂ w) {v : C} (hv : Pr v) (h : Ret₁ v) : Ret₂ v := by
  obtain ⟨w, he, -, hm, hae⟩ := (h1.ret_eq v).mp h
  have hw : Pr w := hp.attackers₁ v hv w .retires hm hae
  refine (h2.ret_eq v).mpr ⟨w, heff w hw he, hp.acc₂ w hw, ?_, ?_⟩
  · rw [← hs.retires w]; exact hm
  · rw [← hp.edges v hv w .retires]; exact hae

theorem sup_faithful (hs : SameBytes W₁ W₂) (hp : Faithful W₁ W₂ AE₁ AE₂ Present₁ Present₂ Acc₁ Acc₂ Pr)
    (heff : ∀ w, Pr w → Eff₁ w → Eff₂ w) {v : C} (h : Superseded W₁ AE₁ Eff₁ Acc₁ v) (hv : Pr v) :
    Superseded W₂ AE₂ Eff₂ Acc₂ v := by
  induction h with
  | @direct w v' hm hae he _ =>
    have hw : Pr w := hp.attackers₁ v' hv w .supersedes hm hae
    refine Superseded.direct ?_ ?_ (heff w hw he) (hp.acc₂ w hw)
    · rw [← hs.supersedes w]; exact hm
    · rw [← hp.edges v' hv w .supersedes]; exact hae
  | @trans w v' hm hae _ ih =>
    have hw : Pr w := hp.attackers₁ v' hv w .supersedes hm hae
    refine Superseded.trans ?_ ?_ (ih hw)
    · rw [← hs.supersedes w]; exact hm
    · rw [← hp.edges v' hv w .supersedes]; exact hae

/-- **The exact condition, Pass 1.** On a closed set accepted on each side, if the latched edges into it agree, so does `Active`.
Test 127 shows each hypothesis needed: `A` latching what `B` did not, `B` latching what `A` cannot. -/
theorem import_faithful (hs : SameBytes W₁ W₂) (hp : Faithful W₁ W₂ AE₁ AE₂ Present₁ Present₂ Acc₁ Acc₂ Pr)
    (h1 : IsPass1 W₁ AE₁ Present₁ isI₁ Auth₁ Inv₁ Eff₁ Ret₁ Acc₁) (h2 : IsPass1 W₂ AE₂ Present₂ isI₂ Auth₂ Inv₂ Eff₂ Ret₂ Acc₂)
    (rank : C → Nat) (hr : ∀ w v k, v ∈ (W₁.info w).edges k → rank v < rank w)
    (N : Nat) (hb : ∀ w, Pr w → Present₁ w → rank w < N) {v : C} (hv : Pr v) :
    Active W₁ AE₁ Eff₁ Acc₁ Ret₁ v ↔ Active W₂ AE₂ Eff₂ Acc₂ Ret₂ v := by
  have heffiff : ∀ w, Pr w → (Eff₁ w ↔ Eff₂ w) := fun w hw =>
    eff_faithful hs hp h1 h2 rank hr N hb (N - rank w) w hw (Nat.le_refl _)
  have heff : ∀ w, Pr w → Eff₁ w → Eff₂ w := fun w hw => (heffiff w hw).mp
  have heff' : ∀ w, Pr w → Eff₂ w → Eff₁ w := fun w hw => (heffiff w hw).mpr
  have hs' : SameBytes W₂ W₁ := ⟨fun c => (hs.invalidates c).symm, fun c => (hs.retires c).symm, fun c => (hs.supersedes c).symm,
    fun c => (hs.schema c).symm, fun c => (hs.verdictInvalid c).symm⟩
  have hp' := Faithful.symm hs hp
  have hret : Ret₁ v ↔ Ret₂ v := ⟨ret_faithful hs hp h1 h2 heff hv, ret_faithful hs' hp' h2 h1 heff' hv⟩
  have hsup : Superseded W₁ AE₁ Eff₁ Acc₁ v ↔ Superseded W₂ AE₂ Eff₂ Acc₂ v :=
    ⟨fun h => sup_faithful hs hp heff h hv, fun h => sup_faithful hs' hp' heff' h hv⟩
  have hedge : ∀ u ∈ (W₁.info v).supersedes, AE₁ v u .supersedes = AE₂ v u .supersedes :=
    fun u hu => hp.edges u (hp.supers v hv u hu) v .supersedes
  constructor
  · rintro ⟨a, b, c, -, e⟩
    refine ⟨(heffiff v hv).mp a, fun h => b (hret.mpr h), fun h => c (hsup.mpr h), hp.acc₂ v hv, ?_⟩
    intro u hu
    have hu₁ : u ∈ (W₁.info v).supersedes := by rw [hs.supersedes v]; exact hu
    rw [← hedge u hu₁]; exact e u hu₁
  · rintro ⟨a, b, c, -, e⟩
    refine ⟨(heffiff v hv).mpr a, fun h => b (hret.mp h), fun h => c (hsup.mp h), hp.acc₁ v hv, ?_⟩
    intro u hu
    rw [hedge u hu]; exact e u (by rw [← hs.supersedes v]; exact hu)

end Faithful

/-! ## Pass 2 -/

section Stale

variable {N : Nat}

/-- A pin of `x`: a local, Active, Authorized acceptance with payload `x`, resting on nothing, so never Stale. -/
structure Pin (I : Pass2In N) (a x : Fin N) : Prop where
  isAcc : I.isAcceptance a
  isLocal : I.isLocal a
  active : I.active a
  authorized : I.authorized a
  payload : I.payload a = some x
  relies : I.relies a = []

/-- A pin is never Stale. -/
theorem pin_not_stale {I : Pass2In N} {a x : Fin N} (h : Pin I a x) : ¬ Stale I a := by
  intro hs
  rcases ((stale_fixed I a).mp hs).2 with ⟨d, hd, -⟩ | ⟨hl, -⟩
  · rw [h.relies] at hd; exact absurd hd (by simp)
  · exact hl h.isLocal

theorem stale_sub2 (I I' : Pass2In N) (Pr : Fin N → Prop)
    (hl : ∀ v, Pr v → I.isLocal v ∨ ∃ a, Pin I a v) (hact : ∀ v, Pr v → (I.active v ↔ I'.active v))
    (hrel : ∀ v, Pr v → I.relies v = I'.relies v) (hclosed : ∀ v, Pr v → ∀ d ∈ I.relies v, Pr d) :
    ∀ v, Pr v → Stale I v → Stale I' v := by
  -- what is stale on the left, among the set, is stale on the right; nothing that pins is ever in it
  let S : Fin N → Prop := fun v => (Pr v → Stale I' v) ∧ ¬ (∃ x, Pin I v x)
  have hpre : Sub (Φ I S) S := by
    rintro v ⟨ha, h⟩
    refine ⟨fun hv => ?_, ?_⟩
    · refine lfp_pre (Φ_mono I') v ⟨(hact v hv).mp ha, Or.inl ?_⟩
      rcases h with ⟨d, hd, h⟩ | ⟨hnl, hna⟩
      · have hdp := hclosed v hv d hd
        refine ⟨d, hrel v hv ▸ hd, ?_⟩
        rcases h with h | h
        · exact Or.inl fun h' => h ((hact d hdp).mpr h')
        · exact Or.inr (h.1 hdp)
      · exfalso
        rcases hl v hv with h | ⟨a, hpin⟩
        · exact hnl h
        · exact hna (LiveAcc.pin hpin.isAcc hpin.isLocal hpin.active hpin.authorized
            (fun hs => hs.2 ⟨v, hpin⟩) hpin.payload)
    · rintro ⟨x, hpin⟩
      rcases h with ⟨d, hd, -⟩ | ⟨hnl, -⟩
      · rw [hpin.relies] at hd; exact absurd hd (by simp)
      · exact hnl hpin.isLocal
  intro v hv h
  exact (stale_least I S hpre v h).1 hv

/-- **The exact condition, Pass 2.** On a set closed under `relies`, each cell local or pinned on each side, with the same `relies`
and the same `Active`, `Stale` agrees. -/
theorem stale_faithful (I I' : Pass2In N) (Pr : Fin N → Prop)
    (hl : ∀ v, Pr v → I.isLocal v ∨ ∃ a, Pin I a v) (hl' : ∀ v, Pr v → I'.isLocal v ∨ ∃ a, Pin I' a v)
    (hact : ∀ v, Pr v → (I.active v ↔ I'.active v)) (hrel : ∀ v, Pr v → I.relies v = I'.relies v)
    (hclosed : ∀ v, Pr v → ∀ d ∈ I.relies v, Pr d) {v : Fin N} (hv : Pr v) : Stale I v ↔ Stale I' v :=
  ⟨stale_sub2 I I' Pr hl hact hrel hclosed v hv,
   stale_sub2 I' I Pr hl' (fun x hx => (hact x hx).symm) (fun x hx => (hrel x hx).symm)
     (fun x hx d hd => hclosed x hx d (hrel x hx ▸ hd)) v hv⟩

end Stale

/-! ## What `A` can do instead -/

section Follow

variable {W : World C K P} {AE : C → C → Kind → Bool} {Present isI : C → Prop} {Auth : C → Bool} {Inv Eff Ret Acc : C → Prop}

/-- **A pinned cell stands.** With no latched edge into it and no supersedes edge of its own, a present cell that `A` accepts is
Active. So `A` needs no cross-seal to keep a cell `B` keeps. -/
theorem pinned_active (h : IsPass1 W AE Present isI Auth Inv Eff Ret Acc) {x : C} (hp : Present x) (ha : Acc x)
    (hn : ∀ w k, AE w x k = false) (hs : (W.info x).supersedes = []) : Active W AE Eff Acc Ret x := by
  have hni : ¬ Inv x := by
    intro hi
    obtain ⟨w, -, -, -, hae, -⟩ := (h.inv_eq x).mp hi
    rw [hn] at hae; exact Bool.noConfusion hae
  refine ⟨(h.eff_eq x).mpr ⟨hp, hni⟩, ?_, ?_, ha, ?_⟩
  · intro hr
    obtain ⟨w, -, -, -, hae⟩ := (h.ret_eq x).mp hr
    rw [hn] at hae; exact Bool.noConfusion hae
  · intro hsp
    cases hsp with
    | direct _ hae _ _ => rw [hn] at hae; exact Bool.noConfusion hae
    | trans _ hae _ => rw [hn] at hae; exact Bool.noConfusion hae
  · intro u hu
    rw [hs] at hu; exact absurd hu (by simp)

/-- **A cell `A` does not accept does not stand.** So `A` lets go of a cell `B` has lost by its own acceptance alone, whoever its
keys are, where a cross-seal may not reach (`edgeCond_out_of_reach`). -/
theorem unpinned_not_active {x : C} (hna : ¬ Acc x) : ¬ Active W AE Eff Acc Ret x :=
  fun ⟨_, _, _, ha, _⟩ => hna ha

end Follow

end Vars1
