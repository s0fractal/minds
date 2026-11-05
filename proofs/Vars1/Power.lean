import Vars1.Fold2
import Vars1.Pass1
import Vars1.Pass2
import Vars1.Pass3

/-!
# Who can change a status: confinement over every extension of the chain

The theorems of `Fold.lean` speak of one commit. Here a coalition `Co` of keys extends the chain by any number of
commits, and we ask what it can change. Its seals are the only new ones: every seal of a commit of the extension is
either an old seal (a commit's seals are those of its tree, so every seal admitted so far stays) or by a key of `Co`.
It makes no rotation: a rotation needs the governing scope's admission quorum, which the gate checks (E-20). A
coalition holding that quorum leaves the keys it removes no move after the wait (`moves_notice`), which is why the
reader's pin exists; a cell with an evaluator policy of its own stays out of its reach except through what it rests on.

* `run_latch`, `run2_latch` — **an edge is confined.** A new latch `w → v` needs either a quorum of `Pol(v)` among
  `w`'s old endorsers and the coalition, or, for a supersedes or a retires edge on a local cell the author may evict,
  one of `v`'s initial endorsers among them (`CanLatch`). This holds for the v1 and for the v2 fold.
* `pass1_frame`, `active_frame` — **the statuses of a closed set are confined.** If no new edge enters a set of local
  cells closed under who attacks it and what it supersedes, every Pass 1 bit of the set is unchanged, whatever the rest
  of the chain does. `confinement` joins this to the fold.
* `stale_frame` — the same for Pass 2, for a set closed under `relies`.
* `settled_keeps` — **a coalition takes back only its own endorsement.** An INVALID verdict by `Co` withdraws no other
  key's endorsement, so a decision whose counted keys outside `Co` still meet its quorum stays Settled.
* `settled_needs` — and a coalition can settle a decision only with the keys already counted.
* `settled_iff_keys` — Settled is a function of the set of keys that count, and of nothing else.

What is not here: the wait of a rotation that has already begun, which any commit counts (`moves_notice`), and foreign
cells, whose acceptance the frame theorems leave out by asking every cell of the set to be local.
-/

set_option linter.unusedSectionVars false

namespace Vars1

variable {C K P : Type} [DecidableEq C] [DecidableEq K]

/-! ## An edge is confined -/

section Latch

variable (W : World C K P) (old : List (Seal C K)) (Co : K → Prop)

/-- A key that may stand behind `w` under `S`: one of the coalition's, or one with an old seal on `w` under `S`. -/
def Backer (S w : C) (e : K) : Prop :=
  Co e ∨ ∃ s ∈ old, s.target = w ∧ s.ctx = S ∧ s.key = e

/-- What it takes to latch `w → v` under `S`, for a cell `v` with InitialEndorsers `iv`: §4.1 step 3, read from what the
coalition can bring. -/
def CanLatch (S w v : C) (k : Kind) (iv : List K) : Prop :=
  (∃ E, (∀ e ∈ E, Backer old Co S w e) ∧ W.quorum E (pol W S v).1 = true) ∨
  (k ≠ .invalidates ∧ (pol W S v).2 = true ∧ (W.info v).isLocal = true ∧ ∃ e ∈ iv, Backer old Co S w e)

/-- Every seal of the commit is old or the coalition's. -/
def SealsFrom (cm : Commit C K) : Prop := ∀ s ∈ cm.seals, s ∈ old ∨ Co s.key

variable {W old Co}

theorem endorsers_back {cm : Commit C K} (hs : SealsFrom old Co cm) {S w : C} {r : P} {e : K}
    (he : e ∈ endorsers W cm S w r) : Backer old Co S w e := by
  simp only [endorsers, List.mem_map, List.mem_filter, sealCounts, Bool.and_eq_true, decide_eq_true_eq] at he
  obtain ⟨s, ⟨hm, ⟨ht, hc⟩, -⟩, rfl⟩ := he
  rcases hs s hm with h | h
  · exact Or.inr ⟨s, h, ht, hc, rfl⟩
  · exact Or.inl h

/-- §4.1 step 3 can hold only for what the coalition can bring. -/
theorem edgeCond_canLatch {cm : Commit C K} (hs : SealsFrom old Co cm) {S w v : C} {k : Kind} {init : C → List K}
    (h : edgeCond W cm S w v k init = true) : CanLatch W old Co S w v k (init v) := by
  simp only [edgeCond, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
    List.contains_iff_mem] at h
  rcases h with h | ⟨⟨⟨hk, hev⟩, hloc⟩, e, he, hi⟩
  · exact Or.inl ⟨_, fun e he => endorsers_back hs he, h⟩
  · exact Or.inr ⟨hk, hev, hloc, e, hi, endorsers_back hs he⟩

/-- **What a threshold above one is worth.** One key `c`, with no old seal under `S` on the source by anyone else, latches no
edge into `v` if no list of `c` alone meets `v`'s policy, unless it is an initial endorser of `v` and may evict it. This is
why an admission threshold of two closes what one key can do by an edge on a verdict, on a ground and on a rotation's
quorum at once: the policy of each of them is the admission policy. -/
theorem one_key_cannot_latch {c : K} {S w v : C} {k : Kind} {iv : List K}
    (hold : ∀ s ∈ old, s.target = w → s.ctx = S → s.key = c)
    (hco : ∀ e, Co e → e = c)
    (hq : ∀ E : List K, (∀ e ∈ E, e = c) → W.quorum E (pol W S v).1 = false)
    (hauthor : k = .invalidates ∨ (pol W S v).2 = false ∨ c ∉ iv) :
    ¬ CanLatch W old Co S w v k iv := by
  have hback : ∀ e, Backer old Co S w e → e = c := by
    rintro e (h | ⟨s, hs, ht, hx, rfl⟩)
    · exact hco e h
    · exact hold s hs ht hx
  rintro (⟨E, hE, hquo⟩ | ⟨hne, hev, -, e, he, hb⟩)
  · rw [hq E (fun e he => hback e (hE e he))] at hquo
    exact Bool.noConfusion hquo
  · rcases hauthor with h | h | h
    · exact hne h
    · rw [h] at hev; exact Bool.noConfusion hev
    · exact h (hback e hb ▸ he)

theorem initAfter_present (st : St C K) (cm : Commit C K) {v : C} (hv : v ∈ st.present) :
    initAfter W st cm v = st.initEnd v := by
  simp [initAfter, hv]

/-- **An edge is confined, under v1.** Over an extension of the chain whose seals are old or the coalition's and which
makes no rotation, a latch on a present cell `v` that was not there is one the coalition can make: `CanLatch` under
the governing scope, with `v`'s InitialEndorsers. -/
theorem run_latch {v w : C} {k : Kind} :
    ∀ (ext : List (Commit C K)) (st : St C K), (∀ cm ∈ ext, SealsFrom old Co cm ∧ cm.newScope = none) →
      v ∈ st.present → (run W st ext).edge w v k = true →
      st.edge w v k = true ∨ (v ∈ (W.info w).edges k ∧ CanLatch W old Co st.scope w v k (st.initEnd v))
  | [], st, _, _, h => Or.inl h
  | cm :: ext, st, hext, hv, h => by
    obtain ⟨hs, hns⟩ := hext cm (by simp)
    have hv' : v ∈ (step W st cm).present := by simp [step, hv]
    have hscope : (step W st cm).scope = st.scope := by simp [step, hns]
    have hinit : (step W st cm).initEnd v = st.initEnd v := by simp [step, initAfter_present st cm hv]
    rcases run_latch ext (step W st cm) (fun c hc => hext c (List.mem_cons_of_mem _ hc)) hv' h with h1 | ⟨hm, hc⟩
    · simp only [step, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
      rcases h1 with h1 | ⟨⟨-, hm⟩, he⟩
      · exact Or.inl h1
      · have := edgeCond_canLatch hs he
        rw [initAfter_present st cm hv] at this
        exact Or.inr ⟨hm, this⟩
    · rw [hscope, hinit] at hc
      exact Or.inr ⟨hm, hc⟩

end Latch

section Latch2

variable (W : World2 C K P) {old : List (Seal C K)} {Co : K → Prop}

theorem step2_quiet (st : St2 C K) (cm : Commit C K) (hw : st.waiting = none) (hns : cm.newScope = none) :
    step2 W st cm = latch2 W st cm ∧ (latch2 W st cm).waiting = none ∧ (latch2 W st cm).scope = st.scope := by
  have hp : pending st cm = none := by simp [pending, hw, hns]
  have hwait : (latch2 W st cm).waiting = none := by simp [latch2, hp, hw]
  refine ⟨?_, hwait, rfl⟩
  simp [step2, settle2, hwait]

/-- **An edge is confined, under v2.** As `run_latch`, on a chain with no rotation waiting at its tip. A rotation that
already waits is outside it: any commit counts its wait. -/
theorem run2_latch {v w : C} {k : Kind} :
    ∀ (ext : List (Commit C K)) (st : St2 C K), st.waiting = none →
      (∀ cm ∈ ext, SealsFrom old Co cm ∧ cm.newScope = none) →
      v ∈ st.present → (run2 W st ext).edge w v k = true →
      st.edge w v k = true ∨
        (v ∈ (W.info w).edges k ∧ CanLatch W.toWorld old Co st.scope w v k (st.initEnd v))
  | [], st, _, _, _, h => Or.inl h
  | cm :: ext, st, hw, hext, hv, h => by
    obtain ⟨hs, hns⟩ := hext cm (by simp)
    obtain ⟨hstep, hwait, hscope⟩ := step2_quiet W st cm hw hns
    have hrun : run2 W st (cm :: ext) = run2 W (latch2 W st cm) ext := by
      show run2 W (step2 W st cm) ext = _
      rw [hstep]
    rw [hrun] at h
    have hv' : v ∈ (latch2 W st cm).present := by simp [latch2, hv]
    have hinit : (latch2 W st cm).initEnd v = st.initEnd v := by
      simp [latch2, initAfter_present st.toSt cm hv]
    rcases run2_latch ext (latch2 W st cm) hwait (fun c hc => hext c (List.mem_cons_of_mem _ hc)) hv' h with
      h1 | ⟨hm, hc⟩
    · simp only [latch2, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
      rcases h1 with h1 | ⟨⟨⟨-, hm⟩, -⟩, he⟩
      · exact Or.inl h1
      · have := edgeCond_canLatch hs he
        rw [initAfter_present st.toSt cm hv] at this
        exact Or.inr ⟨hm, this⟩
    · rw [hscope, hinit] at hc
      exact Or.inr ⟨hm, hc⟩

end Latch2

/-! ## The statuses of a closed set are confined -/

section Frame

variable (W : World C K P) {AE AE' : C → C → Kind → Bool} {Present Present' isI isI' : C → Prop} {Auth Auth' : C → Bool}
  {Inv Eff Ret Acc Inv' Eff' Ret' Acc' : C → Prop} {Pr : C → Prop}

/-- A set of local cells closed under who attacks it and what it supersedes, present alike before and after, that no
new edge enters. -/
structure Protected (W : World C K P) (AE AE' : C → C → Kind → Bool) (Present Present' : C → Prop) (Pr : C → Prop) :
    Prop where
  isLocal : ∀ v, Pr v → (W.info v).isLocal = true
  present : ∀ v, Pr v → (Present v ↔ Present' v)
  edge_in : ∀ v, Pr v → ∀ w k, AE' w v k = AE w v k
  attackers : ∀ v, Pr v → ∀ w k, v ∈ (W.info w).edges k → AE w v k = true → Pr w
  supers : ∀ v, Pr v → ∀ u ∈ (W.info v).supersedes, Pr u

theorem Protected.symm (h : Protected W AE AE' Present Present' Pr) : Protected W AE' AE Present' Present Pr where
  isLocal := h.isLocal
  present := fun v hv => (h.present v hv).symm
  edge_in := fun v hv w k => (h.edge_in v hv w k).symm
  attackers := fun v hv w k hm he => h.attackers v hv w k hm (h.edge_in v hv w k ▸ he)
  supers := h.supers

variable {W}

theorem acc_local (h1 : IsPass1 W AE Present isI Auth Inv Eff Ret Acc) {v : C} (hl : (W.info v).isLocal = true) : Acc v :=
  (h1.acc_eq v).mpr (Or.inr (Or.inl hl))

/-- Half of `Eff` on a set: an attacker's `Eff` carries over, given it for every attacker. -/
theorem inv_step (hp : Protected W AE AE' Present Present' Pr)
    (h1 : IsPass1 W AE Present isI Auth Inv Eff Ret Acc) (h2 : IsPass1 W AE' Present' isI' Auth' Inv' Eff' Ret' Acc')
    {v : C} (hv : Pr v) (heff : ∀ w, Pr w → Eff w → Eff' w) (hi : Inv v) : Inv' v := by
  obtain ⟨w, he, -, hm, hae, hs⟩ := (h1.inv_eq v).mp hi
  have hw : Pr w := hp.attackers v hv w .invalidates hm hae
  refine (h2.inv_eq v).mpr ⟨w, heff w hw he, acc_local h2 (hp.isLocal w hw), hm, ?_, hs⟩
  rw [hp.edge_in v hv w .invalidates]
  exact hae

/-- `Effective` is the same on the set. The attack relation points from newer to older (`rank`), and only a present
cell is Effective, so the argument descends from the newest present cell. -/
theorem eff_frame (hp : Protected W AE AE' Present Present' Pr)
    (h1 : IsPass1 W AE Present isI Auth Inv Eff Ret Acc) (h2 : IsPass1 W AE' Present' isI' Auth' Inv' Eff' Ret' Acc')
    (rank : C → Nat) (hr : ∀ w v k, v ∈ (W.info w).edges k → rank v < rank w)
    (N : Nat) (hb : ∀ w, Pr w → Present w → rank w < N) :
    ∀ n v, Pr v → N - rank v ≤ n → (Eff v ↔ Eff' v) := by
  intro n
  induction n with
  | zero =>
    intro v hv hn
    have hnp : ¬ Present v := fun hpv => by have := hb v hv hpv; omega
    have hnp' : ¬ Present' v := fun h => hnp ((hp.present v hv).mpr h)
    constructor
    · intro h; exact absurd ((h1.eff_eq v).mp h).1 hnp
    · intro h; exact absurd ((h2.eff_eq v).mp h).1 hnp'
  | succ n ih =>
    intro v hv hn
    have hage : ∀ w k, v ∈ (W.info w).edges k → Pr w → Present w → (Eff w ↔ Eff' w) := by
      intro w k hm hw hpw
      have hlt := hr w v k hm
      have hbw := hb w hw hpw
      exact ih w hw (by omega)
    have heff_of : ∀ w k, v ∈ (W.info w).edges k → Pr w → Eff w → Eff' w :=
      fun w k hm hw he => (hage w k hm hw ((h1.eff_eq w).mp he).1).mp he
    have heff_of' : ∀ w k, v ∈ (W.info w).edges k → Pr w → Eff' w → Eff w := by
      intro w k hm hw he
      have hpw : Present w := (hp.present w hw).mpr ((h2.eff_eq w).mp he).1
      exact (hage w k hm hw hpw).mpr he
    have hinv : Inv v → Inv' v := by
      intro hi
      obtain ⟨w, he, -, hm, hae, hs⟩ := (h1.inv_eq v).mp hi
      have hw : Pr w := hp.attackers v hv w .invalidates hm hae
      refine (h2.inv_eq v).mpr ⟨w, heff_of w .invalidates hm hw he, acc_local h2 (hp.isLocal w hw), hm, ?_, hs⟩
      rw [hp.edge_in v hv w .invalidates]
      exact hae
    have hinv' : Inv' v → Inv v := by
      intro hi
      obtain ⟨w, he, -, hm, hae, hs⟩ := (h2.inv_eq v).mp hi
      have hae' : AE w v .invalidates = true := by rw [← hp.edge_in v hv w .invalidates]; exact hae
      have hw : Pr w := hp.attackers v hv w .invalidates hm hae'
      exact (h1.inv_eq v).mpr ⟨w, heff_of' w .invalidates hm hw he, acc_local h1 (hp.isLocal w hw), hm, hae', hs⟩
    constructor
    · intro h
      obtain ⟨hpv, hni⟩ := (h1.eff_eq v).mp h
      exact (h2.eff_eq v).mpr ⟨(hp.present v hv).mp hpv, fun hi => hni (hinv' hi)⟩
    · intro h
      obtain ⟨hpv, hni⟩ := (h2.eff_eq v).mp h
      exact (h1.eff_eq v).mpr ⟨(hp.present v hv).mpr hpv, fun hi => hni (hinv hi)⟩

/-- `Retired` carries over, given `Effective` on the set. -/
theorem ret_step (hp : Protected W AE AE' Present Present' Pr)
    (h1 : IsPass1 W AE Present isI Auth Inv Eff Ret Acc) (h2 : IsPass1 W AE' Present' isI' Auth' Inv' Eff' Ret' Acc')
    (heff : ∀ w, Pr w → Eff w → Eff' w) {v : C} (hv : Pr v) (h : Ret v) : Ret' v := by
  obtain ⟨w, he, -, hm, hae⟩ := (h1.ret_eq v).mp h
  have hw : Pr w := hp.attackers v hv w .retires hm hae
  refine (h2.ret_eq v).mpr ⟨w, heff w hw he, acc_local h2 (hp.isLocal w hw), hm, ?_⟩
  rw [hp.edge_in v hv w .retires]
  exact hae

/-- `Superseded` carries over, given `Effective` on the set. -/
theorem sup_step (hp : Protected W AE AE' Present Present' Pr)
    (h2 : IsPass1 W AE' Present' isI' Auth' Inv' Eff' Ret' Acc')
    (heff : ∀ w, Pr w → Eff w → Eff' w) {v : C} (h : Superseded W AE Eff Acc v) (hv : Pr v) :
    Superseded W AE' Eff' Acc' v := by
  induction h with
  | @direct w v' hm hae he _ =>
    have hw : Pr w := hp.attackers v' hv w .supersedes hm hae
    refine Superseded.direct hm ?_ (heff w hw he) (acc_local h2 (hp.isLocal w hw))
    rw [hp.edge_in v' hv w .supersedes]
    exact hae
  | @trans w v' hm hae _ ih =>
    have hw : Pr w := hp.attackers v' hv w .supersedes hm hae
    refine Superseded.trans hm ?_ (ih hw)
    rw [hp.edge_in v' hv w .supersedes]
    exact hae

/-- **The Pass 1 bits of a closed set are confined.** If no new edge enters a closed set of local cells that stay
present alike, every Pass 1 bit of the set is what it was, whatever the rest of the chain does. -/
theorem pass1_frame (hp : Protected W AE AE' Present Present' Pr)
    (h1 : IsPass1 W AE Present isI Auth Inv Eff Ret Acc) (h2 : IsPass1 W AE' Present' isI' Auth' Inv' Eff' Ret' Acc')
    (rank : C → Nat) (hr : ∀ w v k, v ∈ (W.info w).edges k → rank v < rank w)
    (N : Nat) (hb : ∀ w, Pr w → Present w → rank w < N) {v : C} (hv : Pr v) :
    (Eff v ↔ Eff' v) ∧ (Inv v ↔ Inv' v) ∧ (Ret v ↔ Ret' v) ∧
      (Superseded W AE Eff Acc v ↔ Superseded W AE' Eff' Acc' v) ∧ Acc v ∧ Acc' v := by
  have heffiff : ∀ w, Pr w → (Eff w ↔ Eff' w) := fun w hw =>
    eff_frame hp h1 h2 rank hr N hb (N - rank w) w hw (Nat.le_refl _)
  have heff : ∀ w, Pr w → Eff w → Eff' w := fun w hw => (heffiff w hw).mp
  have heff' : ∀ w, Pr w → Eff' w → Eff w := fun w hw => (heffiff w hw).mpr
  have hps := Protected.symm W hp
  exact ⟨heffiff v hv,
    ⟨inv_step hp h1 h2 hv heff, inv_step hps h2 h1 hv heff'⟩,
    ⟨ret_step hp h1 h2 heff hv, ret_step hps h2 h1 heff' hv⟩,
    ⟨fun h => sup_step hp h2 heff h hv, fun h => sup_step hps h1 heff' h hv⟩,
    acc_local h1 (hp.isLocal v hv), acc_local h2 (hp.isLocal v hv)⟩

/-- **`Active` of a closed set is confined.** -/
theorem active_frame (hp : Protected W AE AE' Present Present' Pr)
    (h1 : IsPass1 W AE Present isI Auth Inv Eff Ret Acc) (h2 : IsPass1 W AE' Present' isI' Auth' Inv' Eff' Ret' Acc')
    (rank : C → Nat) (hr : ∀ w v k, v ∈ (W.info w).edges k → rank v < rank w)
    (N : Nat) (hb : ∀ w, Pr w → Present w → rank w < N) {v : C} (hv : Pr v) :
    Active W AE Eff Acc Ret v ↔ Active W AE' Eff' Acc' Ret' v := by
  obtain ⟨he, -, hret, hsup, ha, ha'⟩ := pass1_frame hp h1 h2 rank hr N hb hv
  have hedge : ∀ u ∈ (W.info v).supersedes, AE' v u .supersedes = AE v u .supersedes :=
    fun u hu => hp.edge_in u (hp.supers v hv u hu) v .supersedes
  constructor
  · rintro ⟨h1', h2', h3', -, h5'⟩
    exact ⟨he.mp h1', fun h => h2' (hret.mpr h), fun h => h3' (hsup.mpr h), ha',
      fun u hu => (hedge u hu).trans (h5' u hu)⟩
  · rintro ⟨h1', h2', h3', -, h5'⟩
    exact ⟨he.mpr h1', fun h => h2' (hret.mp h), fun h => h3' (hsup.mp h), ha,
      fun u hu => (hedge u hu).symm.trans (h5' u hu)⟩

/-- **`Confinement`.** A coalition extends a v2 chain with no rotation waiting at its tip, by commits whose seals are
old or its own, making no rotation. Take any closed set of local cells present at the tip such that the coalition
cannot latch an edge into it that is not there (`CanLatch`). Then `Active` of every cell of the set is unchanged. -/
theorem confinement {W2 : World2 C K P} {old : List (Seal C K)} {Co : K → Prop} {st : St2 C K}
    {ext : List (Commit C K)} {Pr : C → Prop}
    {Present Present' isI isI' : C → Prop} {Auth Auth' : C → Bool}
    {Inv Eff Ret Acc Inv' Eff' Ret' Acc' : C → Prop}
    (hw : st.waiting = none) (hext : ∀ cm ∈ ext, SealsFrom old Co cm ∧ cm.newScope = none)
    (hin : ∀ v, Pr v → v ∈ st.present ∧ (W2.info v).isLocal = true ∧ (Present v ↔ Present' v))
    (hatt : ∀ v, Pr v → ∀ w k, v ∈ (W2.info w).edges k → st.edge w v k = true → Pr w)
    (hsup : ∀ v, Pr v → ∀ u ∈ (W2.info v).supersedes, Pr u)
    (himm : ∀ v, Pr v → ∀ w k, st.edge w v k = false → v ∈ (W2.info w).edges k →
      ¬ CanLatch W2.toWorld old Co st.scope w v k (st.initEnd v))
    (h1 : IsPass1 W2.toWorld st.edge Present isI Auth Inv Eff Ret Acc)
    (h2 : IsPass1 W2.toWorld (run2 W2 st ext).edge Present' isI' Auth' Inv' Eff' Ret' Acc')
    (rank : C → Nat) (hr : ∀ w v k, v ∈ (W2.info w).edges k → rank v < rank w)
    (N : Nat) (hb : ∀ w, Pr w → Present w → rank w < N) {v : C} (hv : Pr v) :
    Active W2.toWorld st.edge Eff Acc Ret v ↔ Active W2.toWorld (run2 W2 st ext).edge Eff' Acc' Ret' v := by
  have hedge : ∀ x, Pr x → ∀ w k, (run2 W2 st ext).edge w x k = st.edge w x k := by
    intro x hx w k
    have hle := (run2_le W2 st ext).1 w x k
    cases he : st.edge w x k with
    | true => exact hle he
    | false =>
      cases he' : (run2 W2 st ext).edge w x k with
      | false => rfl
      | true =>
        rcases run2_latch W2 ext st hw hext (hin x hx).1 he' with h | ⟨hm, hc⟩
        · rw [he] at h; exact absurd h (by decide)
        · exact absurd hc (himm x hx w k he hm)
  have hp : Protected W2.toWorld st.edge (run2 W2 st ext).edge Present Present' Pr :=
    { isLocal := fun x hx => (hin x hx).2.1
      present := fun x hx => (hin x hx).2.2
      edge_in := hedge
      attackers := hatt
      supers := hsup }
  exact active_frame hp h1 h2 rank hr N hb hv

end Frame

/-! ## Pass 2 -/

section Stale

/-- A pre-fixed point of one input's operator from the other's `Stale`. -/
theorem stale_sub {N : Nat} (I I' : Pass2In N) (Pr : Fin N → Prop)
    (hl : ∀ v, Pr v → I.isLocal v) (hact : ∀ v, Pr v → (I.active v ↔ I'.active v))
    (hrel : ∀ v, Pr v → I.relies v = I'.relies v) (hclosed : ∀ v, Pr v → ∀ d ∈ I.relies v, Pr d) :
    ∀ v, Pr v → Stale I v → Stale I' v := by
  have hpre : Sub (Φ I (fun v => Pr v → Stale I' v)) (fun v => Pr v → Stale I' v) := by
    rintro v ⟨ha, h⟩ hv
    refine lfp_pre (Φ_mono I') v ⟨(hact v hv).mp ha, Or.inl ?_⟩
    rcases h with ⟨d, hd, h⟩ | ⟨hnl, -⟩
    · have hdp := hclosed v hv d hd
      refine ⟨d, hrel v hv ▸ hd, ?_⟩
      rcases h with h | h
      · exact Or.inl fun h' => h ((hact d hdp).mpr h')
      · exact Or.inr (h hdp)
    · exact absurd (hl v hv) hnl
  intro v hv h
  exact stale_least I _ hpre v h hv

/-- **`Stale` of a closed set is confined.** On a set of local cells closed under `relies`, with the same `relies` and
the same `Active`, `Stale` is the same. -/
theorem stale_frame {N : Nat} (I I' : Pass2In N) (Pr : Fin N → Prop)
    (hl : ∀ v, Pr v → I.isLocal v) (hl' : ∀ v, Pr v → I'.isLocal v) (hact : ∀ v, Pr v → (I.active v ↔ I'.active v))
    (hrel : ∀ v, Pr v → I.relies v = I'.relies v) (hclosed : ∀ v, Pr v → ∀ d ∈ I.relies v, Pr d)
    {v : Fin N} (hv : Pr v) : Stale I v ↔ Stale I' v :=
  ⟨stale_sub I I' Pr hl hact hrel hclosed v hv,
   stale_sub I' I Pr hl' (fun x hx => (hact x hx).symm) (fun x hx => (hrel x hx).symm)
     (fun x hx d hd => hclosed x hx d (hrel x hx ▸ hd)) v hv⟩

end Stale

/-! ## Pass 3 -/

section Settled

variable (W : World C K P) (X X' : Pass3In C K P) {cells cells' : List C} {wmax wmax' : C → List C}
  {cnt cnt' : C → C → List K} {Co : K → Prop}

/-- The keys that count for `v` at this tip: through a witness of `W_max(v)`, not withdrawn by the key itself. -/
def CountedKey (cells : List C) (v : C) (k : K) : Prop := ∃ w, InWmax W X cells v w ∧ Counts W X cells v w k

/-- A quorum depends only on which keys are in the list. -/
def QuorumExt : Prop := ∀ (E E' : List K) (p : P), (∀ k, k ∈ E ↔ k ∈ E') → W.quorum E p = W.quorum E' p

/-- A quorum stays met as endorsers are added. -/
def QuorumAdd : Prop := ∀ (E E' : List K) (p : P), (∀ k ∈ E, k ∈ E') → W.quorum E p = true → W.quorum E' p = true

variable {W X X'}

/-- **Settled is a function of the keys that count.** For a contract or decision, whatever the presentation, Settled
reads the cell's standing, its evaluator policy and the set of keys that count, and nothing else. -/
theorem settled_iff_keys (hext : QuorumExt W) (hw : WmaxFaithful W X cells wmax) (hc : CntFaithful W X cells cnt)
    {v : C} (hs : (W.info v).schema = .contract ∨ (W.info v).schema = .decision)
    {E : List K} (hE : ∀ k, k ∈ E ↔ CountedKey W X cells v k) :
    Settled W X wmax cnt v ↔ Live X v ∧ W.quorum E (evalPol W X v) = true := by
  have hmem : ∀ k, k ∈ (wmax v).flatMap (cnt v) ↔ k ∈ E := by
    intro k
    rw [hE k]
    constructor
    · intro h
      obtain ⟨w, hw', hk⟩ := List.mem_flatMap.mp h
      exact ⟨w, (hw v w).mp hw', (hc v w k).mp hk⟩
    · rintro ⟨w, h1, h2⟩
      exact List.mem_flatMap.mpr ⟨w, (hw v w).mpr h1, (hc v w k).mpr h2⟩
  have hq := hext _ _ (evalPol W X v) hmem
  unfold Settled
  rcases hs with h | h <;> simp [h, hq]

/-- **A coalition takes back only its own endorsement.** Let a tip's witnesses stay witnesses and their endorsers stay
endorsers after the coalition acts, and let every withdrawal after it be one that was there or the coalition's. If the
keys that counted, less the coalition's, still meet the quorum, the contract or decision stays Settled. So no key can
withdraw another's endorsement, whatever verifier id it names. -/
theorem settled_keeps (hadd : QuorumAdd W) (hw : WmaxFaithful W X cells wmax) (hc : CntFaithful W X cells cnt)
    (hw' : WmaxFaithful W X' cells' wmax') (hc' : CntFaithful W X' cells' cnt')
    {v : C} (hs : (W.info v).schema = .contract ∨ (W.info v).schema = .decision)
    (hlive : Live X' v) (hpol : evalPol W X v = evalPol W X' v)
    (hstay : ∀ w, InWmax W X cells v w → InWmax W X' cells' v w)
    (hend : ∀ w k, k ∈ witnessEndorsers W X w → k ∈ witnessEndorsers W X' w)
    (hwd : ∀ w k, Withdrawn W X' cells' v w k → Withdrawn W X cells v w k ∨ Co k)
    {E : List K} (hE : ∀ k ∈ E, CountedKey W X cells v k ∧ ¬ Co k) (hq : W.quorum E (evalPol W X v) = true) :
    Settled W X' wmax' cnt' v := by
  refine ⟨hlive, ?_⟩
  have hgoal : W.quorum ((wmax' v).flatMap (cnt' v)) (evalPol W X' v) = true := by
    rw [← hpol]
    refine hadd E _ _ (fun k hk => ?_) hq
    obtain ⟨⟨w, hin, hcount⟩, hnc⟩ := hE k hk
    refine List.mem_flatMap.mpr ⟨w, (hw' v w).mpr (hstay w hin), (hc' v w k).mpr ⟨hend w k hcount.1, ?_⟩⟩
    have hnot : ¬ Withdrawn W X cells v w k := by
      have := hcount.2
      rcases hs with h | h <;> simpa [h] using this
    have hnot' : ¬ Withdrawn W X' cells' v w k := fun hk' => (hwd w k hk').elim hnot hnc
    rcases hs with h | h <;> simpa [h] using hnot'
  rcases hs with h | h <;> simp [h, hgoal]

/-- **A coalition settles only with the keys already counted.** If a key that counts after the coalition acts either
counted before or is the coalition's, a contract or decision Settled afterwards has its quorum among those keys. -/
theorem settled_needs (hw' : WmaxFaithful W X' cells' wmax') (hc' : CntFaithful W X' cells' cnt')
    {v : C} (hs : (W.info v).schema = .contract ∨ (W.info v).schema = .decision)
    (hnew : ∀ k, CountedKey W X' cells' v k → CountedKey W X cells v k ∨ Co k)
    (hset : Settled W X' wmax' cnt' v) :
    ∃ E : List K, W.quorum E (evalPol W X' v) = true ∧ ∀ k ∈ E, CountedKey W X cells v k ∨ Co k := by
  refine ⟨(wmax' v).flatMap (cnt' v), ?_, fun k hk => ?_⟩
  · have := hset.2
    rcases hs with h | h <;> simpa [h] using this
  · obtain ⟨w, hw1, hk1⟩ := List.mem_flatMap.mp hk
    exact hnew k ⟨w, (hw' v w).mp hw1, (hc' v w k).mp hk1⟩

end Settled

end Vars1
