import Vars1.Exec

/-!
# The executable lens refines the model

`pass1`/`stale` (`Vars1/Exec.lean`, compiled as `vars1exec`) compute exactly the model's
§4.2 Passes 1–2 on the world the facts describe:

* `pass1_correct` — the Pass 1 bits satisfy `IsPass1`, and `sup`/`act` are the model's
  `Superseded`/`Active`;
* `stale_correct` — the Pass 2 bits are the model's `Stale = lfp Φ`.

Hypotheses: `Facts.Topo` (every reference names an older cell; true of the kernel's input,
which it refuses otherwise) and `Facts.Excl` (no cell is both an acceptance and a verdict).
-/

namespace Vars1.Exec

/-! ## Generic lemmas -/

theorem upd_same {α : Type} (g : Nat → α) (k : Nat) (x : α) : upd g k x k = x := by
  simp [upd]

theorem upd_other {α : Type} (g : Nat → α) {k w : Nat} (x : α) (h : w ≠ k) : upd g k x w = g w := by
  simp [upd, h]

theorem fill_ge {α : Type} (step : (Nat → α) → Nat → α) :
    ∀ k (g : Nat → α) w, k ≤ w → fill step k g w = g w
  | 0, _, _, _ => rfl
  | k + 1, g, w, h => by
    show fill step k (upd g k (step g k)) w = g w
    rw [fill_ge step k _ w (by omega), upd_other _ _ (by omega)]

/-- A newest-first fill is a fixed point of its step, when each step reads only newer cells. -/
theorem fill_fix {α : Type} (step : (Nat → α) → Nat → α)
    (hdep : ∀ g h v, (∀ w, v < w → g w = h w) → step g v = step h v) :
    ∀ k (g : Nat → α) v, v < k → fill step k g v = step (fill step k g) v
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, g, v, h => by
    show fill step k (upd g k (step g k)) v = step (fill step k (upd g k (step g k))) v
    rcases Nat.lt_or_ge v k with hv | hv
    · exact fill_fix step hdep k _ v hv
    · have hvk : v = k := by omega
      subst hvk
      rw [fill_ge step v _ v (Nat.le_refl _), upd_same]
      apply hdep
      intro w hw
      rw [fill_ge step v _ w (by omega), upd_other _ _ (by omega)]

theorem fillUpGo_succ {α : Type} (step : (Nat → α) → Nat → α) :
    ∀ m i (g : Nat → α), fillUpGo step (m + 1) i g =
      upd (fillUpGo step m i g) (i + m) (step (fillUpGo step m i g) (i + m))
  | 0, i, g => by simp [fillUpGo]
  | m + 1, i, g => by
    show fillUpGo step (m + 1) (i + 1) (upd g i (step g i)) = _
    rw [fillUpGo_succ step m (i + 1)]
    have e : i + 1 + m = i + (m + 1) := by omega
    rw [e]
    rfl

/-- An oldest-first fill processes `k` last, from the state after `0 … k-1`. -/
theorem fillUp_succ {α : Type} (step : (Nat → α) → Nat → α) (k : Nat) (g : Nat → α) :
    fillUp step (k + 1) g = upd (fillUp step k g) k (step (fillUp step k g) k) := by
  have := fillUpGo_succ step k 0 g
  simpa [fillUp] using this

theorem geta_tab {α : Type} [Inhabited α] (n : Nat) (g : Nat → α) {v : Nat} (h : v < n) :
    geta (tab n g) v = g v := by
  simp [geta, tab, Array.getD, h]

theorem mem_above {n v w : Nat} : w ∈ above n v ↔ w < n ∧ v < w := by
  simp [above]

/-! ## Pass 1: the fill is a fixed point of `step1` -/

variable (F : Facts)

/-- No cell is both an acceptance and a verdict (schemas are distinct ids). -/
def Facts.Excl : Prop := ∀ w, ¬ ((F.cell w).isAcc = true ∧ (F.cell w).isVerdict = true)

/-- The Pass 1 fill before materialization. -/
def Q : Nat → S1 := fill (step1 F) F.n fun _ => default

theorem step1_dep : ∀ (g h : Nat → S1) v, (∀ w, v < w → g w = h w) → step1 F g v = step1 F h v := by
  intro g h v H
  have e : (fun w => if v < w then g w else default) = (fun w => if v < w then h w else default) := by
    funext w
    by_cases hw : v < w
    · simp [hw, H w hw]
    · simp [hw]
  unfold step1
  rw [e]

theorem Q_eq {v : Nat} (hv : v < F.n) : Q F v = step1 F (Q F) v :=
  fill_fix (step1 F) (step1_dep F) F.n _ v hv

theorem pass1_get {v : Nat} (hv : v < F.n) : geta (pass1 F) v = Q F v := by
  simp [pass1, Q, geta_tab _ _ hv]

theorem inv_raw {v : Nat} (hv : v < F.n) :
    (Q F v).inv = true ↔ ∃ w, (w < F.n ∧ v < w) ∧
      ((Q F w).inv = false ∧ (Q F w).acc = true) ∧ authIn (F.cell w).inv v = true ∧
      ((F.cell w).isVerdict = false ∨ (F.cell w).verdictInvalid = true) := by
  rw [Q_eq F hv]
  simp only [step1, List.any_eq_true, mem_above, Bool.and_eq_true, Bool.not_eq_true',
    Bool.or_eq_true]
  refine exists_congr fun w => and_congr_right fun hw => ?_
  simp [hw.2, and_assoc]

theorem ret_raw {v : Nat} (hv : v < F.n) :
    (Q F v).ret = true ↔ ∃ w, (w < F.n ∧ v < w) ∧
      ((Q F w).inv = false ∧ (Q F w).acc = true) ∧ authIn (F.cell w).ret v = true := by
  rw [Q_eq F hv]
  simp only [step1, List.any_eq_true, mem_above, Bool.and_eq_true, Bool.not_eq_true']
  refine exists_congr fun w => and_congr_right fun hw => ?_
  simp [hw.2, and_assoc]

theorem sup_raw {v : Nat} (hv : v < F.n) :
    (Q F v).sup = true ↔ ∃ w, (w < F.n ∧ v < w) ∧ authIn (F.cell w).sup v = true ∧
      (((Q F w).inv = false ∧ (Q F w).acc = true) ∨ (Q F w).sup = true) := by
  rw [Q_eq F hv]
  simp only [step1, List.any_eq_true, mem_above, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true]
  refine exists_congr fun w => and_congr_right fun hw => ?_
  simp [hw.2]

theorem reach_raw {v : Nat} (hv : v < F.n) :
    (Q F v).reach = true ↔
      (∃ a, (a < F.n ∧ v < a) ∧ (F.cell a).isAcc = true ∧ (F.cell a).isLocal = true ∧
        (Q F a).act = true ∧ (F.cell a).authorized = true ∧ (F.cell a).payload = some v) ∨
      (∃ y, (y < F.n ∧ v < y) ∧ (Q F y).reach = true ∧ v ∈ (F.cell y).refs ∧
        (F.cell y).origin = (F.cell v).origin) := by
  rw [Q_eq F hv]
  simp only [step1, List.any_eq_true, mem_above, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.contains_iff_mem]
  refine or_congr (exists_congr fun a => and_congr_right fun ha => ?_)
    (exists_congr fun y => and_congr_right fun hy => ?_)
  · simp [ha.2, and_assoc]
  · simp [hy.2, and_assoc]

theorem acc_raw {v : Nat} (hv : v < F.n) :
    (Q F v).acc = true ↔ (F.cell v).isLocal = true ∨ (Q F v).reach = true := by
  rw [Q_eq F hv]
  simp only [step1, Bool.or_eq_true]

theorem act_raw {v : Nat} (hv : v < F.n) :
    (Q F v).act = true ↔ (Q F v).inv = false ∧ (Q F v).ret = false ∧ (Q F v).sup = false ∧
      (Q F v).acc = true ∧ ∀ e ∈ (F.cell v).sup, authIn (F.cell v).sup e.dst = true := by
  rw [Q_eq F hv]
  simp only [step1, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, and_assoc]

/-! ## The world the facts describe -/

def toFin (d : Nat) : Option (Fin F.n) := if h : d < F.n then some ⟨d, h⟩ else none

def finList (l : List Nat) : List (Fin F.n) := l.filterMap (toFin F)

theorem mem_finList {l : List Nat} {x : Fin F.n} : x ∈ finList F l ↔ x.val ∈ l := by
  simp only [finList, List.mem_filterMap, toFin]
  constructor
  · rintro ⟨a, ha, h⟩
    split at h
    · cases h; exact ha
    · cases h
  · intro h
    exact ⟨x.val, h, by simp [x.isLt]⟩

def edgesOf (c : CellF) : Kind → List Edge
  | .supersedes => c.sup
  | .retires => c.ret
  | .invalidates => c.inv

def schemaOf (c : CellF) : Schema :=
  if c.isAcc then .acceptance else if c.isVerdict then .verdict else .other

def world : World (Fin F.n) Unit Unit where
  info v :=
    let c := F.cell v.val
    { schema := schemaOf c, isLocal := c.isLocal, origin := c.origin, slotName := 0,
      relies := finList F c.relies, attests := [],
      supersedes := finList F (c.sup.map (·.dst)), retires := finList F (c.ret.map (·.dst)),
      invalidates := finList F (c.inv.map (·.dst)), refs := finList F c.refs,
      payload := c.payload.bind (toFin F), ownerPol := false, customPol := none,
      verdictInvalid := c.verdictInvalid, pol0 := (), pol1 := () }
  member _ _ := false
  quorum _ _ := false

/-- The fold's authorization of edge `w → v`, as the kernel reported it. -/
def ae (w v : Fin F.n) (k : Kind) : Bool := authIn (edgesOf (F.cell w.val) k) v.val

theorem authIn_mem {l : List Edge} {v : Nat} (h : authIn l v = true) : v ∈ l.map (·.dst) := by
  simp only [authIn, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨e, he, hd, _⟩ := h
  exact List.mem_map.2 ⟨e, he, hd⟩

theorem authIn_lt {l : List Edge} {v w : Nat} (hl : ∀ e ∈ l, e.dst < w) (h : authIn l v = true) :
    v < w := by
  obtain ⟨e, he, hd⟩ := List.mem_map.1 (authIn_mem h)
  exact hd ▸ hl e he

/-! ## Pass 1 equals the model -/

section Pass1Model
variable {F}
variable (hT : F.Topo) (hX : F.Excl)

/-- The Pass 1 predicates read off the executable lens. -/
def Inv (v : Fin F.n) : Prop := (Q F v.val).inv = true
def Eff (v : Fin F.n) : Prop := (Q F v.val).inv = false
def Ret (v : Fin F.n) : Prop := (Q F v.val).ret = true
def Acc (v : Fin F.n) : Prop := (Q F v.val).acc = true
def Auth (v : Fin F.n) : Bool := (F.cell v.val).authorized

include hT in
theorem sup_iff (v : Fin F.n) :
    (Q F v.val).sup = true ↔ Superseded (world F) (ae F) Eff Acc v := by
  constructor
  · -- newest first: induction on the distance to the end
    suffices H : ∀ d (v : Fin F.n), F.n - v.val ≤ d → (Q F v.val).sup = true →
        Superseded (world F) (ae F) Eff Acc v from H _ v (Nat.le_refl _)
    intro d
    induction d with
    | zero => intro v hd; have := v.isLt; omega
    | succ d ih =>
      intro v hd hs
      obtain ⟨w, ⟨hwn, hvw⟩, hauth, hlive⟩ := (sup_raw F v.isLt).1 hs
      have hmem : v ∈ ((world F).info ⟨w, hwn⟩).supersedes :=
        (mem_finList F).2 (authIn_mem hauth)
      rcases hlive with ⟨he, ha⟩ | hsw
      · exact Superseded.direct hmem hauth he ha
      · exact Superseded.trans hmem hauth (ih ⟨w, hwn⟩ (by simp; omega) hsw)
  · intro h
    induction h with
    | @direct w v hmem hae he ha =>
      exact (sup_raw F v.isLt).2 ⟨w.val, ⟨w.isLt, authIn_lt (hT.sup _) hae⟩, hae, Or.inl ⟨he, ha⟩⟩
    | @trans w v hmem hae _ ih =>
      exact (sup_raw F v.isLt).2 ⟨w.val, ⟨w.isLt, authIn_lt (hT.sup _) hae⟩, hae, Or.inr ih⟩

include hT in
theorem act_iff (v : Fin F.n) :
    (Q F v.val).act = true ↔ Active (world F) (ae F) Eff Acc Ret v := by
  rw [act_raw F v.isLt]
  have hsup := sup_iff hT v
  constructor
  · rintro ⟨hi, hr, hs, ha, hall⟩
    refine ⟨hi, by simp [Ret, hr], fun h => by simp [(sup_iff hT v).2 h] at hs, ha, ?_⟩
    intro u hu
    have := (mem_finList F).1 hu
    obtain ⟨e, he, hd⟩ := List.mem_map.1 this
    have := hall e he
    simp only [ae, edgesOf]
    rw [← hd]; exact this
  · rintro ⟨hi, hr, hs, ha, hall⟩
    refine ⟨hi, by simpa [Ret] using hr, ?_, ha, ?_⟩
    · cases h : (Q F v.val).sup
      · rfl
      · exact absurd ((sup_iff hT v).1 h) hs
    · intro e he
      have hlt : e.dst < F.n := Nat.lt_trans (hT.sup _ e he) v.isLt
      have := hall ⟨e.dst, hlt⟩ ((mem_finList F).2 (List.mem_map.2 ⟨e, he, rfl⟩))
      simpa [ae, edgesOf] using this

include hT in
theorem reach_iff (x : Fin F.n) :
    (Q F x.val).reach = true ↔
      AccReach (world F) Auth (Active (world F) (ae F) Eff Acc Ret) x := by
  constructor
  · suffices H : ∀ d (x : Fin F.n), F.n - x.val ≤ d → (Q F x.val).reach = true →
        AccReach (world F) Auth (Active (world F) (ae F) Eff Acc Ret) x from H _ x (Nat.le_refl _)
    intro d
    induction d with
    | zero => intro x hd; have := x.isLt; omega
    | succ d ih =>
      intro x hd hr
      rcases (reach_raw F x.isLt).1 hr with ⟨a, ⟨han, hxa⟩, hacc, hloc, hact, hauth, hpay⟩ |
          ⟨y, ⟨hyn, hxy⟩, hry, hmem, hor⟩
      · refine AccReach.pin (a := ⟨a, han⟩) ?_ (by simpa [world] using hloc)
          ((act_iff hT ⟨a, han⟩).1 hact) (by simpa [Auth] using hauth) ?_
        · simp [world, schemaOf, hacc]
        · simp [world, hpay, toFin, x.isLt]
      · exact AccReach.down (ih ⟨y, hyn⟩ (by simp; omega) hry) ((mem_finList F).2 hmem) hor
  · intro h
    induction h with
    | @pin a x hs hl hact hauth hpay =>
      have hacc : (F.cell a.val).isAcc = true := by
        simp only [world, schemaOf] at hs
        split at hs
        · assumption
        · split at hs <;> cases hs
      have hp : (F.cell a.val).payload = some x.val := by
        simp only [world] at hpay
        cases hc : (F.cell a.val).payload with
        | none => simp [hc] at hpay
        | some p =>
          simp only [hc, Option.bind_some, toFin] at hpay
          split at hpay
          · cases hpay; rfl
          · cases hpay
      exact (reach_raw F x.isLt).2 (Or.inl ⟨a.val, ⟨a.isLt, hT.payload _ _ hp⟩, hacc, hl,
        (act_iff hT a).2 hact, hauth, hp⟩)
    | @down y x _ hmem hor ih =>
      have hx := (mem_finList F).1 hmem
      exact (reach_raw F x.isLt).2 (Or.inr ⟨y.val, ⟨y.isLt, hT.refs _ _ hx⟩, ih, hx, hor⟩)

include hT hX in
/-- **The executable Pass 1 satisfies the model's Pass 1 equations**, and its `sup`/`act`
bits are the model's `Superseded`/`Active`. -/
theorem pass1_correct :
    IsPass1 (world F) (ae F) (fun _ => True) (fun _ => False) Auth Inv Eff Ret Acc ∧
    (∀ v, (geta (pass1 F) v.val).sup = true ↔ Superseded (world F) (ae F) Eff Acc v) ∧
    (∀ v, (geta (pass1 F) v.val).act = true ↔ Active (world F) (ae F) Eff Acc Ret v) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun v => ?_, fun v => ?_⟩
  · intro v
    rw [Inv, inv_raw F v.isLt]
    constructor
    · rintro ⟨w, ⟨hwn, _⟩, ⟨he, ha⟩, hauth, hver⟩
      refine ⟨⟨w, hwn⟩, he, ha, (mem_finList F).2 (authIn_mem hauth), hauth, ?_⟩
      rcases hver with hv | hv
      · left; simp only [world, schemaOf]; split <;> simp_all
      · right; exact hv
    · rintro ⟨w, he, ha, _, hauth, hver⟩
      refine ⟨w.val, ⟨w.isLt, authIn_lt (hT.inv _) hauth⟩, ⟨he, ha⟩, hauth, ?_⟩
      rcases hver with hv | hv
      · left
        simp only [world, schemaOf] at hv
        by_cases hacc : (F.cell w.val).isAcc = true
        · cases h : (F.cell w.val).isVerdict
          · rfl
          · exact absurd ⟨hacc, h⟩ (hX w.val)
        · simp [hacc] at hv
          cases h : (F.cell w.val).isVerdict
          · rfl
          · simp [h] at hv
      · right; exact hv
  · intro u; simp [Eff, Inv]
  · intro v
    rw [Ret, ret_raw F v.isLt]
    constructor
    · rintro ⟨w, ⟨hwn, _⟩, ⟨he, ha⟩, hauth⟩
      exact ⟨⟨w, hwn⟩, he, ha, (mem_finList F).2 (authIn_mem hauth), hauth⟩
    · rintro ⟨w, he, ha, _, hauth⟩
      exact ⟨w.val, ⟨w.isLt, authIn_lt (hT.ret _) hauth⟩, ⟨he, ha⟩, hauth⟩
  · intro x
    rw [Acc, acc_raw F x.isLt, reach_iff hT x]
    simp [world]
  · rw [pass1_get F v.isLt]; exact sup_iff hT v
  · rw [pass1_get F v.isLt]; exact act_iff hT v

end Pass1Model

/-! ## Pass 2 equals the model -/

/-- The model's Pass 2 inputs, read off the facts and the executable Pass 1. -/
def inst2 : Pass2In F.n where
  active v := (Q F v.val).act = true
  authorized v := (F.cell v.val).authorized = true
  isLocal v := (F.cell v.val).isLocal = true
  isAcceptance v := (F.cell v.val).isAcc = true
  payload v := (F.cell v.val).payload.bind (toFin F)
  origin v := (F.cell v.val).origin
  relies v := finList F (F.cell v.val).relies
  refs v := finList F (F.cell v.val).refs

/-- The live-acceptance fill for round-start stale set `S`. -/
def Lq (S : Array Bool) : Nat → Bool := fill (stepLive F (pass1 F) S) F.n fun _ => false

theorem stepLive_dep (P : Array S1) (S : Array Bool) :
    ∀ (g h : Nat → Bool) x, (∀ w, x < w → g w = h w) → stepLive F P S g x = stepLive F P S h x := by
  intro g h x H
  have e : (fun w => if x < w then g w else false) = (fun w => if x < w then h w else false) := by
    funext w
    by_cases hw : x < w
    · simp [hw, H w hw]
    · simp [hw]
  unfold stepLive
  rw [e]

theorem Lq_eq (S : Array Bool) {x : Nat} (hx : x < F.n) : Lq F S x = stepLive F (pass1 F) S (Lq F S) x :=
  fill_fix _ (stepLive_dep F _ S) F.n _ x hx

theorem live_get (S : Array Bool) {x : Nat} (hx : x < F.n) : geta (live F (pass1 F) S) x = Lq F S x := by
  simp [live, Lq, geta_tab _ _ hx]

theorem live_raw (S : Array Bool) {x : Nat} (hx : x < F.n) :
    Lq F S x = true ↔
      (∃ a, (a < F.n ∧ x < a) ∧ (F.cell a).isAcc = true ∧ (F.cell a).isLocal = true ∧
        (Q F a).act = true ∧ (F.cell a).authorized = true ∧ geta S a = false ∧
        (F.cell a).payload = some x) ∨
      (∃ y, (y < F.n ∧ x < y) ∧ Lq F S y = true ∧ x ∈ (F.cell y).refs ∧
        (F.cell y).origin = (F.cell x).origin) := by
  rw [Lq_eq F S hx]
  simp only [stepLive, List.any_eq_true, mem_above, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    List.contains_iff_mem, Bool.not_eq_true']
  refine or_congr (exists_congr fun a => and_congr_right fun ha => ?_)
    (exists_congr fun y => and_congr_right fun hy => ?_)
  · simp [pass1_get F ha.1, and_assoc]
  · simp [hy.2, and_assoc]

section Pass2Model
variable {F}
variable (hT : F.Topo)

include hT in
theorem live_iff (S : Array Bool) (x : Fin F.n) :
    Lq F S x.val = true ↔ LiveAcc (inst2 F) (fun a => geta S a.val = true) x := by
  constructor
  · suffices H : ∀ d (x : Fin F.n), F.n - x.val ≤ d → Lq F S x.val = true →
        LiveAcc (inst2 F) (fun a => geta S a.val = true) x from H _ x (Nat.le_refl _)
    intro d
    induction d with
    | zero => intro x hd; have := x.isLt; omega
    | succ d ih =>
      intro x hd hl
      rcases (live_raw F S x.isLt).1 hl with ⟨a, ⟨han, hxa⟩, hacc, hloc, hact, hauth, hS, hpay⟩ |
          ⟨y, ⟨hyn, hxy⟩, hly, hmem, hor⟩
      · refine LiveAcc.pin (a := ⟨a, han⟩) hacc hloc hact hauth (by simp [hS]) ?_
        simp [inst2, hpay, toFin, x.isLt]
      · exact LiveAcc.down (ih ⟨y, hyn⟩ (by simp; omega) hly) ((mem_finList F).2 hmem) hor
  · intro h
    induction h with
    | @pin a x hacc hloc hact hauth hS hpay =>
      have hp : (F.cell a.val).payload = some x.val := by
        simp only [inst2] at hpay
        cases hc : (F.cell a.val).payload with
        | none => simp [hc] at hpay
        | some p =>
          simp only [hc, Option.bind_some, toFin] at hpay
          split at hpay
          · cases hpay; rfl
          · cases hpay
      refine (live_raw F S x.isLt).2 (Or.inl ⟨a.val, ⟨a.isLt, hT.payload _ _ hp⟩, hacc, hloc, hact,
        hauth, ?_, hp⟩)
      simpa using hS
    | @down y x _ hmem hor ih =>
      have hx := (mem_finList F).1 hmem
      exact (live_raw F S x.isLt).2 (Or.inr ⟨y.val, ⟨y.isLt, hT.refs _ _ hx⟩, ih, hx, hor⟩)

include hT in
theorem psi_iff (S : Array Bool) (D : Nat → Bool) (Dm : Fin F.n → Prop)
    (hD : ∀ d : Fin F.n, D d.val = true ↔ Dm d) (v : Fin F.n) :
    psi F (pass1 F) (live F (pass1 F) S) D v.val = true ↔
      Ψ (inst2 F) (fun a => geta S a.val = true) Dm v := by
  simp only [psi, Ψ, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true,
    pass1_get F v.isLt, live_get F S v.isLt]
  refine and_congr Iff.rfl (or_congr ?_ (and_congr ?_ ?_))
  · constructor
    · rintro ⟨d, hd, h⟩
      have hdn : d < F.n := Nat.lt_trans (hT.relies _ _ hd) v.isLt
      refine ⟨⟨d, hdn⟩, (mem_finList F).2 hd, ?_⟩
      rw [pass1_get F hdn] at h
      rcases h with h | h
      · left; simp [inst2, h]
      · right; exact (hD ⟨d, hdn⟩).1 h
    · rintro ⟨d, hd, h⟩
      have hd' := (mem_finList F).1 hd
      refine ⟨d.val, hd', ?_⟩
      rw [pass1_get F d.isLt]
      rcases h with h | h
      · left; simpa [inst2] using h
      · right; exact (hD d).2 h
  · simp [inst2]
  · rw [← live_iff hT S v]
    simp

include hT in
theorem sweep_corr (S : Array Bool) :
    ∀ k (v : Fin F.n), fillUp (psi F (pass1 F) (live F (pass1 F) S)) k (geta S) v.val = true ↔
      sweep (inst2 F) (fun a => geta S a.val = true) k v
  | 0, v => Iff.rfl
  | k + 1, v => by
    rw [fillUp_succ]
    show _ ↔ (if v.val = k then _ else _)
    by_cases hk : v.val = k
    · rw [if_pos hk]
      have h := psi_iff hT S _ _ (sweep_corr S k) v
      rw [hk] at h
      rw [hk, upd_same]
      exact h
    · rw [if_neg hk, upd_other _ _ hk]
      exact sweep_corr S k v

include hT in
theorem round_corr (S : Array Bool) (v : Fin F.n) :
    geta (round F (pass1 F) S) v.val = true ↔ Vars1.round (inst2 F) (fun a => geta S a.val = true) v := by
  simp only [round, geta_tab _ _ v.isLt]
  exact sweep_corr hT S F.n v

include hT in
theorem repeat_corr :
    ∀ k, (fun v : Fin F.n => geta (Nat.repeat (round F (pass1 F)) k (tab F.n fun _ => false)) v.val = true) =
      iter (Vars1.round (inst2 F)) k
  | 0 => by
    funext v
    simp [Nat.repeat, iter, geta_tab _ _ v.isLt]
  | k + 1 => by
    funext v
    show (geta (round F (pass1 F) (Nat.repeat (round F (pass1 F)) k _)) v.val = true) =
      Vars1.round (inst2 F) (iter (Vars1.round (inst2 F)) k) v
    rw [← repeat_corr k]
    exact propext (round_corr hT _ v)

include hT in
/-- **The executable Pass 2 is the model's `Stale`**, the least fixed point of `Φ`. -/
theorem stale_correct (v : Fin F.n) : geta (stale F) v.val = true ↔ Stale (inst2 F) v := by
  have h := congrFun (repeat_corr hT F.n) v
  simp only [stale, staleOf] at h ⊢
  rw [h]
  exact (sweep_reaches_stale (inst2 F)).2.2 v

end Pass2Model

end Vars1.Exec
