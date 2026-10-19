import Vars1.Replay

/-!
# The unverified-parent attack, mechanized

A concrete world showing that the per-transition check alone (`replayOne`, which is
a per-transition check without lineage verification) is unsound, and that `verify` refuses the same
checkpoint. It is the counter-vector of `test_09` in miniature:

* states: `0` = the cold input `I` of the computation, `1` = a fabricated `K`,
  `2` = the true result; `0` fires to `2` at cost 1, `1` and `2` are normal forms;
* `p` (spent 5, state `1`) is over the ceiling `maxAtp = 1`, so `NOT_ASSESSED`;
* `c` relies on `p`, spent 5 (Δ = 0), state `1`, claims `H_NORMAL_FORM`.

`replayOne` accepts `c` (Δ = 0 from the fabricated state is trivially consistent),
`verify` returns `NOT_ASSESSED`, and the true run from `SR.start` by 5 ends at `2`
after spending 1, not at `1` after spending 5.
-/

namespace Vars1.Replay.Attack

def toyStep : Nat → Act Nat
  | 0 => .fire 2 1
  | _ => .nf

abbrev toy : Machine where
  S := Nat
  step := toyStep
  cost_pos := by
    intro s s' c h
    unfold toyStep at h
    split at h
    · cases h; omega
    · cases h

instance : DecidableEq toy.S := inferInstanceAs (DecidableEq Nat)

/-- `false` = the parent `p`, `true` = the child `c`. -/
def ck : Ckpts Bool Unit toy where
  isCkpt := fun _ => true
  comp := fun _ => ()
  spent := fun _ => 5
  state := fun _ => (1 : Nat)
  relies := fun b => if b then [false] else []
  claimsNF := fun _ => true
  start := fun _ => (0 : Nat)

/-- The honest host: it reports `adv`. -/
def host (s : toy.S) (b : Nat) : Option (toy.S × Nat) := some (adv toy s b)

theorem host_sound : HostSound host := fun _ _ _ h => by cases h; rfl

theorem adv_nf (s : Nat) (hs : s ≠ 0) (b : Nat) : adv toy s b = (s, 0) := by
  have h : toy.step s = .nf := by
    show toyStep s = .nf
    unfold toyStep; split
    · contradiction
    · rfl
  rw [adv_eq, h]

theorem adv_start : adv toy (0 : Nat) 5 = ((2 : Nat), 1) := by
  have h : toy.step (0 : Nat) = .fire (2 : Nat) 1 := rfl
  rw [adv_eq, h]; simp only
  rw [adv_nf 2 (by decide)]; decide

theorem parent_true : parent ck true = some false := rfl
theorem parent_false : parent ck false = none := rfl

/-- The per-transition check accepts the child of a fabricated parent. -/
theorem replayOne_accepts : replayOne ck 1 host true = .replayed := by
  unfold replayOne base
  rw [parent_true]
  show (if 5 < 5 then Status.refused else if 1 < 5 - 5 then Status.notAssessed else
    match host (1 : Nat) (5 - 5) with
    | none => .notAssessed
    | some r => if r.1 = (1 : Nat) ∧ r.2 = 5 - 5 ∧ (true = true → (toy.step r.1).isNF = true)
        then .replayed else .refused) = .replayed
  simp only [host, adv_nf 1 (by decide)]
  decide

/-- The lineage verifier does not. -/
theorem verify_refuses (f : Nat) : verify ck 1 host (f + 2) true = .notAssessed := by
  have hp : replayOne ck 1 host false = .notAssessed := by
    unfold replayOne base; rw [parent_false]; decide
  simp only [verify, parent_true, parent_false, hp]

/-- And the per-transition verdict is false: one advance from `SR.start` by
`spent_total(c) = 5` does not reach `state(c)`. -/
theorem replayOne_unsound :
    adv toy (ck.start (ck.comp true)) (ck.spent true) ≠ (ck.state true, ck.spent true) := by
  show adv toy (0 : Nat) 5 ≠ ((1 : Nat), 5)
  rw [adv_start]; intro h; have := congrArg Prod.snd h; simp at this

/-- Hence `verify_sound` fails for a verifier without lineage checks (`replayOne` alone). -/
theorem pre_lineage_unsound :
    ¬ ∀ c, replayOne ck 1 host c = .replayed →
      adv toy (ck.start (ck.comp c)) (ck.spent c) = (ck.state c, ck.spent c) :=
  fun h => replayOne_unsound (h true replayOne_accepts)

end Vars1.Replay.Attack
