/-!
# A frame read from below (`experiments/witness/delta.py`)

`frame.py` builds, for one decision `d`, the cells its status reads: `d`'s judges and named checkpoints (one step),
what those rely on (any number of steps), then the cells that enter that set by an edge or that a member supersedes
(any number of steps): its guard. For Grounded, first every evaluated cell that `d`'s read reaches, and theirs, to the
fixed point. `touches` asks whether a later commit's objects land in one of those sets.

`delta.py` asks the other way: from the cells a commit touches, walk up the inverse of each step, in the reverse
order, and collect the decisions reached. These theorems say the walk is exact, for a frame given by its steps as
relations: a cell is reached from a touch point iff the touch point is in its frame. So the decisions the walk does
not reach are exactly those whose frame the commit leaves untouched (`unreached_frame_untouched`), and for them
`settled_frame` and `grounded_frame` (`Reader.lean`) keep the status, given that an untouched frame meets `Reads`.

That last link, from `touches` to `Reads`, is Python held by tests (`test_witness.py` 17–19), not proved: see
`proofs/README.md`, "Not linked". Test 25 holds `delta.dirty` to `touches` on every pair of tips.

* `rtc_flip` — any number of steps of the inverse relation is any number of steps of the relation, reversed.
* `up_settled_iff` — the guard of a Settled frame (`Opt J`, then `Rel*`, then `B*`), read from below.
* `up_grounded_iff` — the same for Grounded, whose frame first closes over the evaluated cells read (`E*`).
* `unreached_frame_untouched` — so the decisions the walk does not reach have no touch point in their frame.
-/

namespace Vars1

section Delta

variable {C : Type}

/-- Any number of steps of `R`. -/
inductive RTC (R : C → C → Prop) : C → C → Prop where
  | refl (a : C) : RTC R a a
  | tail {a b c : C} : RTC R a b → R b c → RTC R a c

theorem RTC.head {R : C → C → Prop} {a b c : C} (h : R a b) (hbc : RTC R b c) : RTC R a c := by
  induction hbc with
  | refl => exact .tail (.refl a) h
  | tail _ hcd ih => exact .tail ih hcd

/-- **Steps of the inverse, reversed.** -/
theorem rtc_flip {R : C → C → Prop} {a b : C} : RTC (fun x y => R y x) a b ↔ RTC R b a := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl _
    | tail _ hbc ih => exact RTC.head hbc ih
  · intro h
    induction h with
    | refl => exact .refl _
    | tail _ hbc ih => exact RTC.head hbc ih

/-- At most one step: the root itself, or one `J`-step from it (a judge, or a named checkpoint). -/
def Opt (J : C → C → Prop) (a b : C) : Prop := b = a ∨ J a b

/-- The guard of `d`'s Settled frame holds `y`: from `d`, a judge or a named checkpoint (or `d`), what it relies on,
then what enters by an edge or is superseded. -/
def InSettled (J Rel B : C → C → Prop) (d y : C) : Prop :=
  ∃ a b, Opt J d a ∧ RTC Rel a b ∧ RTC B b y

/-- The walk from below: from `y`, the inverse of `B`, then of `Rel`, then of `J`, to `d`. -/
def UpSettled (J Rel B : C → C → Prop) (y d : C) : Prop :=
  ∃ b a, RTC (fun x z => B z x) y b ∧ RTC (fun x z => Rel z x) b a ∧ Opt (fun x z => J z x) a d

/-- **The walk from below reaches `d` from `y` iff `y` is in `d`'s Settled frame.** -/
theorem up_settled_iff {J Rel B : C → C → Prop} {y d : C} : UpSettled J Rel B y d ↔ InSettled J Rel B d y := by
  constructor
  · rintro ⟨b, a, hb, ha, ho⟩
    refine ⟨a, b, ?_, rtc_flip.mp ha, rtc_flip.mp hb⟩
    rcases ho with h | h
    · exact Or.inl h.symm
    · exact Or.inr h
  · rintro ⟨a, b, ho, ha, hb⟩
    refine ⟨b, a, rtc_flip.mpr hb, rtc_flip.mpr ha, ?_⟩
    rcases ho with h | h
    · exact Or.inl h.symm
    · exact Or.inr h

/-- The guard of `d`'s Grounded frame holds `y`: an evaluated cell `v` that `d`'s frame evaluates (`E*`: `v` is read
by one that is), and `y` in `v`'s Settled frame. -/
def InGrounded (E J Rel B : C → C → Prop) (d y : C) : Prop :=
  ∃ v, RTC E d v ∧ InSettled J Rel B v y

/-- The walk from below for Grounded: up to the evaluated cells whose Settled frame holds `y`, then up `E`. -/
def UpGrounded (E J Rel B : C → C → Prop) (y d : C) : Prop :=
  ∃ v, UpSettled J Rel B y v ∧ RTC (fun x z => E z x) v d

/-- **The same for Grounded.** -/
theorem up_grounded_iff {E J Rel B : C → C → Prop} {y d : C} :
    UpGrounded E J Rel B y d ↔ InGrounded E J Rel B d y := by
  constructor
  · rintro ⟨v, hs, he⟩
    exact ⟨v, rtc_flip.mp he, up_settled_iff.mp hs⟩
  · rintro ⟨v, he, hs⟩
    exact ⟨v, up_settled_iff.mpr hs, rtc_flip.mpr he⟩

/-- **What the walk does not reach is untouched.** If no touch point of a commit reaches `d` from below, no touch point
lies in `d`'s frame; and, the walk being exact, every `d` it reaches has one there. -/
theorem unreached_frame_untouched {E J Rel B : C → C → Prop} (P : List C) {d : C} :
    (∀ y ∈ P, ¬ UpGrounded E J Rel B y d) ↔ (∀ y ∈ P, ¬ InGrounded E J Rel B d y) :=
  ⟨fun h y hy hin => h y hy (up_grounded_iff.mpr hin), fun h y hy hup => h y hy (up_grounded_iff.mp hup)⟩

end Delta

end Vars1
