import Vars1.Model

/-!
# The cryptographic assumptions, as hypotheses

Nothing here is a Lean `axiom`. Each assumption is a hypothesis that the
theorems using it take as an argument.

* **SHA-256 injectivity on admitted bytes** (`ShaInjective`). The model treats a
  cell identifier as determining the cell's content (`World.info : C → CellInfo`).
  `info_exists` shows that hypothesis is exactly what makes such a function exist
  and agree with decoding on every admitted byte string.
* **Signature unforgeability** (`Unforgeable`): every valid seal in a commit was
  signed by the holder of its key, over its `(H_target, H_scope_ctx)`. Used by
  `endorser_signed` in `Vars1/Fold.lean`.
-/

namespace Vars1

/-- SHA-256 is injective on the admitted cell byte strings. -/
def ShaInjective {B C : Type} (admitted : B → Prop) (sha : B → C) : Prop :=
  ∀ b₁ b₂, admitted b₁ → admitted b₂ → sha b₁ = sha b₂ → b₁ = b₂

/-- Under `ShaInjective`, the content of an admitted cell is a function of its
identifier: there is `info : C → CellInfo` with `info (sha b) = decode b` for every
admitted `b`. (`dflt` fills identifiers that name no admitted cell.) -/
theorem info_exists {B C P : Type} (admitted : B → Prop) (sha : B → C)
    (decode : B → CellInfo C P) (dflt : CellInfo C P) (h : ShaInjective admitted sha) :
    ∃ info : C → CellInfo C P, ∀ b, admitted b → info (sha b) = decode b := by
  classical
  refine ⟨fun c => if hc : ∃ b, admitted b ∧ sha b = c then decode (Classical.choose hc)
    else dflt, ?_⟩
  intro b hb
  have hc : ∃ b', admitted b' ∧ sha b' = sha b := ⟨b, hb, rfl⟩
  simp only [dif_pos hc]
  have hs := Classical.choose_spec hc
  rw [h _ _ hs.1 hb hs.2]

/-- Without injectivity no such `info` need exist: two admitted byte strings
with one hash and different decodings. -/
theorem info_needs_injective {B C P : Type} (admitted : B → Prop) (sha : B → C)
    (decode : B → CellInfo C P) (b₁ b₂ : B) (h₁ : admitted b₁) (h₂ : admitted b₂)
    (hs : sha b₁ = sha b₂) (hd : decode b₁ ≠ decode b₂) :
    ¬ ∃ info : C → CellInfo C P, ∀ b, admitted b → info (sha b) = decode b := by
  intro ⟨info, hi⟩
  exact hd ((hi b₁ h₁).symm.trans (hs ▸ hi b₂ h₂))

/-- Every valid seal of a commit was signed by its key holder. -/
def Unforgeable {C K : Type} (Signed : K → C → C → Prop) (cm : Commit C K) : Prop :=
  ∀ s ∈ cm.seals, Signed s.key s.target s.ctx

end Vars1
