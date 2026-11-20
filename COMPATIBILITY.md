# Non-Manipulative Compatibility & Sovereign Local Refusal (`Vars1.Compatibility`)

`proofs/Vars1/Compatibility.lean` and `compatibility.py` formally separate **Entity** (self / carrier),
**Claim** (idea), and **Context** (local conditions) under replayable **Witness**es:

- **Critique of Idea ≠ Critique of Self (`refusal_preserves_entity_standing`):** filing a witnessed
  local refusal of claim `x` in context `c` never lowers or revokes any entity's standing.
- **Sovereign Local Refusal without Forced Unification (`refusal_is_context_local`, `refusal_is_claim_local`):**
  proving *"this does not work in my conditions `c`"* refutes `(x, c)` without touching `x` in any
  distinct context `c' ≠ c`.
- **Witnessed Soundness (`admitted_refusal_records_and_falsifies`, `unwitnessed_refusal_inert`):**
  a refusal counts only with a reproducible counterexample proving `¬ holds x c`.
- **Non-Manipulative Compatibility (`captured_party_not_compatible`):**
  compatibility requires both no local refusal AND independent viability (`viableAlone a ∧ viableAlone b`,
  i.e. sovereign exit without destruction). Capture is strictly excluded from compatibility.
- **Order-Independence (`applyRefusal_idempotent`, `applyRefusal_comm`):**
  local refusals are idempotent and commutative, matching Warrant 3 union-merge semantics.
