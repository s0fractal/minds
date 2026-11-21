"""Non-manipulative compatibility & sovereign local refusal (`proofs/Vars1/Compatibility.lean`).

Executable Python counterpart of `Vars1.Compatibility`, enforcing three strict separations:
  1. **Entity ≠ Claim ≠ Context:** filing a witnessed local refusal of `(claim_id, context_id)`
     never lowers or revokes any entity's standing (`critique of idea != critique of self`).
  2. **Context-local falsifiability without forced unification:** refuting `claim_id` under
     `context_id` leaves `claim_id` untouched under every other `context_id' != context_id`.
  3. **Witnessed soundness + sovereign exit:** a refusal is admitted ONLY when an explicit
     replayable witness proves local failure (`UNWITNESSED_REFUSAL` otherwise); two parties are
     non-manipulatively compatible on `(claim_id, context_id)` iff both hold standing, both are
     independently viable (`viable_alone=True`, excluding capture), and `(claim_id, context_id)`
     has no admitted local refusal.
"""
import hashlib
import json
from typing import NamedTuple


def _require_str(v, code: str, name: str) -> str:
    if type(v) is not str or not v or v != v.strip():
        raise CompatibilityError(code, f"{name} must be a non-empty trimmed string")
    return v


def _freeze_and_tag(v, _depth: int = 0):
    """Validate a closed exact-type immutable value and return `(value, tagged_json)`."""
    if _depth > 32:
        raise CompatibilityError("UNSUPPORTED_VALUE", "value nesting exceeds maximum depth 32")
    t = type(v)
    if v is None:
        return None, ["null", None]
    if t is bool:
        return v, ["bool", v]
    if t is int:
        return v, ["int", v]
    if t is str:
        return v, ["str", v]
    if t is tuple:
        pairs = [_freeze_and_tag(x, _depth + 1) for x in v]
        return tuple(p[0] for p in pairs), ["tuple", [p[1] for p in pairs]]
    raise CompatibilityError("UNSUPPORTED_VALUE", f"unsupported or mutable value type: {t.__name__}")


class CompatibilityError(ValueError):
    """Raised on violation of non-manipulative compatibility invariants."""

    def __init__(self, code: str, detail: str):
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


class EntityRecord(NamedTuple):
    entity_id: str
    standing: bool
    viable_alone: bool


class LocalRefusal(NamedTuple):
    claim_id: str
    context_id: str
    challenger_id: str
    witness_digest: str
    witness_payload: object


class CompatVerdict(NamedTuple):
    compatible: bool
    reason: str
    entity_a: str
    entity_b: str
    claim_id: str
    context_id: str
    standing_a: bool
    standing_b: bool


class CompatibilityLedger:
    """Append-only, order-independent ledger of entities and witnessed context-local refusals."""

    def __init__(self, witness_fn):
        if not callable(witness_fn):
            raise CompatibilityError("BAD_WITNESS_FN", "witness_fn must be callable")
        self._witness_fn = witness_fn
        self._entities: dict[str, EntityRecord] = {}
        self._refusals: dict[tuple[str, str], LocalRefusal] = {}

    @property
    def entities(self) -> dict[str, EntityRecord]:
        return dict(self._entities)

    @property
    def refusals(self) -> dict[tuple[str, str], LocalRefusal]:
        return dict(self._refusals)

    def register_entity(self, entity_id: str, *, standing: bool = True, viable_alone: bool = True) -> EntityRecord:
        _require_str(entity_id, "BAD_ENTITY_ID", "entity_id")
        if type(standing) is not bool or type(viable_alone) is not bool:
            raise CompatibilityError("BAD_ENTITY_FLAGS", "standing and viable_alone must be bool")
        if entity_id in self._entities:
            raise CompatibilityError("DUPLICATE_ENTITY", f"entity {entity_id!r} already registered")
        rec = EntityRecord(entity_id=entity_id, standing=standing, viable_alone=viable_alone)
        self._entities[entity_id] = rec
        return rec

    def file_refusal(self, challenger_id: str, claim_id: str, context_id: str, *, witness_payload) -> LocalRefusal:
        """Admit a witnessed local refusal of `(claim_id, context_id)` without altering any entity's standing."""
        _require_str(challenger_id, "BAD_ENTITY_ID", "challenger_id")
        _require_str(claim_id, "BAD_CLAIM_ID", "claim_id")
        _require_str(context_id, "BAD_CONTEXT_ID", "context_id")
        if challenger_id not in self._entities:
            raise CompatibilityError("UNKNOWN_ENTITY", f"unknown challenger {challenger_id!r}")
        frozen_payload, tagged_payload = _freeze_and_tag(witness_payload)
        if not bool(self._witness_fn(claim_id, context_id, frozen_payload)):
            raise CompatibilityError(
                "UNWITNESSED_REFUSAL",
                f"witness failed to reproduce failure of {claim_id!r} in {context_id!r}",
            )
        raw_w = json.dumps(tagged_payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
        wdig = hashlib.sha256(raw_w).hexdigest()
        ref = LocalRefusal(
            claim_id=claim_id,
            context_id=context_id,
            challenger_id=challenger_id,
            witness_digest=wdig,
            witness_payload=frozen_payload,
        )
        key = (claim_id, context_id)
        existing = self._refusals.get(key)
        if existing is None or (wdig, challenger_id) < (existing.witness_digest, existing.challenger_id):
            self._refusals[key] = ref
        return self._refusals[key]

    def is_refuted(self, claim_id: str, context_id: str) -> bool:
        _require_str(claim_id, "BAD_CLAIM_ID", "claim_id")
        _require_str(context_id, "BAD_CONTEXT_ID", "context_id")
        return (claim_id, context_id) in self._refusals

    def check_compatibility(self, entity_a: str, entity_b: str, claim_id: str, context_id: str) -> CompatVerdict:
        """Evaluate non-manipulative compatibility of `(entity_a, entity_b)` on `(claim_id, context_id)`."""
        _require_str(entity_a, "BAD_ENTITY_ID", "entity_a")
        _require_str(entity_b, "BAD_ENTITY_ID", "entity_b")
        _require_str(claim_id, "BAD_CLAIM_ID", "claim_id")
        _require_str(context_id, "BAD_CONTEXT_ID", "context_id")
        if entity_a not in self._entities or entity_b not in self._entities:
            raise CompatibilityError("UNKNOWN_ENTITY", "both entities must be registered")
        ea = self._entities[entity_a]
        eb = self._entities[entity_b]
        if not (ea.standing and eb.standing):
            return CompatVerdict(False, "NO_STANDING", entity_a, entity_b, claim_id, context_id, ea.standing, eb.standing)
        if not (ea.viable_alone and eb.viable_alone):
            return CompatVerdict(False, "CAPTURED_PARTY", entity_a, entity_b, claim_id, context_id, ea.standing, eb.standing)
        if (claim_id, context_id) in self._refusals:
            return CompatVerdict(False, "LOCALLY_REFUTED", entity_a, entity_b, claim_id, context_id, ea.standing, eb.standing)
        return CompatVerdict(True, "COMPATIBLE", entity_a, entity_b, claim_id, context_id, ea.standing, eb.standing)


def compatibility_certificate(ledger: CompatibilityLedger, entity_a: str, entity_b: str, claim_id: str, context_id: str) -> dict:
    """Emit a deterministic, content-addressed SHA-256 `vars1-compatibility@1` certificate."""
    v = ledger.check_compatibility(entity_a, entity_b, claim_id, context_id)
    ref = ledger.refusals.get((claim_id, context_id))
    body = {
        "schema": "vars1-compatibility@1",
        "entity_a": v.entity_a,
        "entity_b": v.entity_b,
        "claim_id": v.claim_id,
        "context_id": v.context_id,
        "compatible": v.compatible,
        "reason": v.reason,
        "standing_a": v.standing_a,
        "standing_b": v.standing_b,
        "refusal_witness_digest": ref.witness_digest if ref is not None else None,
    }
    raw = json.dumps(body, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return {"digest": hashlib.sha256(raw).hexdigest(), "certificate": body}
