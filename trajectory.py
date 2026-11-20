"""Inductive trajectory safety (`D22`) & horizon-bounded semantic mass (`D26`, `proofs/Vars1/Trajectory.lean`).

Executable Python counterpart of `Vars1.Trajectory`, providing:
  1. `SafeTrajectory` (`D22 / F3`): enforces the 3-part trajectory safety law fail-closed
     (base invariant `inv(x0)`, safe action guard `safe_act(x, a)`, and post-step invariant
     preservation `inv(x')` under adversarial environment moves).
  2. `SemanticMassLedger` (`D26 / F7`): computes horizon-bounded semantic mass `M_{sem,H}` with
     exact integer arithmetic, anti-Sybil non-inflation (`retold`/`forked` acts contribute 0 mass,
     replaying an existing `act_id` is idempotent, conflicting `act_id`s fail closed), and
     error-driven revision (`refute()` strictly lowers or preserves mass).
  3. `trajectory_mass_certificate`: emits a deterministic, content-addressed SHA-256
     `vars1-trajectory-mass@1` certificate verifiable offline by `warrant.witness`.
"""
import hashlib
import json
from typing import NamedTuple

VALID_ORIGINS = frozenset(("verified", "retold", "forked"))


def _is_int(v) -> bool:
    return type(v) is int


def _require_non_empty_str(v, code: str, name: str) -> str:
    if type(v) is not str or not v or v != v.strip():
        raise TrajectoryError(code, f"{name} must be a non-empty trimmed string")
    return v


class TrajectoryError(ValueError):
    """Raised on violation of D22 trajectory safety or D26 semantic mass invariants."""

    def __init__(self, code: str, detail: str):
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


class TrajectoryStep(NamedTuple):
    step_idx: int
    prev_state: object
    action: object
    env_move: object
    next_state: object


class SemanticAct(NamedTuple):
    act_id: str
    step_idx: int
    weight: int
    origin: str  # "verified" | "retold" | "forked"
    refuted: bool


class SafeTrajectory:
    """Append-only trajectory enforcing the 3-part inductive safety law (`D22 / F3`)."""

    def __init__(self, initial_state, *, inv_fn, safe_act_fn, step_fn):
        if not bool(inv_fn(initial_state)):
            raise TrajectoryError("BASE_INVARIANT_VIOLATED", f"initial state {initial_state!r} fails inv_fn")
        self._inv_fn = inv_fn
        self._safe_act_fn = safe_act_fn
        self._step_fn = step_fn
        self._initial = initial_state
        self._current = initial_state
        self._steps: list[TrajectoryStep] = []

    @property
    def initial_state(self):
        return self._initial

    @property
    def current_state(self):
        return self._current

    @property
    def steps(self) -> tuple[TrajectoryStep, ...]:
        return tuple(self._steps)

    def advance(self, action, env_move) -> TrajectoryStep:
        """Advance one step under `(action, env_move)`, failing closed on guard or invariant violation."""
        if not bool(self._safe_act_fn(self._current, action)):
            raise TrajectoryError(
                "UNSAFE_ACTION",
                f"action {action!r} refused by safe_act_fn at state {self._current!r}",
            )
        next_state = self._step_fn(self._current, action, env_move)
        if not bool(self._inv_fn(next_state)):
            raise TrajectoryError(
                "STEP_INVARIANT_VIOLATED",
                f"transition ({self._current!r}, {action!r}, {env_move!r}) -> {next_state!r} violates inv_fn",
            )
        step = TrajectoryStep(
            step_idx=len(self._steps),
            prev_state=self._current,
            action=action,
            env_move=env_move,
            next_state=next_state,
        )
        self._steps.append(step)
        self._current = next_state
        return step

    def is_safe(self) -> bool:
        """Independently re-verify base invariant, every guarded transition, and every reached state."""
        if not bool(self._inv_fn(self._initial)):
            return False
        cur = self._initial
        for st in self._steps:
            if st.prev_state != cur:
                return False
            if not bool(self._safe_act_fn(cur, st.action)):
                return False
            if not bool(self._inv_fn(st.next_state)):
                return False
            cur = st.next_state
        return cur == self._current


class SemanticMassLedger:
    """Horizon-bounded, anti-Sybil semantic mass ledger with error-driven revision (`D26 / F7`)."""

    def __init__(self):
        self._acts: dict[str, SemanticAct] = {}
        self._refutation_reasons: dict[str, str] = {}

    @property
    def acts(self) -> tuple[SemanticAct, ...]:
        return tuple(self._acts[k] for k in sorted(self._acts))

    def record(self, act_id: str, *, step_idx: int, weight: int, origin: str = "verified", refuted: bool = False) -> SemanticAct:
        """Record a semantic act; identical replay is idempotent (0 extra mass), conflicting replay is refused."""
        _require_non_empty_str(act_id, "BAD_ACT_ID", "act_id")
        if not (_is_int(step_idx) and step_idx >= 0):
            raise TrajectoryError("BAD_STEP_IDX", "step_idx must be a non-negative integer")
        if not (_is_int(weight) and weight >= 0):
            raise TrajectoryError("BAD_WEIGHT", "weight must be a non-negative integer")
        if type(origin) is not str or origin not in VALID_ORIGINS:
            raise TrajectoryError("BAD_ORIGIN", f"origin must be one of {sorted(VALID_ORIGINS)}")
        if type(refuted) is not bool:
            raise TrajectoryError("BAD_REFUTED", "refuted must be a bool")

        if act_id in self._acts:
            existing = self._acts[act_id]
            if (existing.step_idx, existing.weight, existing.origin) != (step_idx, weight, origin):
                raise TrajectoryError(
                    "CONFLICTING_ACT_ID",
                    f"act_id {act_id!r} already recorded with different metadata",
                )
            if refuted and not existing.refuted:
                updated = SemanticAct(act_id, step_idx, weight, origin, True)
                self._acts[act_id] = updated
                return updated
            return existing

        act = SemanticAct(act_id=act_id, step_idx=step_idx, weight=weight, origin=origin, refuted=refuted)
        self._acts[act_id] = act
        return act

    def refute(self, act_id: str, *, reason: str = "counterexample") -> SemanticAct:
        """Refute an existing act via a counterexample (strictly non-inflationary revision)."""
        _require_non_empty_str(act_id, "BAD_ACT_ID", "act_id")
        _require_non_empty_str(reason, "BAD_REASON", "reason")
        if act_id not in self._acts:
            raise TrajectoryError("UNKNOWN_ACT_ID", f"unknown act_id {act_id!r}")
        cur = self._acts[act_id]
        updated = SemanticAct(cur.act_id, cur.step_idx, cur.weight, cur.origin, True)
        self._acts[act_id] = updated
        self._refutation_reasons[act_id] = reason
        return updated

    def mass(self, horizon: int) -> int:
        """Compute exact integer semantic mass `M_{sem,H}` at finite horizon `H`."""
        if not (_is_int(horizon) and horizon >= 0):
            raise TrajectoryError("BAD_HORIZON", "horizon must be a non-negative integer")
        total = 0
        for act in self._acts.values():
            if act.origin == "verified" and not act.refuted and act.step_idx <= horizon:
                total += act.weight
        return total

    def total_weight(self) -> int:
        """Finite convergence upper bound across all horizons (`sum(weight)` over unique acts)."""
        return sum(act.weight for act in self._acts.values())


def trajectory_mass_certificate(
    trajectory: SafeTrajectory,
    ledger: SemanticMassLedger,
    *,
    horizon: int,
    label: str = "unnamed",
) -> dict:
    """Emit a deterministic, content-addressed SHA-256 `vars1-trajectory-mass@1` certificate."""
    _require_non_empty_str(label, "BAD_LABEL", "label")
    if not (_is_int(horizon) and horizon >= 0):
        raise TrajectoryError("BAD_HORIZON", "horizon must be a non-negative integer")
    safe = trajectory.is_safe()
    verified_acts = []
    non_counting = []
    refuted_ids = []
    for act in ledger.acts:
        if act.refuted:
            refuted_ids.append(act.act_id)
        if act.origin == "verified" and not act.refuted and act.step_idx <= horizon:
            verified_acts.append({"act_id": act.act_id, "step_idx": act.step_idx, "weight": act.weight})
        else:
            non_counting.append({
                "act_id": act.act_id,
                "origin": act.origin,
                "refuted": act.refuted,
                "step_idx": act.step_idx,
                "weight": act.weight,
            })
    vmass = ledger.mass(horizon)
    body = {
        "schema": "vars1-trajectory-mass@1",
        "label": label,
        "trajectory_safe": safe,
        "step_count": len(trajectory.steps),
        "horizon": horizon,
        "verified_mass": vmass,
        "total_weight": ledger.total_weight(),
        "verified_acts": verified_acts,
        "refuted_ids": sorted(refuted_ids),
        "non_counting_acts": non_counting,
    }
    raw = json.dumps(body, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return {"digest": hashlib.sha256(raw).hexdigest(), "certificate": body}
