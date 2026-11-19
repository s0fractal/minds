#!/usr/bin/env python3
"""Metered Portable Agent Spores for minds / VARS-1 (AGENT-SPORE-DIRECTION.md, AS-1..AS-8).

A spore is an addressed, pure, metered unit of computation that unfolds its dependencies on demand within
an explicit resource budget, stops cleanly with a portable checkpoint when out of budget or missing an
object, can be handed over to another agent and resumed without losing progress, never inflates verification
by retelling, and revises dependent conclusions when a counterexample arrives.

Core invariants formalized in Lean 4 (`proofs/Vars1/Spore.lean`, propext + Quot.sound only):
  - AS-1 Unfold on demand: only needed content-addressed atoms are fetched; missing unneeded branches never block.
  - AS-2 Budget conservation & bounded recursion: child spore budgets partition (subtract from) parent budgets
    (`tree_conserves_atp`, `tree_conserves_fetches`, `tree_nodes_bounded`, `spawn_depth_strictly_decreases`).
  - AS-3 Separate identities: `task_id`, `execution_id`, `checkpoint_id`, `result_id` are distinct content hashes;
    changing a local budget changes `execution_id`, never `task_id`.
  - AS-4 Exact 6-dimensional partiality vector: `(integrity, authenticity, slice, execution, history_link, reliance)`
    with componentwise meet (`meet_le_left`, `meet_le_right`).
  - AS-5 No verification inflation by retelling: forwarding a result downgrades `VERIFIED_HERE -> WITNESSED`
    and `RELIABLE -> CONDITIONAL` (`retell_never_inflates`, `retell_never_verified_here`, `retell_idempotent`).
  - AS-6 Counterexample-driven revision: a counterexample hitting any dependency in `deps_used` emits a
    `RevisionRecord` with the shortest causal path while preserving the prior result as immutable history.
  - AS-7 Anchored self-test vectors: canonical positive/negative vectors verified independently of self-claims.
  - AS-8 Pure metered computation only: Book I terms under `sigma_resume` (ATP per step); native code and
    undeclared capabilities are refused before anything runs."""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass, field
import hashlib
import json
from typing import Any, Callable, Dict, Iterable, List, Optional, Sequence, Set, Tuple

import vars1 as V

SR = V.SR

SPORE_FORMAT = "minds.spore/1"
CHECKPOINT_FORMAT = "minds.spore-checkpoint/1"
RESULT_FORMAT = "minds.spore-result/1"
REVISION_FORMAT = "minds.spore-revision/1"

ALLOWED_RUNTIMES = frozenset({"book1/sigma-resume"})
ALLOWED_CAPABILITIES = frozenset({"fetch_by_hash", "spawn_spore"})

# Ordered ranks matching `proofs/Vars1/Spore.lean`
INTEGRITY_RANK = {"FAILED": 0, "VERIFIED": 1}
AUTHENTICITY_RANK = {"FAILED": 0, "UNSIGNED": 1, "UNTRUSTED": 2, "VERIFIED": 3}
SLICE_RANK = {"PARTIAL": 0, "COMPLETE": 1}
EXECUTION_RANK = {"REFUSED": 0, "CHECKPOINTED": 1, "COMPLETED": 2}
HISTORY_RANK = {"UNLINKED": 0, "WITNESSED": 1, "VERIFIED_HERE": 2}
RELIANCE_RANK = {"UNRELIABLE": 0, "CONDITIONAL": 1, "RELIABLE": 2}

SPORE_DOMAIN_RESULT = b"minds.spore.result/1\x00"
SPORE_DOMAIN_CKPT = b"minds.spore.checkpoint/1\x00"


class SporeError(ValueError):
    """Typed refusal of a spore operation (`code`, `message`)."""

    def __init__(self, code: str, message: str):
        super().__init__(f"{code}: {message}")
        self.code = code
        self.message = message


def _canon(obj: Any) -> bytes:
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")


def _h(obj: Any) -> str:
    return hashlib.sha256(_canon(obj)).hexdigest()


def _is_hex64(v: Any) -> bool:
    return isinstance(v, str) and len(v) == 64 and all(c in "0123456789abcdef" for c in v)


def _rank_min(a: str, b: str, ranks: Dict[str, int]) -> str:
    return a if ranks[a] <= ranks[b] else b


# ---------------------------------------------------------------- Budget (AS-2)

@dataclass(frozen=True)
class Budget:
    """Explicit bounded resource envelope; mirrors `Vars1.Spore.Budget`."""

    atp: int
    fetches: int
    spawns: int
    depth: int

    def __post_init__(self) -> None:
        for name, val in (("atp", self.atp), ("fetches", self.fetches), ("spawns", self.spawns), ("depth", self.depth)):
            if not (type(val) is int and val >= 0):
                raise SporeError("BAD_BUDGET", f"{name} must be a non-negative int")

    def spend(self, *, atp: int = 0, fetches: int = 0) -> "Budget":
        if not (type(atp) is int and atp >= 0 and type(fetches) is int and fetches >= 0):
            raise SporeError("BAD_BUDGET", "spend amounts must be non-negative ints")
        if atp > self.atp:
            raise SporeError("ATP_EXHAUSTED", f"need {atp} ATP, only {self.atp} remaining")
        if fetches > self.fetches:
            raise SporeError("FETCH_BUDGET_EXHAUSTED", f"need {fetches} fetch(es), only {self.fetches} remaining")
        return Budget(self.atp - atp, self.fetches - fetches, self.spawns, self.depth)

    def spawn_partition(self, child: "Budget") -> "Budget":
        """Carve `child`'s budget out of `self` (paying 1 spawn slot and strictly decreasing depth)."""
        if self.spawns < 1:
            raise SporeError("SPAWN_BUDGET_EXHAUSTED", "no spawn slots remaining")
        if self.depth < 1:
            raise SporeError("DEPTH_EXCEEDED", "recursion depth is 0; cannot spawn child spore")
        if child.atp > self.atp:
            raise SporeError("BUDGET_OVERALLOCATION", f"child atp {child.atp} > parent {self.atp}")
        if child.fetches > self.fetches:
            raise SporeError("BUDGET_OVERALLOCATION", f"child fetches {child.fetches} > parent {self.fetches}")
        if child.spawns > self.spawns - 1:
            raise SporeError("BUDGET_OVERALLOCATION", f"child spawns {child.spawns} > parent {self.spawns - 1}")
        if child.depth > self.depth - 1:
            raise SporeError("DEPTH_EXCEEDED", f"child depth {child.depth} must be < parent {self.depth}")
        return Budget(
            atp=self.atp - child.atp,
            fetches=self.fetches - child.fetches,
            spawns=self.spawns - 1 - child.spawns,
            depth=self.depth,
        )

    def to_dict(self) -> Dict[str, int]:
        return {"atp": self.atp, "fetches": self.fetches, "spawns": self.spawns, "depth": self.depth}

    @classmethod
    def from_dict(cls, d: Dict[str, Any]) -> "Budget":
        return cls(d["atp"], d["fetches"], d["spawns"], d["depth"])


# ---------------------------------------------------------------- Partiality Lattice (AS-4, AS-5)

@dataclass(frozen=True)
class PartialityVector:
    """Exact 6-dimensional partiality vector; mirrors `Vars1.Spore.Partiality`."""

    integrity: str
    authenticity: str
    slice_completeness: str
    execution: str
    history_link: str
    reliance: str
    missing_hashes: Tuple[str, ...] = ()
    stop_reason: Optional[str] = None

    def __post_init__(self) -> None:
        if self.integrity not in INTEGRITY_RANK:
            raise SporeError("BAD_PARTIALITY", f"invalid integrity {self.integrity!r}")
        if self.authenticity not in AUTHENTICITY_RANK:
            raise SporeError("BAD_PARTIALITY", f"invalid authenticity {self.authenticity!r}")
        if self.slice_completeness not in SLICE_RANK:
            raise SporeError("BAD_PARTIALITY", f"invalid slice_completeness {self.slice_completeness!r}")
        if self.execution not in EXECUTION_RANK:
            raise SporeError("BAD_PARTIALITY", f"invalid execution {self.execution!r}")
        if self.history_link not in HISTORY_RANK:
            raise SporeError("BAD_PARTIALITY", f"invalid history_link {self.history_link!r}")
        if self.reliance not in RELIANCE_RANK:
            raise SporeError("BAD_PARTIALITY", f"invalid reliance {self.reliance!r}")

    def le(self, other: "PartialityVector") -> bool:
        """Componentwise partial order: `self <= other` iff `self` claims no stronger verification."""
        return (
            INTEGRITY_RANK[self.integrity] <= INTEGRITY_RANK[other.integrity]
            and AUTHENTICITY_RANK[self.authenticity] <= AUTHENTICITY_RANK[other.authenticity]
            and SLICE_RANK[self.slice_completeness] <= SLICE_RANK[other.slice_completeness]
            and EXECUTION_RANK[self.execution] <= EXECUTION_RANK[other.execution]
            and HISTORY_RANK[self.history_link] <= HISTORY_RANK[other.history_link]
            and RELIANCE_RANK[self.reliance] <= RELIANCE_RANK[other.reliance]
        )

    def meet(self, other: "PartialityVector") -> "PartialityVector":
        """Componentwise greatest lower bound when composing parent + child evidence."""
        missing = tuple(sorted(set(self.missing_hashes) | set(other.missing_hashes)))
        sl = _rank_min(self.slice_completeness, other.slice_completeness, SLICE_RANK)
        if missing:
            sl = "PARTIAL"
        return PartialityVector(
            integrity=_rank_min(self.integrity, other.integrity, INTEGRITY_RANK),
            authenticity=_rank_min(self.authenticity, other.authenticity, AUTHENTICITY_RANK),
            slice_completeness=sl,
            execution=_rank_min(self.execution, other.execution, EXECUTION_RANK),
            history_link=_rank_min(self.history_link, other.history_link, HISTORY_RANK),
            reliance=_rank_min(self.reliance, other.reliance, RELIANCE_RANK),
            missing_hashes=missing,
            stop_reason=self.stop_reason or other.stop_reason,
        )

    def retell(self) -> "PartialityVector":
        """Downgrade applied when passing a result to another agent without local re-verification (AS-5)."""
        hl = "WITNESSED" if self.history_link == "VERIFIED_HERE" else self.history_link
        rel = "CONDITIONAL" if self.reliance == "RELIABLE" else self.reliance
        return PartialityVector(
            integrity=self.integrity,
            authenticity=self.authenticity,
            slice_completeness=self.slice_completeness,
            execution=self.execution,
            history_link=hl,
            reliance=rel,
            missing_hashes=self.missing_hashes,
            stop_reason=self.stop_reason,
        )

    def to_dict(self) -> Dict[str, Any]:
        return {
            "integrity": self.integrity,
            "authenticity": self.authenticity,
            "slice_completeness": self.slice_completeness,
            "execution": self.execution,
            "history_link": self.history_link,
            "reliance": self.reliance,
            "missing_hashes": list(self.missing_hashes),
            "stop_reason": self.stop_reason,
        }


# ---------------------------------------------------------------- Task, Package, Checkpoint, Result (AS-3)

@dataclass(frozen=True)
class TaskSpec:
    """Identity of the question/computation itself — strictly independent of local budget or executor (AS-3)."""

    subject: str
    rules_hash: str
    runtime: str
    input_term_hash: str
    env_hashes: Tuple[str, ...]
    required_deps: Tuple[str, ...] = ()
    capabilities: Tuple[str, ...] = ("fetch_by_hash",)
    expected_nf_hash: Optional[str] = None

    def to_dict(self) -> Dict[str, Any]:
        return {
            "format": SPORE_FORMAT,
            "subject": self.subject,
            "rules_hash": self.rules_hash,
            "runtime": self.runtime,
            "input_term_hash": self.input_term_hash,
            "env_hashes": list(self.env_hashes),
            "required_deps": sorted(set(self.required_deps)),
            "capabilities": sorted(set(self.capabilities)),
            "expected_nf_hash": self.expected_nf_hash,
        }

    @property
    def task_id(self) -> str:
        return _h(self.to_dict())


@dataclass
class SporeCheckpoint:
    """Portable, content-addressed continuation state (AS-2, AS-3)."""

    task_id: str
    execution_id: str
    rules_hash: str
    computation_id: str
    sr_checkpoint: Dict[str, Any]
    state_bytes_hex: str
    spent_atp: int
    spent_fetches: int
    spent_spawns: int
    remaining_budget: Budget
    peak_semantic_size: int
    outcome: str
    stop_reason: str
    missing_hashes: Tuple[str, ...] = ()
    fetched_hashes: Tuple[str, ...] = ()
    parent_checkpoint_id: Optional[str] = None
    executor_pub: Optional[str] = None
    sig: Optional[str] = None

    def body_dict(self) -> Dict[str, Any]:
        return {
            "format": CHECKPOINT_FORMAT,
            "task_id": self.task_id,
            "execution_id": self.execution_id,
            "rules_hash": self.rules_hash,
            "computation_id": self.computation_id,
            "sr_checkpoint": self.sr_checkpoint,
            "state_bytes_hash": hashlib.sha256(bytes.fromhex(self.state_bytes_hex)).hexdigest(),
            "spent_atp": self.spent_atp,
            "spent_fetches": self.spent_fetches,
            "spent_spawns": self.spent_spawns,
            "remaining_budget": self.remaining_budget.to_dict(),
            "peak_semantic_size": self.peak_semantic_size,
            "outcome": self.outcome,
            "stop_reason": self.stop_reason,
            "missing_hashes": sorted(set(self.missing_hashes)),
            "fetched_hashes": sorted(set(self.fetched_hashes)),
            "parent_checkpoint_id": self.parent_checkpoint_id,
            "executor_pub": self.executor_pub,
        }

    @property
    def checkpoint_id(self) -> str:
        return _h(self.body_dict())

    def sign(self, seed: bytes) -> "SporeCheckpoint":
        pub = V.ed25519_pubkey(seed).hex()
        self.executor_pub = pub
        msg = SPORE_DOMAIN_CKPT + bytes.fromhex(self.checkpoint_id)
        self.sig = V.ed25519_sign(seed, msg).hex()
        return self

    def verify_signature(self) -> bool:
        if not (self.executor_pub and self.sig and _is_hex64(self.executor_pub) and len(self.sig) == 128):
            return False
        msg = SPORE_DOMAIN_CKPT + bytes.fromhex(self.checkpoint_id)
        return V.ed25519_verify(bytes.fromhex(self.executor_pub), msg, bytes.fromhex(self.sig))


@dataclass
class SporeResult:
    """Signed bounded result naming exact provenance, partiality and dependencies (AS-3..AS-6)."""

    task_id: str
    execution_id: str
    subject: str
    rules_hash: str
    outcome: str                     # NORMAL_FORM | NOT_ASSESSED | REFUSED | MISMATCH
    nf_term_hash: Optional[str]
    checkpoint_id: Optional[str]
    partiality: PartialityVector
    verified_here: Tuple[str, ...]
    taken_on_witness: Tuple[str, ...]
    deps_used: Tuple[str, ...]
    spent_atp: int
    spent_fetches: int
    bytes_fetched: int
    remaining_budget: Budget
    trust_context: str
    child_result_ids: Tuple[str, ...] = ()
    executor_pub: Optional[str] = None
    sig: Optional[str] = None

    def body_dict(self) -> Dict[str, Any]:
        return {
            "format": RESULT_FORMAT,
            "task_id": self.task_id,
            "execution_id": self.execution_id,
            "subject": self.subject,
            "rules_hash": self.rules_hash,
            "outcome": self.outcome,
            "nf_term_hash": self.nf_term_hash,
            "checkpoint_id": self.checkpoint_id,
            "partiality": self.partiality.to_dict(),
            "verified_here": sorted(set(self.verified_here)),
            "taken_on_witness": sorted(set(self.taken_on_witness)),
            "deps_used": sorted(set(self.deps_used)),
            "spent_atp": self.spent_atp,
            "spent_fetches": self.spent_fetches,
            "bytes_fetched": self.bytes_fetched,
            "remaining_budget": self.remaining_budget.to_dict(),
            "trust_context": self.trust_context,
            "child_result_ids": sorted(set(self.child_result_ids)),
            "executor_pub": self.executor_pub,
        }

    @property
    def result_id(self) -> str:
        return _h(self.body_dict())

    def sign(self, seed: bytes) -> "SporeResult":
        pub = V.ed25519_pubkey(seed).hex()
        self.executor_pub = pub
        msg = SPORE_DOMAIN_RESULT + bytes.fromhex(self.result_id)
        self.sig = V.ed25519_sign(seed, msg).hex()
        return self

    def verify_signature(self) -> bool:
        if not (self.executor_pub and self.sig and _is_hex64(self.executor_pub) and len(self.sig) == 128):
            return False
        msg = SPORE_DOMAIN_RESULT + bytes.fromhex(self.result_id)
        return V.ed25519_verify(bytes.fromhex(self.executor_pub), msg, bytes.fromhex(self.sig))


@dataclass(frozen=True)
class RevisionRecord:
    """Immutable revision record emitted when a counterexample hits a result's dependency cone (AS-6)."""

    prior_result_id: str
    task_id: str
    counterexample_hash: str
    status: str                      # REASSESS_REQUIRED | UNAFFECTED
    causal_path: Tuple[str, ...]

    def to_dict(self) -> Dict[str, Any]:
        return {
            "format": REVISION_FORMAT,
            "prior_result_id": self.prior_result_id,
            "task_id": self.task_id,
            "counterexample_hash": self.counterexample_hash,
            "status": self.status,
            "causal_path": list(self.causal_path),
        }

    @property
    def revision_id(self) -> str:
        return _h(self.to_dict())


# ---------------------------------------------------------------- Content-Addressed On-Demand Fetcher (AS-1)

class ContentStore:
    """Minimal content-addressed atom store; verifies SHA-256 on every fetch (AS-1, AS-8)."""

    def __init__(self, initial: Optional[Dict[bytes, bytes]] = None):
        self._blobs: Dict[bytes, bytes] = {}
        if initial:
            for h, data in initial.items():
                self._blobs[h] = data

    def put(self, data: bytes) -> bytes:
        h = V.sha256(data)
        self._blobs[h] = data
        return h

    def put_raw_unverified(self, fake_hash: bytes, data: bytes) -> None:
        """Test-only helper to simulate a corrupted or malicious remote mirror."""
        self._blobs[fake_hash] = data

    def has(self, h: bytes) -> bool:
        return h in self._blobs

    def get_raw(self, h: bytes) -> Optional[bytes]:
        return self._blobs.get(h)


def _book1_atom_refs(raw: bytes) -> List[bytes]:
    """Direct child term hashes referenced by a Book I binary atom via sigma-glyph's own `deser`."""
    try:
        node = SR.G.deser(raw)
    except Exception:
        return []
    if not isinstance(node, dict):
        return []
    out: List[bytes] = []
    for key in ("left", "right"):
        val = node.get(key)
        if isinstance(val, bytes) and len(val) == 32:
            out.append(val)
    return out


# ---------------------------------------------------------------- Metered Pure Spore Executor (AS-1..AS-8)

class SporeExecutor:
    """Pure, metered Book I spore executor with on-demand hash-verified fetching and resumable checkpoints."""

    def __init__(
        self,
        seed: bytes,
        local_atoms: Optional[Dict[bytes, bytes]] = None,
        remote_fetch: Optional[Callable[[bytes], Optional[bytes]]] = None,
        trust_context: str = "local/default",
        trusted_executors: Optional[Set[str]] = None,
        supported_rules: Optional[Set[str]] = None,
        granted_capabilities: Optional[Set[str]] = None,
    ):
        self.seed = seed
        self.pub_hex = V.ed25519_pubkey(seed).hex()
        self.local_atoms: Dict[bytes, bytes] = dict(local_atoms or {})
        self.remote_fetch = remote_fetch
        self.trust_context = trust_context
        self.trusted_executors: Set[str] = set(trusted_executors or {self.pub_hex})
        self.supported_rules: Set[str] = set(
            supported_rules or {V.H_LENS_KERNEL.hex(), V.H_LENS_KERNEL_V2.hex()}
        )
        self.granted_capabilities: Set[str] = set(granted_capabilities or ALLOWED_CAPABILITIES)

    def _refused_result(
        self,
        task: TaskSpec,
        exec_id: str,
        budget: Budget,
        reason: str,
        integrity: str = "VERIFIED",
        missing: Tuple[str, ...] = (),
        deps_used: Tuple[str, ...] = (),
        spent_fetches: int = 0,
        bytes_fetched: int = 0,
    ) -> Tuple[SporeResult, None]:
        pv = PartialityVector(
            integrity=integrity,
            authenticity="VERIFIED",
            slice_completeness="PARTIAL" if missing else "COMPLETE",
            execution="REFUSED",
            history_link="UNLINKED",
            reliance="UNRELIABLE",
            missing_hashes=missing,
            stop_reason=reason,
        )
        res = SporeResult(
            task_id=task.task_id,
            execution_id=exec_id,
            subject=task.subject,
            rules_hash=task.rules_hash,
            outcome="REFUSED",
            nf_term_hash=None,
            checkpoint_id=None,
            partiality=pv,
            verified_here=(),
            taken_on_witness=(),
            deps_used=deps_used,
            spent_atp=0,
            spent_fetches=spent_fetches,
            bytes_fetched=bytes_fetched,
            remaining_budget=budget,
            trust_context=self.trust_context,
        ).sign(self.seed)
        return res, None

    def _fetch_needed(
        self,
        needed_hashes: Sequence[bytes],
        budget: Budget,
    ) -> Tuple[Budget, int, int, List[str], List[str], Optional[str]]:
        """Recursively unfold only the atoms demanded by `needed_hashes` (AS-1).

        Returns `(rem_budget, spent_fetches, bytes_fetched, fetched_hex, missing_hex, integrity_error)`."""
        rem = budget
        spent_fetches = 0
        bytes_fetched = 0
        fetched: List[str] = []
        missing: List[str] = []
        seen: Set[bytes] = set()
        queue: deque[bytes] = deque(needed_hashes)

        while queue:
            h = queue.popleft()
            if h in seen:
                continue
            seen.add(h)
            if h in V.INTRINSIC_HASHES:
                continue
            data = self.local_atoms.get(h)
            if data is None:
                if self.remote_fetch is None:
                    missing.append(h.hex())
                    continue
                if rem.fetches < 1:
                    missing.append(h.hex())
                    return rem, spent_fetches, bytes_fetched, fetched, sorted(set(missing)), "FETCH_BUDGET_EXHAUSTED"
                rem = rem.spend(fetches=1)
                spent_fetches += 1
                got = self.remote_fetch(h)
                if got is None:
                    missing.append(h.hex())
                    continue
                if V.sha256(got) != h:
                    return rem, spent_fetches, bytes_fetched, fetched, sorted(set(missing)), "INTEGRITY_FAILED"
                self.local_atoms[h] = got
                bytes_fetched += len(got)
                fetched.append(h.hex())
                data = got
            else:
                if V.sha256(data) != h:
                    return rem, spent_fetches, bytes_fetched, fetched, sorted(set(missing)), "INTEGRITY_FAILED"

            for child_h in _book1_atom_refs(data):
                if child_h not in seen:
                    queue.append(child_h)

        return rem, spent_fetches, bytes_fetched, sorted(set(fetched)), sorted(set(missing)), None

    def execute(
        self,
        task: TaskSpec,
        budget: Budget,
        *,
        resume_from: Optional[SporeCheckpoint] = None,
        child_results: Sequence[SporeResult] = (),
        witnessed_deps: Sequence[str] = (),
    ) -> Tuple[SporeResult, Optional[SporeCheckpoint]]:
        """Execute (or resume) a pure metered Book I spore within `budget`."""
        parent_ckpt_id = resume_from.checkpoint_id if resume_from is not None else None
        exec_id = _h({
            "task_id": task.task_id,
            "executor_pub": self.pub_hex,
            "rules_hash": task.rules_hash,
            "budget": budget.to_dict(),
            "parent_checkpoint_id": parent_ckpt_id,
        })

        # AS-8: Refuse native code or ungranted capabilities BEFORE anything runs
        if task.runtime not in ALLOWED_RUNTIMES:
            return self._refused_result(task, exec_id, budget, f"UNSUPPORTED_RUNTIME:{task.runtime}")
        ungranted = sorted(set(task.capabilities) - self.granted_capabilities)
        if ungranted:
            return self._refused_result(task, exec_id, budget, f"CAPABILITY_REFUSED:{','.join(ungranted)}")
        if task.rules_hash not in self.supported_rules:
            return self._refused_result(task, exec_id, budget, f"UNSUPPORTED_RULES:{task.rules_hash[:12]}")

        # Validate resume checkpoint binding if continuing another agent's work (AS-2, AS-3, AS-5)
        if resume_from is not None:
            if resume_from.task_id != task.task_id or resume_from.rules_hash != task.rules_hash:
                return self._refused_result(task, exec_id, budget, "CHECKPOINT_CONTEXT_MISMATCH")
            if not resume_from.verify_signature():
                return self._refused_result(task, exec_id, budget, "CHECKPOINT_BAD_SIGNATURE", integrity="FAILED")
            if resume_from.executor_pub not in self.trusted_executors:
                return self._refused_result(task, exec_id, budget, "CHECKPOINT_UNTRUSTED_EXECUTOR")
            sb_hash = hashlib.sha256(bytes.fromhex(resume_from.state_bytes_hex)).hexdigest()
            if sb_hash != resume_from.body_dict()["state_bytes_hash"]:
                return self._refused_result(task, exec_id, budget, "CHECKPOINT_STATE_CORRUPT", integrity="FAILED")

        # AS-1: Unfold ONLY the atoms needed by this task (input term + env + explicit required deps)
        demand = [bytes.fromhex(task.input_term_hash)]
        demand += [bytes.fromhex(h) for h in task.env_hashes]
        demand += [bytes.fromhex(h) for h in task.required_deps]
        rem, spent_fetches, bytes_fetched, fetched_hex, missing_hex, fetch_err = self._fetch_needed(demand, budget)
        deps_used = tuple(sorted(set(task.required_deps) | set(task.env_hashes) | {task.input_term_hash} | set(fetched_hex)))

        if fetch_err == "INTEGRITY_FAILED":
            return self._refused_result(
                task, exec_id, rem, "INTEGRITY_FAILED", integrity="FAILED",
                missing=tuple(missing_hex), deps_used=deps_used,
                spent_fetches=spent_fetches, bytes_fetched=bytes_fetched,
            )

        if missing_hex:
            stop = "FETCH_BUDGET_EXHAUSTED" if fetch_err == "FETCH_BUDGET_EXHAUSTED" else "MISSING_DEPENDENCY"
            pv = PartialityVector(
                integrity="VERIFIED",
                authenticity="VERIFIED",
                slice_completeness="PARTIAL",
                execution="CHECKPOINTED",
                history_link="VERIFIED_HERE" if not witnessed_deps else "WITNESSED",
                reliance="UNRELIABLE",
                missing_hashes=tuple(missing_hex),
                stop_reason=stop,
            )
            ckpt = SporeCheckpoint(
                task_id=task.task_id,
                execution_id=exec_id,
                rules_hash=task.rules_hash,
                computation_id=task.task_id,
                sr_checkpoint=resume_from.sr_checkpoint if resume_from is not None else {},
                state_bytes_hex=resume_from.state_bytes_hex if resume_from is not None else "",
                spent_atp=0,
                spent_fetches=spent_fetches,
                spent_spawns=0,
                remaining_budget=rem,
                peak_semantic_size=resume_from.peak_semantic_size if resume_from is not None else 0,
                outcome="NOT_ASSESSED",
                stop_reason=stop,
                missing_hashes=tuple(missing_hex),
                fetched_hashes=tuple(fetched_hex),
                parent_checkpoint_id=parent_ckpt_id,
            ).sign(self.seed)
            res = SporeResult(
                task_id=task.task_id,
                execution_id=exec_id,
                subject=task.subject,
                rules_hash=task.rules_hash,
                outcome="NOT_ASSESSED",
                nf_term_hash=None,
                checkpoint_id=ckpt.checkpoint_id,
                partiality=pv,
                verified_here=tuple(sorted(set(fetched_hex) - set(witnessed_deps))),
                taken_on_witness=tuple(sorted(set(witnessed_deps))),
                deps_used=deps_used,
                spent_atp=0,
                spent_fetches=spent_fetches,
                bytes_fetched=bytes_fetched,
                remaining_budget=rem,
                trust_context=self.trust_context,
                child_result_ids=tuple(sorted(c.result_id for c in child_results)),
            ).sign(self.seed)
            return res, ckpt

        # Build Book I sigma_resume environment from declared + unfolded non-intrinsic term atoms
        unfolded_env: Set[bytes] = set()
        q_env: deque[bytes] = deque([bytes.fromhex(task.input_term_hash)] + [bytes.fromhex(h) for h in task.env_hashes])
        seen_env: Set[bytes] = set()
        while q_env:
            eh = q_env.popleft()
            if eh in seen_env or eh in V.INTRINSIC_HASHES:
                continue
            seen_env.add(eh)
            if eh in self.local_atoms:
                unfolded_env.add(eh)
                for ch in _book1_atom_refs(self.local_atoms[eh]):
                    if ch not in seen_env:
                        q_env.append(ch)
        env_hash_bytes = sorted(unfolded_env)
        sr_env = SR.Environment(env_hash_bytes, self.local_atoms)
        env_id_bytes = bytes.fromhex(sr_env.environment_id)
        root_raw = V.atom_computation_root(bytes.fromhex(task.input_term_hash), env_id_bytes)
        cid_hex = V.sha256(root_raw).hex()

        if resume_from is not None and resume_from.sr_checkpoint:
            base_doc = dict(resume_from.sr_checkpoint)
            base_id = resume_from.checkpoint_id
            base_state = bytes.fromhex(resume_from.state_bytes_hex)
            prior_spent = int(base_doc.get("spent_total", 0))
        else:
            base_doc, base_id, base_state = SR.start(cid_hex, bytes.fromhex(task.input_term_hash))
            prior_spent = 0

        # Metered advance bounded strictly by `rem.atp` (AS-2, AS-8)
        adv = SR.advance(base_doc, base_id, base_state, sr_env, additional_credit=rem.atp)
        new_spent = int(adv.checkpoint.get("spent_total", prior_spent))
        delta_atp = max(0, new_spent - prior_spent)
        if delta_atp > rem.atp:
            return self._refused_result(task, exec_id, rem, "INTERNAL_METER_OVERFLOW")
        rem_after = rem.spend(atp=delta_atp)

        # Determine outcome without ever inventing a refutation on budget exhaustion (AS-4, AS-8)
        nf_hash: Optional[str] = None
        if adv.outcome == SR.NORMAL_FORM:
            _, nf_bytes = V.sgs1_term_hash(adv.state_bytes)
            nf_hash = nf_bytes.hex()
            if task.expected_nf_hash is not None and nf_hash != task.expected_nf_hash:
                outcome = "MISMATCH"
                exec_status = "COMPLETED"
                stop_reason = "EXPECTED_NF_MISMATCH"
                reliance = "UNRELIABLE"
            else:
                outcome = "NORMAL_FORM"
                exec_status = "COMPLETED"
                stop_reason = "NORMAL_FORM"
                reliance = "RELIABLE" if not witnessed_deps else "CONDITIONAL"
        elif adv.outcome == SR.PAUSED:
            outcome = "NOT_ASSESSED"
            exec_status = "CHECKPOINTED"
            stop_reason = "ATP_EXHAUSTED"
            reliance = "UNRELIABLE"
        else:
            outcome = "REFUSED"
            exec_status = "REFUSED"
            stop_reason = f"KERNEL_STOP:{adv.outcome}"
            reliance = "UNRELIABLE"

        hist_link = "WITNESSED" if (witnessed_deps or resume_from is not None) else "VERIFIED_HERE"
        if resume_from is not None and reliance == "RELIABLE":
            # Resumed from another executor's checkpoint without replaying prior steps: honest provenance (AS-5)
            if resume_from.executor_pub != self.pub_hex:
                reliance = "CONDITIONAL"

        pv = PartialityVector(
            integrity="VERIFIED",
            authenticity="VERIFIED",
            slice_completeness="COMPLETE",
            execution=exec_status,
            history_link=hist_link,
            reliance=reliance,
            missing_hashes=(),
            stop_reason=None if exec_status == "COMPLETED" else stop_reason,
        )
        # Compose with any child spore results via monotone meet (never inflate!)
        verified_here = set(deps_used) - set(witnessed_deps)
        taken_on_witness = set(witnessed_deps)
        all_deps = set(deps_used)
        if resume_from is not None and resume_from.executor_pub != self.pub_hex:
            taken_on_witness.add(resume_from.checkpoint_id)
        for cr in child_results:
            pv = pv.meet(cr.partiality.retell())
            all_deps |= set(cr.deps_used)
            taken_on_witness |= set(cr.taken_on_witness) | {cr.result_id}

        ckpt = SporeCheckpoint(
            task_id=task.task_id,
            execution_id=exec_id,
            rules_hash=task.rules_hash,
            computation_id=cid_hex,
            sr_checkpoint=adv.checkpoint,
            state_bytes_hex=adv.state_bytes.hex(),
            spent_atp=delta_atp,
            spent_fetches=spent_fetches,
            spent_spawns=len(child_results),
            remaining_budget=rem_after,
            peak_semantic_size=int(adv.checkpoint.get("peak_semantic_size", 0)),
            outcome=outcome,
            stop_reason=stop_reason,
            missing_hashes=(),
            fetched_hashes=tuple(fetched_hex),
            parent_checkpoint_id=parent_ckpt_id,
        ).sign(self.seed)

        res = SporeResult(
            task_id=task.task_id,
            execution_id=exec_id,
            subject=task.subject,
            rules_hash=task.rules_hash,
            outcome=outcome,
            nf_term_hash=nf_hash,
            checkpoint_id=ckpt.checkpoint_id,
            partiality=pv,
            verified_here=tuple(sorted(verified_here)),
            taken_on_witness=tuple(sorted(taken_on_witness)),
            deps_used=tuple(sorted(all_deps)),
            spent_atp=delta_atp,
            spent_fetches=spent_fetches,
            bytes_fetched=bytes_fetched,
            remaining_budget=rem_after,
            trust_context=self.trust_context,
            child_result_ids=tuple(sorted(c.result_id for c in child_results)),
        ).sign(self.seed)
        return res, ckpt


# ---------------------------------------------------------------- Handover, Reuse & Counterexample Revision (AS-3, AS-5, AS-6)

def receive_result(
    result: SporeResult,
    *,
    expected_task: TaskSpec,
    trusted_executors: Set[str],
    expected_trust_context: Optional[str] = None,
) -> Tuple[bool, str, PartialityVector]:
    """Verify a received `SporeResult` from another agent (AS-3, AS-5).

    Always applies `retell()` so forwarding through agents can NEVER raise `history_link` or `reliance`."""
    if not result.verify_signature():
        bad = PartialityVector("FAILED", "FAILED", result.partiality.slice_completeness,
                               result.partiality.execution, "UNLINKED", "UNRELIABLE",
                               result.partiality.missing_hashes, "BAD_SIGNATURE")
        return False, "BAD_SIGNATURE", bad
    if result.task_id != expected_task.task_id:
        return False, "TASK_MISMATCH", result.partiality.retell()
    if result.subject != expected_task.subject:
        return False, "SUBJECT_MISMATCH", result.partiality.retell()
    if result.rules_hash != expected_task.rules_hash:
        return False, "RULES_MISMATCH", result.partiality.retell()
    if expected_trust_context is not None and result.trust_context != expected_trust_context:
        return False, "TRUST_CONTEXT_MISMATCH", result.partiality.retell()
    if result.executor_pub not in trusted_executors:
        untrusted = PartialityVector(
            integrity=result.partiality.integrity,
            authenticity="UNTRUSTED",
            slice_completeness=result.partiality.slice_completeness,
            execution=result.partiality.execution,
            history_link="UNLINKED",
            reliance="UNRELIABLE",
            missing_hashes=result.partiality.missing_hashes,
            stop_reason="UNTRUSTED_EXECUTOR",
        )
        return False, "UNTRUSTED_EXECUTOR", untrusted
    # AS-5: Retelling NEVER inflates verification
    return True, "OK", result.partiality.retell()


def shortest_causal_path(
    bad_hash: str,
    roots: Iterable[str],
    dep_edges: Dict[str, Sequence[str]],
) -> Optional[Tuple[str, ...]]:
    """Shortest path `(bad_hash, ..., root)` where `dep_edges[node]` lists nodes `node` depends on."""
    root_set = set(roots)
    if bad_hash in root_set:
        return (bad_hash,)
    # Reverse adjacency: dependency -> dependents
    rev: Dict[str, List[str]] = {}
    for node, deps in dep_edges.items():
        for d in deps:
            rev.setdefault(d, []).append(node)
    for k in rev:
        rev[k].sort()
    q: deque[Tuple[str, Tuple[str, ...]]] = deque([(bad_hash, (bad_hash,))])
    seen = {bad_hash}
    while q:
        cur, path = q.popleft()
        for nxt in rev.get(cur, ()):
            if nxt in seen:
                continue
            npath = path + (nxt,)
            if nxt in root_set:
                return npath
            seen.add(nxt)
            q.append((nxt, npath))
    return None


def revise_on_counterexample(
    result: SporeResult,
    counterexample_hash: str,
    dep_edges: Optional[Dict[str, Sequence[str]]] = None,
) -> RevisionRecord:
    """Determine whether `counterexample_hash` invalidates `result` and emit an immutable `RevisionRecord` (AS-6).

    The earlier `SporeResult` is never mutated; its `result_id` is referenced as history."""
    edges = dict(dep_edges or {})
    edges.setdefault(result.task_id, list(result.deps_used))
    path = shortest_causal_path(counterexample_hash, (result.task_id,), edges)
    if path is None and counterexample_hash in result.deps_used:
        path = (counterexample_hash, result.task_id)
    if path is not None:
        return RevisionRecord(
            prior_result_id=result.result_id,
            task_id=result.task_id,
            counterexample_hash=counterexample_hash,
            status="REASSESS_REQUIRED",
            causal_path=path,
        )
    return RevisionRecord(
        prior_result_id=result.result_id,
        task_id=result.task_id,
        counterexample_hash=counterexample_hash,
        status="UNAFFECTED",
        causal_path=(),
    )
