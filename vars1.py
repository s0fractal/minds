#!/usr/bin/env python3
"""VARS-1 reference implementation (no dependencies beyond `sigma-glyph`'s `sigma_resume`).

Section numbers refer to VARS-1-SPEC.md: objects (§1), standard schemas (§2), store and admission gate (§3),
fold and lens (§4), replay against Book I (§5). The fold and lens Passes 1-2 are decided by `kernel/lens.wasm`;
the Python fold and passes here are its differential twin.
"""
from __future__ import annotations

import json
import re
import struct
import shutil
import subprocess
import tempfile
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple


# The bundle verifier (§4.4) is its own standalone file: Ed25519, atoms, cells, seals, the standard schemas and the
# projection/attestation checks live there, and this module re-exports them, so there is one implementation.
def _load_minds_verify():
    import importlib.util
    if "minds_verify" in sys.modules:
        return sys.modules["minds_verify"]
    spec = importlib.util.spec_from_file_location("minds_verify", Path(__file__).resolve().parent / "verify" / "minds_verify.py")
    mod = importlib.util.module_from_spec(spec)
    sys.modules["minds_verify"] = mod  # registered first: its dataclasses resolve their module by name
    spec.loader.exec_module(mod)
    return mod


_MV = _load_minds_verify()
from minds_verify import (  # noqa: E402
    _B, _D, _I, _L, _Q, _ed_add, _ed_dec, _ed_enc, _ed_mul, _xrecover,
    ed25519_pubkey, ed25519_sign, ed25519_verify, weak_public_key, sha256,
    MAX_INT, MAX_STATE_BYTES, MAX_UTF8_BYTES, MAX_LOSS_BYTES, MAX_HVEC_LEN,
    H_I, H_K, H_S, H_FALSE, H_INVALID, H_EMPTY, H_META_SCHEMA, H_ZERO, H_NORMAL_FORM, H_PAUSED, H_BLOCKED_REF,
    H_CYCLE_PROVEN, H_REPLAYED, H_ATTESTED, H_VERDICT_INVALID, H_NOT_ASSESSED, H_PROVISIONAL, H_OWNER, H_LENS_KERNEL,
    VarsError, atom_u64, parse_u64, atom_utf8, parse_utf8, validate_utf8_atom, atom_hvec, parse_hvec, atom_pol1,
    parse_pol1, Cell, Seal, SCHEMA_SPECS, build_standard_schemas, STD_SCHEMAS, STD_SCHEMA_ATOMS, H_SCHEMA,
    KERNEL_BITS, BUNDLE_FORMAT, ATTESTATION_FORMAT, parse_kernel_input, pass3_at_tip, kernel_input_order,
    rules_status, verify_projection, verify_attestation,
)

# ---------------------------------------------------------------------------
# §1 Intrinsic Constants & Hash Helpers
# ---------------------------------------------------------------------------
SLOT_NAME_RE = re.compile(
    r"^[a-zA-Z0-9][a-zA-Z0-9_-]{0,31}/[a-zA-Z0-9][a-zA-Z0-9_.-]{0,63}(/[a-zA-Z0-9][a-zA-Z0-9_.-]{0,63})*$"
)


def validate_slot_name(slot_str: str) -> None:
    """Validate `<scope>/<name>`: no `..`, no `.lock`, no leading/trailing `.` or `/`."""
    if not (1 <= len(slot_str) <= 128) or not SLOT_NAME_RE.match(slot_str):
        raise VarsError(f"invalid slot name syntax: {slot_str!r}")
    for seg in slot_str.split("/"):
        if ".." in seg or seg.endswith(".lock") or seg.endswith("."):
            raise VarsError(f"forbidden path segment in slot name: {slot_str!r}")



# The rules a scope is evaluated under are a stored object: the compiled rules kernel (`kernel/`, Rust -> wasm32,
# reproducible). A scope names it by hash; this host implements exactly these rules.
KERNEL_DIR = Path(__file__).resolve().parent / "kernel"
KERNEL_ATOM = (KERNEL_DIR / "lens.wasm").read_bytes()
if sha256(KERNEL_ATOM) != H_LENS_KERNEL:
    raise RuntimeError("kernel/lens.wasm does not hash to H_LENS_KERNEL")

INTRINSIC_HASHES: Set[bytes] = {
    H_I, H_K, H_S, H_FALSE, H_INVALID,
    H_EMPTY, H_META_SCHEMA, H_ZERO,
    H_NORMAL_FORM, H_PAUSED, H_BLOCKED_REF, H_CYCLE_PROVEN,
    H_REPLAYED, H_ATTESTED, H_VERDICT_INVALID, H_NOT_ASSESSED,
    H_PROVISIONAL, H_OWNER,
}


INTRINSIC_UTF8: Set[bytes] = {
    H_NORMAL_FORM, H_PAUSED, H_BLOCKED_REF, H_CYCLE_PROVEN,
    H_REPLAYED, H_ATTESTED, H_VERDICT_INVALID, H_NOT_ASSESSED,
    H_PROVISIONAL, H_OWNER,
}
# Intrinsic atoms are known without reading the store (§1): their bytes, for every consumer that reads a value
INTRINSIC_ATOMS: Dict[bytes, bytes] = {sha256(raw): raw for raw in (
    b"HVEC", b"U64\x00" + b"\x00" * 8,
    *(b"UTF8" + t for t in (b"NORMAL_FORM", b"PAUSED", b"BLOCKED_REFERENCE", b"CYCLE_PROVEN", b"REPLAYED",
                            b"ATTESTED", b"INVALID", b"NOT_ASSESSED", b"provisional", b"owner")),
)}


assert set(INTRINSIC_ATOMS) <= INTRINSIC_HASHES


def atom_of(h: bytes, atoms: Dict[bytes, bytes], what: str = "atom") -> bytes:
    """The bytes of atom `h`, stored or intrinsic: whether an intrinsic is materialized never changes a result."""
    raw = atoms.get(h)
    if raw is None:
        raw = INTRINSIC_ATOMS.get(h)
    if raw is None:
        raise VarsError(f"{what} {h.hex()[:12]} missing from cas/atoms/")
    return raw


def u64_of(h: bytes, atoms: Dict[bytes, bytes], what: str = "u64") -> int:
    return parse_u64(atom_of(h, atoms, what))


# Fields that may hold H_EMPTY to mean "none"; every other slot must have its declared type.
# Closed: a schema naming another type is refused at the gate, so check_slot_type never sees one
FIELD_TYPES = {"utf8", "u64", "pol1", "root", "digest", "wasm", "cell", "hash"}
VERDICT_CODES = {H_REPLAYED, H_ATTESTED, H_VERDICT_INVALID, H_NOT_ASSESSED}
OPTIONAL_FIELDS = {"required_comp", "expected_outcome", "evaluator_policy", "ckpt_or_witness"}




def atom_environment(node_hashes: Iterable[bytes]) -> bytes:
    hexes = sorted({h.hex() for h in node_hashes})
    if len(hexes) > MAX_HVEC_LEN:
        raise VarsError("Environment exceeds 65535 hashes")
    doc = {"schema": "sigma-resume.environment@draft-1", "hashes": hexes}
    return json.dumps(doc, sort_keys=True, separators=(",", ":")).encode("utf-8")


def atom_computation_root(
    input_term_hash: bytes,
    environment_id: bytes,
    runtime_id: str = "sigma-book1-0.6.0/hash-thunk/leftmost-outermost",
    cost_model_id: str = "atp/size-priced/adr-001+adr-003",
) -> bytes:
    doc = {
        "schema": "sigma-resume.root@draft-1",
        "runtime_semantics_id": runtime_id,
        "cost_model_id": cost_model_id,
        "input_term_hash": input_term_hash.hex(),
        "environment_id": environment_id.hex(),
    }
    return json.dumps(doc, sort_keys=True, separators=(",", ":")).encode("utf-8")


def validate_atom(raw: bytes) -> None:
    """Refuse an atom that is not well formed (§1.1); SGS1 states and SigmaNodeV2 nodes are checked with Book I."""
    _MV.validate_atom(raw, extended=_validate_book1_atom)


def _validate_book1_atom(raw: bytes) -> None:
    if raw[:4] == b"SGS1":
        if len(raw) > MAX_STATE_BYTES or len(raw) < 4 + 32 + 33:
            raise VarsError("invalid SGS1 state size")
        sgs1_term_hash(raw)  # the whole state parses
    elif SR.G.deser(raw) is None:
        raise VarsError("invalid SigmaNodeV2 node")


STD_SCHEMA_IDS: Set[bytes] = set(H_SCHEMA.values())
STD_SCHEMA_ATOMS[H_LENS_KERNEL] = KERNEL_ATOM  # every genesis stores the rules object

_SIGMA_IMPL_DIR = Path(__file__).resolve().parent.parent / "sigma-glyph" / "impl"
if str(_SIGMA_IMPL_DIR) not in sys.path:
    sys.path.insert(0, str(_SIGMA_IMPL_DIR))
import sigma_resume as SR  # noqa: E402


# ---------------------------------------------------------------------------
# Book I `term_hash` decoding & Deterministic Replay
# ---------------------------------------------------------------------------
def sgs1_term_hash(state_bytes: bytes) -> Tuple[bytes, bytes]:
    """Decode `SGS1` bytes -> (computation_id, book1_term_hash)."""
    if len(state_bytes) < 4 + 32 + 33 or state_bytes[:4] != b"SGS1":
        raise VarsError("not an SGS1 state")
    cid = state_bytes[4:36]
    i = 36
    frames: List[List[bytes]] = []
    op_map = {ord("L"): 0x00, ord("R"): 0x01, ord("D"): 0xFF}
    while True:
        if i >= len(state_bytes):
            raise VarsError("truncated SGS1 state")
        tag = state_bytes[i]
        if tag == ord("A"):
            frames.append([])
            i += 1
            continue
        if i + 33 > len(state_bytes):
            raise VarsError("truncated SGS1 leaf")
        payload = state_bytes[i + 1 : i + 33]
        i += 33
        if tag == ord("T"):
            th = payload
        elif tag in op_map:
            th = sha256(bytes([op_map[tag], 0x01]) + payload)
        else:
            raise VarsError(f"unknown SGS1 tag: {tag}")
        while frames:
            frames[-1].append(th)
            if len(frames[-1]) < 2:
                break
            left, right = frames.pop()
            th = sha256(bytes([0x02, 0x06]) + left + right)
        else:
            if i != len(state_bytes):
                raise VarsError("trailing bytes in SGS1 state")
            return cid, th


def _parent_checkpoint(
    c: Cell, atoms: Dict[bytes, bytes], cells: Optional[Dict[bytes, Cell]]
) -> Optional[Tuple[int, bytes, Cell]]:
    """The highest-spent `schema.checkpoint` of the same computation listed in `c.h_relies`, or None."""
    if cells is None or c.h_relies == H_EMPTY:
        return None
    parent_ckpts = [
        (u64_of(cells[pid].slots[2], atoms), pid, cells[pid])
        for pid in parse_hvec(atoms[c.h_relies], require_sorted=True)
        if pid in cells and cells[pid].h_schema == H_SCHEMA["checkpoint"] and cells[pid].slots[0] == c.slots[0]
    ]
    return max(parent_ckpts, key=lambda item: item[0]) if parent_ckpts else None


def verify_checkpoint_replay(
    c: Cell,
    atoms: Dict[bytes, bytes],
    cells: Optional[Dict[bytes, Cell]] = None,
    *,
    max_atp: Optional[int] = None,
    gate_mode: bool = False,
    memo: Optional[Dict[bytes, str]] = None,
) -> str:
    """Deterministically replay a `schema.checkpoint` cell.

    Each checkpoint is replayed incrementally from the highest-spent parent `schema.checkpoint` in its
    `h_relies` (if any), else from `ComputationRoot`. : a parent's state is a trusted starting point only
    if the parent is itself replay-verified, transitively back to `ComputationRoot`, so the whole lineage is
    verified oldest-first. When `gate_mode=True`, a transition exceeding `VERIFIER_LIMITS['max_atp']` is admitted
    on structure alone as `'NOT_ASSESSED'`, and so is every checkpoint whose lineage contains one. Outside gate
    mode a lineage that is not fully replay-verified raises. `memo` caches per-cell results within one caller.
    """
    lineage = [c]
    seen = {c.id}
    while True:
        parent = _parent_checkpoint(lineage[-1], atoms, cells)
        if parent is None:
            break
        if parent[1] in seen:
            raise VarsError("checkpoint lineage is cyclic")
        seen.add(parent[1])
        lineage.append(parent[2])

    memo = {} if memo is None else memo
    for i in range(len(lineage) - 1, -1, -1):
        cell = lineage[i]
        status = memo.get(cell.id)
        if status is None:
            try:
                status = _replay_from_parent(cell, atoms, cells, max_atp=max_atp, gate_mode=gate_mode)
            except VarsError as e:
                if i == 0:
                    raise
                raise VarsError(
                    f"parent checkpoint {cell.id.hex()[:12]} is not replay-verified, so its state cannot "
                    f"root the replay of {c.id.hex()[:12]}: {e}"
                ) from None
            memo[cell.id] = status
        if status != "REPLAYED":
            # Only gate mode returns a non-REPLAYED status; everything newer in the lineage inherits it.
            for newer in lineage[:i]:
                memo[newer.id] = status
            return status
    return "REPLAYED"


def _replay_from_parent(
    c: Cell,
    atoms: Dict[bytes, bytes],
    cells: Optional[Dict[bytes, Cell]],
    *,
    max_atp: Optional[int],
    gate_mode: bool,
) -> str:
    """Replay one checkpoint from its immediate parent's state (or from `ComputationRoot`).

    Trusts the parent's state: callers MUST go through `verify_checkpoint_replay`, which verifies the
    lineage first."""
    cid_bytes = c.slots[0]
    root_doc, env_doc = _load_root_and_env(cid_bytes, atoms)
    env = SR.Environment([bytes.fromhex(h) for h in env_doc["hashes"]], atoms)
    ctx_err = SR._context_error(root_doc, env)
    if ctx_err:
        raise VarsError(f"checkpoint context error: {ctx_err}")

    credit_total = u64_of(c.slots[1], atoms)
    spent_total = u64_of(c.slots[2], atoms)
    peak_size = u64_of(c.slots[3], atoms)
    outcome_h = c.slots[4]
    if credit_total < spent_total:
        raise VarsError("checkpoint credit_total < spent_total")

    # Incremental replay from the parent checkpoint in H_relies; the caller has verified it
    b_doc, b_id, b_state = SR.start(cid_bytes.hex(), bytes.fromhex(root_doc["input_term_hash"]))
    parent_spent = 0
    parent = _parent_checkpoint(c, atoms, cells)
    if parent is not None:
        parent_spent, p_id, p_cell = parent
        if spent_total < parent_spent:
            raise VarsError("checkpoint spent_total decreased relative to parent checkpoint")
        b_doc = {
            "schema": "sigma-resume.checkpoint@draft-1",
            "computation_id": cid_bytes.hex(),
            "parent_checkpoint_id": p_id.hex(),
            "state_id": p_cell.h_payload.hex(),
            "credit_total": parent_spent,
            "spent_total": parent_spent,
            "peak_semantic_size": u64_of(p_cell.slots[3], atoms),
            "kernel_outcome": "PAUSED",
            "transition_claim": {"actions": 0, "spent_delta": 0},
        }
        b_id = p_id.hex()
        b_state = atoms[p_cell.h_payload]

    delta_spent = spent_total - parent_spent
    eff_max_atp = max_atp if max_atp is not None else SR.G.VERIFIER_LIMITS.get("max_atp", 10_000_000)
    if delta_spent > eff_max_atp:
        if gate_mode:
            return "NOT_ASSESSED"
        raise VarsError("checkpoint delta_spent exceeds host verifier ceiling (NOT_ASSESSED)")

    runtime = root_doc["runtime_semantics_id"]
    try:
        replay = SR.advance(b_doc, b_id, b_state, env, delta_spent, SR.G.VERIFIER_LIMITS, runtime)
    except Exception as e:
        raise VarsError(f"checkpoint replay failed: {e}") from None
    if not replay.kernel:
        if gate_mode and replay.outcome in (SR.RESOURCE_FAULT, SR.ADMISSION_REFUSED, SR.INCOMPLETE):
            return "NOT_ASSESSED"
        raise VarsError(f"checkpoint replay stopped locally ({replay.outcome})")
    if (
        replay.state_bytes != atoms[c.h_payload]
        or replay.checkpoint["spent_total"] != spent_total
        or replay.checkpoint["peak_semantic_size"] != peak_size
    ):
        raise VarsError("forged checkpoint state_bytes, spent_total, or peak_size mismatch on replay")
    if replay.checkpoint["transition_claim"]["actions"] != u64_of(c.slots[5], atoms):
        raise VarsError("checkpoint actions differ from the replayed transition's action count")

    probe_doc = dict(replay.checkpoint, credit_total=spent_total)
    probe = SR.advance(
        probe_doc,
        c.h_payload.hex(),
        replay.state_bytes,
        env,
        credit_total - spent_total,
        SR.G.VERIFIER_LIMITS,
        runtime,
        max_actions=1,
    )
    if outcome_h == H_NORMAL_FORM:
        if not (probe.outcome == "NORMAL_FORM" and probe.checkpoint["transition_claim"]["actions"] == 0):
            raise VarsError("checkpoint claims H_NORMAL_FORM but probe is not terminal NORMAL_FORM")
    elif outcome_h == H_PAUSED:
        if probe.outcome != "PAUSED":
            raise VarsError("checkpoint claims H_PAUSED but probe outcome differs")
    elif outcome_h == H_BLOCKED_REF:
        if not (probe.outcome == "BLOCKED_REFERENCE" and probe.checkpoint["transition_claim"]["actions"] == 0):
            raise VarsError("checkpoint claims H_BLOCKED_REF but probe outcome differs")
    else:
        raise VarsError("unknown checkpoint kernel_outcome hash")
    return "REPLAYED"


def check_slot_type(h: bytes, typ: str, atoms: Dict[bytes, bytes], cells: Dict[bytes, "Cell"]) -> None:
    """a slot must hold a value of the type its schema field declares, not merely an existing hash."""
    def atom(prefix: bytes) -> bytes:
        raw = atoms.get(h)
        if raw is None or not raw.startswith(prefix):
            raise VarsError(f"slot type: {h.hex()[:12]} is not a {typ} atom")
        return raw
    if typ == "utf8":
        if h not in INTRINSIC_UTF8:
            validate_utf8_atom(atom(b"UTF8"))
    elif typ == "u64":
        if h != H_ZERO:
            parse_u64(atom(b"U64\x00"))
    elif typ == "pol1":
        thr, hvec_h = parse_pol1(atom(b"POL1"))
        if hvec_h not in atoms:
            raise VarsError("slot type: POL1 pubkey HVEC missing from cas/atoms/")
        pks = parse_hvec(atoms[hvec_h], require_sorted=True)
        for pk in pks:
            if weak_public_key(pk):
                raise VarsError("weak or non-canonical Ed25519 public key in POL1")
            try:
                _ed_dec(pk)
            except ValueError as e:
                raise VarsError(f"invalid Ed25519 curve point in POL1: {e}") from None
        if not 1 <= thr <= len(pks):
            raise VarsError("slot type: POL1 threshold outside 1..len(pubkeys)")
    elif typ == "root":
        _load_root_and_env(h, atoms)
    elif typ == "digest":
        pass  # a bare SHA-256 value; it names bytes that need not be stored (§2, projection)
    elif typ == "wasm":
        atom(b"\x00asm")
    elif typ == "cell":
        if h not in cells:
            raise VarsError(f"slot type: {h.hex()[:12]} is not a cell")
    elif typ == "hash":
        if h not in atoms and h not in cells and h not in INTRINSIC_HASHES:
            raise VarsError(f"slot type: {h.hex()[:12]} missing from CAS")


def _load_root_and_env(cid_bytes: bytes, atoms: Dict[bytes, bytes]) -> Tuple[dict, dict]:
    """The `ComputationRoot` and `Environment` documents behind `cid_bytes`, or a VarsError (never a JSON/Key error)."""
    def doc(h: bytes, schema: str, what: str) -> dict:
        raw = atoms.get(h)
        if raw is None:
            raise VarsError(f"{what} missing from cas/atoms/")
        try:
            d = json.loads(raw.decode("utf-8"))
        except (UnicodeDecodeError, ValueError):
            raise VarsError(f"{what} is not a canonical JSON atom") from None
        if not isinstance(d, dict) or d.get("schema") != schema:
            raise VarsError(f"invalid {what} schema")
        return d
    root_doc = doc(cid_bytes, "sigma-resume.root@draft-1", "ComputationRoot")
    env_hex = root_doc.get("environment_id")
    if not isinstance(env_hex, str) or len(env_hex) != 64:
        raise VarsError("ComputationRoot environment_id malformed")
    env_doc = doc(bytes.fromhex(env_hex), "sigma-resume.environment@draft-1", "Environment")
    return root_doc, env_doc


def verify_cycle_witness_replay(c: Cell, atoms: Dict[bytes, bytes], *, gate_mode: bool = False) -> str:
    """Deterministically verify a `schema.cycle_witness` cell via `sigma_resume.verify_cycle`."""
    cid_bytes = c.slots[0]
    root_doc, env_doc = _load_root_and_env(cid_bytes, atoms)
    env = SR.Environment([bytes.fromhex(h) for h in env_doc["hashes"]], atoms)
    witness_doc = {
        "schema": "sigma-resume.cycle@draft-1",
        "computation_id": cid_bytes.hex(),
        "entry_spent_total": u64_of(c.slots[1], atoms),
        "entry_state_id": c.h_payload.hex(),
        "cycle_action_count": u64_of(c.slots[2], atoms),
        "cycle_cost": u64_of(c.slots[3], atoms),
    }
    verdict = SR.verify_cycle((root_doc, cid_bytes.hex()), env, witness_doc)
    if verdict.startswith("NOT_ASSESSED") and gate_mode:
        return "NOT_ASSESSED"
    if verdict != "CYCLE_PROVEN":
        raise VarsError(f"cycle_witness replay failed: {verdict}")
    return "CYCLE_PROVEN"


KERNEL_CODES = {
    -1: "malformed input", -2: "edge not in forward topological order", -3: "out of memory",
    -4: "Pass 2 not monotone", -5: "Pass 2 without fixed point",
    -10: "genesis scope shape", -11: "genesis scope lacks its admission quorum", -12: "local seal context",
    -13: "local seal key", -14: "cross-seal", -15: "unsealed local cell", -16: "evaluator policy not within roster",
    -17: "foreign cell without self-sealed scope", -18: "several new local scopes", -19: "new scope shape",
    -20: "new scope lacks admission quorum", -21: "acceptance not pinned to a self-sealed scope",
    -22: "binding does not reach a prior binding of its name", -23: "unknown policy",
}


class KernelRefusal(VarsError):
    """The rules kernel returned a negative code: the fold refused the commit log (or its input was malformed)."""

    def __init__(self, code: int):
        self.code = code
        super().__init__(f"rules kernel E{code}: {KERNEL_CODES.get(code, 'unknown code')}")


class TwinDivergence(RuntimeError):
    """The rules kernel and the host's differential twin disagree: a defect in one of them, never a refusal."""


class KernelRunner:
    """Runs `kernel/lens.wasm` under Node (WebAssembly, no other dependency): the rules object of §4.3."""

    def __init__(self) -> None:
        self.proc = subprocess.Popen(
            ["node", str(KERNEL_DIR / "run.mjs"), str(KERNEL_DIR / "lens.wasm")],
            stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True,
        )

    def run(self, kernel_input: bytes) -> bytes:
        """The kernel's output bytes; raises KernelRefusal on a negative code."""
        self.proc.stdin.write(kernel_input.hex() + "\n")
        self.proc.stdin.flush()
        line = self.proc.stdout.readline().strip()
        if not line:
            raise RuntimeError("rules kernel produced no output")
        if line.startswith("E"):
            raise KernelRefusal(int(line[1:]))
        return bytes.fromhex(line)

    def statuses(self, lens: Dict[str, object]) -> Dict[bytes, Dict[str, bool]]:
        """Kernel statuses for a lens result, keyed by cell id, from a fresh run of its kernel input."""
        out = self.run(lens["kernel_input"])
        n = len(lens["kernel_order"])
        return {cid: {name: bool(out[4 + i] >> b & 1) for b, name in enumerate(KERNEL_BITS)}
                for i, cid in enumerate(lens["kernel_order"])}

    def close(self) -> None:
        self.proc.stdin.close()
        self.proc.wait(timeout=10)


_KERNEL: Optional[KernelRunner] = None


def kernel_runner() -> KernelRunner:
    global _KERNEL
    if _KERNEL is None:
        _KERNEL = KernelRunner()
    return _KERNEL


def topo_order(cells: Dict[bytes, "Cell"], atoms: Dict[bytes, bytes]) -> Tuple[List[bytes], Dict[bytes, Set[bytes]], Dict[bytes, Set[bytes]]]:
    """Forward topological order (oldest first) over every cell reference, with parents (older) and children (newer)."""

    def hvec_items(h: bytes) -> List[bytes]:
        return [] if h == H_EMPTY else parse_hvec(atoms[h], require_sorted=True)

    parents_of: Dict[bytes, Set[bytes]] = {cid: set() for cid in cells}  # u -> older v
    children_of: Dict[bytes, Set[bytes]] = {cid: set() for cid in cells}  # older v -> newer u
    for u, c in cells.items():
        refs: Set[bytes] = set()
        for mh in (c.h_relies, c.h_attests, c.h_supersedes, c.h_retires, c.h_invalidates):
            refs.update(hvec_items(mh))
        refs.update(x for x in (c.h_payload, *c.slots) if x in cells)
        for v in refs:
            if v in cells and v != u:
                parents_of[u].add(v)
                children_of[v].add(u)
    indeg = {u: len(parents_of[u]) for u in cells}
    queue = sorted(u for u, d in indeg.items() if d == 0)
    order: List[bytes] = []
    while queue:
        u = queue.pop(0)
        order.append(u)
        for ch in sorted(children_of[u]):
            indeg[ch] -= 1
            if indeg[ch] == 0:
                queue.append(ch)
    if len(order) != len(cells):
        raise VarsError("cell references are cyclic")
    return order, parents_of, children_of


def strong_pol1(raw: bytes, atoms: Dict[bytes, bytes]) -> Optional[Tuple[int, List[bytes]]]:
    """A POL1 atom's threshold and keys if it is well formed with strong, distinct-enough keys; else None."""
    try:
        thr, hvec_h = parse_pol1(raw)
        pks = parse_hvec(atoms[hvec_h], require_sorted=True)
        for pk in pks:
            if weak_public_key(pk):
                return None
            _ed_dec(pk)
    except (VarsError, KeyError, ValueError):
        return None
    return (thr, pks) if len(set(pks)) >= thr else None


def kernel_facts(scope: str, trees: List[Tuple[Dict[bytes, bytes], Dict[bytes, "Cell"], Dict[bytes, "Seal"]]]) -> Tuple[bytes, List[bytes]]:
    """Encode a commit log as the rules kernel's input (§4.3): parsed cells, verified seals, POL1 rosters.

    Only parsing happens here: the order of cells, interned origins and keys, and edge lists as cell indices."""
    atoms, cells, seals = trees[-1]
    birth_c: Dict[bytes, int] = {}
    birth_s: Dict[bytes, int] = {}
    for i, (_, cs, ss) in enumerate(trees):
        for cid in cs:
            birth_c.setdefault(cid, i)
        for sid in ss:
            birth_s.setdefault(sid, i)
    order, _, _ = topo_order(cells, atoms)
    pos = {cid: i for i, cid in enumerate(order)}

    def origin(c: "Cell") -> str:
        return parse_utf8(atoms[c.h_slot_name]).split("/", 1)[0]

    origins = sorted({origin(c) for c in cells.values()} - {scope})
    origin_ix = {scope: 0, **{o: i + 1 for i, o in enumerate(origins)}}
    pols = {}
    for h, raw in atoms.items():
        if raw[:4] == b"POL1":
            got = strong_pol1(raw, atoms)
            if got is not None:
                pols[h] = got
    keys = sorted({pk for _, pks in pols.values() for pk in pks} | {s.actor_pubkey for s in seals.values()})
    key_ix = {k: i for i, k in enumerate(keys)}

    out = bytearray(struct.pack("<4I", len(trees), len(order), len(keys), len(pols)))
    for h in sorted(pols):
        thr, pks = pols[h]
        out += h + struct.pack(f"<{2 + len(pks)}I", thr, len(pks), *(key_ix[k] for k in pks))
    for cid in order:
        c = cells[cid]
        out += cid + c.h_schema + c.h_payload + c.h_slot_name + c.h_loss
        out += struct.pack("<3I", origin_ix[origin(c)], birth_c[cid], len(c.slots)) + b"".join(c.slots)
        for mh in (c.h_relies, c.h_attests, c.h_supersedes, c.h_retires, c.h_invalidates):
            items = [] if mh == H_EMPTY else parse_hvec(atoms[mh], require_sorted=True)
            out += struct.pack(f"<{1 + len(items)}I", len(items), *(pos[v] for v in items))
    out += struct.pack("<I", len(seals))
    for sid in sorted(seals):
        sl = seals[sid]
        out += struct.pack("<4I", pos[sl.h_target], pos[sl.h_scope_ctx], key_ix[sl.actor_pubkey], birth_s[sid])
    return bytes(out), order


# ---------------------------------------------------------------------------
# §3 Git Plumbing Store & Mandatory 5-Check Admission Gate
# ---------------------------------------------------------------------------
class GitVarsRepo:
    def __init__(self, repo_dir: Path | str):
        self.repo_dir = Path(repo_dir)
        self._blob_by_oid: Dict[str, bytes] = {}
        self._oid_by_raw: Dict[bytes, str] = {}

    def _git(self, *args: str, input_bytes: Optional[bytes] = None) -> bytes:
        res = subprocess.run(
            ["git", "-C", str(self.repo_dir), *args],
            input=input_bytes,
            capture_output=True,
            check=False,
        )
        if res.returncode != 0:
            raise VarsError(f"git {' '.join(args)} failed: {res.stderr.decode('utf-8', 'replace').strip()}")
        return res.stdout

    def ref_commit(self, scope: str) -> Optional[str]:
        res = subprocess.run(
            ["git", "-C", str(self.repo_dir), "rev-parse", "--verify", "-q", f"refs/vars/heads/{scope}"],
            capture_output=True,
            text=True,
            check=False,
        )
        return res.stdout.strip() if res.returncode == 0 else None

    def commit_chain(self, tip_commit: str) -> List[str]:
        out = self._git("rev-list", "--reverse", tip_commit).decode().splitlines()
        return [c.strip() for c in out if c.strip()]

    def read_cas_tree(self, commit_oid: str) -> Tuple[Dict[bytes, bytes], Dict[bytes, Cell], Dict[bytes, Seal]]:
        atoms: Dict[bytes, bytes] = {}
        cells: Dict[bytes, Cell] = {}
        seals: Dict[bytes, Seal] = {}
        ls = self._git("ls-tree", "-r", commit_oid).decode().splitlines()
        for line in ls:
            if not line.strip():
                continue
            meta, path = line.split("\t", 1)
            mode, _obj_type, oid = meta.split()
            if mode != "100644":
                raise VarsError(f"non-100644 mode {mode} at {path}")
            m = re.match(r"^cas/(atoms|cells|seals)/([0-9a-f]{2})/([0-9a-f]{62})$", path)
            if not m:
                raise VarsError(f"invalid cas path: {path}")
            kind_dir, aa, bb = m.groups()
            expected_h = bytes.fromhex(aa + bb)
            raw = self._blob_by_oid.get(oid)
            if raw is None:
                raw = self._git("cat-file", "blob", oid)
                self._blob_by_oid[oid] = raw
                self._oid_by_raw[raw] = oid
            if sha256(raw) != expected_h:
                raise VarsError(f"CAS SHA-256 mismatch at {path}")
            if kind_dir == "atoms":
                validate_atom(raw)
                atoms[expected_h] = raw
            elif kind_dir == "cells":
                cells[expected_h] = Cell.decode(raw)
            elif kind_dir == "seals":
                seals[expected_h] = Seal.decode(raw)
        return atoms, cells, seals

    def build_candidate_commit(
        self,
        scope: str,
        atoms: Dict[bytes, bytes],
        cells: Sequence[Cell],
        seals: Sequence[Seal],
        parent_commit: Optional[str] = None,
        extra_tree_entries: Optional[List[Tuple[str, str, str, bytes]]] = None,
    ) -> str:
        """Write blobs into Git and build a candidate commit (without updating the ref yet)."""
        base_atoms, base_cells, base_seals = ({}, {}, {})
        if parent_commit:
            base_atoms, base_cells, base_seals = self.read_cas_tree(parent_commit)

        all_atoms = dict(base_atoms)
        all_atoms.update(atoms)
        all_cells = {cid: c.encode() for cid, c in base_cells.items()}
        for c in cells:
            all_cells[c.id] = c.encode()
        all_seals = {sid: s.encode() for sid, s in base_seals.items()}
        for s in seals:
            all_seals[s.id] = s.encode()

        index_lines: List[str] = []

        def stage_entry(mode: str, path: str, data: bytes) -> None:
            oid = self._oid_by_raw.get(data)
            if oid is None:
                oid = self._git("hash-object", "-w", "--stdin", input_bytes=data).decode().strip()
                self._oid_by_raw[data] = oid
                self._blob_by_oid[oid] = data
            index_lines.append(f"{mode} blob {oid}\t{path}")

        for h, raw in sorted(all_atoms.items()):
            hx = h.hex()
            stage_entry("100644", f"cas/atoms/{hx[:2]}/{hx[2:]}", raw)
        for h, raw in sorted(all_cells.items()):
            hx = h.hex()
            stage_entry("100644", f"cas/cells/{hx[:2]}/{hx[2:]}", raw)
        for h, raw in sorted(all_seals.items()):
            hx = h.hex()
            stage_entry("100644", f"cas/seals/{hx[:2]}/{hx[2:]}", raw)
        for mode, _kind, path, data in extra_tree_entries or []:
            stage_entry(mode, path, data)

        # A private index per call: concurrent builders never share or delete each other's staging
        idx_dir = tempfile.mkdtemp(prefix="vars-idx-")
        env = {**subprocess.os.environ, "GIT_INDEX_FILE": str(Path(idx_dir) / "index")}
        try:
            res_idx = subprocess.run(
                ["git", "-C", str(self.repo_dir), "update-index", "--index-info"],
                input=("\n".join(index_lines) + "\n").encode("utf-8"),
                env=env,
                capture_output=True,
                check=False,
            )
            if res_idx.returncode != 0:
                raise VarsError(res_idx.stderr.decode())
            res_tree = subprocess.run(
                ["git", "-C", str(self.repo_dir), "write-tree"],
                env=env,
                capture_output=True,
                check=True,
            )
        finally:
            shutil.rmtree(idx_dir, ignore_errors=True)
        tree_oid = res_tree.stdout.decode().strip()
        cmd = ["commit-tree", tree_oid, "-m", f"vars({scope}): transition"]
        if parent_commit:
            cmd.extend(["-p", parent_commit])
        return self._git(*cmd).decode().strip()

    def admit_and_advance(self, scope: str, candidate_commit: str, expected_old: Optional[str]) -> None:
        """Run the §3.2 5-Check Admission Gate, then atomically advance `refs/vars/heads/<scope>`.

        Every refusal is a VarsError: an unexpected exception from malformed input is a refusal too,
        never a crash, and nothing is written before all checks pass."""
        try:
            self._admit_and_advance(scope, candidate_commit, expected_old)
        except VarsError:
            raise
        except (KeyError, IndexError, TypeError, ValueError, UnicodeDecodeError) as e:
            raise VarsError(f"malformed commit refused ({type(e).__name__}: {e})") from None

    def _admit_and_advance(self, scope: str, candidate_commit: str, expected_old: Optional[str]) -> None:
        actual_old = self.ref_commit(scope)
        if actual_old != expected_old:
            raise VarsError(f"CAS ref mismatch: expected {expected_old}, actual {actual_old}")

        # Check #1: Single-parent linear chain (or Genesis)
        cat_commit = self._git("cat-file", "commit", candidate_commit).decode()
        header = cat_commit.split("\n\n", 1)[0]  # the message may contain any line
        parents = [line.split()[1] for line in header.splitlines() if line.startswith("parent ")]
        if expected_old is None:
            if parents:
                raise VarsError("Check #1 failed: Genesis commit must have 0 parents")
        else:
            if parents != [expected_old]:
                raise VarsError(f"Check #1 failed: expected single parent {[expected_old]}, got {parents}")

        # Check #2: Strict append-only tree (`--no-renames --diff-filter=a` empty + mode 100644)
        if expected_old is not None:
            diff_out = self._git("diff-tree", "-r", "--no-renames", "--diff-filter=a", expected_old, candidate_commit)
            if diff_out.strip():
                raise VarsError(f"Check #2 failed: non-A tree changes:\n{diff_out.decode()}")

        # Check #3 & #4 & #5: Read and validate full CAS tree, references, replay, and authority fold
        atoms, cells, seals = self.read_cas_tree(candidate_commit)
        known = set(atoms.keys()) | set(cells.keys()) | INTRINSIC_HASHES

        def req_atom(h: bytes, desc: str) -> bytes:
            return atom_of(h, atoms, f"Check #4 failed: atom for {desc}")

        def origin_of(c: Cell) -> str:
            return parse_utf8(req_atom(c.h_slot_name, "H_slot_name")).split("/", 1)[0]

        def req_hvec_cells(src_cid: bytes, src_c: Cell, h: bytes, mname: str) -> List[bytes]:
            if h == H_EMPTY:
                return []
            items = parse_hvec(req_atom(h, mname), require_sorted=True)
            for item in items:
                if item not in cells:
                    raise VarsError(f"{mname} references non-Cell {item.hex()[:12]}")
                if item == src_cid:
                    raise VarsError(f"self-loop on {src_cid.hex()[:12]} in {mname}")
                target_c = cells[item]
                if mname == "supersedes" and target_c.h_schema != src_c.h_schema:
                    raise VarsError("cross-schema supersedes is forbidden")
                if mname == "attests" and target_c.h_schema not in (
                    H_SCHEMA["contract"],
                    H_SCHEMA["decision"],
                    H_SCHEMA["question"],
                ):
                    raise VarsError("attests target must be contract, decision, or question")
                if target_c.h_schema == H_SCHEMA["projection"]:
                    raise VarsError("a projection is an immutable historical fact: no edge may name it")
                if target_c.h_schema == H_SCHEMA["scope"] and not (
                    mname == "supersedes" and src_c.h_schema == H_SCHEMA["scope"]
                ):
                    raise VarsError("scope cell can only be superseded by another scope cell")
                if target_c.h_schema == H_SCHEMA["scope"] and origin_of(src_c) != origin_of(target_c):
                    raise VarsError("a scope cell can only be superseded by a scope cell of the same origin")
            return items

        # Validate every cell's references, edge types & deterministic replay (Check #3 & #4)
        replay_memo: Dict[bytes, str] = {}
        for cid, c in cells.items():
            slot_str = parse_utf8(req_atom(c.h_slot_name, "H_slot_name"))
            validate_slot_name(slot_str)
            if slot_str.startswith("core/schema.") and cid not in STD_SCHEMA_IDS:
                raise VarsError(f"slot name {slot_str!r} is reserved for intrinsic standard schemas")
            # Lean stage-1 finding: `<origin>/SCOPE` is reserved both ways, so a scope rotation can never take the
            # name of another binding (Rule 6 exempts scope cells) and no other cell can take a scope's name.
            is_scope_name = slot_str == f"{slot_str.split('/', 1)[0]}/SCOPE"
            if (c.h_schema == H_SCHEMA["scope"]) != is_scope_name:
                raise VarsError(f"reserved scope name: {slot_str!r} must be <origin>/SCOPE iff the cell is a schema.scope")
            if c.h_schema == H_SCHEMA["scope"] and len(c.slots) == 3 and c.slots[2] != H_LENS_KERNEL:
                raise VarsError("scope names rules this host does not implement (slots[2] != H_LENS_KERNEL)")
            if c.h_schema == H_META_SCHEMA:
                if c.h_payload != H_EMPTY or any(
                    m != H_EMPTY for m in (c.h_relies, c.h_attests, c.h_supersedes, c.h_retires, c.h_invalidates, c.h_loss)
                ):
                    raise VarsError("schema definition cell must have H_EMPTY payload and morphisms")
                for s_h in c.slots:
                    raw = req_atom(s_h, "schema slot descriptor")
                    validate_utf8_atom(raw)
                    fname, sep, ftype = parse_utf8(raw).partition(":")
                    if not fname or not sep or ftype not in FIELD_TYPES:
                        raise VarsError(f"schema field descriptor {parse_utf8(raw)!r} is not name:type of a known type")
                continue

            if c.h_schema not in cells or cells[c.h_schema].h_schema != H_META_SCHEMA:
                raise VarsError(f"Check #4 failed: H_schema {c.h_schema.hex()[:12]} is not a valid schema cell")
            if len(cells[c.h_schema].slots) != len(c.slots):
                raise VarsError("Check #3 failed: cell arity does not match schema arity")
            if c.h_payload not in known:
                raise VarsError("Check #4 failed: H_payload missing from CAS")
            if c.h_schema == H_SCHEMA["projection"] and any(
                m != H_EMPTY for m in (c.h_relies, c.h_attests, c.h_supersedes, c.h_retires, c.h_invalidates, c.h_loss)
            ):
                raise VarsError("a projection has no edges and no loss")
            if c.h_schema in (H_SCHEMA["acceptance"], H_SCHEMA["verdict"]) and c.h_payload not in cells:
                raise VarsError("Check #4 failed: ACCEPTANCE/VERDICT H_payload must be in cas/cells/")

            relies_ids = req_hvec_cells(cid, c, c.h_relies, "relies")
            req_hvec_cells(cid, c, c.h_attests, "attests")
            req_hvec_cells(cid, c, c.h_supersedes, "supersedes")
            req_hvec_cells(cid, c, c.h_retires, "retires")
            req_hvec_cells(cid, c, c.h_invalidates, "invalidates")

            if c.h_loss != H_EMPTY:
                loss_raw = req_atom(c.h_loss, "H_loss")
                validate_utf8_atom(loss_raw)
                if not (1 <= len(loss_raw) - 4 <= MAX_LOSS_BYTES):
                    raise VarsError("H_loss exceeds 4096 bytes")

            digest_slots = {
                i for i, d in enumerate(cells[c.h_schema].slots)
                if d in atoms and parse_utf8(atoms[d]).endswith(":digest")
            }
            for i, s_h in enumerate(c.slots):
                if i not in digest_slots and s_h not in known:
                    raise VarsError(f"Check #4 failed: slot {s_h.hex()[:12]} missing from CAS")
            # every slot must have the type its schema field declares ("name:type")
            for s_h, desc_h in zip(c.slots, cells[c.h_schema].slots):
                fname, _, ftype = parse_utf8(req_atom(desc_h, "schema field descriptor")).partition(":")
                if s_h == H_EMPTY and fname in OPTIONAL_FIELDS:
                    continue
                check_slot_type(s_h, ftype, atoms, cells)

            # Payloads and enumerations by kind (§2 "Payloads and meaning")
            if c.h_schema in (H_SCHEMA["axiom"], H_SCHEMA["contract"], H_SCHEMA["decision"], H_SCHEMA["question"],
                              H_SCHEMA["scope"]) and c.h_payload not in INTRINSIC_UTF8:
                check_slot_type(c.h_payload, "utf8", atoms, cells)
            if c.h_schema == H_SCHEMA["computation"]:
                _load_root_and_env(c.h_payload, atoms)
            if c.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]) and c.slots[0] not in (H_PROVISIONAL, H_OWNER):
                raise VarsError("tier must be H_PROVISIONAL or H_OWNER")
            if c.h_schema == H_SCHEMA["projection"] and c.h_payload != H_EMPTY:
                raise VarsError("a projection's payload is H_EMPTY")
            if c.h_schema == H_SCHEMA["verdict"]:
                if c.slots[1] not in VERDICT_CODES:
                    raise VarsError("verdict_code is not one of REPLAYED, ATTESTED, INVALID, NOT_ASSESSED")
                if c.slots[1] == H_ATTESTED and c.slots[0] != H_EMPTY:
                    raise VarsError("an ATTESTED verdict has an empty ckpt_or_witness")


            # Kind-specific structural & deterministic replay invariants
            if c.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]):
                if c.slots[1] != H_EMPTY:
                    if not any(
                        cells[r].h_schema == H_SCHEMA["computation"] and cells[r].h_payload == c.slots[1]
                        for r in relies_ids
                    ):
                        raise VarsError(
                            "contract/decision with non-empty required_comp must rely on a matching computation cell"
                        )
            elif c.h_schema == H_SCHEMA["checkpoint"]:
                sgs1 = req_atom(c.h_payload, "checkpoint SGS1")
                if sgs1[:4] != b"SGS1" or sgs1[4:36] != c.slots[0]:
                    raise VarsError("Check #4 failed: SGS1 computation_id != CHECKPOINT.slots[0]")
                if c.h_supersedes != H_EMPTY:
                    raise VarsError("CHECKPOINT must chain via H_relies, never H_supersedes")
                verify_checkpoint_replay(c, atoms, cells, gate_mode=True, memo=replay_memo)
            elif c.h_schema == H_SCHEMA["cycle_witness"]:
                actions = parse_u64(req_atom(c.slots[2], "cycle_actions"))
                cost = parse_u64(req_atom(c.slots[3], "cycle_cost"))
                if actions < 1 or cost < actions:
                    raise VarsError("CYCLE_WITNESS requires actions >= 1 and cost >= actions")
                verify_cycle_witness_replay(c, atoms, gate_mode=True)
            elif c.h_schema == H_SCHEMA["verdict"]:
                if c.slots[0] == H_EMPTY and c.slots[1] == H_REPLAYED:
                    raise VarsError("VERDICT with H_EMPTY checkpoint must use H_ATTESTED, not H_REPLAYED")
                if c.slots[0] != H_EMPTY and c.slots[0] not in relies_ids:
                    raise VarsError("VERDICT with non-empty ckpt_or_witness must include it in H_relies")
                if c.slots[0] != H_EMPTY and cells[c.slots[0]].h_schema not in (H_SCHEMA["checkpoint"],
                                                                                H_SCHEMA["cycle_witness"]):
                    raise VarsError("a verdict's ckpt_or_witness is a checkpoint or cycle witness")
                if c.slots[1] != H_VERDICT_INVALID and cells[c.h_payload].h_schema not in (
                        H_SCHEMA["contract"], H_SCHEMA["decision"], H_SCHEMA["question"]):
                    raise VarsError("only an INVALID verdict may judge a cell other than a contract, decision or question")
            elif c.h_schema == H_SCHEMA["acceptance"]:
                target_origin = parse_utf8(req_atom(cells[c.h_payload].h_slot_name, "target slot")).split("/", 1)[0]
                src_scope = parse_utf8(req_atom(c.slots[0], "source_scope"))
                if src_scope != target_origin or src_scope == scope:
                    raise VarsError("ACCEPTANCE source_scope does not match foreign target cell origin")
                sf_id = c.slots[1]
                if sf_id not in cells or cells[sf_id].h_schema != H_SCHEMA["scope"]:
                    raise VarsError("ACCEPTANCE slots[1] must reference a foreign schema.scope cell")
                sf_origin = parse_utf8(req_atom(cells[sf_id].h_slot_name, "foreign scope slot")).split("/", 1)[0]
                if sf_origin != src_scope:
                    raise VarsError("ACCEPTANCE foreign_scope_cell origin mismatch")

        for sid, s in seals.items():
            if s.h_target not in cells or s.h_scope_ctx not in cells:
                raise VarsError("Check #4 failed: Seal target or scope_ctx missing from cas/cells/")

        prior_cells = self.read_cas_tree(expected_old)[1] if expected_old is not None else {}
        prior = set(prior_cells)
        # References never point forward in time (§4.3): the rules read any payload or slot equal to a cell id as
        # a reference, so a new cell may not have an id that an older cell already names there
        named_before = {x for pc in prior_cells.values() for x in (pc.h_payload, *pc.slots)}
        for cid in set(cells) - prior:
            if cid in named_before:
                raise VarsError(f"an older cell names {cid.hex()[:12]} in a payload or slot: a reference to a later-born cell")

        # Projections: the gate recomputes the rules at the named tip and refuses any digest that differs
        chain = set(self.commit_chain(expected_old)) if expected_old is not None else set()
        for cid, c in cells.items():
            if c.h_schema != H_SCHEMA["projection"] or cid in prior:
                continue
            tip = parse_utf8(req_atom(c.slots[0], "projection tip"))
            if tip not in chain:
                raise VarsError(f"projection tip {tip[:12]} is not a commit of refs/vars/heads/{scope} before this one")
            if c.slots[1] != H_LENS_KERNEL:
                raise VarsError("projection names rules this host does not implement")
            h_in, h_state = self.projection_digests(scope, tip)
            if (c.slots[2], c.slots[3]) != (h_in, h_state):
                raise VarsError("projection digests differ from the gate's recomputation of the rules at its tip")

        # Run the commit-chain fold to verify admission authority on the new commit
        self._evaluate_commit_chain(scope, self.commit_chain(candidate_commit))

        # Atomic compare-and-swap update-ref
        cmd = ["update-ref", f"refs/vars/heads/{scope}", candidate_commit]
        if expected_old is not None:
            cmd.append(expected_old)
        else:
            cmd.append("0" * 40)
        self._git(*cmd)

    # -----------------------------------------------------------------------
    # §4 Commit-Chain Fold & Three-Pass Lensing
    # -----------------------------------------------------------------------
    def projection_digests(self, scope: str, tip: str) -> Tuple[bytes, bytes]:
        """`(sha256(kernel input), sha256(kernel output))` for the scope's chain up to and including `tip`: the
        `input` and `state` a projection at `tip` must carry. Anyone holding the chain can recompute them."""
        trees = [self.read_cas_tree(c) for c in self.commit_chain(tip)]
        kernel_input, _ = kernel_facts(scope, trees)
        return sha256(kernel_input), sha256(kernel_runner().run(kernel_input))

    def _evaluate_commit_chain(self, scope: str, commits: List[str]) -> Dict[str, object]:
        """§4.1 fold. The rules kernel decides authority; `_fold_twin` recomputes it in Python and must agree."""
        trees = [self.read_cas_tree(c) for c in commits]
        try:
            twin, twin_err = self._fold_twin(scope, trees), None
        except VarsError as e:
            twin, twin_err = None, e
        kernel_input, order = kernel_facts(scope, trees)
        try:
            out = kernel_runner().run(kernel_input)
        except KernelRefusal as e:
            if twin_err is None:
                raise TwinDivergence(f"{e}, but the host fold admits the commit log") from None
            raise VarsError(f"{twin_err} [{e}]") from None
        if twin_err is not None:
            raise TwinDivergence(f"host fold refused ({twin_err}) but the rules kernel admits the commit log")
        cells: Dict[bytes, Cell] = twin["cells"]
        atoms: Dict[bytes, bytes] = twin["atoms"]
        n = len(order)
        status, auth, flags = out[4:4 + n], out[4 + n:4 + 2 * n], iter(out[4 + 2 * n:])
        kernel = {
            "active_scope_id": order[int.from_bytes(out[:4], "little")],
            "latched_scope_auth": {cid for i, cid in enumerate(order) if auth[i] and cells[cid].h_schema == H_SCHEMA["scope"]},
            "latched_acc_auth": {cid for i, cid in enumerate(order) if auth[i] and cells[cid].h_schema == H_SCHEMA["acceptance"]},
            "latched_schema_auth": {cid for i, cid in enumerate(order) if auth[i] and cells[cid].h_schema == H_META_SCHEMA},
            "latched_edge_auth": set(),
        }
        for wid in order:
            w = cells[wid]
            for kind, mh in (("invalidates", w.h_invalidates), ("retires", w.h_retires), ("supersedes", w.h_supersedes)):
                for vid in [] if mh == H_EMPTY else parse_hvec(atoms[mh], require_sorted=True):
                    if next(flags):
                        kernel["latched_edge_auth"].add((wid, vid, kind))
        for k, v in kernel.items():
            if twin[k] != v:
                raise TwinDivergence(f"rules kernel and host fold disagree on {k}")
        return {
            **twin,
            **kernel,
            "kernel_input": kernel_input,
            "kernel_order": order,
            "kernel_status": {cid: {name: bool(status[i] >> b & 1) for b, name in enumerate(KERNEL_BITS)}
                              for i, cid in enumerate(order)},
        }

    def _fold_twin(self, scope: str, trees: List[Tuple[Dict[bytes, bytes], Dict[bytes, Cell], Dict[bytes, Seal]]]) -> Dict[str, object]:
        """The host's differential twin of the kernel fold (§4.1), plus the endorser sets Pass 3 needs."""
        latched_scope_auth: Set[bytes] = set()
        latched_acc_auth: Set[bytes] = set()
        latched_schema_auth: Set[bytes] = set(STD_SCHEMA_IDS)
        latched_edge_auth: Set[Tuple[bytes, bytes, str]] = set()
        initial_endorsers: Dict[bytes, Set[bytes]] = {}
        cumulative_endorsers: Dict[bytes, Set[bytes]] = {}
        foreign_endorsers_by_scope: Dict[Tuple[bytes, bytes], Set[bytes]] = {}
        self_sealed_foreign_scopes: Set[bytes] = set()
        seen_cells: Set[bytes] = set()
        seen_seals: Set[bytes] = set()
        active_scope_id: Optional[bytes] = None

        for idx, (atoms, cells, seals) in enumerate(trees):

            def pol_quorum(pol_hash: bytes) -> Tuple[int, Set[bytes]]:
                thr, hvec_h = parse_pol1(atoms[pol_hash])
                pks_list = parse_hvec(atoms[hvec_h], require_sorted=True)
                for pk in pks_list:
                    if weak_public_key(pk):
                        raise VarsError("weak or non-canonical Ed25519 public key in POL1")
                    try:
                        _ed_dec(pk)
                    except ValueError as e:
                        raise VarsError(f"invalid Ed25519 curve point in POL1: {e}") from None
                pks = set(pks_list)
                if len(pks) < thr:
                    raise VarsError("POL1 threshold exceeds pubkey count")
                return thr, pks

            def cell_origin(c: Cell) -> str:
                return parse_utf8(atoms[c.h_slot_name]).split("/", 1)[0]

            def hvec_items(h: bytes) -> List[bytes]:
                return [] if h == H_EMPTY else parse_hvec(atoms[h], require_sorted=True)

            new_cids = set(cells.keys()) - seen_cells
            new_sids = set(seals.keys()) - seen_seals

            if idx == 0:
                local_scopes = [
                    cid for cid in new_cids if cells[cid].h_schema == H_SCHEMA["scope"] and cell_origin(cells[cid]) == scope
                ]
                if len(local_scopes) != 1:
                    raise VarsError("Genesis commit must contain exactly one local schema.scope cell")
                active_scope_id = local_scopes[0]
                s0 = cells[active_scope_id]
                if (
                    s0.h_supersedes != H_EMPTY
                    or s0.h_retires != H_EMPTY
                    or s0.h_invalidates != H_EMPTY
                    or s0.h_loss != H_EMPTY
                ):
                    raise VarsError("Genesis scope cell must have empty eviction slots")
                thr0, pks0 = pol_quorum(s0.slots[0])
                pol_quorum(s0.slots[1])
                s0_signers = {
                    seals[sid].actor_pubkey
                    for sid in new_sids
                    if seals[sid].h_target == active_scope_id
                    and seals[sid].h_scope_ctx == active_scope_id
                    and seals[sid].actor_pubkey in pks0
                }
                if len(s0_signers) < thr0:
                    raise VarsError("Genesis scope cell lacks admission quorum seals")
                latched_scope_auth.add(active_scope_id)

            assert active_scope_id is not None
            # Keep s_base_id fixed for the entire commit evaluation
            s_base_id = active_scope_id
            s_base = cells[s_base_id]
            adm_thr, adm_pks = pol_quorum(s_base.slots[0])
            acc_thr, acc_pks = pol_quorum(s_base.slots[1])

            # Self-sealed foreign scopes present in cas/cells/
            valid_foreign_scopes: Dict[str, List[Tuple[bytes, Set[bytes]]]] = {}
            for scid, sc in cells.items():
                if sc.h_schema == H_SCHEMA["scope"] and cell_origin(sc) != scope:
                    f_origin = cell_origin(sc)
                    f_thr, f_pks = pol_quorum(sc.slots[0])
                    pol_quorum(sc.slots[1])
                    f_signers = {
                        seals[sid].actor_pubkey
                        for sid in seals
                        if seals[sid].h_target == scid
                        and seals[sid].h_scope_ctx == scid
                        and seals[sid].actor_pubkey in f_pks
                    }
                    if len(f_signers) >= f_thr:
                        self_sealed_foreign_scopes.add(scid)
                        valid_foreign_scopes.setdefault(f_origin, []).append((scid, f_pks))

            # foreign endorsements accumulate the same way. Recount every foreign cell against each
            # self-sealed scope of its origin, so a foreign co-signature added later is not ignored.
            for fcid, fc in cells.items():
                if fcid in STD_SCHEMA_IDS or cell_origin(fc) == scope:
                    continue
                for sf_id, sf_pks in valid_foreign_scopes.get(cell_origin(fc), []):
                    foreign_endorsers_by_scope[(fcid, sf_id)] = {
                        seals[sid].actor_pubkey
                        for sid in seals
                        if seals[sid].h_target == fcid
                        and seals[sid].h_scope_ctx == sf_id
                        and seals[sid].actor_pubkey in sf_pks
                    }

            # Check #3: Every new local seal must bind to s_base_id and be signed by a roster member
            for sid in new_sids:
                s = seals[sid]
                target_c = cells[s.h_target]
                ctx_c = cells[s.h_scope_ctx]
                local_ctx = ctx_c.h_schema == H_SCHEMA["scope"] and cell_origin(ctx_c) == scope
                if cell_origin(target_c) != scope and local_ctx:
                    # Cross-seal: a local roster member endorses a foreign cell (its only route to local edge authority)
                    if s.h_scope_ctx != s_base_id or s.actor_pubkey not in adm_pks:
                        raise VarsError("Cross-seal on a foreign cell must use the active SCOPE and a roster key")
                if cell_origin(target_c) == scope:
                    if s.h_scope_ctx != s_base_id:
                        raise VarsError("Local seal H_scope_ctx does not match active SCOPE")
                    allowed = adm_pks | (acc_pks if target_c.h_schema == H_SCHEMA["acceptance"] else set())
                    if target_c.h_schema == H_SCHEMA["projection"]:
                        allowed = allowed | pol_quorum(target_c.slots[4])[1]  # its witnesses, roster or not (§4.4)
                    if s.actor_pubkey not in allowed:
                        raise VarsError("Local seal signer not in active SCOPE policy")
                    # an admitted local seal is an endorsement for good. It was checked against the scope
                    # active at its own commit, so a late co-signature counts exactly like a birth signature.
                    cumulative_endorsers.setdefault(s.h_target, set()).add(s.actor_pubkey)

            # Check #3: every new non-standard cell must carry valid seals
            for cid in new_cids:
                if cid in STD_SCHEMA_IDS:
                    continue
                c = cells[cid]
                c_orig = cell_origin(c)
                if c_orig == scope:
                    # writing a cell, and InitialEndorsers, count roster keys only (a projection's outside witnesses
                    # sign it, they do not write it)
                    roster = adm_pks | (acc_pks if c.h_schema == H_SCHEMA["acceptance"] else set())
                    c_signers = {
                        seals[sid].actor_pubkey
                        for sid in seals
                        if seals[sid].h_target == cid and seals[sid].h_scope_ctx == s_base_id
                        and seals[sid].actor_pubkey in roster
                    }
                    if not c_signers:
                        raise VarsError(f"New local cell {cid.hex()[:12]} lacks a valid Seal under active SCOPE")
                    initial_endorsers[cid] = set(c_signers)
                    # Check POL1 subset rule
                    pol_slot = None
                    if c.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]):
                        pol_slot = c.slots[3]
                    elif c.h_schema == H_SCHEMA["question"]:
                        pol_slot = c.slots[1]
                    if pol_slot and pol_slot != H_EMPTY:
                        _, custom_pks = pol_quorum(pol_slot)
                        if not custom_pks.issubset(adm_pks):
                            raise VarsError("local cell evaluator policy pubkeys not a subset of scope roster")

                else:
                    # A foreign cell must belong to a self-sealed foreign scope in cas/cells/
                    f_scopes = valid_foreign_scopes.get(c_orig, [])
                    if not f_scopes:
                        raise VarsError(f"foreign cell {cid.hex()[:12]} from {c_orig!r} lacks self-sealed foreign SCOPE")
                    f_ends_union: Set[bytes] = set()
                    for sf_id, sf_pks in f_scopes:
                        sf_ends = {
                            seals[sid].actor_pubkey
                            for sid in seals
                            if seals[sid].h_target == cid
                            and seals[sid].h_scope_ctx == sf_id
                            and seals[sid].actor_pubkey in sf_pks
                        }
                        f_ends_union |= sf_ends
                    initial_endorsers[cid] = f_ends_union

            # Strictly epoch-scoped endorsers under s_base_id
            def endorsers_under_base(cid: bytes, allowed_pks: Set[bytes]) -> Set[bytes]:
                return {
                    seals[sid].actor_pubkey
                    for sid in seals
                    if seals[sid].h_target == cid
                    and seals[sid].h_scope_ctx == s_base_id
                    and seals[sid].actor_pubkey in allowed_pks
                }

            # At most one new local schema.scope cell in any transition commit
            pending_next_scope: Optional[bytes] = None
            if idx >= 1:
                new_local_scopes = [
                    cid for cid in new_cids if cells[cid].h_schema == H_SCHEMA["scope"] and cell_origin(cells[cid]) == scope
                ]
                if len(new_local_scopes) > 1:
                    raise VarsError("multiple local schema.scope cells introduced in a single commit")
                if len(new_local_scopes) == 1:
                    s_next_id = new_local_scopes[0]
                    s_next = cells[s_next_id]
                    pol_quorum(s_next.slots[0])
                    pol_quorum(s_next.slots[1])
                    if (
                        hvec_items(s_next.h_supersedes) != [s_base_id]
                        or s_next.h_retires != H_EMPTY
                        or s_next.h_invalidates != H_EMPTY
                    ):
                        raise VarsError("new schema.scope cell must supersede active SCOPE only")
                    if len(endorsers_under_base(s_next_id, adm_pks)) < adm_thr:
                        raise VarsError("new schema.scope cell lacks admission quorum under active SCOPE")
                    pending_next_scope = s_next_id

            # Latch ACCEPTANCE (pinned to a self-sealed foreign scope per §2.5) and custom META_SCHEMA cells
            for cid, c in cells.items():
                if cell_origin(c) != scope:
                    continue
                if c.h_schema == H_SCHEMA["acceptance"] and cid not in latched_acc_auth:
                    if c.slots[1] not in self_sealed_foreign_scopes:
                        raise VarsError("ACCEPTANCE foreign_scope_cell is not self-sealed")
                    if len(endorsers_under_base(cid, acc_pks)) >= acc_thr:
                        latched_acc_auth.add(cid)
                elif c.h_schema == H_META_SCHEMA and cid not in latched_schema_auth:
                    if len(endorsers_under_base(cid, adm_pks)) >= adm_thr:
                        latched_schema_auth.add(cid)

            # Latch eviction / invalidation edges under s_base
            for wid, w in cells.items():
                if w.h_schema == H_META_SCHEMA:
                    continue
                w_ends_adm = endorsers_under_base(wid, adm_pks)
                w_ends_acc = endorsers_under_base(wid, acc_pks)
                for edge_kind, mh in (
                    ("invalidates", w.h_invalidates),
                    ("retires", w.h_retires),
                    ("supersedes", w.h_supersedes),
                ):
                    for vid in hvec_items(mh):
                        if (wid, vid, edge_kind) in latched_edge_auth:
                            continue
                        v = cells[vid]
                        # Total Governing Policy Function Pol_i(v) & AuthorCanEvict(v)
                        if v.h_schema == H_SCHEMA["scope"] or (
                            v.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]) and v.slots[0] == H_OWNER
                        ):
                            p_thr, p_pks, w_ends = adm_thr, adm_pks, w_ends_adm
                            author_can = False
                        elif v.h_schema == H_SCHEMA["acceptance"]:
                            p_thr, p_pks, w_ends = acc_thr, acc_pks, w_ends_acc
                            author_can = False
                        elif v.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]) and v.slots[0] == H_PROVISIONAL:
                            p_thr, p_pks = pol_quorum(v.slots[3]) if v.slots[3] != H_EMPTY else (adm_thr, adm_pks)
                            w_ends = w_ends_adm
                            author_can = True
                        elif v.h_schema == H_SCHEMA["question"]:
                            p_thr, p_pks = pol_quorum(v.slots[1]) if v.slots[1] != H_EMPTY else (adm_thr, adm_pks)
                            w_ends = w_ends_adm
                            author_can = True
                        else:
                            p_thr, p_pks, w_ends = adm_thr, adm_pks, w_ends_adm
                            author_can = True

                        quorum_ok = len(w_ends & p_pks) >= p_thr
                        author_ok = (
                            edge_kind in ("supersedes", "retires")
                            and author_can
                            and cell_origin(v) == scope  # foreign birth signers are not local authors
                            and bool(w_ends & initial_endorsers.get(vid, set()))
                        )
                        if quorum_ok or author_ok:
                            latched_edge_auth.add((wid, vid, edge_kind))

            # unique binding per H_slot_name, checked after this commit's authorization latch.
            # Every new local cell c (except a scope cell, which has its own single-lineage rule) must reach every
            # other local cell bound to the same name through supersedes edges: c's own first hop may still await
            # co-signatures (c stays inactive until all its supersedes edges latch), every later hop must already be
            # latched. Latches never unlatch and Superseded is transitive in Pass 1, so at most one binding is Active.
            latched_sup: Dict[bytes, Set[bytes]] = {}
            for e_w, e_v, e_kind in latched_edge_auth:
                if e_kind == "supersedes":
                    latched_sup.setdefault(e_w, set()).add(e_v)
            any_sup: Dict[bytes, Set[bytes]] = {oid: set(hvec_items(oc.h_supersedes)) for oid, oc in cells.items()}

            def sup_reach(src: bytes, adj: Dict[bytes, Set[bytes]]) -> Set[bytes]:
                out: Set[bytes] = set()
                todo = list(adj.get(src, ()))
                while todo:
                    nxt = todo.pop()
                    if nxt not in out:
                        out.add(nxt)
                        todo.extend(adj.get(nxt, ()))
                return out

            bound_by_name: Dict[bytes, List[bytes]] = {}
            for oid, oc in cells.items():
                if oid not in STD_SCHEMA_IDS and cell_origin(oc) == scope:
                    bound_by_name.setdefault(oc.h_slot_name, []).append(oid)
            for cid in sorted(new_cids):
                c = cells[cid]
                if cid in STD_SCHEMA_IDS or cell_origin(c) != scope or c.h_schema == H_SCHEMA["scope"]:
                    continue
                peers = [oid for oid in bound_by_name.get(c.h_slot_name, []) if oid != cid]
                if not peers:
                    continue
                def binding_reach(src: bytes) -> Set[bytes]:
                    first = set(hvec_items(cells[src].h_supersedes))
                    out = set(first)
                    for hop in first:
                        out |= sup_reach(hop, latched_sup)
                    return out

                reach_c = binding_reach(cid)
                for oid in peers:
                    if oid in reach_c:
                        continue
                    if oid in new_cids and cid in binding_reach(oid):
                        continue  # same-commit pair: the other cell is the newer binding
                    slot = parse_utf8(atoms[c.h_slot_name])
                    linked = oid in sup_reach(cid, any_sup) or any(
                        oid in hvec_items(m) for m in (c.h_retires, c.h_invalidates)
                    )
                    if linked:
                        raise VarsError(
                            f"binding of slot {slot!r} does not reach the prior binding "
                            f"{oid.hex()[:12]} through authorized supersedes edges"
                        )
                    raise VarsError(f"duplicate unlinked binding for slot {slot!r}")

            # End-of-commit scope transition
            if pending_next_scope is not None:
                latched_scope_auth.add(pending_next_scope)
                active_scope_id = pending_next_scope

            seen_cells |= new_cids
            seen_seals |= new_sids

        return {
            "atoms": atoms,
            "cells": cells,
            "seals": seals,
            "active_scope_id": active_scope_id,
            "latched_scope_auth": latched_scope_auth,
            "latched_acc_auth": latched_acc_auth,
            "latched_schema_auth": latched_schema_auth,
            "latched_edge_auth": latched_edge_auth,
            "initial_endorsers": initial_endorsers,
            "cumulative_endorsers": cumulative_endorsers,
            "foreign_endorsers_by_scope": foreign_endorsers_by_scope,
        }

    def lens(self, scope: str) -> Dict[str, object]:
        tip = self.ref_commit(scope)
        if tip is None:
            raise VarsError(f"no ref refs/vars/heads/{scope}")
        fold = self._evaluate_commit_chain(scope, self.commit_chain(tip))
        atoms: Dict[bytes, bytes] = fold["atoms"]
        cells: Dict[bytes, Cell] = fold["cells"]
        latched_scope_auth: Set[bytes] = fold["latched_scope_auth"]
        latched_acc_auth: Set[bytes] = fold["latched_acc_auth"]
        latched_schema_auth: Set[bytes] = fold["latched_schema_auth"]
        latched_edge_auth: Set[Tuple[bytes, bytes, str]] = fold["latched_edge_auth"]
        cumulative_endorsers: Dict[bytes, Set[bytes]] = fold["cumulative_endorsers"]
        foreign_endorsers_by_scope: Dict[Tuple[bytes, bytes], Set[bytes]] = fold["foreign_endorsers_by_scope"]
        active_scope_id: bytes = fold["active_scope_id"]
        s_active = cells[active_scope_id]

        def hvec_items(h: bytes) -> List[bytes]:
            return [] if h == H_EMPTY else parse_hvec(atoms[h], require_sorted=True)

        def cell_origin(c: Cell) -> str:
            return parse_utf8(atoms[c.h_slot_name]).split("/", 1)[0]

        forward_order, parents_of, children_of = topo_order(cells, atoms)
        reverse_order = list(reversed(forward_order))

        # Pass 1 (Reverse-Topological: newest/sinks -> oldest/sources)
        accepted: Dict[bytes, bool] = {}
        accepted_scopes: Dict[bytes, Set[bytes]] = {cid: set() for cid in cells}
        invalidated: Dict[bytes, bool] = {}
        effective: Dict[bytes, bool] = {}
        retired: Dict[bytes, bool] = {}
        superseded: Dict[bytes, bool] = {}
        active: Dict[bytes, bool] = {}

        for cid in reverse_order:
            c = cells[cid]
            c_orig = cell_origin(c)
            if cid in STD_SCHEMA_IDS or c_orig == scope:
                accepted[cid] = True
            else:
                direct_scopes = {
                    cells[ch].slots[1]
                    for ch in children_of[cid]
                    if ch in active and active[ch]
                    and cells[ch].h_schema == H_SCHEMA["acceptance"]
                    and ch in latched_acc_auth
                    and cells[ch].h_payload == cid
                }
                # Hereditary acceptance bounded to the same foreign origin scope
                hereditary_scopes: Set[bytes] = set()
                for ch in children_of[cid]:
                    if ch in accepted and accepted[ch] and cell_origin(cells[ch]) == c_orig:
                        hereditary_scopes |= accepted_scopes[ch]
                accepted_scopes[cid] = direct_scopes | hereditary_scopes
                accepted[cid] = bool(accepted_scopes[cid])

            inv = any(
                w in effective and effective[w] and accepted.get(w, False)
                and cid in hvec_items(cells[w].h_invalidates)
                and (w, cid, "invalidates") in latched_edge_auth
                and (cells[w].h_schema != H_SCHEMA["verdict"] or cells[w].slots[1] == H_VERDICT_INVALID)
                for w in children_of[cid]
            )
            invalidated[cid] = inv
            effective[cid] = not inv

            ret = any(
                w in effective and effective[w] and accepted.get(w, False)
                and cid in hvec_items(cells[w].h_retires)
                and (w, cid, "retires") in latched_edge_auth
                for w in children_of[cid]
            )
            # supersession is transitive along authorized supersedes edges. v is Superseded if some
            # Effective and Accepted cell reaches it, even when an intermediate replacement was invalidated.
            sup = any(
                cid in hvec_items(cells[w].h_supersedes)
                and (w, cid, "supersedes") in latched_edge_auth
                and ((effective.get(w, False) and accepted.get(w, False)) or superseded.get(w, False))
                for w in children_of[cid]
            )
            # A replacement cell with non-empty `supersedes` is only Active once all its supersedes edges are authorized
            sup_edges_authorized = all(
                (cid, vid, "supersedes") in latched_edge_auth for vid in hvec_items(c.h_supersedes)
            )
            retired[cid] = ret
            superseded[cid] = sup
            active[cid] = effective[cid] and not ret and not sup and accepted[cid] and sup_edges_authorized

        # Pass 2 (Forward-Topological LFP: oldest/sources -> newest/sinks, fixing ,  & )
        # iterate to the least fixed point, never a fixed number of rounds. The round operator is monotone:
        # dependency staleness grows with `stale`, and LiveAcceptedScopes only shrinks as `stale` grows, so from
        # all-False every round only flips False -> True. At most |cells| rounds change something; one more confirms.
        stale: Dict[bytes, bool] = {cid: False for cid in cells}
        live_accepted_scopes: Dict[bytes, Set[bytes]] = {cid: set() for cid in cells}
        for _round in range(len(cells) + 1):
            live_accepted_scopes = {cid: set() for cid in cells}
            for cid in reverse_order:
                c = cells[cid]
                c_orig = cell_origin(c)
                if cid in STD_SCHEMA_IDS or c_orig == scope:
                    continue
                direct_live = {
                    cells[ch].slots[1]
                    for ch in children_of[cid]
                    if active.get(ch, False)
                    and not stale.get(ch, False)
                    and cells[ch].h_schema == H_SCHEMA["acceptance"]
                    and ch in latched_acc_auth
                    and cells[ch].h_payload == cid
                }
                hereditary_live: Set[bytes] = set()
                for ch in children_of[cid]:
                    if live_accepted_scopes.get(ch) and cell_origin(cells[ch]) == c_orig:
                        hereditary_live |= live_accepted_scopes[ch]
                live_accepted_scopes[cid] = direct_live | hereditary_live

            changed = False
            for cid in forward_order:
                if not active[cid]:
                    new_st = False
                else:
                    deps = hvec_items(cells[cid].h_relies)
                    dep_st = any(not active.get(d, False) or stale.get(d, False) for d in deps)
                    foreign_st = (
                        cid not in STD_SCHEMA_IDS
                        and cell_origin(cells[cid]) != scope
                        and not bool(live_accepted_scopes.get(cid))
                    )
                    new_st = dep_st or foreign_st
                if new_st != stale[cid]:
                    if stale[cid]:
                        raise VarsError("Pass 2 is not monotone (a cell went from Stale back to non-Stale)")
                    stale[cid] = new_st
                    changed = True
            if not changed:
                break
        else:
            raise VarsError("Pass 2 did not reach its fixed point within |cells| + 1 rounds")

        # The rules kernel computed Passes 1-2; the Python passes above are its differential twin.
        kst: Dict[bytes, Dict[str, bool]] = fold["kernel_status"]
        twin_st = {"accepted": accepted, "invalidated": invalidated, "effective": effective, "retired": retired,
                   "superseded": superseded, "active": active, "stale": stale}
        if fold["kernel_order"] != forward_order:
            raise TwinDivergence("rules kernel and host lens order cells differently")
        for cid in forward_order:
            for name in KERNEL_BITS:
                if kst[cid][name] != twin_st[name][cid]:
                    raise TwinDivergence(f"rules kernel and host lens disagree on {name} of {cid.hex()[:12]}")
        accepted, invalidated, effective, retired, superseded, active, stale = (
            {cid: kst[cid][name] for cid in forward_order} for name in KERNEL_BITS)

        # Pass 3 (Constructive Maximal Witness Set W_max -> Settled vs Provisional)
        def pol_quorum(pol_hash: bytes) -> Tuple[int, Set[bytes]]:
            thr, hvec_h = parse_pol1(atoms[pol_hash])
            return thr, set(parse_hvec(atoms[hvec_h], require_sorted=True))

        adm_thr, adm_pks = pol_quorum(s_active.slots[0])
        lens_replay_memo: Dict[bytes, str] = {}
        settled: Dict[bytes, bool] = {}
        provisional: Dict[bytes, bool] = {}

        def witness_endorsers(wid: bytes) -> Set[bytes]:
            w_cell = cells[wid]
            if cell_origin(w_cell) == scope:
                return cumulative_endorsers.get(wid, set())  # late co-signatures count
            out_ends: Set[bytes] = set()
            for sf_id in live_accepted_scopes.get(wid, set()):
                out_ends |= foreign_endorsers_by_scope.get((wid, sf_id), set())
            return out_ends

        for cid in forward_order:
            c = cells[cid]
            if not active[cid] or stale[cid]:
                settled[cid] = False
                provisional[cid] = False
                continue
            if c.h_schema == H_META_SCHEMA:
                is_auth = cid in latched_schema_auth
                settled[cid] = is_auth
                provisional[cid] = not is_auth
                continue
            if c.h_schema == H_SCHEMA["scope"]:
                is_auth = cid in latched_scope_auth
                settled[cid] = is_auth
                provisional[cid] = not is_auth
                continue
            if c.h_schema == H_SCHEMA["axiom"]:
                settled[cid] = True
                provisional[cid] = False
                continue
            if c.h_schema == H_SCHEMA["projection"]:
                # Settled once its witness policy has signed it (late co-signatures count)
                w_thr, w_pks = pol_quorum(c.slots[4])
                is_set = len(witness_endorsers(cid) & w_pks) >= w_thr
                settled[cid] = is_set
                provisional[cid] = not is_set
                continue

            # Determine evaluation policy `EvalPol(v)`
            if c.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]):
                p_thr, p_pks = pol_quorum(c.slots[3]) if c.slots[3] != H_EMPTY else (adm_thr, adm_pks)
            elif c.h_schema == H_SCHEMA["question"]:
                p_thr, p_pks = pol_quorum(c.slots[1]) if c.slots[1] != H_EMPTY else (adm_thr, adm_pks)
            else:
                settled[cid] = True
                provisional[cid] = False
                continue

            valid_endorsers: Set[bytes] = set()
            for wid in children_of[cid]:
                w = cells[wid]
                if not active.get(wid, False) or stale.get(wid, False):
                    continue
                if cid not in hvec_items(w.h_attests):
                    continue
                if c.h_schema in (H_SCHEMA["contract"], H_SCHEMA["decision"]):
                    if w.h_schema != H_SCHEMA["verdict"] or w.h_payload != cid:
                        continue
                    # Contradictory active INVALID verdict under the same verifier_id blocks settlement
                    has_conflict = any(
                        active.get(bad_id, False)
                        and not stale.get(bad_id, False)
                        and bad_c.h_schema == H_SCHEMA["verdict"]
                        and bad_c.slots[1] == H_VERDICT_INVALID
                        and bad_c.slots[2] == w.slots[2]
                        and (
                            bad_c.h_payload == cid
                            or (w.slots[0] != H_EMPTY and bad_c.slots[0] == w.slots[0])
                        )
                        and bool(witness_endorsers(bad_id) & p_pks)
                        for bad_id, bad_c in cells.items()
                    )
                    if has_conflict:
                        continue
                    req_comp, exp_out = c.slots[1], c.slots[2]
                    if req_comp == H_EMPTY:
                        if w.slots[0] != H_EMPTY or w.slots[1] != H_ATTESTED:
                            continue
                    else:
                        if w.slots[1] != H_REPLAYED or w.slots[0] not in cells:
                            continue
                        cw_id = w.slots[0]
                        cw = cells[cw_id]
                        if not active.get(cw_id, False) or stale.get(cw_id, False):
                            continue
                        if cw.h_schema == H_SCHEMA["checkpoint"]:
                            if cw.slots[0] != req_comp or cw.slots[4] != H_NORMAL_FORM:
                                continue
                            try:
                                if verify_checkpoint_replay(cw, atoms, cells, gate_mode=False, memo=lens_replay_memo) != "REPLAYED":
                                    continue
                            except VarsError:
                                continue
                            _, th = sgs1_term_hash(atoms[cw.h_payload])
                            if th != exp_out:
                                continue
                        elif cw.h_schema == H_SCHEMA["cycle_witness"]:
                            if cw.slots[0] != req_comp or exp_out != H_CYCLE_PROVEN:
                                continue
                            try:
                                if verify_cycle_witness_replay(cw, atoms, gate_mode=False) != "CYCLE_PROVEN":
                                    continue
                            except VarsError:
                                continue
                        else:
                            continue
                elif c.h_schema == H_SCHEMA["question"]:
                    if w.h_schema != c.slots[0]:
                        continue
                valid_endorsers |= (witness_endorsers(wid) & p_pks)

            is_set = len(valid_endorsers) >= p_thr
            settled[cid] = is_set
            provisional[cid] = not is_set

        return {
            "kernel_input": fold["kernel_input"],
            "kernel_order": forward_order,
            "cells": cells,
            "atoms": atoms,
            "accepted": accepted,
            "invalidated": invalidated,
            "effective": effective,
            "retired": retired,
            "superseded": superseded,
            "active": active,
            "stale": stale,
            "settled": settled,
            "provisional": provisional,
        }


# ---------------------------------------------------------------------------
# §4.4 Projection bundles: what a client without the repository holds and checks (checked by verify/minds_verify.py)
# ---------------------------------------------------------------------------
def export_projection(repo: "GitVarsRepo", scope: str, projection_id: bytes, with_data: bool = True) -> Dict[str, object]:
    """A self-contained bundle for `projection_id` at the scope's tip: the cell, the atoms its check needs, every
    seal on it, and (with `with_data`) the kernel's input and output at its tip, which its digests commit to."""
    atoms, cells, seals = repo.read_cas_tree(repo.ref_commit(scope))
    cell = cells.get(projection_id)
    if cell is None or cell.h_schema != H_SCHEMA["projection"]:
        raise VarsError("not a projection cell of this scope")
    pol = atoms[cell.slots[4]]
    need = [cell.slots[0], cell.slots[4], parse_pol1(pol)[1]]
    bundle: Dict[str, object] = {
        "format": BUNDLE_FORMAT,
        "cell": cell.encode().hex(),
        "atoms": [atoms[h].hex() for h in need],
        "seals": sorted(s.encode().hex() for s in seals.values() if s.h_target == projection_id),
    }
    if with_data:
        tip = parse_utf8(atoms[cell.slots[0]])
        trees = [repo.read_cas_tree(c) for c in repo.commit_chain(tip)]
        kernel_input, _ = kernel_facts(scope, trees)
        bundle["input"] = kernel_input.hex()
        bundle["output"] = kernel_runner().run(kernel_input).hex()
    return bundle


def export_attestation(repo: "GitVarsRepo", scope: str, decision_id: bytes,
                       projection_id: Optional[bytes] = None) -> Dict[str, object]:
    """A self-contained bundle for a contract or decision at the scope's tip: the cell, the governing scope cell, the
    atoms its evaluator policy and statement need, every verdict on it and every seal on it and on those verdicts,
    and optionally a projection bundle whose statuses cover them. With a projection, the scope is the one governing
    the projection's tip, which its evidence is about; a later rotation does not change it."""
    tip = repo.ref_commit(scope)
    atoms, cells, seals = repo.read_cas_tree(tip)
    d = cells.get(decision_id)
    if d is None or d.h_schema not in (H_SCHEMA["contract"], H_SCHEMA["decision"]):
        raise VarsError("not a contract or decision cell of this scope")
    at = tip
    if projection_id is not None:
        pc = cells.get(projection_id)
        if pc is None or pc.h_schema != H_SCHEMA["projection"]:
            raise VarsError("not a projection cell of this scope")
        at = parse_utf8(atoms[pc.slots[0]])
    s_cell = cells[repo._evaluate_commit_chain(scope, repo.commit_chain(at))["active_scope_id"]]
    pol = d.slots[3] if d.slots[3] != H_EMPTY else s_cell.slots[0]
    verdicts = [c for c in cells.values() if c.h_schema == H_SCHEMA["verdict"] and c.h_payload == decision_id]
    need = [pol, parse_pol1(atoms[pol])[1], d.h_payload]
    for w in verdicts:
        need += [w.h_attests, w.slots[2]]
    targets = {decision_id} | {w.id for w in verdicts}
    bundle: Dict[str, object] = {
        "format": ATTESTATION_FORMAT,
        "cell": d.encode().hex(),
        "scope": s_cell.encode().hex(),
        "atoms": sorted({atoms[h].hex() for h in need if h in atoms}),
        "verdicts": sorted(w.encode().hex() for w in verdicts),
        "seals": sorted(x.encode().hex() for x in seals.values() if x.h_target in targets),
    }
    if projection_id is not None:
        bundle["projection"] = export_projection(repo, scope, projection_id)
    return bundle


def _main(argv: List[str]) -> int:
    return _MV.main(argv)


if __name__ == "__main__":
    sys.exit(_main(sys.argv[1:]))

