"""Relational identity vs. fork continuity (`D21` / Thesis 2, `proofs/Vars1/Identity.lean`).

Executable Python counterpart of `Vars1.Identity`, resolving F2 / D21 by separating two warrant sorts:
  - `EnabledBy(w)`: authorizes a transition (`step` or `fork`) to exist under constitutional `inv_ok`.
  - `IdentityContinuation(w)`: authorizes unique single-branch identity continuity (`step` only, never `fork`).

Core invariants enforced fail-closed:
  1. No split-brain continuity (`UniqueContinuation`): a node can have at most ONE outgoing
     `IdentityContinuation` successor (`SPLIT_BRAIN_CONTINUATION` refused).
  2. Fork births a new entity (Thesis 2): a `fork` transition requires `enabled_warrant`, forbids
     `continuation_warrant` (`FORK_CANNOT_CONTINUE_IDENTITY`), inherits causal provenance (`Ancestor`)
     and byte invariants, splits ATP budget conservatively (`parent_rem + child_atp <= parent_atp`),
     and isolates external relational standing (`relations` starts empty on the forked child unless
     explicitly re-granted by a separate relational act).
  3. Path-indexed queries: `auth_path(dag, u, v)` (necessary, holds across `fork`) vs
     `same_entity(dag, u, v)` (strictly single-branch continuation, never crosses `fork`).
"""
from dataclasses import dataclass
import hashlib
import json


def _is_int(v):
    return isinstance(v, int) and not isinstance(v, bool)


def _tag_val(v):
    """Collision-free canonical encoding distinguishing e.g. `0` (int) from `"0"` (str)."""
    if v is None:
        return ["null", None]
    if isinstance(v, bool):
        return ["bool", v]
    if isinstance(v, int):
        return ["int", v]
    if isinstance(v, str):
        return ["str", v]
    if isinstance(v, (list, tuple)):
        return ["list", [_tag_val(x) for x in v]]
    if isinstance(v, (set, frozenset)):
        items = [_tag_val(x) for x in v]
        items.sort(key=lambda x: json.dumps(x, sort_keys=True, separators=(",", ":")))
        return ["set", items]
    if isinstance(v, dict):
        pairs = [[_tag_val(k), _tag_val(val)] for k, val in v.items()]
        pairs.sort(key=lambda p: json.dumps(p[0], sort_keys=True, separators=(",", ":")))
        return ["dict", pairs]
    raise TypeError(f"unsupported value type for canonical identity encoding: {type(v).__name__}")


def _sort_key(v):
    return json.dumps(_tag_val(v), sort_keys=True, separators=(",", ":"))


@dataclass(frozen=True)
class EntityNode:
    node_id: str
    entity_root: str
    invariants: frozenset
    relations: frozenset
    atp: int
    parent: str | None
    birth_kind: str  # "genesis" | "step" | "fork"


@dataclass(frozen=True)
class TransitionEdge:
    src: str
    dst: str
    kind: str  # "step" | "fork"
    enabled_warrant: str
    continuation_warrant: str | None


class IdentityError(ValueError):
    """Raised on violation of D21 identity/fork invariants."""

    def __init__(self, code: str, detail: str):
        super().__init__(f"{code}: {detail}")
        self.code = code
        self.detail = detail


def _require_warrant(w, code, name):
    if not isinstance(w, str) or not w.strip():
        raise IdentityError(code, f"{name} must be a non-empty warrant reference")


def default_inv_ok(prev_inv: frozenset, next_inv: frozenset) -> bool:
    """Default constitutional meta-invariant `I*`: byte/constitution invariants are preserved."""
    return prev_inv <= next_inv


class LineageDAG:
    """Append-only causal DAG separating `EnabledBy` (existence) from `IdentityContinuation` (continuity)."""

    def __init__(self, inv_ok=default_inv_ok):
        self._inv_ok = inv_ok
        self._nodes: dict[str, EntityNode] = {}
        self._edges: list[TransitionEdge] = []
        self._out_enabled: dict[str, list[TransitionEdge]] = {}
        self._out_cont: dict[str, str] = {}   # src -> unique continuation dst
        self._in_cont: dict[str, str] = {}    # dst -> continuation src
        self._unallocated_atp: dict[str, int] = {}

    @property
    def nodes(self):
        return dict(self._nodes)

    @property
    def edges(self):
        return tuple(self._edges)

    def available_atp(self, node_id: str) -> int:
        if node_id not in self._nodes:
            raise IdentityError("UNKNOWN_NODE", f"unknown node {node_id!r}")
        return self._unallocated_atp[node_id]

    def genesis(self, node_id: str, *, invariants=(), relations=(), atp: int = 0) -> EntityNode:
        if not isinstance(node_id, str) or not node_id.strip():
            raise IdentityError("BAD_NODE_ID", "node_id must be a non-empty string")
        if node_id in self._nodes:
            raise IdentityError("DUPLICATE_NODE", f"node {node_id!r} already exists")
        if not (_is_int(atp) and atp >= 0):
            raise IdentityError("BAD_ATP", "atp must be a non-negative integer")
        node = EntityNode(
            node_id=node_id,
            entity_root=node_id,
            invariants=frozenset(invariants),
            relations=frozenset(relations),
            atp=atp,
            parent=None,
            birth_kind="genesis",
        )
        self._nodes[node_id] = node
        self._out_enabled[node_id] = []
        self._unallocated_atp[node_id] = atp
        return node

    def continue_step(
        self,
        parent_id: str,
        next_id: str,
        *,
        enabled_warrant: str,
        continuation_warrant: str,
        invariants=None,
        add_relations=(),
        drop_relations=(),
        atp_spent: int = 0,
    ) -> EntityNode:
        """Advance an entity along its unique single-branch identity continuation (`step`)."""
        if parent_id not in self._nodes:
            raise IdentityError("UNKNOWN_PARENT", f"unknown parent {parent_id!r}")
        if not isinstance(next_id, str) or not next_id.strip():
            raise IdentityError("BAD_NODE_ID", "next_id must be a non-empty string")
        if next_id in self._nodes:
            raise IdentityError("DUPLICATE_NODE", f"node {next_id!r} already exists")
        _require_warrant(enabled_warrant, "MISSING_ENABLED_WARRANT", "enabled_warrant")
        _require_warrant(continuation_warrant, "MISSING_CONTINUATION_WARRANT", "continuation_warrant")
        if parent_id in self._out_cont:
            raise IdentityError(
                "SPLIT_BRAIN_CONTINUATION",
                f"parent {parent_id!r} already continued to {self._out_cont[parent_id]!r}",
            )
        parent = self._nodes[parent_id]
        next_inv = parent.invariants if invariants is None else frozenset(invariants)
        if not self._inv_ok(parent.invariants, next_inv):
            raise IdentityError("CONSTITUTION_VIOLATED", f"inv_ok failed on {parent_id!r} -> {next_id!r}")
        avail = self._unallocated_atp[parent_id]
        if not (_is_int(atp_spent) and 0 <= atp_spent <= avail):
            raise IdentityError("ATP_INFLATION", f"atp_spent={atp_spent!r} outside 0..{avail}")

        add_set = frozenset(add_relations)
        drop_set = frozenset(drop_relations)
        next_rels = (parent.relations - drop_set) | add_set
        next_atp = avail - atp_spent
        node = EntityNode(
            node_id=next_id,
            entity_root=parent.entity_root,
            invariants=next_inv,
            relations=next_rels,
            atp=next_atp,
            parent=parent_id,
            birth_kind="step",
        )
        edge = TransitionEdge(
            src=parent_id,
            dst=next_id,
            kind="step",
            enabled_warrant=enabled_warrant,
            continuation_warrant=continuation_warrant,
        )
        self._nodes[next_id] = node
        self._edges.append(edge)
        self._out_enabled[parent_id].append(edge)
        self._out_enabled[next_id] = []
        self._out_cont[parent_id] = next_id
        self._in_cont[next_id] = parent_id
        self._unallocated_atp[parent_id] = 0
        self._unallocated_atp[next_id] = next_atp
        return node

    def fork(
        self,
        parent_id: str,
        child_id: str,
        *,
        enabled_warrant: str,
        continuation_warrant=None,
        invariants=None,
        child_atp: int = 0,
        parent_remaining_atp: int | None = None,
        initial_relations=(),
    ) -> EntityNode:
        """Birth a new entity via `fork` (Thesis 2).

        Requires `enabled_warrant`, strictly forbids `continuation_warrant`, enforces conservative ATP
        allocation across arbitrary repeated forks (`rem + child_atp <= available_atp(parent_id)`),
        preserves provenance (`Ancestor`), and refuses cloning external relations (`FORK_CLONED_RELATIONS`).
        """
        if parent_id not in self._nodes:
            raise IdentityError("UNKNOWN_PARENT", f"unknown parent {parent_id!r}")
        if not isinstance(child_id, str) or not child_id.strip():
            raise IdentityError("BAD_NODE_ID", "child_id must be a non-empty string")
        if child_id in self._nodes:
            raise IdentityError("DUPLICATE_NODE", f"node {child_id!r} already exists")
        _require_warrant(enabled_warrant, "MISSING_ENABLED_WARRANT", "enabled_warrant")
        if continuation_warrant is not None:
            raise IdentityError(
                "FORK_CANNOT_CONTINUE_IDENTITY",
                "fork births a new entity and must not carry an IdentityContinuation warrant",
            )
        parent = self._nodes[parent_id]
        child_inv = parent.invariants if invariants is None else frozenset(invariants)
        if not self._inv_ok(parent.invariants, child_inv):
            raise IdentityError("CONSTITUTION_VIOLATED", f"inv_ok failed on fork {parent_id!r} -> {child_id!r}")
        if not (_is_int(child_atp) and child_atp >= 0):
            raise IdentityError("BAD_ATP", "child_atp must be a non-negative integer")
        avail = self._unallocated_atp[parent_id]
        rem = (avail - child_atp) if parent_remaining_atp is None else parent_remaining_atp
        if not (_is_int(rem) and rem >= 0) or (rem + child_atp > avail):
            raise IdentityError(
                "ATP_INFLATION",
                f"fork budget rem={rem} + child={child_atp} exceeds available_atp={avail}",
            )
        init_rels = frozenset(initial_relations)
        if init_rels:
            raise IdentityError(
                "FORK_CLONED_RELATIONS",
                "forked entity must start with isolated (empty) external relations; re-grant explicitly after birth",
            )
        child = EntityNode(
            node_id=child_id,
            entity_root=child_id,  # New entity root!
            invariants=child_inv,
            relations=frozenset(),
            atp=child_atp,
            parent=parent_id,
            birth_kind="fork",
        )
        edge = TransitionEdge(
            src=parent_id,
            dst=child_id,
            kind="fork",
            enabled_warrant=enabled_warrant,
            continuation_warrant=None,
        )
        self._nodes[child_id] = child
        self._edges.append(edge)
        self._out_enabled[parent_id].append(edge)
        self._out_enabled[child_id] = []
        self._unallocated_atp[parent_id] = rem
        self._unallocated_atp[child_id] = child_atp
        return child


# ---------------------------------------------------------------- path-indexed queries & certificates


def auth_path(dag: LineageDAG, src: str, dst: str) -> list[TransitionEdge] | None:
    """Return a witness path of enabled constitutionally valid edges (`step` or `fork`) from `src` to `dst`, or None."""
    nodes = dag.nodes
    if src not in nodes or dst not in nodes:
        return None
    if src == dst:
        return []
    queue = [(src, [])]
    visited = {src}
    while queue:
        cur, path = queue.pop(0)
        for edge in dag._out_enabled.get(cur, ()):
            if edge.dst == dst:
                return path + [edge]
            if edge.dst not in visited:
                visited.add(edge.dst)
                queue.append((edge.dst, path + [edge]))
    return None


def same_entity(dag: LineageDAG, src: str, dst: str) -> bool:
    """True iff `dst` is reachable from `src` via `IdentityContinuation` edges only (never crosses a `fork`)."""
    nodes = dag.nodes
    if src not in nodes or dst not in nodes:
        return False
    cur = src
    seen = set()
    while cur is not None and cur not in seen:
        if cur == dst:
            return True
        seen.add(cur)
        cur = dag._out_cont.get(cur)
    return False


def provenance_chain(dag: LineageDAG, node_id: str) -> list[str]:
    """Return causal provenance chain `[genesis, ..., node_id]` (crosses `fork` edges)."""
    nodes = dag.nodes
    if node_id not in nodes:
        raise IdentityError("UNKNOWN_NODE", f"unknown node {node_id!r}")
    chain = []
    cur = node_id
    while cur is not None:
        chain.append(cur)
        cur = nodes[cur].parent
    chain.reverse()
    return chain


def entity_lineage(dag: LineageDAG, node_id: str) -> list[str]:
    """Return single-entity continuation chain `[entity_root, ..., node_id]` (stops at `fork`)."""
    nodes = dag.nodes
    if node_id not in nodes:
        raise IdentityError("UNKNOWN_NODE", f"unknown node {node_id!r}")
    chain = []
    cur = node_id
    while cur is not None:
        chain.append(cur)
        cur = dag._in_cont.get(cur)
    chain.reverse()
    return chain


def identity_certificate(dag: LineageDAG, node_id: str) -> dict:
    """Emit a deterministic, content-addressed SHA-256 identity & provenance certificate for `node_id`."""
    nodes = dag.nodes
    if node_id not in nodes:
        raise IdentityError("UNKNOWN_NODE", f"unknown node {node_id!r}")
    n = nodes[node_id]
    body = {
        "schema": "vars1-identity-lineage@1",
        "node_id": n.node_id,
        "entity_root": n.entity_root,
        "birth_kind": n.birth_kind,
        "invariants": [_tag_val(x) for x in sorted(n.invariants, key=_sort_key)],
        "relations": [_tag_val(x) for x in sorted(n.relations, key=_sort_key)],
        "atp": n.atp,
        "provenance_chain": provenance_chain(dag, node_id),
        "entity_lineage": entity_lineage(dag, node_id),
    }
    raw = json.dumps(body, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return {"digest": hashlib.sha256(raw).hexdigest(), "certificate": body}
