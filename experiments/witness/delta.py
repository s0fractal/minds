"""Which statuses a later commit can change, found from below: the cells it touches, walked up (proofs/Vars1/Delta.lean).

`frame.py` answers from a decision: `frame(T, d)` is what `d`'s Settled (or Grounded) reads at the tip `T`, and
`touches` says whether the objects of later commits touch it. With many decisions and a small commit that asks for a
frame per decision. Here the question runs the other way: from the objects a later tip adds, which contracts,
decisions and questions have a frame they touch? Each step `frame` takes downward has an inverse here (`Up`), built
once per tip from the store: who relies on a cell, which cells a judge judges, which cells a named checkpoint is named
for, which cells an edge enters, which cells supersede a cell. `dirty` reads each new object's touch points, walks
up from them and returns the evaluated cells reached. On every pair of tips it is exactly the set of cells whose frame
`touches` reports touched (`experiments/witness/test_witness.py` 25), so a cell outside it keeps its status
(`settled_frame`, `grounded_frame`) without its frame ever being built.

The reverse index of `revindex.py` names, for a cell, who attests it, whose payload it is, who names it, who points an
edge at it and who seals it; not who relies on it, which this walk also needs. The store gives that in one pass, so
`Up` reads the store, not the index.

This module reads vars1 through the `V` of the `Tip` it is given and imports nothing of minds itself.
"""
from typing import Dict, Iterable, List, Optional, Set

from frame import EVICT, Tip, evaluated, named_slot, own_policy



class Up:
    """The inverse of `frame`'s steps at one tip, for the frame of Settled or of Grounded."""

    def __init__(self, T: Tip, grounded: bool = False) -> None:
        V, cells = T.V, T.cells
        self.T, self.V, self.grounded = T, V, grounded
        self.evaluated = {x for x, c in cells.items() if evaluated(V, c)}
        self.relied_by: Dict[bytes, Set[bytes]] = {}
        self.direct_of: Dict[bytes, Set[bytes]] = {}  # a judge -> the cells it judges directly (attests, verdict payload)
        self.on_named: Dict[bytes, Set[bytes]] = {}  # a checkpoint -> the verdicts that name it
        self.edges_of: Dict[bytes, Set[bytes]] = {}  # a cell -> the cells its eviction edges enter
        self.superseders: Dict[bytes, Set[bytes]] = {}  # a cell -> the cells that supersede it
        for x, c in cells.items():
            for r in T.hv(c.h_relies):
                self.relied_by.setdefault(r, set()).add(x)
            direct = set(T.hv(c.h_attests))
            if c.h_schema == V.H_SCHEMA["verdict"]:
                direct.add(c.h_payload)
                n = named_slot(V, c)
                if n is not None:
                    self.on_named.setdefault(n, set()).add(x)
            self.direct_of[x] = direct
            for field in EVICT:
                for t in T.hv(getattr(c, field)):
                    self.edges_of.setdefault(x, set()).add(t)
            for y in T.hv(c.h_supersedes):
                self.superseders.setdefault(y, set()).add(x)
        self._read: Dict[bytes, Set[bytes]] = {}
        self._above: Dict[bytes, Set[bytes]] = {}
        self._guard: Dict[bytes, Set[bytes]] = {}
        self._uncovered: Optional[Set[bytes]] = None
        self._fallback: Optional[Set[bytes]] = None

    # --- one step up -------------------------------------------------------------------------------------------------

    def judged(self, j: bytes) -> Set[bytes]:
        """The cells `j` judges in `frame`'s sense (`judges_of`): those it attests or is a verdict on, and those for
        which a verdict on them names the checkpoint `j` names."""
        out = set(self.direct_of.get(j, ()))
        n = named_slot(self.V, self.T.cells[j]) if j in self.T.cells else None
        if n is not None:
            for w in self.on_named.get(n, ()):
                out |= self.direct_of.get(w, set())
        return out

    def named_for(self, n: bytes) -> Set[bytes]:
        """The cells for which the checkpoint `n` is named: a verdict on them names it (and `n` is a cell)."""
        if n not in self.T.cells:
            return set()
        out: Set[bytes] = set()
        for w in self.on_named.get(n, ()):
            out |= self.direct_of.get(w, set())
        return out

    def read_of(self, x: bytes) -> Set[bytes]:
        """The evaluated cells `v` with `x` in the cells their own Settled reads (`frame`'s `read`): `x`, or what
        relies on it transitively, is `v`, a judge of `v`, or a checkpoint named for `v`."""
        if x not in self._read:
            ys, todo = {x}, [x]
            while todo:
                for y in self.relied_by.get(todo.pop(), ()):
                    if y not in ys:
                        ys.add(y)
                        todo.append(y)
            out: Set[bytes] = set()
            for y in ys:
                out |= ({y} | self.judged(y) | self.named_for(y)) & self.evaluated
            self._read[x] = out
        return self._read[x]

    def above(self, v: bytes) -> Set[bytes]:
        """The evaluated cells whose frame evaluates `v`: `v` itself, and for Grounded every cell whose read reaches an
        evaluated cell that reaches `v`, to the fixed point (`frame`'s loop over `evaluated`)."""
        if not self.grounded:
            return {v} & self.evaluated
        if v not in self._above:
            out, todo = {v} & self.evaluated, [v] if v in self.evaluated else []
            while todo:
                for u in self.read_of(todo.pop()):
                    if u not in out:
                        out.add(u)
                        todo.append(u)
            self._above[v] = out
        return self._above[v]

    def lift(self, vs: Iterable[bytes]) -> Set[bytes]:
        out: Set[bytes] = set()
        for v in vs:
            out |= self.above(v)
        return out

    # --- the sets `touches` reads ------------------------------------------------------------------------------------

    def read(self, x: bytes) -> Set[bytes]:
        """The evaluated cells whose frame's `read` holds `x`."""
        return self.lift(self.read_of(x))

    def ev(self, x: bytes) -> Set[bytes]:
        """... whose frame's `evaluated` holds `x`."""
        return self.above(x)

    def judges(self, j: bytes) -> Set[bytes]:
        """... whose frame's `judges` holds `j`."""
        return self.lift(self.judged(j) & self.evaluated)

    def named(self, n: bytes) -> Set[bytes]:
        """... whose frame's `named` holds `n`."""
        return self.lift(self.named_for(n) & self.evaluated)

    def guard(self, x: bytes) -> Set[bytes]:
        """... whose frame's `guard` holds `x`: `x` is in their read, or enters by an edge a cell of their guard, or is
        superseded by one."""
        if x not in self._guard:
            rs, todo = {x}, [x]
            while todo:
                u = todo.pop()
                for y in self.edges_of.get(u, set()) | self.superseders.get(u, set()):
                    if y not in rs:
                        rs.add(y)
                        todo.append(y)
            out: Set[bytes] = set()
            for r in rs:
                out |= self.read(r)
            self._guard[x] = out
        return self._guard[x]

    def watch(self, x: bytes) -> Set[bytes]:
        """... whose frame's `watch` holds `x`: a judge of theirs, the source of an edge into their guard, or a scope,
        acceptance or custom-schema cell of their guard."""
        V, c = self.V, self.T.cells.get(x)
        out = self.judges(x)
        for t in self.edges_of.get(x, ()):
            out |= self.guard(t)
        if c is not None and c.h_schema in (V.H_META_SCHEMA, V.H_SCHEMA["acceptance"], V.H_SCHEMA["scope"]):
            out |= self.guard(x)
        return out

    def uncovered(self) -> Set[bytes]:
        """The evaluated cells whose guard holds a cell of another scope: `touches` answers NOT_COVERED for them."""
        if self._uncovered is None:
            self._uncovered = set()
            for x in self.T.cells:
                if not self.T.is_local(x):
                    self._uncovered |= self.guard(x)
        return set(self._uncovered)

    def fallback(self) -> Set[bytes]:
        """The evaluated cells whose frame evaluates a cell that names no evaluator policy (the scope caveat)."""
        if self._fallback is None:
            self._fallback = set()
            for v in self.evaluated:
                if own_policy(self.V, self.T.cells[v]) == self.V.H_EMPTY:
                    self._fallback |= self.above(v)
        return set(self._fallback)


def dirty(up: Up, new_atoms, new_cells, new_seals) -> Set[bytes]:
    """The evaluated cells of `up.T` whose frame (Settled, or Grounded for an `Up` of Grounded) the new objects touch,
    by `touches`'s rules, read from below: a frame that holds a cell of another scope (NOT_COVERED), a rules change
    waiting at the tip or named by a new scope cell (RULES, every frame), a rotation waiting or a new scope cell for a
    frame that reads the scope's policy (WAITING, SCOPE), a new cell with an eviction edge into the guard (EDGE), a new
    cell that attests an evaluated cell of the frame or a verdict on one or naming a checkpoint the frame names (JUDGE),
    a new seal on a cell the frame watches (SEAL)."""
    T, V = up.T, up.V
    out = up.uncovered()
    every = set(up.evaluated)
    if T.waiting and T.waiting[2]:
        return every
    if T.waiting:
        out |= up.fallback()

    def hv(h: bytes) -> List[bytes]:
        return [] if h == V.H_EMPTY else V.parse_hvec(new_atoms[h] if h in new_atoms else T.atoms[h], require_sorted=True)

    rules = T.cells[T.governing].slots[2]
    for cid in sorted(new_cells):
        c = new_cells[cid]
        if c.h_schema == V.H_SCHEMA["scope"]:
            if c.slots[2] != rules:
                return every
            out |= up.fallback()
        for field in EVICT:
            for t in hv(getattr(c, field)):
                out |= up.guard(t)
        for t in hv(c.h_attests):
            out |= up.ev(t)
        if c.h_schema == V.H_SCHEMA["verdict"]:
            out |= up.ev(c.h_payload)
            n = named_slot(V, c)
            if n is not None:
                out |= up.named(n)
    for sid in sorted(new_seals):
        out |= up.watch(new_seals[sid].h_target)
    return out & every
