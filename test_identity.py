#!/usr/bin/env python3
"""Tests & surgical mutant harness for `identity.py` and `proofs/Vars1/Identity.lean` (`ID01..ID10`).

    python3 test_identity.py
"""
import importlib.util
from pathlib import Path
import tempfile
import unittest

import identity as ID


class TestIdentity(unittest.TestCase):
    def test_id01_step_continuation_preserves_identity_and_relations(self):
        """ID01: Linear continuation with EnabledBy + IdentityContinuation preserves SameEntity and relations."""
        dag = ID.LineageDAG()
        dag.genesis("a0", invariants=["const-1"], relations=["pact:1", "trust:bob"], atp=100)
        a1 = dag.continue_step(
            "a0", "a1",
            enabled_warrant="w:en-1",
            continuation_warrant="w:cont-1",
            add_relations=["pact:2"],
            atp_spent=20,
        )
        self.assertEqual(a1.entity_root, "a0")
        self.assertEqual(a1.atp, 80)
        self.assertTrue(ID.same_entity(dag, "a0", "a1"))
        self.assertIsNotNone(ID.auth_path(dag, "a0", "a1"))
        self.assertEqual(ID.entity_lineage(dag, "a1"), ["a0", "a1"])
        self.assertEqual(ID.provenance_chain(dag, "a1"), ["a0", "a1"])
        self.assertIn("pact:1", a1.relations)
        self.assertIn("pact:2", a1.relations)

    def test_id02_fork_satisfies_authpath_and_provenance_yet_is_new_entity(self):
        """ID02: Constructive F2 / D21 witness — fork copies identical byte invariants yet is NOT SameEntity."""
        dag = ID.LineageDAG()
        dag.genesis("a0", invariants=["inv-42"], relations=["obl:debt-1"], atp=100)
        b0 = dag.fork("a0", "b0", enabled_warrant="w:fork-1", child_atp=40)
        a1 = dag.continue_step("a0", "a1", enabled_warrant="w:e1", continuation_warrant="w:c1", atp_spent=10)
        self.assertEqual(b0.invariants, ID.TypedSet(["inv-42"]))
        self.assertEqual(b0.entity_root, "b0")
        self.assertEqual(b0.relations, ID.TypedSet())
        self.assertEqual(a1.atp, 50)
        # AuthPath & provenance hold across fork, yet SameEntity is strictly False!
        self.assertIsNotNone(ID.auth_path(dag, "a0", "b0"))
        self.assertEqual(ID.provenance_chain(dag, "b0"), ["a0", "b0"])
        self.assertEqual(ID.entity_lineage(dag, "b0"), ["b0"])
        self.assertFalse(ID.same_entity(dag, "a0", "b0"))
        self.assertTrue(ID.same_entity(dag, "a0", "a1"))

    def test_id03_split_brain_continuation_refused(self):
        """ID03: UniqueContinuation refuses a second IdentityContinuation from the same parent."""
        dag = ID.LineageDAG()
        dag.genesis("a0", invariants=["i"], atp=50)
        dag.continue_step("a0", "a1", enabled_warrant="w:e1", continuation_warrant="w:c1")
        with self.assertRaises(ID.IdentityError) as ctx:
            dag.continue_step("a0", "a2", enabled_warrant="w:e2", continuation_warrant="w:c2")
        self.assertEqual(ctx.exception.code, "SPLIT_BRAIN_CONTINUATION")

    def test_id04_fork_forbids_continuation_warrant_and_cloned_relations(self):
        """ID04: Fork refuses IdentityContinuation warrant and refuses cloning parent relations."""
        dag = ID.LineageDAG()
        dag.genesis("a0", invariants=["i"], relations=["trust:alice"], atp=50)
        with self.assertRaises(ID.IdentityError) as ctx1:
            dag.fork("a0", "b1", enabled_warrant="w:f1", continuation_warrant="w:cont-illegal")
        self.assertEqual(ctx1.exception.code, "FORK_CANNOT_CONTINUE_IDENTITY")
        with self.assertRaises(ID.IdentityError) as ctx2:
            dag.fork("a0", "b2", enabled_warrant="w:f2", initial_relations=["trust:alice"])
        self.assertEqual(ctx2.exception.code, "FORK_CLONED_RELATIONS")

    def test_id05_missing_warrants_and_constitution_violation_refused(self):
        """ID05: Missing warrants or violated constitutional inv_ok fail closed."""
        dag = ID.LineageDAG()
        dag.genesis("a0", invariants=["core-safety"], atp=50)
        with self.assertRaises(ID.IdentityError) as ctx1:
            dag.continue_step("a0", "a1", enabled_warrant="", continuation_warrant="w:c1")
        self.assertEqual(ctx1.exception.code, "MISSING_ENABLED_WARRANT")
        with self.assertRaises(ID.IdentityError) as ctx2:
            dag.continue_step("a0", "a1", enabled_warrant="w:e1", continuation_warrant="  ")
        self.assertEqual(ctx2.exception.code, "MISSING_CONTINUATION_WARRANT")
        with self.assertRaises(ID.IdentityError) as ctx3:
            dag.continue_step("a0", "a1", enabled_warrant="w:e1", continuation_warrant="w:c1", invariants=[])
        self.assertEqual(ctx3.exception.code, "CONSTITUTION_VIOLATED")

    def test_id06_atp_conservation_on_step_and_fork(self):
        """ID06: Step spending > available, fork inflation, and repeated multi-fork Sybil inflation are refused."""
        dag = ID.LineageDAG()
        dag.genesis("a0", invariants=["i"], atp=50)
        with self.assertRaises(ID.IdentityError) as ctx1:
            dag.continue_step("a0", "a1", enabled_warrant="w:e1", continuation_warrant="w:c1", atp_spent=51)
        self.assertEqual(ctx1.exception.code, "ATP_INFLATION")
        with self.assertRaises(ID.IdentityError) as ctx2:
            dag.fork("a0", "b0", enabled_warrant="w:f1", child_atp=30, parent_remaining_atp=25)
        self.assertEqual(ctx2.exception.code, "ATP_INFLATION")
        # Two forks summing > 50 from same parent must fail (anti-Sybil ATP conservation!)
        dag.fork("a0", "b1", enabled_warrant="w:f2", child_atp=30)
        self.assertEqual(dag.available_atp("a0"), 20)
        with self.assertRaises(ID.IdentityError) as ctx3:
            dag.fork("a0", "b2", enabled_warrant="w:f3", child_atp=25)
        self.assertEqual(ctx3.exception.code, "ATP_INFLATION")

    def test_id07_fork_child_can_continue_its_own_new_lineage(self):
        """ID07: A forked entity starts a fresh lineage that continues itself while staying distinct from ancestor."""
        dag = ID.LineageDAG()
        dag.genesis("a0", invariants=["i"], relations=["r0"], atp=100)
        dag.fork("a0", "b0", enabled_warrant="w:f", child_atp=40)
        b1 = dag.continue_step("b0", "b1", enabled_warrant="w:eb1", continuation_warrant="w:cb1",
                               add_relations=["own-pact"], atp_spent=5)
        self.assertEqual(b1.entity_root, "b0")
        self.assertTrue(ID.same_entity(dag, "b0", "b1"))
        self.assertFalse(ID.same_entity(dag, "a0", "b1"))
        self.assertIsNotNone(ID.auth_path(dag, "a0", "b1"))
        self.assertEqual(ID.provenance_chain(dag, "b1"), ["a0", "b0", "b1"])
        self.assertEqual(ID.entity_lineage(dag, "b1"), ["b0", "b1"])
        self.assertEqual(b1.relations, ID.TypedSet(["own-pact"]))

    def test_id08_certificate_distinguishes_typed_invariants_and_is_deterministic(self):
        """ID08: Identity certificates are deterministic and distinguish `0` (int) from `'0'` (str)."""
        dag = ID.LineageDAG()
        dag.genesis("n0", invariants=(x for x in [0, "0"]), relations=(r for r in ["rel"]), atp=10)
        c1 = ID.identity_certificate(dag, "n0")
        c2 = ID.identity_certificate(dag, "n0")
        self.assertEqual(c1.get("digest"), c2.get("digest"))
        self.assertEqual(len(c1.get("digest", "")), 64)
        self.assertEqual(len(c1.get("certificate", {}).get("invariants", [])), 2)

    def test_id09_typed_invariant_and_relation_equality_prevents_bool_int_erasure(self):
        """ID09: TypedSet distinguishes bool False/True from int 0/1 in invariants, relations, and digests (Codex F1)."""
        for op in ("continue_step", "fork"):
            d = ID.LineageDAG()
            d.genesis("p", invariants=[False], atp=10)
            kw = {"enabled_warrant": "w:en", "invariants": [0]}
            if op == "continue_step":
                kw["continuation_warrant"] = "w:cont"
            with self.assertRaises(ID.IdentityError) as ctx:
                getattr(d, op)("p", "c", **kw)
            self.assertEqual(ctx.exception.code, "CONSTITUTION_VIOLATED")
        # Order-independence and collision-free retention for [0, False] vs [False, 0]
        d1, d2 = ID.LineageDAG(), ID.LineageDAG()
        d1.genesis("p", invariants=[0, False], relations=[False, 0])
        d2.genesis("p", invariants=[False, 0], relations=[0, False])
        c1, c2 = ID.identity_certificate(d1, "p"), ID.identity_certificate(d2, "p")
        self.assertEqual(c1["digest"], c2["digest"])
        self.assertEqual(c1["certificate"]["invariants"], [["bool", False], ["int", 0]])
        self.assertEqual(c1["certificate"]["relations"], [["bool", False], ["int", 0]])
        # Dropping int 0 must not drop bool False from relations
        p1 = d1.continue_step("p", "p1", enabled_warrant="w:e", continuation_warrant="w:c", drop_relations=[0])
        self.assertIn(False, p1.relations)
        self.assertNotIn(0, p1.relations)

    def test_id10_mutants_all_killed_on_assertion(self):
        """ID10: 10 surgical mutants of identity.py all fail on assertion (zero crashes, zero survivors)."""
        src_path = Path(__file__).resolve().parent / "identity.py"
        orig = src_path.read_text(encoding="utf-8")
        mutants = [
            ("ID-M1-split-brain", "        if parent_id in self._out_cont:", "        if False:",
             "test_id03_split_brain_continuation_refused"),
            ("ID-M2-fork-cont", "        if continuation_warrant is not None:", "        if False:",
             "test_id04_fork_forbids_continuation_warrant_and_cloned_relations"),
            ("ID-M3-fork-rels", "        if init_rels:", "        if False:",
             "test_id04_fork_forbids_continuation_warrant_and_cloned_relations"),
            ("ID-M4-const-step", "        if not self._inv_ok(parent.invariants, next_inv):", "        if False:",
             "test_id05_missing_warrants_and_constitution_violation_refused"),
            ("ID-M5-atp-step", "        if not (_is_int(atp_spent) and 0 <= atp_spent <= avail):", "        if False:",
             "test_id06_atp_conservation_on_step_and_fork"),
            ("ID-M6-atp-fork", "        if not (_is_int(rem) and rem >= 0) or (rem + child_atp > avail):", "        if False:",
             "test_id06_atp_conservation_on_step_and_fork"),
            ("ID-M7-fork-debit", "        self._unallocated_atp[parent_id] = rem", "        pass",
             "test_id06_atp_conservation_on_step_and_fork"),
            ("ID-M8-fork-root", "            entity_root=child_id,  # New entity root!", "            entity_root=parent.entity_root,",
             "test_id02_fork_satisfies_authpath_and_provenance_yet_is_new_entity"),
            ("ID-M9-same-uses-cont", "        cur = dag._out_cont.get(cur)",
             "        edges = dag._out_enabled.get(cur, ()); cur = edges[0].dst if edges else None",
             "test_id02_fork_satisfies_authpath_and_provenance_yet_is_new_entity"),
            ("ID-M10-typed-set-le", "        return self._map.keys() <= other_ts._map.keys()",
             "        return set(self._map.values()) <= set(other_ts._map.values())",
             "test_id09_typed_invariant_and_relation_equality_prevents_bool_int_erasure"),
        ]
        for mid, find, repl, test_name in mutants:
            self.assertEqual(orig.count(find), 1, f"{mid}: find must match uniquely")
            mutated = orig.replace(find, repl, 1)
            with tempfile.TemporaryDirectory() as td:
                mp = Path(td) / "identity.py"
                mp.write_text(mutated, encoding="utf-8")
                spec = importlib.util.spec_from_file_location("_identity_mut", mp)
                mod = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(mod)
                saved = globals()["ID"]
                globals()["ID"] = mod
                try:
                    res = unittest.TestResult()
                    TestIdentity(test_name).run(res)
                finally:
                    globals()["ID"] = saved
                self.assertEqual(len(res.errors), 0, f"{mid} crashed instead of failing assertion: {res.errors}")
                self.assertEqual(len(res.failures), 1, f"{mid} SURVIVED {test_name}!")


if __name__ == "__main__":
    unittest.main()
