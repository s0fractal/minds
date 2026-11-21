#!/usr/bin/env python3
"""Tests & surgical mutant harness for `compatibility.py` and `proofs/Vars1/Compatibility.lean` (`CM01..CM07`).

    python3 test_compatibility.py
"""
import importlib.util
from pathlib import Path
import tempfile
import unittest

import compatibility as CM


def _toy_witness(claim_id, context_id, payload):
    return claim_id == "claim-0" and context_id == "ctx-b" and payload == ("counterexample", 1)


class TestCompatibility(unittest.TestCase):
    def test_cm01_local_refusal_preserves_standing_and_other_contexts(self):
        """CM01: Refuting claim-0 in ctx-b breaks ctx-b compatibility, keeps ctx-a compatible, and preserves standing."""
        led = CM.CompatibilityLedger(_toy_witness)
        led.register_entity("human", standing=True, viable_alone=True)
        led.register_entity("agent", standing=True, viable_alone=True)

        v_before = led.check_compatibility("human", "agent", "claim-0", "ctx-b")
        self.assertTrue(v_before.compatible)

        ref = led.file_refusal("human", "claim-0", "ctx-b", witness_payload=("counterexample", 1))
        self.assertEqual(len(ref.witness_digest), 64)

        # Standing untouched (critique of idea != critique of self)
        self.assertTrue(led.entities["human"].standing)
        self.assertTrue(led.entities["agent"].standing)
        # Local context ctx-b is refuted; distinct context ctx-a remains compatible!
        v_b = led.check_compatibility("human", "agent", "claim-0", "ctx-b")
        v_a = led.check_compatibility("human", "agent", "claim-0", "ctx-a")
        self.assertFalse(v_b.compatible)
        self.assertEqual(v_b.reason, "LOCALLY_REFUTED")
        self.assertTrue(v_a.compatible)
        self.assertEqual(v_a.reason, "COMPATIBLE")

    def test_cm02_unwitnessed_refusal_fails_closed(self):
        """CM02: Refusal without a reproducible witness is refused (UNWITNESSED_REFUSAL) and changes nothing."""
        led = CM.CompatibilityLedger(_toy_witness)
        led.register_entity("human")
        led.register_entity("agent")
        with self.assertRaises(CM.CompatibilityError) as ctx:
            led.file_refusal("human", "claim-0", "ctx-b", witness_payload=("ego-opinion",))
        self.assertEqual(ctx.exception.code, "UNWITNESSED_REFUSAL")
        self.assertFalse(led.is_refuted("claim-0", "ctx-b"))

    def test_cm03_captured_party_is_not_non_manipulatively_compatible(self):
        """CM03: A party lacking independent viability (viable_alone=False) is refused as CAPTURED_PARTY."""
        led = CM.CompatibilityLedger(_toy_witness)
        led.register_entity("captor", standing=True, viable_alone=True)
        led.register_entity("captive", standing=True, viable_alone=False)
        v = led.check_compatibility("captor", "captive", "claim-0", "ctx-a")
        self.assertFalse(v.compatible)
        self.assertEqual(v.reason, "CAPTURED_PARTY")

    def test_cm04_order_independence_and_idempotence(self):
        """CM04: Filing two local refusals in either order produces identical refuted sets and idempotent digests."""
        def wfn(claim, ctx, payload):
            return payload == ("proof", claim, ctx)

        l1, l2 = CM.CompatibilityLedger(wfn), CM.CompatibilityLedger(wfn)
        for l in (l1, l2):
            l.register_entity("a")
            l.register_entity("b")
        l1.file_refusal("a", "c1", "x1", witness_payload=("proof", "c1", "x1"))
        l1.file_refusal("b", "c2", "x2", witness_payload=("proof", "c2", "x2"))
        l1.file_refusal("a", "c1", "x1", witness_payload=("proof", "c1", "x1"))  # idempotent replay

        l2.file_refusal("b", "c2", "x2", witness_payload=("proof", "c2", "x2"))
        l2.file_refusal("a", "c1", "x1", witness_payload=("proof", "c1", "x1"))

        self.assertEqual(set(l1.refusals), set(l2.refusals))
        self.assertEqual(
            CM.compatibility_certificate(l1, "a", "b", "c1", "x1")["digest"],
            CM.compatibility_certificate(l2, "a", "b", "c1", "x1")["digest"],
        )

        # Same-pair two distinct valid witnesses in opposite arrival orders must converge to identical certificate (Codex F1)
        def wfn_pair(claim, ctx, payload):
            return (claim, ctx) == ("c", "x") and payload in (("w", 1), ("w", 2))

        p1, p2 = CM.CompatibilityLedger(wfn_pair), CM.CompatibilityLedger(wfn_pair)
        for p in (p1, p2):
            p.register_entity("a")
            p.register_entity("b")
        p1.file_refusal("a", "c", "x", witness_payload=("w", 1))
        p1.file_refusal("b", "c", "x", witness_payload=("w", 2))
        p2.file_refusal("b", "c", "x", witness_payload=("w", 2))
        p2.file_refusal("a", "c", "x", witness_payload=("w", 1))
        self.assertEqual(
            CM.compatibility_certificate(p1, "a", "b", "c", "x"),
            CM.compatibility_certificate(p2, "a", "b", "c", "x"),
        )

    def test_cm05_mutable_witness_payload_and_bad_flags_refused(self):
        """CM05: Mutable witness payloads (list/dict) and non-bool flags fail closed."""
        led = CM.CompatibilityLedger(lambda _c, _x, _p: True)
        led.register_entity("a")
        with self.assertRaises(CM.CompatibilityError) as c1:
            led.file_refusal("a", "c1", "x1", witness_payload=["mutable"])
        self.assertEqual(c1.exception.code, "UNSUPPORTED_VALUE")
        with self.assertRaises(CM.CompatibilityError) as c2:
            led.register_entity("b", viable_alone=1)
        self.assertEqual(c2.exception.code, "BAD_ENTITY_FLAGS")

    def test_cm06_mutants_all_killed_on_assertion(self):
        """CM06: 6 surgical mutants of compatibility.py all fail on assertion (zero crashes, zero survivors)."""
        src_path = Path(__file__).resolve().parent / "compatibility.py"
        orig = src_path.read_text(encoding="utf-8")
        mutants = [
            ("CM-M1-witness-gate", "        if not bool(self._witness_fn(claim_id, context_id, frozen_payload)):",
             "        if False:", "test_cm02_unwitnessed_refusal_fails_closed"),
            ("CM-M2-capture-gate", "        if not (ea.viable_alone and eb.viable_alone):",
             "        if False:", "test_cm03_captured_party_is_not_non_manipulatively_compatible"),
            ("CM-M3-refuted-gate", "        if (claim_id, context_id) in self._refusals:",
             "        if False:", "test_cm01_local_refusal_preserves_standing_and_other_contexts"),
            ("CM-M4-context-local", "        if (claim_id, context_id) in self._refusals:",
             "        if any(c == claim_id for c, _ in self._refusals):",
             "test_cm01_local_refusal_preserves_standing_and_other_contexts"),
            ("CM-M5-mutable-payload", '    raise CompatibilityError("UNSUPPORTED_VALUE", f"unsupported or mutable value type: {t.__name__}")',
             '    return v, ["raw", v]', "test_cm05_mutable_witness_payload_and_bad_flags_refused"),
            ("CM-M6-bool-flags", "        if type(standing) is not bool or type(viable_alone) is not bool:",
             "        if False:", "test_cm05_mutable_witness_payload_and_bad_flags_refused"),
            ("CM-M7-canonical-order",
             "        if existing is None or (wdig, challenger_id) < (existing.witness_digest, existing.challenger_id):",
             "        if existing is None:", "test_cm04_order_independence_and_idempotence"),
        ]
        for mid, find, repl, test_name in mutants:
            self.assertEqual(orig.count(find), 1, f"{mid}: find must match uniquely")
            mutated = orig.replace(find, repl, 1)
            with tempfile.TemporaryDirectory() as td:
                mp = Path(td) / "compatibility.py"
                mp.write_text(mutated, encoding="utf-8")
                spec = importlib.util.spec_from_file_location("_compat_mut", mp)
                mod = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(mod)
                saved = globals()["CM"]
                globals()["CM"] = mod
                try:
                    res = unittest.TestResult()
                    TestCompatibility(test_name).run(res)
                finally:
                    globals()["CM"] = saved
                self.assertEqual(len(res.errors), 0, f"{mid} crashed instead of failing assertion: {res.errors}")
                self.assertEqual(len(res.failures), 1, f"{mid} SURVIVED {test_name}!")


if __name__ == "__main__":
    unittest.main()
