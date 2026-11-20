#!/usr/bin/env python3
"""Tests & surgical mutant harness for `trajectory.py` and `proofs/Vars1/Trajectory.lean` (`TR01..TR10`).

    python3 test_trajectory.py
"""
import importlib.util
from pathlib import Path
import tempfile
import unittest

import trajectory as TR


def _toy_system():
    return dict(
        inv_fn=lambda s: type(s) is int and 0 <= s < 2,
        safe_act_fn=lambda _s, a: a is True,
        step_fn=lambda s, a, e: (1 if e else 0) if (a is True and 0 <= s < 2) else 2,
    )


class TestTrajectory(unittest.TestCase):
    def test_tr01_base_invariant_and_safe_trajectory_induction(self):
        """TR01: Base invariant violation fails closed; safe actions preserve inv across adversarial moves."""
        sys_kw = _toy_system()
        with self.assertRaises(TR.TrajectoryError) as ctx:
            TR.SafeTrajectory(2, **sys_kw)
        self.assertEqual(ctx.exception.code, "BASE_INVARIANT_VIOLATED")

        traj = TR.SafeTrajectory(0, **sys_kw)
        s0 = traj.advance(True, False)
        s1 = traj.advance(True, True)
        self.assertEqual((s0.step_idx, s0.next_state), (0, 0))
        self.assertEqual((s1.step_idx, s1.next_state), (1, 1))
        self.assertEqual(traj.current_state, 1)
        self.assertTrue(traj.is_safe())

    def test_tr02_unsafe_action_and_step_invariant_violation_refused(self):
        """TR02: Guard-violating action and post-step invariant violation both fail closed without mutating state."""
        traj = TR.SafeTrajectory(0, **_toy_system())
        with self.assertRaises(TR.TrajectoryError) as ctx1:
            traj.advance(False, True)
        self.assertEqual(ctx1.exception.code, "UNSAFE_ACTION")
        self.assertEqual(len(traj.steps), 0)

        # System whose guard allows an action that violates post-step invariant
        leaky = TR.SafeTrajectory(
            0,
            inv_fn=lambda s: s < 2,
            safe_act_fn=lambda _s, _a: True,
            step_fn=lambda _s, _a, _e: 2,
        )
        with self.assertRaises(TR.TrajectoryError) as ctx2:
            leaky.advance("bad", "env")
        self.assertEqual(ctx2.exception.code, "STEP_INVARIANT_VIOLATED")
        self.assertEqual(leaky.current_state, 0)
        self.assertEqual(len(leaky.steps), 0)

    def test_tr03_horizon_monotonicity_and_finite_convergence_bound(self):
        """TR03: Semantic mass is monotonic in horizon H and bounded above by total_weight for all H."""
        led = TR.SemanticMassLedger()
        led.record("a0", step_idx=0, weight=10)
        led.record("a2", step_idx=2, weight=7)
        led.record("a5", step_idx=5, weight=13)
        masses = [led.mass(h) for h in (0, 1, 2, 4, 5, 100)]
        self.assertEqual(masses, [10, 10, 17, 17, 30, 30])
        for h1, h2 in zip(masses, masses[1:]):
            self.assertLessEqual(h1, h2)
        self.assertLessEqual(led.mass(100), led.total_weight())
        self.assertEqual(led.total_weight(), 30)

    def test_tr04_forked_retold_and_duplicate_replay_add_zero_mass(self):
        """TR04: Anti-Sybil non-inflation — forked, retold, and replayed acts contribute 0 extra mass."""
        led = TR.SemanticMassLedger()
        led.record("v1", step_idx=0, weight=10, origin="verified")
        led.record("v2", step_idx=1, weight=7, origin="verified")
        led.record("f1", step_idx=1, weight=50, origin="forked")
        led.record("r1", step_idx=1, weight=50, origin="retold")
        # Identical replay is idempotent (0 extra mass)
        led.record("v1", step_idx=0, weight=10, origin="verified")
        self.assertEqual(led.mass(5), 17)
        # Conflicting replay on same act_id fails closed
        with self.assertRaises(TR.TrajectoryError) as ctx:
            led.record("v1", step_idx=0, weight=999, origin="verified")
        self.assertEqual(ctx.exception.code, "CONFLICTING_ACT_ID")

    def test_tr05_error_driven_refutation_is_non_inflationary(self):
        """TR05: Refuting an act lowers mass strictly and never inflates; unknown act_id fails closed."""
        led = TR.SemanticMassLedger()
        led.record("v1", step_idx=0, weight=10)
        led.record("v2", step_idx=1, weight=7)
        before = led.mass(5)
        led.refute("v1", reason="codex-countermodel")
        after = led.mass(5)
        self.assertEqual((before, after), (17, 7))
        self.assertLessEqual(after, before)
        # Re-recording a refuted act without refuted=True cannot un-refute it!
        led.record("v1", step_idx=0, weight=10, origin="verified", refuted=False)
        self.assertEqual(led.mass(5), 7)
        with self.assertRaises(TR.TrajectoryError) as ctx:
            led.refute("missing")
        self.assertEqual(ctx.exception.code, "UNKNOWN_ACT_ID")

    def test_tr06_strict_input_validation_rejects_bool_as_int_and_bad_origin(self):
        """TR06: Bool weights/horizons/steps and unknown origins fail closed with TrajectoryError."""
        led = TR.SemanticMassLedger()
        with self.assertRaises(TR.TrajectoryError) as c1:
            led.record("a", step_idx=True, weight=1)
        self.assertEqual(c1.exception.code, "BAD_STEP_IDX")
        with self.assertRaises(TR.TrajectoryError) as c2:
            led.record("a", step_idx=0, weight=False)
        self.assertEqual(c2.exception.code, "BAD_WEIGHT")
        with self.assertRaises(TR.TrajectoryError) as c3:
            led.record("a", step_idx=0, weight=1, origin="laundered")
        self.assertEqual(c3.exception.code, "BAD_ORIGIN")
        with self.assertRaises(TR.TrajectoryError) as c4:
            led.mass(True)
        self.assertEqual(c4.exception.code, "BAD_HORIZON")

    def test_tr07_certificate_determinism_and_immutability(self):
        """TR07: vars1-trajectory-mass@1 certificate is deterministic, content-addressed, and immutable."""
        traj = TR.SafeTrajectory(0, **_toy_system())
        traj.advance(True, False)
        traj.advance(True, True)
        led = TR.SemanticMassLedger()
        led.record("a1", step_idx=0, weight=10)
        led.record("a2", step_idx=1, weight=7)
        led.record("f1", step_idx=1, weight=50, origin="forked")
        led.refute("a1", reason="bug")
        c1 = TR.trajectory_mass_certificate(traj, led, horizon=5, label="organism-run")
        c2 = TR.trajectory_mass_certificate(traj, led, horizon=5, label="organism-run")
        self.assertEqual(c1["digest"], c2["digest"])
        self.assertEqual(len(c1["digest"]), 64)
        cert = c1["certificate"]
        self.assertEqual(cert["schema"], "vars1-trajectory-mass@1")
        self.assertTrue(cert["trajectory_safe"])
        self.assertEqual(cert["verified_mass"], 7)
        self.assertEqual(cert["refuted_ids"], ["a1"])
        self.assertEqual(len(cert["verified_acts"]), 1)

    def test_tr08_mutable_state_isolation_and_failure_atomicity(self):
        """TR08: In-place refused transitions and caller/exported state mutations cannot alter history (Codex F1)."""
        def inplace_step(state, _action, env):
            state["n"] = env
            return state

        init = {"n": 0}
        traj = TR.SafeTrajectory(
            init, inv_fn=lambda s: 0 <= s["n"] < 2, safe_act_fn=lambda _s, _a: True, step_fn=inplace_step,
        )
        init["n"] = 99
        self.assertEqual(traj.initial_state, {"n": 0})
        with self.assertRaises(TR.TrajectoryError) as ctx:
            traj.advance("go", 2)
        self.assertEqual(ctx.exception.code, "STEP_INVARIANT_VIOLATED")
        self.assertEqual(traj.initial_state, {"n": 0})
        self.assertEqual(traj.current_state, {"n": 0})
        self.assertEqual(traj.steps, ())

        # Pure step: mutating exported current_state or returned step cannot rewrite recorded history
        traj2 = TR.SafeTrajectory(
            {"n": 0}, inv_fn=lambda s: 0 <= s["n"] < 10,
            safe_act_fn=lambda _s, _a: True, step_fn=lambda s, a, _e: {"n": s["n"] + a},
        )
        ret = traj2.advance(1, None)
        ret.next_state["n"] = 8
        exported = traj2.current_state
        exported["n"] = 7
        self.assertEqual(traj2.current_state, {"n": 1})
        self.assertEqual(traj2.steps[0].next_state, {"n": 1})
        self.assertTrue(traj2.is_safe())

        # Closed state domain refuses functions and custom mutable objects even nested inside dicts
        def box():
            pass

        box.n = 0
        with self.assertRaises(TR.TrajectoryError) as ctx_fn:
            TR.SafeTrajectory({"box": box}, inv_fn=lambda _s: True, safe_act_fn=lambda _s, _a: True, step_fn=lambda s, _a, _e: s)
        self.assertEqual(ctx_fn.exception.code, "UNSUPPORTED_STATE")

    def test_tr09_mutants_all_killed_on_assertion(self):
        """TR09: 12 surgical mutants of trajectory.py all fail on assertion (zero crashes, zero survivors)."""
        src_path = Path(__file__).resolve().parent / "trajectory.py"
        orig = src_path.read_text(encoding="utf-8")
        mutants = [
            ("TR-M1-base-inv", "        if not bool(inv_fn(_snapshot(init_snap))):", "        if False:",
             "test_tr01_base_invariant_and_safe_trajectory_induction"),
            ("TR-M2-safe-act", "        if not bool(self._safe_act_fn(_snapshot(self._current), _snapshot(act_snap))):", "        if False:",
             "test_tr02_unsafe_action_and_step_invariant_violation_refused"),
            ("TR-M3-step-inv", "        if not bool(self._inv_fn(_snapshot(next_state))):", "        if False:",
             "test_tr02_unsafe_action_and_step_invariant_violation_refused"),
            ("TR-M4-horizon-cmp", '            if act.origin == "verified" and not act.refuted and act.step_idx <= horizon:\n                total += act.weight',
             '            if act.origin == "verified" and not act.refuted:\n                total += act.weight',
             "test_tr03_horizon_monotonicity_and_finite_convergence_bound"),
            ("TR-M5-origin-check", '            if act.origin == "verified" and not act.refuted and act.step_idx <= horizon:\n                total += act.weight',
             "            if not act.refuted and act.step_idx <= horizon:\n                total += act.weight",
             "test_tr04_forked_retold_and_duplicate_replay_add_zero_mass"),
            ("TR-M6-refuted-check", '            if act.origin == "verified" and not act.refuted and act.step_idx <= horizon:\n                total += act.weight',
             '            if act.origin == "verified" and act.step_idx <= horizon:\n                total += act.weight',
             "test_tr05_error_driven_refutation_is_non_inflationary"),
            ("TR-M7-conflict-id", "            if (existing.step_idx, existing.weight, existing.origin) != (step_idx, weight, origin):",
             "            if False:",
             "test_tr04_forked_retold_and_duplicate_replay_add_zero_mass"),
            ("TR-M8-bool-int", "    return type(v) is int", "    return isinstance(v, int)",
             "test_tr06_strict_input_validation_rejects_bool_as_int_and_bad_origin"),
            ("TR-M9-origin-allow", "        if type(origin) is not str or origin not in VALID_ORIGINS:", "        if False:",
             "test_tr06_strict_input_validation_rejects_bool_as_int_and_bad_origin"),
            ("TR-M10-unknown-refute",
             '        if act_id not in self._acts:\n            raise TrajectoryError("UNKNOWN_ACT_ID", f"unknown act_id {act_id!r}")',
             "        if act_id not in self._acts:\n            return None",
             "test_tr05_error_driven_refutation_is_non_inflationary"),
            ("TR-M11-state-dict-copy",
             "    if t is dict:\n        return {_snapshot(k, _depth + 1): _snapshot(val, _depth + 1) for k, val in v.items()}",
             "    if t is dict:\n        return v",
             "test_tr08_mutable_state_isolation_and_failure_atomicity"),
            ("TR-M12-closed-domain",
             '    raise TrajectoryError("UNSUPPORTED_STATE", f"unsupported state/input type: {t.__name__}")',
             "    return v",
             "test_tr08_mutable_state_isolation_and_failure_atomicity"),
        ]
        for mid, find, repl, test_name in mutants:
            self.assertEqual(orig.count(find), 1, f"{mid}: find must match uniquely")
            mutated = orig.replace(find, repl, 1)
            with tempfile.TemporaryDirectory() as td:
                mp = Path(td) / "trajectory.py"
                mp.write_text(mutated, encoding="utf-8")
                spec = importlib.util.spec_from_file_location("_trajectory_mut", mp)
                mod = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(mod)
                saved = globals()["TR"]
                globals()["TR"] = mod
                try:
                    res = unittest.TestResult()
                    TestTrajectory(test_name).run(res)
                finally:
                    globals()["TR"] = saved
                self.assertEqual(len(res.errors), 0, f"{mid} crashed instead of failing assertion: {res.errors}")
                self.assertEqual(len(res.failures), 1, f"{mid} SURVIVED {test_name}!")


if __name__ == "__main__":
    unittest.main()
