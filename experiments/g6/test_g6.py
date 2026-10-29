"""Tests of the G6 pilot's generator, renderings, runner and scorer (PREREG.md). Run from the repository root:

    .venv/bin/python experiments/g6/test_g6.py              # the tests
    .venv/bin/python experiments/g6/test_g6.py --mutants    # each mutant in mutants.json must fail its named test

A mutant must fail its test on an assertion: an error is not a kill.
"""
import hashlib
import importlib.util
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
import urllib.error
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = Path(os.environ.get("G6_SOURCE", HERE / "g6.py"))
spec = importlib.util.spec_from_file_location("g6", SOURCE)
g6 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(g6)
WORK = Path.home() / "Projects" / ".worktrees" / "g6-work"
WORK.mkdir(parents=True, exist_ok=True)
_TASKS = {}


def task(i: int):
    """The i-th task of the seed `test`, built once per run (a chain takes seconds)."""
    if i not in _TASKS:
        s, size = g6.seeds("test", i + 1)[i]
        _TASKS[i] = g6.task(s, size, WORK)
    return _TASKS[i]


def evidence(prompt: str) -> str:
    return prompt.split("<record>\n", 1)[1].split("\n</record>", 1)[0]


def decode_markdown(text: str) -> dict:
    """The facts a reader of M can take from it, read with patterns of this test's own."""
    grounds = [{"id": m[0], "name": m[1], "by": m[2], "text": m[3]}
               for m in re.findall(r"^\| (G\d+) (.+?) \| (\w+) \| (.+?) \|$", text, re.M)]
    checks = [{"id": m[0], "name": m[1], "by": m[2], "rests": m[3].split(", ")}
              for m in re.findall(r"^\| (K\d+) `(.+?)` \| (\w+) \| passed \| (.+?) \|$", text, re.M)]
    decisions, approvals = [], []
    for block in re.split(r"^### Pull request #\d+: ", text, flags=re.M)[1:]:
        head = re.match(r"(D\d+) (.+?) \(merged\)\n\nOpened by (\w+)\.\nRests on checks: (.+?)\.\n", block)
        did = head.group(1)
        decisions.append({"id": did, "title": head.group(2), "by": head.group(3),
                          "rests": re.findall(r"(K\d+) `", head.group(4))})
        for who, ran in re.findall(r'^- (\w+) approved: "I ran (.+?); approving\."$', block, re.M):
            approvals.append({"decision": did, "by": who, "relies": re.findall(r"(K\d+) `", ran)})
    failed = re.search(r"^### Issue #\d+: (G\d+) ", text, re.M).group(1)
    return {"grounds": grounds, "checks": checks, "decisions": decisions, "approvals": approvals, "failed": failed}


def decode_chain(text: str) -> dict:
    """The facts a reader of C can take from its cells, by following ids."""
    rows = [json.loads(x) for x in text.splitlines() if x.startswith("{")]
    label = {r["id"]: r["name"].split("/")[2] for r in rows if r["name"].split("/")[1] in ("ground", "check", "decision")}
    grounds, checks, decisions, approvals, failed = [], [], [], [], None
    for r in rows:
        kind = r["name"].split("/")[1]
        if kind == "ground":
            name, text_ = r["payload"].split(": ", 1)
            grounds.append({"id": label[r["id"]], "name": name, "by": r["sealed_by"], "text": text_})
        elif kind == "check":
            checks.append({"id": label[r["id"]], "name": re.match(r"`(.+)` passed$", r["payload"]).group(1),
                           "by": r["sealed_by"], "rests": [label[x] for x in r["relies_on"]]})
        elif kind == "decision" and r["schema"] == "decision":
            did, title = r["payload"].split(": ", 1)
            decisions.append({"id": did, "title": title, "by": r["sealed_by"],
                              "rests": [label[x] for x in r["relies_on"]]})
        elif r["schema"] == "verdict":
            approvals.append({"decision": label[r["attests"][0]], "by": r["sealed_by"],
                              "relies": [label[x] for x in r["relies_on"]]})
        elif kind == "notice":
            failed = label[r["invalidates"][0]]
    return {"grounds": grounds, "checks": checks, "decisions": decisions, "approvals": approvals, "failed": failed}


def facts(h: dict) -> dict:
    """The facts as sets: a chain lists what a cell relies on in hash order, a pull request in the order written."""
    key = lambda d: sorted(json.dumps(x, sort_keys=True) for x in d)
    norm = lambda xs, fields: key([{f: sorted(x[f]) if isinstance(x[f], list) else x[f] for f in fields} for x in xs])
    return {"grounds": norm(h["grounds"], ("id", "name", "by", "text")),
            "checks": norm(h["checks"], ("id", "name", "by", "rests")),
            "decisions": norm(h["decisions"], ("id", "title", "by", "rests")),
            "approvals": norm(h["approvals"], ("decision", "by", "relies")), "failed": h["failed"]}


class T(unittest.TestCase):
    def test_01_a_seed_gives_one_task(self) -> None:
        """The same seed and size give the same history, answer and prompts, byte for byte."""
        s, size = g6.seeds("test", 1)[0]
        again = g6.task(s, size, WORK)
        self.assertEqual(json.dumps(again, sort_keys=True), json.dumps(task(0), sort_keys=True))
        self.assertNotEqual(g6.seeds("test", 2)[1][0], s)
        self.assertEqual([z for _, z in g6.seeds("x", 4)], ["S", "L", "S", "L"])

    def test_02_the_chain_and_the_closure_agree_or_the_task_is_refused(self) -> None:
        """The chain's `what_if` and the closure give the same answer, of both kinds; a closure that disagrees with the
        chain is refused."""
        for s, size in g6.seeds("test", 2):
            h = g6.history(s, size)
            with tempfile.TemporaryDirectory(dir=WORK) as d:
                chain = g6.build_chain(h, s, Path(d))
                self.assertEqual(g6.whatif_truth(h, chain), g6.closure_truth(h))
            self.assertEqual(set(g6.closure_truth(h).values()), {g6.RELY, g6.DROP})
        s, size = g6.seeds("test", 1)[0]
        real = g6.closure_truth
        flipped = lambda h: {**real(h), "D01": g6.RELY if real(h)["D01"] == g6.DROP else g6.DROP}
        g6.closure_truth = flipped
        try:
            with self.assertRaisesRegex(SystemExit, "disagree"):
                g6.task(s, size, WORK)
        finally:
            g6.closure_truth = real

    def test_03_every_case_occurs(self) -> None:
        """Each history has a decision lost by its own check, one lost by its approvals, one kept on a thinner
        margin, and answers of both kinds within the size's bounds."""
        for i in range(2):
            t = task(i)
            h = t["history"]
            self.assertTrue({"own", "approvals", "margin"} <= set(t["kinds"].values()))
            low, high, keep = g6.BOUNDS[h["size"]]
            drop = list(t["truth"].values()).count(g6.DROP)
            self.assertTrue(low <= drop <= high and len(t["truth"]) - drop >= keep)
            self.assertEqual(len(h["decisions"]), g6.SIZES[h["size"]][2])
            for d in h["decisions"]:  # in force before the failure: two approvals or more
                self.assertGreaterEqual(len({a["by"] for a in h["approvals"] if a["decision"] == d["id"]}), 2)

    def test_04_every_rendering_carries_the_same_facts(self) -> None:
        """M and C each decode, with this test's own reading, to exactly the history's facts; W is C with the report
        after it."""
        for i in range(2):
            t = task(i)
            want = facts(t["history"])
            self.assertEqual(facts(decode_markdown(evidence(t["prompts"]["M"]))), want)
            self.assertEqual(facts(decode_chain(evidence(t["prompts"]["C"]))), want)
            self.assertTrue(evidence(t["prompts"]["W"]).startswith(evidence(t["prompts"]["C"]) + "\n\n"))

    def test_05_the_report_answers_what_the_truth_says(self) -> None:
        """W's report lists as lost exactly the decisions no longer in force, and the digest is the chain's."""
        for i in range(2):
            t = task(i)
            w = evidence(t["prompts"]["W"]).split("\n\nlost:\n", 1)[1].split("\n\nheld:\n", 1)[0]
            lost = {json.loads(x)["name"].split("/")[2] for x in w.splitlines()
                    if json.loads(x)["name"].count("/") == 2 and "/decision/" in json.loads(x)["name"]}
            self.assertEqual(lost, {d for d, v in t["truth"].items() if v == g6.DROP})
            self.assertRegex(t["whatif_digest"], r"^[0-9a-f]{64}$")

    def test_06_only_the_evidence_differs(self) -> None:
        """The instructions, rules and question are the same text in every arm."""
        t = task(1)
        strip = lambda p: p.split("<record>\n", 1)[0] + p.split("\n</record>", 1)[1]
        self.assertEqual(len({strip(t["prompts"][a]) for a in g6.ARMS}), 1)
        self.assertIn("D01 to D30", t["prompts"]["M"])

    def test_07_a_reply_is_its_last_json_block_or_invalid(self) -> None:
        items = ["D01", "D02"]
        ok = 'thinking\n```json\n{"D01": "RELY", "D02": "DO_NOT_RELY"}\n```'
        self.assertEqual(g6.parse_answer(ok, items), {"D01": "RELY", "D02": "DO_NOT_RELY"})
        two = '```json\n{"D01": "RELY", "D02": "RELY"}\n```\nno, wait\n```json\n{"D01": "DO_NOT_RELY", "D02": "RELY"}\n```'
        self.assertEqual(g6.parse_answer(two, items), {"D01": "DO_NOT_RELY", "D02": "RELY"}, "the last block counts")
        for bad in ['{"D01": "RELY", "D02": "RELY"}',  # no fence
                    '```json\n{"D01": "RELY"}\n```',  # a decision missing
                    '```json\n{"D01": "RELY", "D02": "RELY", "D03": "RELY"}\n```',  # one too many
                    '```json\n{"D01": "rely", "D02": "RELY"}\n```',  # not one of the two words
                    '```json\n{"D01": "RELY", "D02": \n```',  # cut off
                    '```json\n["RELY", "RELY"]\n```', "", None]:
            self.assertIsNone(g6.parse_answer(bad, items), bad)

    def test_08_rates_and_the_paired_contrast(self) -> None:
        truth = {"D01": g6.DROP, "D02": g6.DROP, "D03": g6.RELY, "D04": g6.RELY}
        all_rely = {d: g6.RELY for d in truth}
        self.assertEqual(g6.rates(all_rely, truth), {"wrong_reliance": 1.0, "over_caution": 0.0})
        self.assertEqual(g6.rates({**truth, "D01": g6.RELY, "D03": g6.DROP}, truth),
                         {"wrong_reliance": 0.5, "over_caution": 0.5})
        self.assertIsNone(g6.rates(None, truth))
        good, bad = g6.rates(truth, truth), g6.rates(all_rely, truth)
        cells = {}
        for i in range(8):
            cells[(f"h{i}", "m", "M")] = bad
            cells[(f"h{i}", "m", "W")] = good
            cells[(f"h{i}", "m", "C")] = bad
        w = g6.contrast(cells, "W", "wrong_reliance")
        self.assertEqual((w["pairs"], w["mean_difference"], w["positive"], w["verdict"]), (8, 1.0, 8, "W lowers it"))
        self.assertEqual(g6.contrast(cells, "C", "wrong_reliance")["verdict"], "no difference detected")
        cells[("h0", "m", "W")] = None
        self.assertEqual(g6.contrast(cells, "W", "wrong_reliance")["pairs"], 7, "an invalid reply leaves its pair out")
        self.assertEqual(g6.contrast(cells, "W", "wrong_reliance", invalid_as_worst=True)["pairs"], 8)
        flip = {k: (good if k[2] == "M" else bad) for k in cells}
        self.assertEqual(g6.contrast(flip, "W", "wrong_reliance")["verdict"], "W raises it")

    def test_09_the_sign_test_is_exact(self) -> None:
        self.assertAlmostEqual(g6.sign_test([1.0] * 10)["p"], 2 / 1024)
        self.assertEqual(g6.sign_test([1.0, 1.0, -1.0])["p"], 1.0)
        self.assertAlmostEqual(g6.sign_test([0.5] * 6 + [-0.5, 0.0])["p"], 2 * 8 / 128)
        self.assertEqual(g6.sign_test([0.0, 0.0])["ties"], 2)
        self.assertEqual(g6.sign_test([0.0, 0.0])["p"], 1.0)

    def test_10_the_runner_asks_each_once_retries_resumes_and_stops_at_the_budget(self) -> None:
        with tempfile.TemporaryDirectory(dir=WORK) as d:
            d = Path(d)
            tasks = d / "tasks"
            tasks.mkdir()
            for i in range(2):
                (tasks / f"h{i:02d}.json").write_text(json.dumps(task(i)))
            files = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(tasks.glob("h*.json"))}
            (tasks / "MANIFEST.json").write_text(json.dumps({"seed": "test", "count": 2, "files": files}))
            asked, flaky = [], {"left": 2}

            def caller(model, text, key, max_tokens):
                if flaky["left"]:
                    flaky["left"] -= 1
                    raise urllib.error.URLError("down")
                asked.append((model, text))
                t = next(task(i) for i in range(2) if text in task(i)["prompts"].values())
                return {"model": model, "usage": {"cost": 0.02},
                        "choices": [{"message": {"content": "```json\n" + json.dumps(t["truth"]) + "\n```"}}]}
            g6.time.sleep = lambda s: None
            st = g6.run(tasks, d / "out", ["a/x", "b/y"], 5.0, 100, caller=caller, key="k")
            self.assertEqual((st["recorded"], st["planned"], st["stopped"]), (12, 12, None))
            self.assertEqual(len(asked), 12)
            self.assertEqual(len(set(asked)), 12, "each prompt to each model once")
            first = json.loads(next((d / "out" / "raw").glob("*.json")).read_text())
            self.assertIn("attempts", first)
            self.assertEqual(sum(len(json.loads(p.read_text())["attempts"]) for p in (d / "out" / "raw").glob("*")),
                             14, "two failed attempts, then one each")
            g6.run(tasks, d / "out", ["a/x", "b/y"], 5.0, 100, caller=caller, key="k")
            self.assertEqual(len(asked), 12, "a recorded reply is not asked again")
            st = g6.run(tasks, d / "out2", ["a/x", "b/y"], 0.30, 100, caller=caller, key="k")
            self.assertEqual(st["recorded"], 3, "it stops once less than a quarter of a dollar is left (0.06 of 0.30)")
            self.assertIn("budget", st["stopped"])
            s = g6.score(tasks, d / "out")
            self.assertEqual(s["primary"]["mean_difference"], 0.0)
            self.assertEqual(s["invalid"], {"M": 0, "C": 0, "W": 0})
            self.assertTrue(all(v == 1.0 for v in s["accuracy_by_case"].values()))

    def test_12_the_closure_reads_the_rules(self) -> None:
        """A history small enough to answer by hand: G1 fails; D02 rests on K1 (own), D03 keeps one approval
        (approvals), D01 keeps two of three (margin), D04 is untouched."""
        h = {"size": "S", "failed": "G1",
             "checks": [{"id": "K1", "rests": ["G1"]}, {"id": "K2", "rests": ["G2"]}, {"id": "K3", "rests": ["G1", "G2"]}],
             "decisions": [{"id": "D01", "rests": ["K2"]}, {"id": "D02", "rests": ["K1"]}, {"id": "D03", "rests": ["K2"]},
                           {"id": "D04", "rests": ["K2"]}],
             "approvals": [{"decision": "D01", "by": "ana", "relies": ["K1"]},
                           {"decision": "D01", "by": "bo", "relies": ["K2"]},
                           {"decision": "D01", "by": "cy", "relies": ["K2"]},
                           {"decision": "D02", "by": "ana", "relies": ["K2"]},
                           {"decision": "D02", "by": "bo", "relies": ["K2"]},
                           {"decision": "D03", "by": "ana", "relies": ["K3"]},
                           {"decision": "D03", "by": "bo", "relies": ["K2", "K1"]},
                           {"decision": "D03", "by": "cy", "relies": ["K2"]},
                           {"decision": "D04", "by": "ana", "relies": ["K2"]},
                           {"decision": "D04", "by": "cy", "relies": ["K2"]}]}
        self.assertEqual(g6.closure_truth(h), {"D01": g6.RELY, "D02": g6.DROP, "D03": g6.DROP, "D04": g6.RELY})
        self.assertEqual(g6.kinds(h), {"D01": "margin", "D02": "own", "D03": "approvals", "D04": "untouched"})

    def test_13_a_history_lacking_a_case_is_not_accepted(self) -> None:
        real_k, real_t = g6.kinds, g6.closure_truth
        truth = {f"D{i:02d}": g6.DROP if i <= 4 else g6.RELY for i in range(1, 13)}
        full = {f"D{i:02d}": k for i, k in zip(range(1, 13), ["own", "approvals", "margin"] + ["untouched"] * 9)}
        try:
            g6.closure_truth = lambda h: truth
            for missing in ("own", "approvals", "margin"):
                g6.kinds = lambda h, m=missing: {d: ("untouched" if k == m else k) for d, k in full.items()}
                self.assertFalse(g6.accept({"size": "S"}), missing)
            g6.kinds = lambda h: full
            self.assertTrue(g6.accept({"size": "S"}))
            g6.closure_truth = lambda h: {d: g6.DROP for d in truth}
            self.assertFalse(g6.accept({"size": "S"}), "too few still in force")
        finally:
            g6.kinds, g6.closure_truth = real_k, real_t

    def test_14_the_key_holds_the_cap(self) -> None:
        """A key with no credit limit, or one above the cap, is refused; the budget is what the key has left, at most
        the cap."""
        info = lambda d: (lambda key: d)
        with self.assertRaisesRegex(SystemExit, "no credit limit"):
            g6.key_budget("k", 5, info({"limit": None, "limit_remaining": None, "usage": 1.0}))
        with self.assertRaisesRegex(SystemExit, "above the cap"):
            g6.key_budget("k", 5, info({"limit": 20, "limit_remaining": 4.0, "usage": 16.0}))
        self.assertEqual(g6.key_budget("k", 5, info({"limit": 5, "limit_remaining": 4.948, "usage": 0.052})), 4.948)
        self.assertEqual(g6.key_budget("k", 5, info({"limit": 5, "limit_remaining": 5.0, "usage": 0})), 5.0)
        self.assertEqual(g6.key_budget("k", 3, info({"limit": 3, "limit_remaining": 3.0, "usage": 0})), 3.0)

    def _tasks(self, d: Path, seed: str, n: int) -> Path:
        """Stub tasks with a manifest as `generate` writes it."""
        tasks = d / "tasks"
        tasks.mkdir()
        for i in range(n):
            (tasks / f"h{i:02d}.json").write_text(json.dumps({"prompts": {a: f"{seed} {i} {a}" for a in g6.ARMS},
                                                              "truth": {"D01": g6.RELY, "D02": g6.DROP},
                                                              "kinds": {"D01": "untouched", "D02": "own"},
                                                              "history": {"size": "S"}}))
        files = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(tasks.glob("h*.json"))}
        (tasks / "MANIFEST.json").write_text(json.dumps({"seed": seed, "count": n, "files": files}, indent=1) + "\n")
        return tasks

    def test_15_a_resumed_run_spends_what_the_key_has_left(self) -> None:
        """Codex F1 (PR #40): an interrupted run resumes against what the key has left, counting only what it spends
        from then on, so an interruption does not change where the run stops."""
        with tempfile.TemporaryDirectory(dir=WORK) as d:
            d = Path(d)
            tasks = self._tasks(d, "freeze", 16)
            models, made = ["one/m", "two/m", "three/m"], []
            reply = {"usage": {"cost": 0.03}, "choices": [{"message": {"content": ""}}]}

            def interrupted(model, text, key, max_tokens):
                if len(made) == 80:
                    raise KeyboardInterrupt()
                made.append(text)
                return reply
            with self.assertRaises(KeyboardInterrupt):
                g6.run(tasks, d / "out", models, 5.0, 100, caller=interrupted, key="k")
            st = g6.run(tasks, d / "out", models, 5.0 - 80 * 0.03, 100, caller=lambda *a: reply, key="k")
            self.assertEqual((st["recorded"], st["stopped"]), (144, None))
            self.assertAlmostEqual(st["spent"], 144 * 0.03)

    def test_16_results_belong_to_the_tasks_they_were_made_from(self) -> None:
        """Codex F2 (PR #40): replies recorded for one set of tasks are neither resumed nor scored against another."""
        with tempfile.TemporaryDirectory(dir=WORK) as d:
            d = Path(d)
            tasks = self._tasks(d, "smoke-old", 2)
            reply = lambda *a: {"usage": {"cost": 0.0},
                                "choices": [{"message": {"content": '```json\n{"D01": "RELY", "D02": "RELY"}\n```'}}]}
            g6.run(tasks, d / "out", ["a/m"], 5.0, 100, caller=reply, key="k")
            shutil.rmtree(tasks)
            tasks = self._tasks(d, "smoke-new", 2)
            asked = []
            with self.assertRaisesRegex(SystemExit, "other tasks"):
                g6.run(tasks, d / "out", ["a/m"], 5.0, 100, caller=lambda *a: asked.append(a) or reply(), key="k")
            self.assertEqual(asked, [])
            with self.assertRaisesRegex(SystemExit, "other tasks"):
                g6.score(tasks, d / "out")

    def test_17_tasks_bind_to_their_seed_count_and_bytes(self) -> None:
        """`bind` returns the tasks' identity only for the seed and count asked, and only while every task file is the
        one its manifest names."""
        with tempfile.TemporaryDirectory(dir=WORK) as d:
            tasks = self._tasks(Path(d), "smoke-f", 2)
            self.assertEqual(g6.bind(tasks, "smoke-f", 2), g6.tasks_identity(tasks))
            with self.assertRaisesRegex(SystemExit, "seed"):
                g6.bind(tasks, "smoke-g", 2)
            with self.assertRaisesRegex(SystemExit, "count"):
                g6.bind(tasks, "smoke-f", 3)
            (tasks / "h01.json").write_text((tasks / "h01.json").read_text().replace("smoke-f 1", "smoke-f 9"))
            with self.assertRaisesRegex(SystemExit, "not the file its manifest names"):
                g6.bind(tasks, "smoke-f", 2)
            (tasks / "h01.json").write_text((tasks / "h01.json").read_text().replace("smoke-f 9", "smoke-f 1"))
            self.assertEqual(g6.bind(tasks, "smoke-f", 2), g6.tasks_identity(tasks), "restored, it binds again")
            (tasks / "h02.json").write_text((tasks / "h01.json").read_text())
            with self.assertRaisesRegex(SystemExit, "not the ones its manifest names"):
                g6.bind(tasks, "smoke-f", 2)
            (tasks / "h02.json").unlink()
            (tasks / "h01.json").unlink()
            with self.assertRaisesRegex(SystemExit, "not the ones its manifest names"):
                g6.bind(tasks, "smoke-f", 2)

    def test_18_the_runner_and_scorer_check_the_task_bytes(self) -> None:
        """Codex F3 (PR #40): a task file changed under an unchanged manifest is refused by the runner and the scorer
        themselves, not only by `bind`: no reply is reused for another prompt or scored against another answer."""
        with tempfile.TemporaryDirectory(dir=WORK) as d:
            d = Path(d)
            tasks = self._tasks(d, "freeze", 2)
            reply = lambda *a: {"usage": {"cost": 0.0},
                                "choices": [{"message": {"content": '```json\n{"D01": "RELY", "D02": "DO_NOT_RELY"}\n```'}}]}
            g6.run(tasks, d / "out", ["a/m"], 5.0, 100, caller=reply, key="k")
            ident = g6.tasks_identity(tasks)
            t = json.loads((tasks / "h00.json").read_text())
            t["truth"] = {"D01": g6.DROP, "D02": g6.RELY}
            (tasks / "h00.json").write_text(json.dumps(t))
            self.assertEqual(g6.tasks_identity(tasks), ident, "the manifest itself is unchanged")
            asked = []
            with self.assertRaisesRegex(SystemExit, "not the file its manifest names"):
                g6.run(tasks, d / "out", ["a/m"], 5.0, 100, caller=lambda *a: asked.append(a) or reply(), key="k")
            self.assertEqual(asked, [])
            with self.assertRaisesRegex(SystemExit, "not the file its manifest names"):
                g6.score(tasks, d / "out")

    def test_19_an_invalid_reply_says_why(self) -> None:
        """A reply cut off at the token cap is `truncated`, one that answered otherwise than asked is `format`, and a
        request with no response is `no answer`; the scorer counts them by arm."""
        cut = {"response": {"choices": [{"finish_reason": "length", "message": {"content": ""}}]}}
        bad = {"response": {"choices": [{"finish_reason": "stop", "message": {"content": "RELY"}}]}}
        self.assertEqual([g6.invalid_reason(r) for r in (cut, bad, {"attempts": []})],
                         ["truncated", "format", "no answer"])
        with tempfile.TemporaryDirectory(dir=WORK) as d:
            d = Path(d)
            tasks = self._tasks(d, "freeze", 2)
            replies = iter([cut["response"], bad["response"]] + [{"choices": [{"finish_reason": "stop", "message": {
                "content": '```json\n{"D01": "RELY", "D02": "DO_NOT_RELY"}\n```'}}]}] * 4)
            order = g6.plan({"h00": {}, "h01": {}}, ["a/m"], "freeze")
            g6.run(tasks, d / "out", ["a/m"], 5.0, 100, caller=lambda *x: next(replies), key="k")
            s = g6.score(tasks, d / "out")
            self.assertEqual(s["invalid_reasons"], {f"{order[0][2]} truncated": 1, f"{order[1][2]} format": 1}
                             if order[0][2] != order[1][2] else {f"{order[0][2]} format": 1, f"{order[0][2]} truncated": 1})
            self.assertEqual(sum(s["invalid"].values()), 2)

    def test_11_the_order_mixes_the_arms(self) -> None:
        """Every (history, model, arm) once, in an order fixed by the seed, not arm after arm."""
        ts = {f"h{i:02d}": {} for i in range(4)}
        p = g6.plan(ts, ["a", "b"], "s")
        self.assertEqual(sorted(p), sorted((t, m, a) for t in ts for m in ("a", "b") for a in g6.ARMS))
        self.assertEqual(p, g6.plan(ts, ["a", "b"], "s"))
        self.assertNotEqual(p, g6.plan(ts, ["a", "b"], "t"))
        self.assertNotEqual([a for _, _, a in p[:8]], ["M"] * 8)


def mutants() -> int:
    """Apply each mutant of mutants.json to a copy of g6.py and run its named test against the copy; it must fail on
    an assertion. Prints one line per mutant; returns the number that survived."""
    survived = 0
    for mid, m in json.loads((HERE / "mutants.json").read_text()).items():
        src = (HERE / "g6.py").read_text()
        if src.count(m["find"]) != 1:
            print(f"lost     {mid}: its text is not in g6.py exactly once")
            survived += 1
            continue
        copy = HERE / "_mutant.py"  # beside g6.py, so that it finds the repository as g6.py does
        try:
            copy.write_text(src.replace(m["find"], m["replace"]))
            r = subprocess.run([sys.executable, str(Path(__file__)), f"T.{m['kills']}"], capture_output=True, text=True,
                               env={**os.environ, "G6_SOURCE": str(copy)}, cwd=HERE.parents[1])
        finally:
            copy.unlink(missing_ok=True)
        out = r.stdout + r.stderr
        killed = r.returncode != 0 and "AssertionError" in out and "Error: " not in out.replace("AssertionError: ", "")
        print(f"{'killed' if killed else 'SURVIVED'} {mid}: {m['kills']}")
        survived += not killed
    return survived


if __name__ == "__main__":
    if sys.argv[1:] == ["--mutants"]:
        sys.exit(1 if mutants() else 0)
    unittest.main(argv=[sys.argv[0], *sys.argv[1:]], verbosity=1)
