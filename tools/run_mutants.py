#!/usr/bin/env python3
"""Run the mutants of mutants.json: each replaces one exact string in one file, then the tests it names must fail
on an assertion, or on a TwinDivergence (the rules kernel and its Python twin disagree: the differential witness
caught the mutant). An import error or any other crash proves nothing, and neither does a test whose only failure
is assertRaisesRegex meeting the expected refusal in other words: the input is still refused (by another layer, or
by the gate's net for crashes), so the mutant took nothing away. A mutant of a value the module checks as it loads
names that check (`refused_at_import`: module and message) and counts only if that check stops the import. The file
is restored after every mutant.
A mutant of a crate's src/ in KERNELS is built to wasm in its own target directory (under MINDS_KERNEL_TARGET,
default kernel-mutants-target in the checkout's git directory) and its tests receive the build in the variable KERNELS names.

    .venv/bin/python tools/run_mutants.py                     # all, one worker per CPU
    .venv/bin/python tools/run_mutants.py ID...               # some
    .venv/bin/python tools/run_mutants.py --shard 2/3 --jobs 4  # the second of three shards, four at once

Workers run in clones of their own under the checkout's git directory (`worker_trees`): a mutant is applied, built
and tested in one of them alone, so N at once give the verdicts of one at a time.

A kill names a test of test_vars1.TestVars1Conformance by its method, or any other test by its dotted name. A test
that asks for a named refusal (`_gate_refuses`) is run first asking only for the refusal: a mutant caught only by the
name must be declared `diagnostic`, and a mutant so declared must be caught so by none of its tests (`classify`,
`decide`).
"""
from __future__ import annotations

import hashlib
import json
import os
import queue
import shutil
import subprocess
import sys
import tempfile
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
# A kernel build a mutant may need: its crate, cargo's features, the wasm, the variable that hands it to the tests,
# and the pinned module it must differ from. A mutant of a crate's src/ gets that crate's default build.
KERNELS = {"kernel": ("kernel", (), "vars_lens.wasm", "MINDS_KERNEL_WASM", "kernel/lens.wasm"),
           "kernel2": ("kernel2", (), "vars_lens2.wasm", "MINDS_KERNEL2_WASM", "kernel2/lens2.wasm"),
           # experiment 6a (experiments/warrant-checker/README.md): test 135 asks the build
           "warrant-checker": ("experiments/warrant-checker", (), "warrant_checker.wasm", "MINDS_WARRANT_CHECKER_WASM",
                               "experiments/warrant-checker/checker.wasm")}


def git_dir() -> Path:
    # the checkout's own git directory: in a linked worktree .git is a file naming it
    return Path(subprocess.run(["git", "rev-parse", "--absolute-git-dir"], cwd=ROOT, check=True,
                               capture_output=True, text=True).stdout.strip())


def outcomes(test: str, cwd: Path, env: dict) -> list:
    """Every failure of one test under a mutant (tools/mutant_test.py), as (kind, message): `kill`, `twin`,
    `wording` or `crash`; empty when the test passed. A run that gives no report is one crash."""
    # a fresh bytecode cache per run: a cache written for an earlier mutant of the same size in the same second
    # would otherwise be loaded in place of this one's source
    with tempfile.TemporaryDirectory() as cache:
        # the harness of the tree under test, as a mutant of the harness itself sees it; a fixture has none
        harness = Path(cwd) / "tools" / "mutant_test.py"
        if not harness.is_file():
            harness = Path(__file__).resolve().parent / "mutant_test.py"
        out = subprocess.run([sys.executable, "-X", f"pycache_prefix={cache}", str(harness), test],
                             cwd=cwd, capture_output=True, text=True, env=env)
    try:
        return [tuple(o) for o in json.loads(out.stdout.strip().splitlines()[-1])["outcomes"]]
    except (IndexError, ValueError, KeyError, TypeError):
        return [("crash", (out.stderr.strip().splitlines() or [""])[-1])]


def verdict(test: str, cwd: Path, env: dict) -> tuple[str, str]:
    """How one test ended under a mutant: `kill` or `twin` if any failure says so, else `wording` if one does, else
    `none` (passed, or only crashed); with the first message of that kind."""
    found = outcomes(test, cwd, env)
    for how in ("kill", "twin", "wording"):
        for kind, message in found:
            if kind == how:
                return how, message
    return "none", next((message for _, message in found), "passed")


def classify(test: str, cwd: Path, env: dict) -> tuple[str, str]:
    """What one named test sees of a mutant, as (kind, message). First with `_gate_refuses` asking only that the
    input is refused and the ref unmoved (MINDS_REFUSAL=semantic): a kill there is `semantic` (or `twin`), a lost
    behaviour. Only if that run passed, the test as written: a kill now is `named`, the input still refused and
    only its named reason lost. A crash or other words in the first run give no ground to call what follows a lost
    reason (Codex, P27-F2): they are `none` or `wording`, as a run that passed or only crashed is."""
    first = outcomes(test, cwd, dict(env, MINDS_REFUSAL="semantic"))
    for kind, label in (("kill", "semantic"), ("twin", "twin")):
        hit = next((message for k, message in first if k == kind), None)
        if hit is not None:
            return label, hit
    if first:  # the run asking only for the refusal did not pass
        kind = "wording" if any(k == "wording" for k, _ in first) else "none"
        return kind, f"with only the refusal asked: {first[0][0]}: {first[0][1][:200]}"
    how, message = verdict(test, cwd, env)
    return ("named" if how in ("kill", "twin") else how), message


def decide(rows: list, diagnostic: bool) -> tuple[bool, str]:
    """Whether the named tests together catch a mutant for what it is declared to be. `rows`: (test, kind,
    message) of every test asked. An undeclared mutant counts once a test catches it `semantic` (or `twin`). A
    mutant declared `diagnostic` (its claim is about a reason) counts only if no test catches it so, whatever the
    order of its tests (Codex, P27-F1), and some test catches it `named`."""
    caught = [r for r in rows if r[1] in ("semantic", "twin")]
    named = [r for r in rows if r[1] == "named"]
    if diagnostic:
        if caught:
            return False, (f"declared diagnostic, yet {caught[0][0]} catches it with only the refusal asked: "
                           f"{caught[0][2][:200]}")
        if named:
            return True, f"killed by {named[0][0]}, by its named reason only (declared diagnostic)"
    elif caught:
        return True, f"killed by {caught[0][0]}" + (" (kernel and twin diverge)" if caught[0][1] == "twin" else "")
    elif named:
        return False, (f"{named[0][0]} catches it only by its named reason: the input stays refused; find an input "
                       "it admits, or declare it diagnostic for a claim about the reason")
    wording = next((r for r in rows if r[1] == "wording"), None)
    if wording:
        # the refusal is still there under another message: the mutant took nothing a test can see
        return False, f"refused only in other words by {wording[0]}: {wording[2][:300]}"
    return False, "survived " + ", ".join(r[0] for r in rows)


def import_refuses(module: str, check: str, cwd: Path, env: dict) -> tuple[bool, str]:
    """Does importing `module` stop at the import-time check whose message is `check`? For a claim held by such a
    check (a value the module verifies as it loads): the mutant is caught by that check, named in advance, and by
    nothing else; any other failure, or a clean import, proves nothing."""
    with tempfile.TemporaryDirectory() as cache:
        out = subprocess.run([sys.executable, "-X", f"pycache_prefix={cache}", "-c", f"import {module}"],
                             cwd=cwd, capture_output=True, text=True, env=env)
    last = (out.stderr.strip().splitlines() or [""])[-1]
    return out.returncode != 0 and check in last, last or "imported cleanly"


def kernel_of(m: dict) -> str | None:
    """The kernel build of KERNELS a mutant needs, if any: the one it names, or the crate whose src/ it mutates."""
    return m.get("build") or next((k for k, spec in KERNELS.items() if m["file"].startswith(f"{spec[0]}/src/")), None)


def baseline(builds) -> list[str]:
    """Each kernel crate of `builds` built once, unmutated, one after another, before any mutant: the first `cargo` in a
    crate installs the toolchain its rust-toolchain.toml pins and fetches its dependencies, which workers starting at
    once would each do into the same rustup and cargo homes (CI run 43531374137: 51 mutants that did not build, every
    error rustup's or cargo's). A crate that does not build unmutated gives no ground to read any of its mutants:
    the problems, one per crate, and then nothing runs."""
    problems = []
    base = Path(os.environ.get("MINDS_KERNEL_TARGET") or git_dir() / "kernel-mutants-target")
    base.mkdir(parents=True, exist_ok=True)
    for build in sorted(builds):
        crate, features, wasm, _var, _pinned = KERNELS[build]
        target = Path(tempfile.mkdtemp(prefix=f"baseline-{build}-", dir=base))
        try:
            b = subprocess.run(["cargo", "build", "--release", "--target", "wasm32-unknown-unknown", *features],
                               cwd=ROOT / crate, capture_output=True, text=True,
                               env=dict(os.environ, CARGO_TARGET_DIR=str(target)))
            if b.returncode != 0 or not (target / "wasm32-unknown-unknown" / "release" / wasm).is_file():
                problems.append(f"{build}: the unmutated crate does not build: "
                                + ((b.stderr.strip().splitlines() or ["no wasm"])[-1][:160]))
        except OSError as e:
            problems.append(f"{build}: cargo cannot run in {crate}: {e}")
        finally:
            shutil.rmtree(target, ignore_errors=True)
    return problems


def run(mid: str, m: dict, root: Path | None = None) -> tuple[bool, str]:
    """One mutant in the tree at `root` (default ROOT): applied, its tests run there, the file restored."""
    root = root or ROOT
    path = root / m["file"]
    original = path.read_text()
    if original.count(m["find"]) != 1:
        return False, f"find string occurs {original.count(m['find'])} times in {m['file']}"
    env_extra: dict = {}
    cleanup: list = []
    try:
        path.write_text(original.replace(m["find"], m["replace"]))
        build = kernel_of(m)
        if build:
            # a mutant of a rules kernel: build it beside the real one (its own target directory, never the crate's)
            # and hand the build to the tests; the kernel the gate runs is untouched
            crate, features, wasm, var, pinned = KERNELS[build]
            # a fresh target per mutant: cargo decides what to rebuild by modification time, so a mutant written in the
            # same second as the previous one could be served the previous mutant's build
            base = Path(os.environ.get("MINDS_KERNEL_TARGET") or git_dir() / "kernel-mutants-target")
            base.mkdir(parents=True, exist_ok=True)
            target = Path(tempfile.mkdtemp(prefix=f"{mid}-", dir=base))
            cleanup.append(target)
            b = subprocess.run(["cargo", "build", "--release", "--target", "wasm32-unknown-unknown", *features],
                               cwd=root / crate, capture_output=True, text=True,
                               env=dict(os.environ, CARGO_TARGET_DIR=str(target)))
            if b.returncode != 0:
                return False, "the mutant does not build: " + b.stderr.strip().splitlines()[-1][:120]
            built = target / "wasm32-unknown-unknown" / "release" / wasm
            if hashlib.sha256(built.read_bytes()).digest() == hashlib.sha256((root / pinned).read_bytes()).digest():
                return False, "the mutant builds to the unmutated kernel (an equivalent mutant)"
            env_extra[var] = str(built)
        if "refused_at_import" in m:
            module, check = m["refused_at_import"]
            ok, last = import_refuses(module, check, root, dict(os.environ, MINDS_MUTANT=mid))
            return ok, (f"refused at import by {check!r}" if ok else f"not refused at import by {check!r}: {last[:160]}")
        rows = []
        for t in m["kills"]:
            env = dict(os.environ, MINDS_MUTANT=mid, **env_extra)  # check_claims skips the applied mutant
            rows.append((t, *classify(t if "." in t else f"test_vars1.TestVars1Conformance.{t}", root, env)))
            if not m.get("diagnostic") and rows[-1][1] in ("semantic", "twin"):
                break  # a burn: the other tests need not run; a declared mutant asks them all
        return decide(rows, m.get("diagnostic", False))
    finally:
        path.write_text(original)
        for d in cleanup:
            shutil.rmtree(d, ignore_errors=True)


def worker_trees(n: int, base: Path) -> list[Path]:
    """`n` copies of the tree under test, one per worker, so that each mutates its own files. Each is a clone sharing
    this repository's objects (as `minds_chain.checks_at` makes its checkout), at HEAD, with the working tree's own
    changes copied in and the chain's refs fetched, so that it is the tree a serial run would mutate; the Lean
    executables the tests run are this checkout's, by a link (built, never tracked, never mutated)."""
    git = lambda *a, cwd=ROOT: subprocess.run(["git", *a], cwd=cwd, check=True, capture_output=True).stdout
    head = git("rev-parse", "HEAD").decode().strip()
    # tracked files that differ from HEAD, and files git does not track or ignore; build outputs are not the tree
    changed = [p for p in git("status", "--porcelain=v1", "-z", "--untracked-files=all", "--no-renames", "--", ".",
                              ":(exclude)proofs/.lake", ":(exclude,glob)**/target/**").decode().split("\0") if p]
    trees = []
    for k in range(n):
        tree = base / f"w{k}"
        git("clone", "-q", "--shared", "--no-checkout", "--no-tags", str(ROOT), str(tree))
        git("fetch", "-q", "--no-tags", str(ROOT), "+refs/vars/*:refs/vars/*", cwd=tree)
        git("checkout", "-q", "--detach", head, cwd=tree)
        for entry in changed:
            rel = entry[3:]
            src, dst = ROOT / rel, tree / rel
            if src.is_file():
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
            elif dst.is_file():
                dst.unlink()
        lake = ROOT / "proofs" / ".lake"
        if lake.exists():
            (tree / "proofs").mkdir(exist_ok=True)
            (tree / "proofs" / ".lake").symlink_to(lake, target_is_directory=True)
        trees.append(tree)
    return trees


def main(argv: list[str]) -> int:
    """`[--jobs N] [--shard I/K] [ID...]`: the mutants named (all if none), or the I-th of K shards of them (every
    K-th in sorted order), run by N workers at once (MINDS_MUTANT_JOBS, default the CPUs), each in a tree of its own.
    The verdicts are the serial run's: each mutant is applied, built and tested alone, in a tree that differs from
    this one only by that mutant."""
    mutants = json.loads((ROOT / "mutants.json").read_text())
    jobs = int(os.environ.get("MINDS_MUTANT_JOBS") or os.cpu_count() or 1)
    shard = None
    ids = []
    it = iter(argv)
    for a in it:
        if a == "--jobs":
            jobs = int(next(it))
        elif a == "--shard":
            i, k = map(int, next(it).split("/"))
            if not 1 <= i <= k:
                raise SystemExit(f"--shard {i}/{k}: I must be in 1..K")
            shard = (i, k)
        else:
            ids.append(a)
    chosen = ids or sorted(mutants)
    if shard:
        chosen = chosen[shard[0] - 1::shard[1]]
    jobs = max(1, min(jobs, len(chosen)))
    problems = baseline({b for mid in chosen if (b := kernel_of(mutants[mid]))})
    if problems:
        for p in problems:
            print(f"BASELINE {p}")
        print(f"nothing run: {len(problems)} kernel crate(s) do not build unmutated")
        return 2
    results: dict[str, tuple[bool, str]] = {}
    if jobs == 1:
        for mid in chosen:
            results[mid] = run(mid, mutants[mid])
            print(f"{'killed  ' if results[mid][0] else 'SURVIVED'} {mid}: {results[mid][1]}", flush=True)
    else:
        base = git_dir() / "mutant-workers"
        base.mkdir(parents=True, exist_ok=True)
        base = Path(tempfile.mkdtemp(prefix="run-", dir=base))
        try:
            pending = queue.SimpleQueue()
            for mid in chosen:
                pending.put(mid)
            lock = threading.Lock()

            def work(tree: Path) -> None:
                while True:
                    try:
                        mid = pending.get_nowait()
                    except queue.Empty:
                        return
                    try:
                        got = run(mid, mutants[mid], tree)
                    except Exception as e:  # noqa: BLE001  a runner fault is a survivor, never a kill
                        got = (False, f"the runner failed: {type(e).__name__}: {e}")
                    with lock:
                        results[mid] = got
                        print(f"{'killed  ' if got[0] else 'SURVIVED'} {mid}: {got[1]}", flush=True)

            threads = [threading.Thread(target=work, args=(t,)) for t in worker_trees(jobs, base)]
            for t in threads:
                t.start()
            for t in threads:
                t.join()
        finally:
            shutil.rmtree(base, ignore_errors=True)
    survived = sorted(mid for mid in chosen if not results.get(mid, (False, ""))[0])
    for mid in survived:
        print(f"SURVIVED {mid}: {results.get(mid, (False, 'not run'))[1]}")
    print(f"{len(chosen) - len(survived)}/{len(chosen)} killed")
    return 1 if survived else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
