# Reviewing minds

For any reviewer, human or agent, asked to "review minds" or "verify minds". Work from the code, not from the
maintainer's summaries: read commit messages, README and ASSURANCE.md last, as claims to test.

## 0. Which changes get a model's review

Review is expensive and a weak reviewer is worse than none (a false ACCEPT), so the strength of review follows the
cost of a mistake, not the size of the diff.

- **Always, for every change: the mechanical checks.** CI (conformance, properties, kernel hash, claims) and the
  mutants job. A killed mutant is a claim no reviewer needs to recheck by hand.
- **A strong adversarial review, one reviewer per pull request, only where a mistake is costly:** the gate
  (`vars1.py` admission), the rules kernel (`kernel/`, `kernel2/`) and the meter that bounds its steps (`meter.py`), rules changes (VARS-1-SPEC.md §4.3), the bundle
  verifier (`verify/`), the release tool's checks, and any change to a normative block of the spec. Not two
  reviewers on the same head: a second opinion is a deliberate choice, recorded as such.
- **No model review** for documentation, tests, tooling or refactors that change no behaviour; CI and the mutants
  carry them.
- **Scope the review to the claims that moved.** The reviewer starts from the change to `claims.json` (new or
  changed claims, their witnesses and mutants), then reads the code those claims point at. Checking that each quote,
  witness and mutant matches the code is mechanical and may go to a lighter model; trying to refute the claims may not.
- **Batch by theme.** A pull request carries one theme in full rather than one commit at a time: review costs per
  round, not per line.
- **One round, then only where it costs.** After a strong review's findings are fixed, a further round is run only
  when a fix touched a costly surface above; fixes to tooling, tests or documentation get CI and their mutants. The
  final round is scoped to the costly claims that moved, by name.
- **A finding that recurs in a new form is a design signal.** When each round finds another corner of the same
  thing (PR #4: nine rounds on lists of files a gate loads and on hand-read Markdown), stop patching instances:
  generate the artifact from data, or refuse what cannot be read, so the class closes.
- **Locally, what the change touches; everything in CI.** Before a push, run the tests and the mutants of the claims
  that moved (minutes); the full suites and every mutant run in CI on each push (a few minutes there, twenty or more
  here, serially), and a pull request merges only on green CI.

### How a model's review is recorded

A pull request that gets a strong review carries its review as Warrant 3 records in `.warrant/records.jsonl`, as
s0fractal/warrant does (its docs/REPOSITORY.md, "Reviews as records"). `.warrant/v3.json` names both model
families (`claude`, `codex`) `pr/acceptor` and `roadmap/owner` beside the owner, and the owner `pr/owner` (a veto, not
an acceptance) and `challenger` (his challenge counts against any record); his key is the one s0fractal/warrant
trusts. `.warrant/merge.json` names the base, the required checks, the owner paths and the tiers below.

- The author pushes the change (commit X), then files the review's root and a head version naming X, from a checkout
  of the branch: `python3 -m warrant.review open --pr N --title T` and `python3 -m warrant.review head --pr N`, each
  `--actor claude --key <its seed>`. The record commit after X adds record lines only.
- Once that head version is at the pull request's head and CI is green, the review waker wakes the reviewer. The
  reviewer files its acceptance (an `attest` with `{"verdict": "accept"}` on the head version) or `finding@1`
  challenges, and pushes them onto the pull request. Fixes go into a new head version.
- The merge gate merges it (`.github/workflows/merge-on-acceptance.yml`, warrant's `warrant/gate.py` from the
  pinned warrant-graph wheel): a head version, no standing finding, required checks green, no owner path changed.
  The merge is the bot's, not anyone's account. When it may merge depends on the paths the change touches:
  - **No listed path:** at once, accepted by the other family or solo (its author a `pr/acceptor`).
  - **`watched`:** the costly surfaces above (`vars1.py`, `kernel/`, `kernel2/`, `meter.py`, `verify/`,
    `tools/minds_chain.py`, `VARS-1-SPEC.md`) and `requirements.txt`, which with them is what the witness key runs
    (the import closure of `tools/minds_chain.py` is `vars1.py` and `meter.py`).
    Two families accepting and 24 h after green checks, or one family and 72 h.
  - **`constitutional`:** `.warrant/v3.json`, `.warrant/v3/` and this file. 72 h with two families, 168 h with one,
    and the gate comments once, naming the owner, when the window opens.
  - **Owner paths:** `.github/` and `.warrant/merge.json`, that is, the brake itself and what the gate's token can
    do. The owner merges these.
  - **What the gate also takes for the owner's:** a module added beside a listed Python file or where the
    interpreter searches for one (here the root and `tools/`), a new top-level directory, and any `.gitattributes`.
- **While the owner is present, the windows come after the merge, not before.** He counts as present for 14 days after
  a merge of his on GitHub or a reaction of his to a comment of the gate (`presence` in `.warrant/merge.json`, signs
  from its `since` on): a watched or constitutional change then merges once its other conditions hold, and for as long
  as its window would have run, his `hold` label or challenge on the merged pull request has the gate revert it. When
  he has been away 14 days, the gate opens one issue naming him, and the windows come before the merge again.
- **The owner's stops, at every tier:** a challenge on the head version (`warrant challenge`, as `pr/owner`); the label
  `hold` on a pull request; the repository variable `WARRANT_MERGE_GATE=hold`, which holds them all.
- **Every merge goes through the gate**, the solo ones too: no agent merges with `gh pr merge` under the owner's
  account. The owner's name in the history means the owner acted.
- **Every pull request carries a review lineage**: its root and head version, filed by the author. Without one the
  gate does not merge it. A model review is still asked for by §0 above, not by the gate.

## 1. Verify releases (members only)

```
.venv/bin/python tools/minds_chain.py status          # releases whose "awaiting" lists your key need your verdict
.venv/bin/python tools/minds_chain.py verify-release <decision> --key <your key file> --name <your verifier id>
git push origin refs/vars/heads/minds
```

`verify-release` reruns every check on the released commit in a fresh checkout, against the chain as it stood when
the release was recorded, and records your verdict under your
own key. It shows that the checks pass; it does not show that what the commits claim is true. That is step 2.
`minds_chain.py witness --key <file> --name <id>` does it for every release waiting for your key; the GitHub
Actions witness runs it (README, "The GitHub Actions witness").

## 2. Try to refute the claims

Take the diff since the last release you reviewed (`git log`, `git diff <old>..<new>`). Then:

- List every claim the change makes (commit messages, README, ASSURANCE.md, docstrings, test names).
- For each, find the code or test that establishes it. A claim wider than what its test checks is a finding.
- Try to break the strongest ones: a counterexample, a mutant the tests miss, an input the gate admits wrongly.

## 3. Report

Findings only, each with: the claim, where it is made, what you ran or read, and the result (refuted, unsupported,
or confirmed). Do not restate the maintainer's summary. Write it to a file outside the repository and give its
path; the maintainer fixes reproduced findings with regression tests.

Constraints: run heavy checks one at a time (the Kani harnesses need about 15 GB each; `kernel/assure.sh`), never
use another member's key, and do not push anything but your own `refs/vars/heads/minds` verdicts.
