# Reviewing minds

For any reviewer, human or agent, asked to "review minds" or "verify minds". Work from the code, not from the
maintainer's summaries: read commit messages, README and ASSURANCE.md last, as claims to test.

## 1. Verify releases (members only)

```
.venv/bin/python tools/minds_chain.py show            # releases with "settled": false need your verdict
.venv/bin/python tools/minds_chain.py verify-release <decision> --key <your key file> --name <your verifier id>
git push origin refs/vars/heads/minds
```

`verify-release` reruns every check on the released commit in a fresh worktree and records your verdict under your
own key. It shows that the checks pass; it does not show that what the commits claim is true. That is step 2.

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
