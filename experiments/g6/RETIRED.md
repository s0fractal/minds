# G6 pilot: retired

Roadmap goal G6 asked whether a minds chain helps a reader decide what it may still rely on after a ground fails. It
was withdrawn on 2026-10-30, after the pilot's null result at the ceiling (`REPORT.md`). The question is closed;
nothing here is current work.

**Kept, unchanged:** `PREREG.md` (what was fixed before the run) and `REPORT.md` (the result). Records in
`.warrant/records.jsonl` cite lines of `REPORT.md`, so neither file is edited. Both name files that are no longer in
the tree.

**Retired from the tree on 2026-10-31:**
- the harness: `g6.py`, `test_g6.py`, `mutants.json`, `models.json`, `run.sh`;
- the run data: `run/`, `smoke/`, `smoke-16b727b/` (tasks, raw replies, scores, `run/describe.py`);
- the two CI steps that ran the harness and its mutants.

Their bytes are at commit `7997a623bcb69b56749382e63cc8b2f71162dd45`, under `experiments/g6/`; every path in
`REPORT.md` and `PREREG.md` resolves there. To read them:

```
git checkout 7997a623bcb69b56749382e63cc8b2f71162dd45 -- experiments/g6
```

**Not retired: the history generator.** The witness spike runs on its histories, so it lives on as
`experiments/witness/histories.py`, unchanged wherever it shapes a history (the same seeds give the same histories and
cell ids).

A new pilot would be a new roadmap goal with its own pre-registration, not a restore of this one.
