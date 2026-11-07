# Task 5, a real history of withdrawals: report

**Status:** closed on 2026-11-07 by its own stop rule. No adapter and no chain were built.

## The question and the rule

Task 5 of the owner's task list of 2026-11-05 (`.drafts/MINDS-TASKS-2026-11-05.md`, a local draft) set both before any of the data below was read:

- **The decision:** a release of sokol-core (interdict-mesh) is clean under RustSec, by its `Cargo.lock`.
- **The question a chain alone might answer:** which of my past release decisions relied on an advisory that was later withdrawn, and who decided.
- **The rule:**
  - if some question is answered only by the chain, the task has a result;
  - if none is, minds is not needed for this problem and the work stops.

The draft is not witnessed, so this is not a pre-registration in the sense of G6's `PREREG.md`.

## Data

- **RustSec `advisory-db` at `99670cfc0bc574433034b75876a4b791ccaa2efb`** (2026-10-27): the checkout that cargo-deny 0.20.2 keeps in `~/.cargo/advisory-dbs`, a shallow clone of one commit. It holds 1360 advisories, 25 of them withdrawn.
- **Tags:** every tag of sokol-core, sigma-glyph and minds that holds a `Cargo.lock`: 22 tags with 44 lockfiles.
  - A tag named `v<digit>` is a release: 10 tags with 17 lockfiles.
  - The other tags are snapshots (`archive/…`), not decisions.
  - `releases.json` lists each tag with its commit.
- **Releases with dependencies:** only one, sokol-core `v0.1.0-rc.1` (2026-10-29, lockfiles of 216, 32 and 16 packages).
  - sigma-glyph's nine releases with a lockfile lock no package but their own.
  - minds has no release tag.

## Baseline

`baseline.py` uses the standard library only. For each lockfile it lists the advisories on a locked registry package whose `patched` and `unaffected` requirements leave the locked version out. That is how cargo-deny reads them. Withdrawn advisories are marked, since cargo-deny skips them.

I cross-checked it against `cargo deny --offline --all-features check advisories`, on the same database, at two revisions of sokol-core:

| Revision | Both report | Both leave out |
|---|---|---|
| `archive/2026-10-12` | RUSTSEC-2026-0385 (ctutils 0.4.2), RUSTSEC-2026-0386 (tokio 1.53.1) | the withdrawn RUSTSEC-2025-0014 |
| `v0.1.0-rc.1` | nothing | |

These are two points of agreement, not a proof of the matcher.

## Results

| | Lockfiles |
|---|---|
| Release lockfiles with a live advisory | 0 |
| Release lockfiles with a withdrawn advisory | 1 |
| Snapshot lockfiles with a live advisory | 6 |

**The release lockfile with a withdrawn advisory:**
- RC-1 locks humantime 2.4.0.
- RUSTSEC-2025-0014 (unmaintained, dated 2025-03-08) was withdrawn on 2025-03-12.
- That is 16 months before our earliest tagged lockfile and 19 months before the release.

**The six snapshot lockfiles with a live advisory:**
- The root `Cargo.lock` of the three `archive/` tags before RC-1 (`2026-09-29`, `2026-10-05`, `2026-10-12`) locks tokio 1.53.1 and ctutils 0.4.2.
  - The advisories on them are dated 2026-10-13 and 2026-10-23.
  - `Cargo.lock` moved to tokio 1.54.1 and ctutils 0.4.6 on 2026-10-28, the day before the release tag.
- The three review-evidence lockfiles under `archive/2026-09-29` all lock tokio 1.53.1.
  - Two of them also lock four unmaintained crates.
  - The third also locks ctutils 0.4.2.

**Across RustSec as a whole:**
- 25 of 1360 advisories are withdrawn: 20 unmaintained notices, 4 vulnerabilities and 1 unsound.
- From an advisory's date to its withdrawal: median 893 days, range 1 to 2019.
- Of the 25 withdrawn packages, only humantime appears in any lockfile of ours.

## The answer

**The answer to the question is empty, and the baseline gives it in one pass.**
- No release decision of ours relied on an advisory that was later withdrawn.
- No release locked a version that a live advisory affects.
- The one withdrawn advisory on a crate we lock was withdrawn before any lockfile of ours existed.
- "Who decided" is not a question for minds here: sokol-core's release decision is a Warrant 3 record (RC-1 admitted).

**I found no other question on these data that only a chain answers.** The events a chain exists for did not occur once: a ground invalidated, the invalidation then withdrawn, a decision restored.

**By its rule, task 5 stops: minds is not needed for this problem.**

## What a chain could not have expressed

This list comes from reading the format. No adapter was built, so none of it is measured.

1. **Keys.** RustSec has no VARS keys. A scope `rustsec` would be sealed by the adapter: one actor, not several.
2. **"No advisory affects P" is not a `relies`.** It can only be an edge from an advisory into a claim about P, and that edge needs the importer's quorum on a cross-seal (task 4, `proofs/Vars1/Morphism.lean`).
3. **"Version v is affected" is the semver match of `baseline.py`.** In a chain it would be one of two things:
   - an adapter's attestation of that same computation;
   - a `computation` cell for sigma-glyph, which is frozen and is used 0 times on the live chain.

   Either way the chain would seal the script's answer, not replace it.
4. **When an advisory became visible.**
   - An advisory's `date` is its disclosure date.
   - When its file entered the database is in the database's own history, not in this shallow checkout.
   - A chain's commit time would be the adapter's import time.

   None of these says what the decider's tool knew on the day. The release's CI log does.

## What this does not show

- **Scope:** this is not a test of minds in general, only of this problem on our data.
- **Thin data:** there is one release with dependencies.
- **Same session:** the question and the rule predate the data, but the counts above were taken in the session that applied the rule.
- **Matcher limits:**
  - the matcher agrees with cargo-deny at two points only;
  - it compares pre-release identifiers as strings, and no version we lock is a pre-release.

## Reproduce

```
git clone https://github.com/rustsec/advisory-db && git -C advisory-db checkout 99670cfc0bc574433034b75876a4b791ccaa2efb
python3 -I experiments/rustsec/baseline.py advisory-db <sokol-core> <sigma-glyph> <minds> > releases.json
```

Tags made after 2026-11-07 add rows to the output. The rows above are the ones whose commits `releases.json` names.
