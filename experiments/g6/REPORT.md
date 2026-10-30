# G6 pilot: report

The confirmatory run of the pilot pre-registered in `PREREG.md`, at the freeze `c042df8f89295243d5ef5b0d7b92c21ac34328bf`
(the merge of #41), run on 2026-10-30. It is complete: 144 of 144 requests recorded, $1.570 spent, nothing stopped.

## The answer

**The primary verdict is "no difference detected".**

- There were 42 valid (history, model) pairs, and in every one WR(M) = WR(W) = 0.
- The sign test has no nonzero difference to count: p = 1.

This is a ceiling result, not evidence against W:
- Every valid M reply was right on every decision: 44 of 44.
- So were all valid W replies: 45 of 45.
- Given the rules, histories of up to 30 decisions, and the pull requests and Markdown, these three readers computed
  the consequences of the failed ground themselves. W had no wrong reliance to lower.

The pilot therefore does not show whether minds' computed consequences help a reader. It shows that, under these
conditions, the readers needed no help. G6 asked for the result to be reported, a null one included; this is it.

## The run

| | |
|---|---|
| freeze | `c042df8f89295243d5ef5b0d7b92c21ac34328bf` |
| tasks | `generate --seed c042df8f… --count 16`: 8 S (12 decisions), 8 L (30 decisions) |
| decisions | 336: 174 untouched, 73 own, 50 approvals, 39 margin; 123 no longer in force |
| tasks' identity (`RUN.json`) | `8dd093e20a31485469b29142a964cd0b0ac944b5b32261a6d61300420c530d6d` |
| requests | 144, in the seed's shuffled order; 6491 s of request time |
| served model | the model asked, on every answered request |
| cost | $1.570 (gemini $1.105, deepseek $0.293, qwen $0.172) |

`g6.py score` reproduces `run/score.json` byte for byte from `run/tasks` and `run/results`.

### Invalid replies

There were 14 invalid replies, 130 valid.

| reason | M | C | W | model |
|---|---|---|---|---|
| truncated at the token cap | 4 | 6 | 2 | all deepseek |
| no answer | 0 | 1 | 1 | qwen: HTTP 429 on all three attempts |
| not in the asked format | 0 | 0 | 0 | |

- **Every truncated reply ends in repetition.**
  - Each used the whole completion cap of 32000 tokens and returned no answer text.
  - OpenRouter reports 32000 of those tokens as reasoning for 11 of the 12. For h03 deepseek M it reports 12350.
    That reply's reasoning text is 49383 characters long, as long as the others'. The discrepancy is OpenRouter's
    metadata, and is kept as recorded (`run/describe.json` lists both counts for every truncated reply).
  - The last 20000 bytes of each one's reasoning compress to 0.002 of their size, against about 0.3 for the reasoning
    of an answered reply. Those tails are repetition loops.
  - That a higher cap would not have ended them is an inference from those tails. The run has only capped replies.
  - deepseek stopped this way on 12 of its 48 requests.
- **gemini answered all 48 validly.**

## Results (the frozen scorer, `run/score.json`)

**Primary and secondary contrasts:** pairs with an invalid reply in either arm left out; mean *d* = M − arm.

| contrast | pairs | mean *d* | + | − | ties | p | verdict |
|---|---|---|---|---|---|---|---|
| **WR, M vs W (primary)** | 42 | 0 | 0 | 0 | 42 | 1 | **no difference detected** |
| WR, M vs C | 37 | −0.019 | 0 | 1 | 36 | 1 | no difference detected |
| OC, M vs W | 42 | 0 | 0 | 0 | 42 | 1 | no difference detected |
| OC, M vs C | 37 | −0.001 | 0 | 1 | 36 | 1 | no difference detected |

**Sensitivity:** an invalid reply counted as wrong on every decision.

| contrast | pairs | mean *d* | + | − | ties | p | verdict |
|---|---|---|---|---|---|---|---|
| WR, M vs W | 48 | 0.021 | 3 | 2 | 43 | 1 | no difference detected |
| WR, M vs C | 48 | −0.077 | 4 | 8 | 36 | 0.388 | no difference detected |

**Accuracy by case:**

| case | M | C | W |
|---|---|---|---|
| own | 1 | 0.9948 | 1 |
| approvals | 1 | 0.9701 | 1 |
| margin | 1 | 1 | 1 |
| untouched | 1 | 0.9979 | 1 |

**Mean WR and OC.** These are 0 for every model and arm except qwen C (WR 0.048, OC 0.003, n 15). By size, they are 0
for every arm except L C (WR 0.031, OC 0.002, n 23).

## Descriptive, not pre-registered (`run/describe.py` → `run/describe.json`)

These were written after the run. Nothing in them changes the verdict.

**Not right on every decision:** two of the 130 valid replies, both qwen, arm C, on L histories.
- h13: it would still rely on 5 of the 7 decisions no longer in force (one `own`, four `approvals`). This is the only
  wrong reliance in the run.
- h05: it would drop one decision that still stands (`untouched`).

**Tokens per valid reply** (means):

| arm | prompt | completion | reasoning | cost, all replies |
|---|---|---|---|---|
| M | 2955 | 4121 | 3613 | $0.419 |
| C | 9679 | 6237 | 5787 | $0.638 |
| W | 12883 | 4413 | 4039 | $0.514 |

- W's prompt is 4.4 times M's.
- W replies did not reason less than M replies overall. Against M, W reasoned less for deepseek (3715 against 4126)
  and gemini (3044 against 3277), and more for qwen (5403 against 3564).

## The designer's predictions

1. **W: WR near 0 for every model.** Held.
   **The primary verdict "W lowers it".** Failed, because M was at 0 too.
2. **C: "no difference detected" or "C raises it".** Held, as "no difference detected". C had the only wrong reliance,
   in one reply.
3. **M: WR higher on L than on S.** Failed: 0 on both.
4. **OC lowest under W.** Failed: tied with M at 0.
5. **Under M, `approvals` and `margin` have the lowest accuracy.** Failed: every case under M is 1.

The designer expected the pull-request arm to fail on exactly the cases where a decision is lost by its approvals or
kept on a margin. It did not.

## What the result establishes, and what it does not

**It establishes:**
- On these 16 histories, with the rules stated, three current reasoning models given pull requests and Markdown
  wrongly relied on no decision.
- Adding minds' what-if report did not change that, and could not have.

**It does not establish that minds' computed consequences are useless.** The design put the comparison arm at its
ceiling. A pilot that can separate the arms needs conditions under which M fails, and none of these was run:
- the rules not stated, as for a real reader of pull requests;
- approvals that do not name the checks their maintainer ran;
- records the size of a real project;
- readers that do not reason, or people.

Each would be a new pre-registration and a new freeze. The limits in `PREREG.md` apply unchanged.

## Smoke runs

Their replies are not observations. They were read only for their validity, finish reasons, token counts and cost.

- **At `16b727b`** (`smoke-16b727b/`): 18 of 18 answered, $0.167. One reply stopped at the old cap of 8000. That cap
  was within the range normal replies used (up to 6592), so it was a harness defect, fixed in #41.
- **At `c042df8`** (`smoke/`): 18 of 18 answered, $0.186. Two deepseek replies, h00 C and h01 W, stopped at the new cap
  of 32000. Every other reply used at most 7940.
  - Their reasoning ended in repetition loops: their tails compress to 0.002.
  - From that, I inferred that a higher cap would not have ended them, so the stops were the reader's behaviour and
    not a harness defect. The confirmatory run followed at the same freeze.
  - This was a judgement, made before the confirmatory run, from those numbers only. No reply was run at a higher cap.

## Deviations

There are no departures from `PREREG.md`. Three things are named here for the review:

- **Smoke at `c042df8`.** Its two cap stops were judged not to be a harness defect (see above). If that judgement is
  wrong, `PREREG.md` makes it a harness defect found after the confirmatory run: the run is void, and the protocol
  repeats from a new freeze.
- **The two HTTP 429s.** They were retried twice, as pre-registered, then recorded as no answer.
- **`run/describe.py`.** It was written after the run, and is descriptive only.

## Spending

| | |
|---|---|
| G6 in all | $1.923 (smoke $0.167 + smoke $0.186 + confirmatory $1.570) |
| the key's limit | $5, shared with EXP-001's $0.052 |

## Files

- `run/tasks/`: the 16 tasks and their manifest.
- `run/results/`:
  - `raw/`: every reply as returned;
  - `ledger.jsonl`;
  - `STATUS.json`;
  - `RUN.json`.
- `run/score.json`: the frozen scorer's output.
- `run/describe.py` and `run/describe.json`: the descriptive numbers above.
- `smoke/`: the smoke run at `c042df8`.
- `smoke-16b727b/`: the smoke run at `16b727b`.
