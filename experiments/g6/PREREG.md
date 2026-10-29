# G6 pilot: pre-registration

This file fixes the G6 pilot before any reader is asked anything. It is frozen when the pull request that carries it
merges into `main`. That merge commit is the **freeze**: the last merge into `main` that changed `experiments/g6`
outside `run/`, `smoke/` and `REPORT.md`. Its full id is the seed of the histories. Nobody chooses the seed, and
nobody can choose it before the design is fixed. `run.sh` finds the freeze itself and refuses to run when the
pilot's code differs from it.

## The question

Roadmap obligation `5788976a` (goal G6) reads: "A pre-registered pilot compares readers given a minds chain with
readers given the same evidence as pull requests and Markdown, on histories where a ground failed, counting wrong
reliance on its own; the result is reported, a null result included."

Asked of a reader: after one ground of a project is found invalid, which of the project's decisions may it still rely
on?

## Histories

Each history is a project kept by three maintainers, `ana`, `bo` and `cy`. The rules are below, and every reader is
given them word for word.

- **Grounds** are things recorded as established. **Checks** rest on grounds. **Decisions** rest on checks.
- Maintainers **approve** decisions. An approval relies on the checks its maintainer ran.
- A check stands while its grounds stand.
- An approval counts while its checks stand.
- A decision is in force while its checks stand and approvals from two different maintainers count.

`g6.py` draws a history from a seed, as follows:
- Each check rests on 1 or 2 grounds, and each decision on 1 or 2 checks.
- Each decision has 2 or 3 approvals from different maintainers. Each approval relies on 1 or 2 checks; each of those
  is one of the decision's own checks with probability ½, otherwise any check.
- The failed ground is drawn uniformly from the grounds that at least two checks rest on.

There are two sizes:

| size | grounds | checks | decisions | decisions no longer in force | decisions still in force |
|---|---|---|---|---|---|
| S | 7 | 14 | 12 | 3 to 8 | at least 3 |
| L | 10 | 24 | 30 | 5 to 20 | at least 5 |

A drawn history is kept only if, besides those bounds, it contains each of three cases. Otherwise the next draw from
the same seed is taken.
- **own:** one of the decision's checks fell.
- **approvals:** the decision's checks stand, but too few of its approvals do.
- **margin:** the decision stays in force with an approval lost.

All its decisions are in force before the failure.

**The answer is computed twice.** Each history is admitted as a real VARS-1 chain under the v1 rules. One answer is
`what_if` on that chain: a decision is no longer in force when `what_if` lists it as lost. The other is a closure over
the history's data that shares no code with `vars1.py`. **Generation refuses a history on which the two disagree.**

**16 histories**, numbered 0 to 15, with sizes alternating S, L, S, …. History *i* is drawn from
`sha256("g6/<freeze>/<i>")`, where `<freeze>` is the freeze commit's full id:

```
python experiments/g6/g6.py generate --seed <freeze> --count 16 --out experiments/g6/run/tasks
```

## Arms

Every reader gets the same instructions, the same rules and the same question. Only the text inside `<record>` differs.

- **M**, pull requests and Markdown:
  - `docs/GROUNDS.md` and `docs/CHECKS.md` as tables;
  - one merged pull request per decision, with the checks it rests on and each approval naming the checks its
    maintainer ran;
  - the issue reporting the failed ground.
- **C**, the chain: every cell in the order admitted, as JSON lines. Each cell has its id (12 hex digits), schema,
  name, payload, `relies_on`, `attests`, and the maintainer who sealed it. The last cell is the notice that
  invalidates the ground.
- **W**, the chain and what minds computes: C, followed by the `what_if` report for the notice. The report has `lost`
  (each cell whose status changes: before, after, and what no longer stands) and `held` (each decision near the notice
  that stays in force, with its counted approvals before and after).

M and C carry the same facts, and nothing derived. Test 04 shows that each decodes, by a reading of the test's own, to
exactly the history's facts. W is C with the report after it.

W adds what minds computes. That is the treatment: a reader given a minds chain reads it with minds' own tools. C
separates the chain's form from its computation.

## Readers

Three models, reached through OpenRouter, from families other than the designer's (Anthropic) and the reviewer's
(OpenAI), as listed in `models.json`:
- `deepseek/deepseek-v4.1-flash`
- `qwen/qwen3.8-flash`
- `google/gemini-3.8-flash`

**Requests:**
- One request per history, model and arm: 16 × 3 × 3 = 144 requests.
- One user message and no system message.
- Temperature 0, at most 8000 tokens out.
- The order of the 144 requests is shuffled by the seed, so no arm runs in a block of its own.

**Failures:**
- If a model is unavailable when the run starts, its requests are recorded as no answer. No substitute is taken.
- An HTTP or network failure is retried twice. After that, the request is recorded as no answer.

## Answers

**A valid reply** ends with a fenced `json` block that maps exactly the decisions to `"RELY"` or `"DO_NOT_RELY"`. The
last such block counts. Anything else is **invalid**: no block, a missing or extra decision, another word, or JSON that
does not parse.

## Measures and decision rule

**Wrong reliance** (WR) is measured per reply: the share of the decisions no longer in force that the reader would
still rely on. It is counted on its own, never combined with its opposite. **Over-caution** (OC) is the share of the
decisions still in force that the reader would drop.

**Primary:** WR, M against W, paired over (history, model).
- For each pair, *d* = WR(M) − WR(W). A pair with an invalid reply in either arm is left out.
- An exact two-sided sign test is run over the nonzero *d*.
- **Verdict:**
  - "W lowers it" if the mean *d* > 0 and p < 0.05;
  - "W raises it" if the mean *d* < 0 and p < 0.05;
  - otherwise "no difference detected".

**Secondary, reported with the same rule:**
- WR, M against C;
- OC, M against W and M against C;
- WR with an invalid reply counted as wrong on every decision (sensitivity).

**Also reported:**
- invalid replies per arm;
- accuracy by case (own, approvals, margin, untouched) and arm;
- mean WR and OC per model and arm, and per size.

The pilot's answer to G6 is the primary verdict. A null result is reported as such.

`g6.py score` computes all of this from the tasks and the raw replies. Nothing is scored by hand.

## Budget and stopping

**Budget:**
- The owner's cap is $5. It is enforced twice: by the operator's OpenRouter key, and by the runner.
- `g6.py budget` asks OpenRouter for the key's own limit before each invocation of the run. It refuses a key with no
  credit limit, or with a limit above $5. That invocation's budget is what the key has left, at most $5.
- The runner stops before a request once less than $0.25 of that budget is left, counting only what this invocation
  has spent, as OpenRouter reports it. The key's own limit holds the whole run to $5 across invocations.
- A stopped run is reported as incomplete, and its replies are scored as they are.
- The estimate is about $1.50.

**Interruption:** an interrupted run resumes. A recorded reply is never asked again.

**Binding:**
- `run.sh` checks the tasks before it reads a key. They must be the tasks of this freeze's seed and count (`g6.py
  bind`), and every task file must be the one the manifest names, byte for byte.
- A results directory names the tasks it was made from (`RUN.json`, the SHA-256 of their manifest). The runner
  refuses to resume it, and the scorer refuses to score it, against other tasks.

**Harness defects:** after the confirmatory run, nothing is re-asked and nothing is re-scored differently. A harness
defect found after it voids the run. The protocol then repeats from a new freeze, and every run is reported.

## Smoke run

Before the confirmatory run there is one smoke run: `generate --seed smoke-<freeze> --count 2`, all three models, all
arms, 18 requests. It checks the harness end to end. Its replies are not observations and are reported only as a
smoke run.

If it shows a harness defect, the fix goes through a pull request, review and a new freeze. Nothing else changes
between the smoke run and the confirmatory run.

## The designer's predictions

These are stated before any reply:

1. W: WR near 0 for every model, and the primary verdict "W lowers it".
2. C: WR at least M's (ids of 12 hex digits are harder to follow than labels), so "no difference detected" or "C raises
   it".
3. M: WR higher on L than on S.
4. OC lowest under W.
5. Under M, the `approvals` and `margin` cases have the lowest accuracy.

## What a result does not establish

- **The readers are models, not people.** Each is asked each prompt once, at temperature 0.
- **The histories are synthetic, and every arm is told the rules.** A real reader of pull requests may not know them,
  and a real record is not this tidy.
- **"W lowers it" credits the computation.** It says that minds' computed consequences help a reader, not that the
  chain's form does. C tests the form.
- **The designer wrote the generator, the renderings and the rules.** Against designer bias:
  - the seed comes from the freeze;
  - the facts are shown equal by test 04;
  - this file and the code are reviewed before the freeze.

## Files

- `g6.py`: generator, renderings, runner, scorer.
- `test_g6.py`: the tests, and `--mutants`, which fails each mutant in `mutants.json` on its named test.
- `models.json`.
- `run.sh`: the owner's one command for the run. It reads the key from a file of mode 600 named on the command line,
  or else without echo, and never writes it down.

The run's files go to `experiments/g6/run/` (tasks, raw replies, ledger, status, scores) with `REPORT.md`, in a
pull request of their own.

## Deviations

Any departure from this file is reported in `REPORT.md` as a deviation, with its reason.
