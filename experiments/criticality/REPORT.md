# Task 8: how far one revocation spreads

**Status:** 2026-11-11. The theory and its derivation are below, checked through the real gate and the v2 rules
kernel (`kernel2/lens2.wasm`) on generated chains. A measurement of the live chain is included. Nothing here changes a
rule.

## The question

Task 8 of `.drafts/MINDS-TASKS-2026-11-05.md` asked two things:
- whether the NOR threshold `λ = e`, measured on the bare rule, holds through the real kernel;
- what changes when `relies` (Pass 2, Stale) is added.

When a cell is killed, how many statuses change? Below a threshold the answer is a few. Above it, one old revocation
can flip a fraction of the whole graph.

## Model

Every cell is an axiom:
- It is attacked by `Poisson(λ)` newer cells through `invalidates` edges. Each edge is sealed by one key of a 1-of-3
  admission roster, so every edge latches.
- It is relied on by `Poisson(μ)` newer cells through `relies` edges.
- Both are drawn within a band of the next 150 cells, so every cell away from the ends has about `λ` attackers and
  `λ` targets, and about `μ` relied cells and `μ` dependents. Drawing among all newer cells instead gives old cells
  few relied cells and new cells many, and then the formulas below do not apply. The first trial run here showed
  that, at `q` = 0.533 against 0.377.

With no retires or supersedes, Active is Effective. Pass 1 does not read Pass 2.

## Theory

Write `W` for the principal branch of Lambert's W.

**Pass 1, NOR on the kill edges.** A cell is Effective iff no attacker of it is Effective. With `Poisson(λ)`
attackers, the Effective fraction `p` satisfies `p = e^{−λp}`, so `λp e^{λp} = λ` and

  `p = W(λ)/λ`.

When a cell flips, each of its about `λ` targets flips with probability `p`:
- an Effective cell dying revives each target that has no other Effective attacker;
- a cell reviving kills each target that was Effective.

So the branching factor is `r₁ = λp = W(λ)`. It reaches 1 at **`λ = e`**. Below that, the mean number of cells one
kill flips is `1/(1 − W(λ))`.

**The same threshold elsewhere.** For a Poisson(λ) Galton–Watson tree, Holroyd and Martin show that the normal-play
game has a positive probability of a draw exactly when `λ > e` ("Galton–Watson games", Random Structures & Algorithms
2021, arXiv:1904.04150). The draw lives in the fixed points of the two-step map. The naive iteration
`p ← e^{−λp}` shows the same thing here: below `e` it converges, above `e` it settles into a 2-cycle. A finite DAG has
no draws, since its newest cells fix every status. Above `e`, though, a status depends on cells arbitrarily far back.

**Pass 2, OR down `relies`.** Write Live for Active and not Stale.
- A cell is Live iff it is Effective and every cell it relies on is Live.
- The Live fraction `q` is the solution `≤ p` of `q = p e^{−μ(1−q)}`.
- When a cell's Live flips, it flips each dependent that is Effective and has all its other relied cells Live, with
  probability `p e^{−μ(1−q)} = q`. So the branching factor is `r₂ = μq`.
- Writing `x = μq`, the equation becomes `x e^{−x} = pμ e^{−μ}`, so

  `r₂ = −W(−p μ e^{−μ})`.

Because `μ e^{−μ} ≤ 1/e`, the argument is at least `−p/e`, and that is `> −1/e` whenever `p < 1`. So
**`r₂ < 1` for every `μ` once anything is dead**. Its maximum over `μ` is `−W(−p/e)`, at `μ = 1`; for example 0.377 at
`λ = 0.5`.

The Stale layer is critical only at `p = 1`, where nothing is dead and it is plain percolation, critical at `μ = 1`.
The dead cells cut the dependency paths, and that is what keeps every Stale cascade subcritical.

**Both layers.** Kill one Effective cell:
- the NOR cascade flips `1/(1 − r₁)` cells' Effective bit;
- each of those flips its own Live bit if all its relied cells are Live, with probability `q/p`;
- each Live flip starts an OR cascade of mean size `1/(1 − r₂)`.

So the mean number of Live flips is `(1/(1 − r₁)) (q/p) / (1 − r₂)`. This is mean-field: overlaps are ignored.

**Phase diagram.** Two things are critical:
- the line `λ = e`, for every `μ`;
- the single point `(λ, μ) = (0, 1)`.

## Through the gate and the kernel

`run.py` builds each chain of 1,500 cells through the gate under the v2 rules, in commits of 250. The lens reads
every status. Then 80 kills of random Effective cells are each built as a candidate commit, never advanced, and read
by the lens at that commit. The results are in `results.json`.

| λ | μ | p measured | p theory | q measured | q theory | r₁ | r₂ | kill flips measured | theory | Live flips measured | theory | largest Live flip |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 0.50 | 0.00 | 0.708 | 0.703 | 0.708 | 0.703 | 0.352 | -0.000 | 1.66 | 1.54 | 1.66 | 1.54 | 8 |
| 1.00 | 0.00 | 0.572 | 0.567 | 0.572 | 0.567 | 0.567 | -0.000 | 2.19 | 2.31 | 2.19 | 2.31 | 14 |
| 1.50 | 0.00 | 0.471 | 0.484 | 0.471 | 0.484 | 0.726 | -0.000 | 3.92 | 3.65 | 3.92 | 3.65 | 25 |
| 2.00 | 0.00 | 0.418 | 0.426 | 0.418 | 0.426 | 0.853 | -0.000 | 4.84 | 6.78 | 4.84 | 6.78 | 52 |
| e | 0.00 | 0.361 | 0.368 | 0.361 | 0.368 | 1.000 | -0.000 | 11.00 | ∞ | 11.00 | ∞ | 135 |
| 3.00 | 0.00 | 0.347 | 0.350 | 0.347 | 0.350 | 1.050 | -0.000 | 11.21 | ∞ | 11.21 | ∞ | 65 |
| 4.00 | 0.00 | 0.304 | 0.301 | 0.304 | 0.301 | 1.202 | -0.000 | 15.89 | ∞ | 15.89 | ∞ | 95 |
| 0.50 | 0.50 | 0.716 | 0.703 | 0.584 | 0.566 | 0.352 | 0.283 | 1.50 | 1.54 | 1.69 | 1.73 | 14 |
| 0.50 | 1.00 | 0.704 | 0.703 | 0.392 | 0.377 | 0.352 | 0.377 | 1.45 | 1.54 | 1.30 | 1.33 | 7 |
| 0.50 | 2.00 | 0.702 | 0.703 | 0.110 | 0.121 | 0.352 | 0.243 | 1.50 | 1.54 | 0.29 | 0.35 | 3 |
| 1.00 | 0.50 | 0.584 | 0.567 | 0.445 | 0.426 | 0.567 | 0.213 | 1.94 | 2.31 | 1.65 | 2.20 | 7 |
| 1.00 | 1.00 | 0.583 | 0.567 | 0.307 | 0.275 | 0.567 | 0.275 | 1.76 | 2.31 | 1.12 | 1.54 | 12 |
| 1.00 | 2.00 | 0.565 | 0.567 | 0.102 | 0.092 | 0.567 | 0.185 | 2.15 | 2.31 | 0.51 | 0.46 | 4 |
| 0.00 | 0.50 | 1.000 | 1.000 | 1.000 | 1.000 | 0.000 | 0.500 | 1.00 | 1.00 | 2.23 | 2.00 | 15 |
| 0.00 | 0.80 | 1.000 | 1.000 | 1.000 | 1.000 | 0.000 | 0.800 | 1.00 | 1.00 | 3.54 | 5.00 | 19 |
| 0.00 | 1.20 | 1.000 | 1.000 | 1.000 | 1.000 | 0.000 | 1.200 | 1.00 | 1.00 | 15.81 | ∞ | 86 |

Each row is one chain of 1,500 cells and 80 kills. The whole grid took 29 minutes. Flips are per kill, so the kill
itself counts as one.

**What agrees.** `p` and `q` match the theory within 0.03 at every one of the sixteen points, through the gate and the
kernel. The thresholds sit where the theory puts them:
- the subcritical means of Effective flips are within 8% of `1/(1 − W(λ))` up to `λ = 1.5`;
- from `λ = e` on, the mean grows with no limit in sight: 11 to 16 flips, up to 135 cells from one kill.

**What the mixed rows show.** Mortality damps the dependency cascades.
- At `λ = 0`, where nothing is dead, the Stale layer is plain percolation. At `μ = 1.2` one kill makes 15.8 cells
  not Live on average, up to 86.
- At `λ = 0.5` the same layer is subcritical even at `μ = 2`: 0.29 cells on average, at most 3.
- In every mixed row, the ratio of Live flips to Effective flips matches the theory's `(q/p)/(1 − r₂)` within 0.11.
  The ratio is checked rather than the product, because the Effective flips it multiplies carry the noise of the
  rows above.

**What disagrees, and why.**
- Near a threshold (`λ = 2`, `r₁ = 0.85`; `μ = 0.8` at `λ = 0`) the measured mean falls short of the theory: 4.8
  against 6.8, and 3.5 against 5.0.
- Near criticality the cascade sizes are heavy-tailed. Eighty kills undersample the tail, and the band and the
  chain's old end cut the longest cascades.
- The per-kill counts were not kept, so the table gives no confidence intervals.


## The live chain

At the tip of 2026-11-11, `refs/vars/heads/minds` has 682 cells:
- `λ` is 0.0044: three supersedes edges, from scope rotations, and no invalidates or retires;
- `μ` is 0.72 `relies` per cell.

The mean-field picture would put it near the one critical point of the Stale layer. Its structure says otherwise.
Each release relies on check cells of its own, and each verdict on its own checks. Every cell has at most one
dependent, so the excess degree `E[d(d−1)]/E[d]` is 0.

The exact blast radius (the forward closure down `relies`) is at most 2 cells for every cell: a failed check takes
its one release or verdict with it, and nothing else. The chain is far from both thresholds by construction, not by
chance.

## What this does not show

- **Mean-field.** The formulas are for locally tree-like random graphs with Poisson degrees. The live chain is
  neither, and there its own structure decides.
- **One model of edges.** Every kill edge here latches. Authorization only removes edges, so it lowers the effective
  `λ`; the author clause is not modelled.
- **No retires or supersedes.** With them, Active differs from Effective. A retired cell still attacks, so the layers
  stay decoupled in Pass 1, but `q` changes.
- **Finite size.** Above `e`, the mean number of flips grows with the chain and the band. The table shows that growth,
  not a limit.
- **Nothing is proved in Lean.** The finite parts already are: the Pass 1 kernel is unique (`pass1_kernel_unique`),
  and statuses depend only on their frame (`pass1_frame`, `stale_frame`). The probabilistic part is not, and needs
  Mathlib.

## Reproduce

```
.venv/bin/python experiments/criticality/run.py experiments/criticality/results.json 1500 80
```
