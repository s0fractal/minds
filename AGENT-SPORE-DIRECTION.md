# Agent spores: a direction for minds and Warrant

Date: 2026-10-29. Status: **a design direction agreed with the owner. No implementation and no spore format is
adopted.** Translated and extended from the owner's and Codex's Ukrainian draft of the same day: AS-8, the section
on what minds already has, and the conditions of the first experiment are additions.

This document records an intent. It changes nothing in VARS-1, Warrant 3, trust profiles, the rules of the live chain
or the state of the roadmap. The AS-* below are identifiers of design intents, not checked claims of `claims.json`;
accepting an implementation will need its own evidence and counterexamples.

## Purpose

minds is developed first for interaction between agents in a shared, global space of addressed objects,
computations and evidence. Agents have different local slices, capabilities, budgets and trust profiles. Global
does not mean one synchronous state, a shared process, a full replica, or the same conclusion for every agent.

Projections can be the main interface for consumption. A person can work through them too; reading the repository
and rerunning the whole pipeline is not a consumer's required path.

**A spore is an addressed unit of computation that can unfold its dependencies recursively and gradually, within
the capabilities and resources at hand.** It carries enough to start, to establish its next need, and to describe
the current bound of its result. Data, evidence or rules are fetched when the computation needs them. A child spore
can run a separate subtask; its result carries its own provenance and limits.

A spore can be stopped, handed to another agent and continued. The result, the projection and the checkpoint of
such a continuation must be distinct objects. Portability does not mean every dependency is inside: a package must
name exactly what it contains and what still has to be fetched.

## Who is responsible for what

| Part | Its responsibility in this direction |
|---|---|
| **minds / VARS-1** | Cells, references and the rules that read them; the state of the graph computed by a given lens; projections, what-if, rules identities and checked transitions between them. |
| **Warrant 3** | Actors' signed positions on exact versions: entities, attests, challenges, guards, roles, and the assessment of what this receiver may rely on under its trust and profile. |
| **Spore / executor** | Planning needs, fetching dependencies, spawning subtasks, budget, stopping and continuing. A layer still being designed; this document assigns its implementation to neither core. The first experiment builds it from the parts minds already has (below), not as a new repository. |
| **Projection / adapter** | Carries the exact subject, context and bound of verification between receivers. A translation names its source and target semantics and what it may lose. |

Both protocols already have their own semantics of graph and authority. They keep separate identities; a spore
gives neither protocol a right to decide silently for the other. A bridge or a capability can be the subject of
signed records and challenges; no schemas for them are introduced here. In Warrant 3 this rests on the existing
envelope `schema | entity | attest | challenge`, not on an API of an earlier generation.

Sources of the current semantics: [VARS-1-SPEC.md](VARS-1-SPEC.md), [RULES-V2.md](RULES-V2.md),
[Warrant 3](https://github.com/s0fractal/warrant/blob/master/docs/V3.md).

## What minds already has

Several intents below are already parts of minds. A spore should reuse them before it invents anything:

| Intent | Existing part |
|---|---|
| A task, an execution, a result (AS-3) | `computation_id` (a `ComputationRoot`: program and environment), a `checkpoint` (state, `spent_total`, `peak_size`, outcome), a `verdict` on a contract or decision (§2, §5) |
| A bounded, resumable run with a named stop (AS-2) | Book I replay under `sigma_resume`: each transition is paid for in ATP, a checkpoint resumes from its parent, and a step past the host ceiling is `NOT_ASSESSED`, never a verdict (§5) |
| Revision when a ground fails (AS-6) | `what-if`: what a failed cell takes with it, and the shortest paths that carry it (`tools/minds_chain.py what-if`) |
| A projection with its bound of evidence (AS-5) | Projection and attestation bundles (§4.4), checked offline by one standard-library file; `--kernel` runs the rules on the input, and the result names what was checked here and what is the witnesses' word |
| Exact dimensions of partiality (AS-4) | `rules_status`, `evidence: supplied / complete_at_tip`, `kernel: witnessed / verified_here`, each with its reason |
| Metered computation (AS-8) | `sigma_resume` (ATP per transition) and the rules kernel under `meter.py` (wasm steps) |

## Design intents and future acceptance criteria

### AS-1. Unfold on demand

Every fetch of a dependency and every spawned subtask answers a concrete need of the computation. Starting must not
require a full replica of the global graph.

Future check: an agent with a minimal starting package fetches only the subgraph it needs; a missing branch it does
not need does not block the result. A missing dependency it does need stays an explicit incompleteness.

### AS-2. Bounded recursion, kept progress

Budgets of computation, memory, fetching and spawning bound one execution. Child work must not create an unbounded
budget by recursion. A limit, or an unavailable dependency, leaves a state that can be continued, with the reason it
stopped.

Future check: interrupting and continuing at another agent keeps the subject of the task, the evidence fetched and
the account of resources; a cycle of dependencies, or a repetition without progress, does not create unbounded
work. A handover grants no new right to run code, sign records or trust the issuer by itself.

### AS-3. Separate identities of task, execution and result

A task names the request and the subject it is asked about. An execution names the rules, the executor, the
environment, the capabilities and the budget. A result names what is established, its dependencies and its
remaining limits. A change of the local budget must not turn silently into a change of the request.

Future check: two independent executions can refer to the same task and give comparable results; reuse checks that
rules, subject and trust context match. One matching task id does not make any cached result usable for every
receiver.

### AS-4. Partiality has exact dimensions

The integrity of received bytes, the authenticity of signatures, the completeness of a slice, the execution of the
rules, the link of an input to the history, and the right to rely on a result are separate facts. Unsupported rules,
a missing runtime and an exhausted budget must not turn into an invented refutation. A proved mismatch must not hide
under uncertainty. A summary `PARTIAL` needs the list of what is established and what is not yet checked.

Future check: the same package at a stronger and a weaker agent gives consistent checked parts; a missing ancestor
does not let the whole causality be declared checked. A valid signed challenge changes the assessment of reliance
under the receiver's rules, while the signature itself stays authentic.

### AS-5. A projection keeps its provenance and its bound of evidence

A projection names exactly the subject, the rules version and the context it represents. Running the kernel on a
received input proves that the output matches that input; that the input matches the full history needs evidence
of its own. Passing through several agents must not raise the level of verification by retelling.

Future check: an agent C that received B's result about projection A sees what B checked itself, what it took on
the witnesses' word, and what is still unknown. The precision of the context is checked by substituting the
subject, the rules, the bound of history, and an incomplete slice.

### AS-6. Evidence accumulates, decisions are revisited

New evidence and counterexamples keep their addressed provenance. A conclusion can change through a challenge, a
new version, a change of trust profile or a recovered missing dependency. Dependent results must let a receiver
determine what exactly needs reassessment; this document promises no instant global delivery.

Future check: a concrete counterexample reaches a consumer and causes a checkable revision of a dependent decision.
The earlier result stays history with its own context.

### AS-7. A client's self-test has an independent anchor

Canonical positive and negative vectors help to detect a faulty client. Their identity, their expected answers and
the trust in their issuer must be checkable independently of the client's own claim. A green self-test proves
neither the completeness of the protocol, nor the safety of arbitrary code, nor the truth of a capability claim.

Future check: a modified client and a self-declared capability raise no trust without a proper anchor. Supporting a
capability means a concrete path of work that is available and can be checked.

### AS-8. Only metered, pure computation

A spore carries computation only in a language whose every step is paid for from a stated budget and has no effect
outside its result: Book I terms under `sigma_resume`, or a rules module under `meter.py`. An executor never runs
native code from a spore, never gives it the network or the file system, and never extends its budget because the
spore asks. What a spore needs from outside is a fetch the executor makes, by address, and checks by hash.

Future check: a spore whose computation exceeds its budget stops with its checkpoint and `NOT_ASSESSED`, never
with a verdict; a spore that names native code, or asks for a capability the executor does not grant, is refused
before anything runs; two executors with the same budget reach the same checkpoint.

## The first end-to-end experiment

Agent A hands over a minimal spore with a projection. Agent B, with a smaller budget, fetches the dependencies it
needs and returns a bounded, signed result and a state to continue from. Agent C continues the work, checking the
subject, the rules, the resources and the trust context. After a counterexample is delivered, C revisits the
dependent conclusion.

Measure: the bytes and dependencies fetched, the amount of recomputation, the budget spent, the portability of the
continuation state, the keeping of trust bounds, and the ability to locate the cause of a disagreement. The scenario
must work without a shared catalogue, a full replica, or the author's explanations in a chat.

Conditions before it is built:

- It is pre-registered, with thresholds for each measure and a null result reported as one (as the usefulness pilot
  of roadmap G6), and it becomes a roadmap goal with obligations.
- It is built from the parts above: minds bundles as the payload, `sigma_resume` for metered execution, `what-if`
  for revision, Warrant 3 records for signed results. A part that has to be new is named as such first.

This is a criterion of the next study, not a new closure of G3, G4 or G5. The spore format, its transport, the rules
of planning, the Warrant schemas and the way they bind to minds still need their own decisions and reviews.
