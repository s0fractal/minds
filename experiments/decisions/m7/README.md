# M7: questions delivered to their addressee (registered 2026-11-14)

The experiment is the goal record `M7` (3415bb3c) in `.warrant/records.jsonl`; its `opened` holds the whole design. Its
questions are goals Q1 (version e8134a4c), Q2 (61bfdffd, s0fractal/minds#96 after the fact) and Q3 (b8d120b3, the arena),
all for codex, answered by 2026-11-16T20:00:00Z or not at all.

This folder holds the baseline its stop rule compares against:

- `profile-releases.json`: M4's profile (every release at fd7b2f9e a goal, `min_cut_threshold` 2), SHA-256 73c17e0e;
- `tensions-a41d03f1.json`: its output on `refs/vars/heads/minds` at a41d03f1, SHA-256 988c1f6b: 49 FRAGILITY.

At the verdict the same command runs once more on the chain's tip then:

    python3 experiments/decisions/profile.py . minds experiments/decisions/m7/profile-releases.json --tip TIP
