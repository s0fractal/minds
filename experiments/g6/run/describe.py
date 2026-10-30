"""Descriptive numbers for REPORT.md that the frozen scorer does not compute. Not pre-registered: nothing here changes
the verdict, which is `g6.py score`'s alone.

    .venv/bin/python experiments/g6/run/describe.py > experiments/g6/run/describe.json

For every arm and every model: requests, valid replies, the invalid ones by reason, mean tokens (prompt, completion,
reasoning; over valid replies only, so a reply stopped at the cap does not count) and cost (over all replies). For
every truncated reply: its completion and reasoning tokens as OpenRouter reports them, and how well the last 20000
bytes of its reasoning compress (a reply in a repetition loop compresses to almost nothing). And every valid reply that
is not right on every decision.
"""
import json
import sys
import zlib
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import g6  # noqa: E402

TASKS, RESULTS = HERE / "tasks", HERE / "results"


def tail_ratio(text: str) -> float:
    b = text.encode()[-20000:]
    return round(len(zlib.compress(b, 9)) / len(b), 3) if b else 0.0


def main() -> None:
    g6._bound(TASKS, RESULTS)
    tasks = {p.stem: json.loads(p.read_text()) for p in sorted(TASKS.glob("h*.json"))}
    groups, loops, wrong = {}, [], []
    for p in sorted((RESULTS / "raw").glob("*.json")):
        rec = json.loads(p.read_text())
        t, m, a = rec["task"], rec["model"], rec["arm"]
        truth = tasks[t]["truth"]
        ans = g6.parse_answer(g6.reply_text(rec), sorted(truth))
        usage = (rec.get("response") or {}).get("usage") or {}
        reasoning = (usage.get("completion_tokens_details") or {}).get("reasoning_tokens") or 0
        for key in (f"arm {a}", f"model {m}", f"model {m} arm {a}"):
            g = groups.setdefault(key, {"requests": 0, "valid": 0, "invalid": {}, "prompt": [], "completion": [],
                                        "reasoning": [], "cost": 0.0})
            g["requests"] += 1
            g["cost"] += float(usage.get("cost") or 0.0)
            if ans is None:
                r = g6.invalid_reason(rec)
                g["invalid"][r] = g["invalid"].get(r, 0) + 1
            else:
                g["valid"] += 1
                g["prompt"].append(usage.get("prompt_tokens") or 0)
                g["completion"].append(usage.get("completion_tokens") or 0)
                g["reasoning"].append(reasoning)
        if ans is None and g6.invalid_reason(rec) == "truncated":
            msg = rec["response"]["choices"][0]["message"]
            loops.append({"task": t, "model": m, "arm": a, "completion_tokens": usage.get("completion_tokens"),
                          "reasoning_tokens": reasoning, "reasoning_chars": len(msg.get("reasoning") or ""),
                          "tail_compression": tail_ratio(msg.get("reasoning") or "")})
        if ans is not None and any(ans[d] != truth[d] for d in truth):
            r = g6.rates(ans, truth)
            wrong.append({"task": t, "size": tasks[t]["history"]["size"], "model": m, "arm": a,
                          "wrong_reliance": round(r["wrong_reliance"], 4), "over_caution": round(r["over_caution"], 4),
                          "missed": sorted(f"{d} ({tasks[t]['kinds'][d]}, truth {truth[d]})"
                                           for d in truth if ans[d] != truth[d])})
    mean = lambda v: round(sum(v) / len(v)) if v else None
    out = {k: {"requests": g["requests"], "valid": g["valid"], "invalid": dict(sorted(g["invalid"].items())),
               "mean_prompt_tokens": mean(g["prompt"]), "mean_completion_tokens": mean(g["completion"]),
               "mean_reasoning_tokens": mean(g["reasoning"]), "cost": round(g["cost"], 4)}
           for k, g in sorted(groups.items())}
    print(json.dumps({"groups": out, "truncated": loops, "not_right_on_every_decision": wrong}, indent=1))


if __name__ == "__main__":
    main()
