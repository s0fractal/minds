#!/bin/bash
# The G6 pilot's run (PREREG.md), started by the owner from the repository root at the freeze:
#
#   bash experiments/g6/run.sh smoke [KEY_FILE]     # the smoke run: 2 histories, 18 requests
#   bash experiments/g6/run.sh confirm [KEY_FILE]   # the confirmatory run: 16 histories, 144 requests
#
# The OpenRouter key is read from KEY_FILE (mode 600), or else without echo, and lives only in this process's
# environment. `g6.py budget` refuses a key with no credit limit or one above $5; the run's budget is what the key
# has left, at most $5.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
# the freeze: the last merge into main that changed the pilot itself, not its run's files
code=(experiments/g6 ':!experiments/g6/run' ':!experiments/g6/smoke' ':!experiments/g6/REPORT.md')
freeze=$(git log --first-parent --merges --format=%H -1 main -- "${code[@]}")
[ -n "$freeze" ] || { echo "no freeze: the pilot has not been merged into main" >&2; exit 1; }
git diff --quiet "$freeze" HEAD -- "${code[@]}" || { echo "the pilot's code differs from the freeze $freeze" >&2; exit 1; }
[ -z "$(git status --porcelain -- . ':!experiments/g6/run' ':!experiments/g6/smoke')" ] || {
    echo "the tree is not clean" >&2; exit 1; }
echo "freeze $freeze" >&2
case "${1:-}" in
    smoke) seed="smoke-$freeze"; count=2; out=experiments/g6/smoke ;;
    confirm) seed="$freeze"; count=16; out=experiments/g6/run ;;
    *) echo "usage: run.sh smoke|confirm" >&2; exit 2 ;;
esac
[ -e "$out/tasks" ] || .venv/bin/python experiments/g6/g6.py generate --seed "$seed" --count "$count" --out "$out/tasks"
# tasks left from another freeze, or changed since, are refused before any key is read
.venv/bin/python experiments/g6/g6.py bind --tasks "$out/tasks" --seed "$seed" --count "$count" >/dev/null
if [ -n "${2:-}" ]; then
    [ "$(stat -f %Lp "$2")" = 600 ] || { echo "$2 must be mode 600" >&2; exit 1; }
    IFS= read -r OPENROUTER_API_KEY < "$2"
else
    printf 'OpenRouter key (not shown), then Enter: ' >&2
    IFS= read -rs OPENROUTER_API_KEY
    printf '\n' >&2
    pbcopy </dev/null 2>/dev/null || true
fi
export OPENROUTER_API_KEY
budget=$(.venv/bin/python experiments/g6/g6.py budget --cap 5)
.venv/bin/python experiments/g6/g6.py run --tasks "$out/tasks" --out "$out/results" --budget "$budget"
unset OPENROUTER_API_KEY
.venv/bin/python experiments/g6/g6.py score --tasks "$out/tasks" --results "$out/results" > "$out/score.json"
echo "scored: $out/score.json" >&2
