#!/bin/zsh
# Local assurance for the rules kernel (not in CI: the model checker needs ~15 GB per harness).
#   kernel/assure.sh kani     each Kani harness, one at a time, under a 20 GB / 30 min watchdog
#   kernel/assure.sh fuzz [S] libFuzzer on `evaluate` for S seconds (default 600), seeded from the property suite
# Never run harnesses in parallel on a workstation: each CBMC peaks at 10-15 GB.
set -u
cd "${0:A:h}"
FLAGS=(-Z unstable-options --cbmc-args --max-field-sensitivity-array-size 2048 --unwindset memcmp.0:33)
case "${1:-}" in
  kani)
    for h in two_cells_axiom_relies two_cells_acceptance two_cells_foreign_scope; do
      ( sleep 20
        while true; do
          ps -eo pid,etime,rss,comm | awk '$4 ~ /cbmc/ {split($2,t,":"); m=(length(t)==3)?t[1]*60+t[2]:t[1]; if ($3 > 20971520 || m >= 30) print $1}' \
            | xargs -r kill 2>/dev/null
          pgrep -f cargo-kani >/dev/null || exit 0
          sleep 5
        done ) &
      start=$(date +%s)
      cargo kani --harness $h "${FLAGS[@]}" > /tmp/kani-$h.log 2>&1
      echo "$h $(( $(date +%s) - start ))s $(grep -E '^VERIFICATION' /tmp/kani-$h.log)"
      wait
    done ;;
  fuzz)
    ( cd .. && .venv/bin/python tools/fuzz_seeds.py )
    cd fuzz && cargo +nightly fuzz run evaluate corpus/evaluate -- \
      -max_total_time="${2:-600}" -rss_limit_mb=2048 -timeout=10 ;;
  *) echo "usage: kernel/assure.sh kani | fuzz [SECONDS]" >&2; exit 2 ;;
esac
