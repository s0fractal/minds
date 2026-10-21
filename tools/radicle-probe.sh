#!/usr/bin/env bash
# Does Radicle replicate refs/vars/*? Two throwaway nodes on 127.0.0.1, test network, static peers, no seeds:
# nothing leaves this machine. Usage: tools/radicle-probe.sh [WORKDIR]   (needs rad and radicle-node)
set -euo pipefail
W=${1:-$(mktemp -d)}; W=$(cd "$W" && pwd)
export RAD_PASSPHRASE=probe-only
# The control socket path must stay under 104 bytes (macOS SUN_LEN), so sockets live in a short temp dir.
SOCK=$(mktemp -d /tmp/radp.XXXX)
node() { RAD_HOME="$W/$1" RAD_SOCKET="$SOCK/$1" "${@:2}"; }
trap 'node a rad node stop >/dev/null 2>&1 || true; node b rad node stop >/dev/null 2>&1 || true; rm -rf "$SOCK"' EXIT

for n in a b; do mkdir -p "$W/$n"; node $n rad auth --alias "vars-$n" >/dev/null; done
NA=$(node a rad self --nid 2>/dev/null)
for n in a b; do
  python3 - "$W/$n/config.json" "$n" "$NA" <<'PY'
import json, sys
p, n, na = sys.argv[1:]
c = json.load(open(p)); c["preferredSeeds"] = []
c["node"].update({"listen": ["127.0.0.1:%d" % (18776 if n == "a" else 18777)], "peers": {"type": "static"},
                  "connect": [] if n == "a" else [na + "@127.0.0.1:18776"], "externalAddresses": [], "network": "test"})
json.dump(c, open(p, "w"), indent=2)
PY
  node $n rad node start >/dev/null
done
sleep 3

R="$W/repo"; mkdir -p "$R"; cd "$R"
git init -q -b main; git -c user.email=p@l -c user.name=p commit -q --allow-empty -m main
mk() {  # a vars commit whose tree is cas/<name> -> blob(<text>), with optional parent
  local b t t2; b=$(printf '%s\n' "$2" | git hash-object -w --stdin)
  t=$(printf "100644 blob %s\t%s\n" "$b" "$1" | git mktree); t2=$(printf "040000 tree %s\tcas\n" "$t" | git mktree)
  git -c user.email=p@l -c user.name=p commit-tree "$t2" ${3:+-p "$3"} -m "$1"
}
C1=$(mk cell "first"); git update-ref refs/vars/heads/core "$C1"
node a rad init --name vars-probe --description probe --default-branch main --public --no-confirm >/dev/null
RID=$(node a rad inspect --rid)
node a git push -q rad 'refs/vars/heads/core:refs/vars/heads/core' 2>/dev/null
C2=$(mk cell2 "second" "$C1"); git update-ref refs/vars/heads/core "$C2" "$C1"
node a git push -q rad 'refs/vars/heads/core:refs/vars/heads/core' 2>/dev/null
# a rules change's evidence ref (§4.3): an unrelated commit, reachable only from refs/vars/evidence/*
E1=$(mk evidence "counterexample"); git update-ref refs/vars/evidence/core/decision "$E1"
node a git push -q rad 'refs/vars/evidence/core/decision:refs/vars/evidence/core/decision' 2>/dev/null

node b rad seed "$RID" --scope all >/dev/null
node b rad sync --fetch "$RID" --timeout 30sec >/dev/null
A="$W/a/storage/${RID#rad:}"; B="$W/b/storage/${RID#rad:}"; REF="refs/namespaces/$NA/refs/vars/heads/core"
signed=$(git --git-dir "$A" show "refs/namespaces/$NA/refs/rad/sigrefs:refs" | grep -c ' refs/vars/heads/core$' || true)
got=$(git --git-dir "$B" rev-parse "$REF" 2>/dev/null || echo none)
echo "rid=$RID nid_a=$NA"
echo "A signs refs/vars/heads/core in rad/sigrefs: $signed"
echo "A head=$C2  B head=$got"
[ "$signed" = 1 ] && [ "$got" = "$C2" ] && git --git-dir "$B" merge-base --is-ancestor "$C1" "$got" \
  && echo "REPLICATED: refs/vars/heads/core arrives at B as $REF, signed, with history" \
  || { echo "NOT REPLICATED"; exit 1; }
EREF="refs/namespaces/$NA/refs/vars/evidence/core/decision"
esigned=$(git --git-dir "$A" show "refs/namespaces/$NA/refs/rad/sigrefs:refs" | grep -c ' refs/vars/evidence/core/decision$' || true)
egot=$(git --git-dir "$B" rev-parse "$EREF" 2>/dev/null || echo none)
echo "A signs refs/vars/evidence/core/decision in rad/sigrefs: $esigned"
echo "A evidence=$E1  B evidence=$egot"
[ "$esigned" = 1 ] && [ "$egot" = "$E1" ] && git --git-dir "$B" cat-file -e "$E1^{commit}" \
  && echo "REPLICATED: refs/vars/evidence/core/decision arrives at B as $EREF, signed, with its commit" \
  || { echo "EVIDENCE NOT REPLICATED"; exit 1; }
