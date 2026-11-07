"""Which tags of our repositories locked a version that a RustSec advisory affects (REPORT.md).

Standard library only. Reads a checkout of the advisory database and each repository's tags. For every Cargo.lock a tag
holds, it lists the advisories on a registry package it locks whose patched and unaffected requirements leave that
version out, as cargo-deny reads them, and marks the withdrawn ones (cargo-deny skips those). A tag named v<digit> is a
release; the others are snapshots. Data files are read, never executed.

    python3 -I baseline.py DB REPO [REPO ...] > releases.json
"""
import glob, json, os, re, subprocess, sys, tomllib


def ver(s):
    s = s.strip()
    core, _, pre = s.partition("-")
    core = core.partition("+")[0]
    parts = [int(x) for x in core.split(".")]
    n = len(parts)
    parts += [0] * (3 - n)
    return (parts[0], parts[1], parts[2], pre), n


def key(v):
    a, b, c, pre = v
    # a pre-release sorts before its release; pre-release identifiers compare as strings here (none is locked by us)
    return (a, b, c, 0 if pre else 1, pre)


def comparator(op, s):
    (a, b, c, pre), n = ver(s)
    lo = (a, b, c, pre)
    if op in ("^", ""):
        if a > 0 or n == 1:
            hi = (a + 1, 0, 0, "")
        elif b > 0 or n == 2:
            hi = (0, b + 1, 0, "")
        else:
            hi = (0, 0, c + 1, "")
        return lambda v: key(lo) <= key(v) < key(hi)
    if op == "~":
        hi = (a, b + 1, 0, "") if n >= 2 else (a + 1, 0, 0, "")
        return lambda v: key(lo) <= key(v) < key(hi)
    if op == "=":
        return lambda v: key(v) == key(lo)
    return {">=": lambda v: key(v) >= key(lo), ">": lambda v: key(v) > key(lo),
            "<=": lambda v: key(v) <= key(lo), "<": lambda v: key(v) < key(lo)}[op]


def req(text):
    cs = []
    for part in text.split(","):
        m = re.fullmatch(r"\s*(>=|<=|>|<|=|\^|~)?\s*([0-9][0-9A-Za-z.+-]*)\s*", part)
        if not m:
            raise ValueError(text)
        cs.append(comparator(m.group(1) or "", m.group(2)))
    return lambda v: all(c(v) for c in cs)


def advisories(db):
    out = []
    for f in sorted(glob.glob(os.path.join(db, "crates", "*", "*.md"))):
        s = open(f, encoding="utf-8").read()
        meta = tomllib.loads(re.search(r"```toml\n(.*?)\n```", s, re.S).group(1))
        a, vs = meta["advisory"], meta.get("versions", {})
        reqs = [req(r) for r in vs.get("patched", []) + vs.get("unaffected", [])]
        out.append({"id": a["id"], "package": a["package"], "date": a.get("date"), "withdrawn": a.get("withdrawn"),
                    "kind": a.get("informational") or "vulnerability", "reqs": reqs})
    return out


def git(repo, *args):
    return subprocess.run(["git", "-C", repo, *args], capture_output=True, text=True).stdout


def main():
    db, repos = sys.argv[1], sys.argv[2:]
    advs = advisories(db)
    by_pkg = {}
    for a in advs:
        by_pkg.setdefault(a["package"], []).append(a)
    report = {"db": git(db, "rev-parse", "HEAD").strip(), "advisories": len(advs),
              "withdrawn": sum(1 for a in advs if a["withdrawn"]), "tags": []}
    for repo in repos:
        for line in git(repo, "tag", "-l", "--format=%(refname:short) %(creatordate:short)").splitlines():
            tag, date = line.split()
            for lock in git(repo, "ls-tree", "-r", "--name-only", tag).split():
                if not lock.endswith("Cargo.lock"):
                    continue
                pkgs = tomllib.loads(git(repo, "show", f"{tag}:{lock}")).get("package", [])
                hits = []
                for p in pkgs:
                    if "source" not in p:
                        continue  # a workspace member, not from the registry
                    v = ver(p["version"])[0]
                    for a in by_pkg.get(p["name"], []):
                        if not any(r(v) for r in a["reqs"]):
                            hits.append({"id": a["id"], "crate": f'{p["name"]}@{p["version"]}', "date": a["date"],
                                         "kind": a["kind"], "withdrawn": a["withdrawn"]})
                report["tags"].append({"repo": os.path.basename(repo.rstrip("/")), "tag": tag, "tag_date": date,
                                       "commit": git(repo, "rev-parse", tag + "^{commit}").strip(),
                                       "release": re.match(r"v[0-9]", tag) is not None,
                                       "lockfile": lock, "packages": len(pkgs), "hits": hits})
    json.dump(report, sys.stdout, indent=1, sort_keys=True)
    print()


if __name__ == "__main__":
    main()
