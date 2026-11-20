"""Strategic coalitional viability, blocking power & alternating-simulation dynamic loss (`COALITION.md`).

Executable Python counterpart of `proofs/Vars1/Coalition.lean`, implementing:
  1. Two-player coalitional transition games `Game(states, act_ok, env_ok, step)` with explicit
     environment liveness checking (`check_live_env`, preventing vacuous controllability).
  2. Exact finite-state fixed-point solvers for angelic (`Reach^∃`, `K_viab^∃`) vs controllable
     (`Reach^⟨⟨C⟩⟩`, `K_viab^⟨⟨C⟩⟩`) reachability and viability kernels.
  3. Blocking power attribution (`blocking_power`) with concrete adversarial witnesses, plus
     deterministic survival policy synthesis and independent verification (`synthesize_survival_policy`,
     `verify_survival_policy`).
  4. Alternating-simulation checker and dynamic translation loss report (`check_alternating_simulation`,
     `translation_loss_report`), mechanically computing `lost_dyn_angelic`, `introduced_dyn_angelic`,
     and `lost_dyn_control_viab`.
  5. Metered ATP spore-viability game builder (`spore_fuel_game`) and canonical content-addressed
     viability certificates (`viability_certificate`).
"""
from dataclasses import dataclass
import hashlib
import json


def _order(x):
    """A total order over states and actions of any hashable types (Codex F1 on #135, twice): a tuple or a frozenset by
    the order of what it holds, a scalar by type name and then value, anything else by type name and repr; values of
    different types are never compared."""
    if isinstance(x, tuple):
        return ("tuple", tuple(_order(y) for y in x))
    if isinstance(x, frozenset):
        return ("frozenset", tuple(sorted(_order(y) for y in x)))
    if x is None or isinstance(x, (bool, int, float, str, bytes)):
        return (type(x).__name__, x)
    return (type(x).__name__, repr(x))


def _sorted(xs):
    return sorted(xs, key=_order)


def _canon(x):
    """The certificate body as JSON that names every state and action unambiguously (Codex F2 on #135): a dict whose
    keys are all strings stays an object, any other dict is {"map": [[key, value], ...]} in key order (0 and "0" are
    two keys, not one); a tuple is {"tuple": [...]}, a frozenset {"set": [...]} in order; a list keeps its order. A
    game whose states and actions are strings encodes as before."""
    if isinstance(x, dict):
        if all(isinstance(k, str) for k in x):
            return {k: _canon(v) for k, v in x.items()}
        return {"map": [[_canon(k), _canon(x[k])] for k in sorted(x, key=_order)]}
    if isinstance(x, tuple):
        return {"tuple": [_canon(y) for y in x]}
    if isinstance(x, frozenset):
        return {"set": [_canon(y) for y in _sorted(x)]}
    if isinstance(x, list):
        return [_canon(y) for y in x]
    return x


@dataclass(frozen=True)
class Game:
    """Finite two-player coalitional transition game (coalition actions vs environment moves)."""
    states: frozenset
    act_ok: dict      # state -> frozenset[action]
    env_ok: dict      # state -> frozenset[env_move]
    step: dict        # (state, action, env_move) -> frozenset[next_state]


def make_game(states, act_ok, env_ok, step):
    """Construct and validate a finite `Game` (fail-closed on unknown states or malformed transitions)."""
    st = frozenset(states)
    if not st:
        raise ValueError("game states must be non-empty")
    a_map = {}
    e_map = {}
    for s in st:
        a_map[s] = frozenset(act_ok.get(s, ()))
        e_map[s] = frozenset(env_ok.get(s, ()))
    for k in act_ok:
        if k not in st:
            raise ValueError(f"act_ok references unknown state {k!r}")
    for k in env_ok:
        if k not in st:
            raise ValueError(f"env_ok references unknown state {k!r}")
    s_map = {}
    for key, nxt in step.items():
        if not (isinstance(key, tuple) and len(key) == 3):
            raise ValueError(f"step key must be (state, act, env), got {key!r}")
        s, a, e = key
        if s not in st:
            raise ValueError(f"step references unknown source state {s!r}")
        nxt_set = frozenset(nxt)
        bad = nxt_set - st
        if bad:
            raise ValueError(f"step({s!r}, {a!r}, {e!r}) targets unknown states {_sorted(bad)}")
        s_map[(s, a, e)] = nxt_set
    return Game(states=st, act_ok=a_map, env_ok=e_map, step=s_map)


def check_live_env(game: Game):
    """Verify `LiveEnv`: every admissible `(s, a)` has at least one admissible `e` with a successor.

    Prevents vacuous truth in `CPre` (a dead environment with zero moves must not forge controllability).
    Returns `(is_live, dead_pairs)`.
    """
    dead = []
    for s in _sorted(game.states):
        envs = game.env_ok.get(s, frozenset())
        for a in _sorted(game.act_ok.get(s, frozenset())):
            has_succ = any(bool(game.step.get((s, a, e))) for e in envs)
            if not has_succ:
                dead.append((s, a))
    return len(dead) == 0, dead


# ---------------------------------------------------------------- predecessor operators


def apre(game: Game, prop):
    """Angelic predecessor (`APre`): states from which some cooperative `(a, e)` reaches `prop`."""
    target = frozenset(prop)
    out = set()
    for s in game.states:
        envs = game.env_ok.get(s, frozenset())
        found = False
        for a in game.act_ok.get(s, frozenset()):
            for e in envs:
                if game.step.get((s, a, e), frozenset()) & target:
                    found = True
                    break
            if found:
                break
        if found:
            out.add(s)
    return frozenset(out)


def cpre(game: Game, prop, *, require_live=True):
    """Controllable predecessor (`CPre`, ATL `<<C>>`): states from which coalition has an admissible
    action `a` whose EVERY admissible environment response stays inside `prop`.

    When `require_live=True` (default), `(s, a)` must also have at least one admissible `(e, s')`
    successor so deadlocks never pass vacuously.
    """
    target = frozenset(prop)
    out = set()
    for s in game.states:
        envs = game.env_ok.get(s, frozenset())
        for a in game.act_ok.get(s, frozenset()):
            saw_succ = False
            ok = True
            for e in envs:
                succs = game.step.get((s, a, e), frozenset())
                if succs:
                    saw_succ = True
                    if not (succs <= target):
                        ok = False
                        break
            if ok and (not require_live or saw_succ):
                out.add(s)
                break
    return frozenset(out)


# ---------------------------------------------------------------- reachability & viability fixpoints


def angelic_reach(game: Game, targets):
    """Least fixpoint `Reach^∃(targets)`: states that can cooperatively reach `targets`."""
    cur = frozenset(targets) & game.states
    while True:
        nxt = cur | apre(game, cur)
        if nxt == cur:
            return cur
        cur = nxt


def controllable_reach(game: Game, targets, *, require_live=True):
    """Least fixpoint `Reach^⟨⟨C⟩⟩(targets)`: states from which coalition can force `targets`."""
    cur = frozenset(targets) & game.states
    while True:
        nxt = cur | cpre(game, cur, require_live=require_live)
        if nxt == cur:
            return cur
        cur = nxt


def angelic_viability(game: Game, safe):
    """Greatest fixpoint `K_viab^∃(safe)`: states with an infinite cooperative trajectory inside `safe`."""
    cur = frozenset(safe) & game.states
    while True:
        nxt = cur & apre(game, cur)
        if nxt == cur:
            return cur
        cur = nxt


def controllable_viability(game: Game, safe, *, require_live=True):
    """Greatest fixpoint `K_viab^⟨⟨C⟩⟩(safe)`: sovereign viability kernel (anti-capture floor)."""
    cur = frozenset(safe) & game.states
    while True:
        nxt = cur & cpre(game, cur, require_live=require_live)
        if nxt == cur:
            return cur
        cur = nxt


# ---------------------------------------------------------------- blocking power & survival policy


def blocking_power(game: Game, safe, *, require_live=True):
    """Compute blocking power `K_viab^∃(safe) \\ K_viab^⟨⟨C⟩⟩(safe)` with adversarial witnesses.

    Every blocked state is viable ONLY under environment cooperation; the adversary can force it
    outside the controllable viability kernel regardless of the coalition's action choice.
    """
    safe = frozenset(safe)                      # an iterable is read once, for both solvers (Codex F2 on #134)
    ang = angelic_viability(game, safe)
    ctrl = controllable_viability(game, safe, require_live=require_live)
    blocked = _sorted(ang - ctrl)
    witnesses = {}
    for s in blocked:
        per_action = {}
        envs = _sorted(game.env_ok.get(s, frozenset()))
        for a in _sorted(game.act_ok.get(s, frozenset())):
            counter = None
            for e in envs:
                bad_succs = _sorted(game.step.get((s, a, e), frozenset()) - ctrl)
                if bad_succs:
                    counter = {"env_move": e, "exits_control_kernel_to": bad_succs}
                    break
            per_action[a] = counter if counter is not None else {"env_move": None, "reason": "NO_LIVE_SUCCESSOR"}
        witnesses[s] = per_action
    ratio = (len(ctrl) / len(ang)) if ang else 1.0
    return {
        "angelic_viability": _sorted(ang),
        "controllable_viability": _sorted(ctrl),
        "blocked_states": blocked,
        "blocking_count": len(blocked),
        "sovereign_ratio": ratio,
        "witnesses": witnesses,
    }


_NOT_FOUND = object()


def synthesize_survival_policy(game: Game, safe, *, require_live=True):
    """Synthesize a deterministic survival strategy `π : K_viab^⟨⟨C⟩⟩(safe) -> Action`."""
    ctrl = controllable_viability(game, safe, require_live=require_live)
    policy = {}
    for s in _sorted(ctrl):
        envs = game.env_ok.get(s, frozenset())
        chosen = _NOT_FOUND                      # None is a legal action: the sentinel is no action (Codex F1 on #134)
        for a in _sorted(game.act_ok.get(s, frozenset())):
            saw_succ = False
            ok = True
            for e in envs:
                succs = game.step.get((s, a, e), frozenset())
                if succs:
                    saw_succ = True
                    if not (succs <= ctrl):
                        ok = False
                        break
            if ok and (not require_live or saw_succ):
                chosen = a
                break
        if chosen is not _NOT_FOUND:
            policy[s] = chosen
    return policy


def verify_survival_policy(game: Game, safe, policy, *, require_live=True):
    """Independently verify that `policy` keeps every state in `policy.keys()` inside `safe`
    and closed inside `policy.keys()` against ALL admissible environment responses."""
    safe_set = frozenset(safe) & game.states
    dom = frozenset(policy.keys())
    if not (dom <= safe_set):
        return False, {"reason": "OUTSIDE_SAFE", "states": _sorted(dom - safe_set)}
    for s in _sorted(dom):
        a = policy[s]
        if a not in game.act_ok.get(s, frozenset()):
            return False, {"reason": "INADMISSIBLE_ACTION", "state": s, "action": a}
        saw_succ = False
        for e in _sorted(game.env_ok.get(s, frozenset())):
            succs = game.step.get((s, a, e), frozenset())
            if succs:
                saw_succ = True
                escaped = _sorted(succs - dom)
                if escaped:
                    return False, {
                        "reason": "ESCAPED_KERNEL",
                        "state": s,
                        "action": a,
                        "env_move": e,
                        "escaped_to": escaped,
                    }
        if require_live and not saw_succ:
            return False, {"reason": "DEAD_ENVIRONMENT", "state": s, "action": a}
    return True, {"verified_states": len(dom)}


# ---------------------------------------------------------------- alternating simulation & F5 dynamic loss


def check_alternating_simulation(g1: Game, g2: Game, phi: dict):
    """Check whether `phi : dom(phi) -> g2.states` is an alternating simulation from `g1` to `g2`.

    For every `s1 in dom(phi)` and `a1 in g1.act_ok[s1]`, there must exist `a2 in g2.act_ok[phi[s1]]`
    such that every `(e2, s2')` reachable from `(phi[s1], a2)` in `g2` reflects back to some
    `(e1, s1')` reachable from `(s1, a1)` in `g1` with `s1' in dom(phi)` and `phi[s1'] == s2'`.
    """
    uncovered = _sorted(g1.states - set(phi))
    bad_images = _sorted(s1 for s1, s2 in phi.items() if s1 in g1.states and s2 not in g2.states)
    if bad_images:
        return {
            "is_alt_sim": False,
            "uncovered_states": uncovered,
            "counterexamples": [{"state": s1, "reason": "IMAGE_NOT_IN_G2", "image": phi[s1]} for s1 in bad_images],
        }

    counterexamples = []
    for s1 in _sorted(s for s in phi if s in g1.states):
        s2 = phi[s1]
        e1_set = g1.env_ok.get(s1, frozenset())
        e2_set = g2.env_ok.get(s2, frozenset())
        for a1 in _sorted(g1.act_ok.get(s1, frozenset())):
            g1_succ_images = set()
            for e1 in e1_set:
                for s1p in g1.step.get((s1, a1, e1), frozenset()):
                    if s1p in phi:
                        g1_succ_images.add(phi[s1p])

            matched = False
            for a2 in _sorted(g2.act_ok.get(s2, frozenset())):
                ok_a2 = True
                for e2 in e2_set:
                    for s2p in g2.step.get((s2, a2, e2), frozenset()):
                        if s2p not in g1_succ_images:
                            ok_a2 = False
                            break
                    if not ok_a2:
                        break
                if ok_a2:
                    matched = True
                    break
            if not matched:
                counterexamples.append({
                    "state": s1,
                    "image": s2,
                    "action": a1,
                    "reason": "NO_SIMULATING_ACTION",
                })

    return {
        "is_alt_sim": len(counterexamples) == 0 and len(uncovered) == 0,
        "uncovered_states": uncovered,
        "counterexamples": counterexamples,
    }


def translation_loss_report(g1: Game, g2: Game, phi: dict, safe1, safe2, *, require_live=True):
    """Compute static & dynamic translation loss report (`F5 / D24`) for partial morphism `phi`."""
    safe1, safe2 = frozenset(safe1), frozenset(safe2)      # read once: static and dynamic analyses both use them
    dom = _sorted(s for s in phi if s in g1.states and phi[s] in g2.states)
    uncovered = _sorted(g1.states - set(dom))
    s1_safe = frozenset(safe1) & g1.states
    s2_safe = frozenset(safe2) & g2.states
    static_lost = _sorted(s for s in dom if s in s1_safe and phi[s] not in s2_safe)

    def _forward_angelic(game, start):
        visited = {start}
        frontier = [start]
        while frontier:
            cur = frontier.pop()
            for a in game.act_ok.get(cur, frozenset()):
                for e in game.env_ok.get(cur, frozenset()):
                    for nxt in game.step.get((cur, a, e), frozenset()):
                        if nxt not in visited:
                            visited.add(nxt)
                            frontier.append(nxt)
        return visited

    fwd1 = {s: _forward_angelic(g1, s) for s in dom}
    fwd2 = {phi[s]: _forward_angelic(g2, phi[s]) for s in dom}

    lost_dyn_angelic = []
    intro_dyn_angelic = []
    for x in dom:
        for y in dom:
            r1 = y in fwd1[x]
            r2 = phi[y] in fwd2[phi[x]]
            if r1 and not r2:
                lost_dyn_angelic.append([x, y])
            elif (not r1) and r2:
                intro_dyn_angelic.append([x, y])

    cv1 = controllable_viability(g1, safe1, require_live=require_live)
    cv2 = controllable_viability(g2, safe2, require_live=require_live)
    lost_dyn_ctrl = _sorted(s for s in dom if s in cv1 and phi[s] not in cv2)

    alt = check_alternating_simulation(g1, g2, phi)
    faithful = bool(alt["is_alt_sim"]) and not uncovered and not static_lost and not lost_dyn_ctrl

    return {
        "warrant": "translation-loss/1",
        "dom_size": len(dom),
        "uncovered_states": uncovered,
        "static_lost": static_lost,
        "lost_dyn_angelic": lost_dyn_angelic,
        "introduced_dyn_angelic": intro_dyn_angelic,
        "lost_dyn_control_viab": lost_dyn_ctrl,
        "alt_sim": alt,
        "faithful_control_transport": faithful,
    }


# ---------------------------------------------------------------- standard models & certificates


def f6_toy_game():
    """Exact executable counterpart of `Vars1.Coalition.f6Game` (`K_viab^∃ = {0,1,2,3}`, `K_viab^⟨⟨C⟩⟩ = {0,1,2}`)."""
    states = ["0", "1", "2", "3", "4"]
    act_ok = {s: ["act"] for s in states}
    env_ok = {s: ["coop", "block"] for s in states}
    step = {}
    for s in ["0", "1", "2"]:
        for e in ["coop", "block"]:
            step[(s, "act", e)] = ["0"]
    step[("3", "act", "coop")] = ["2"]
    step[("3", "act", "block")] = ["4"]
    for e in ["coop", "block"]:
        step[("4", "act", e)] = ["4"]
    return make_game(states, act_ok, env_ok, step), frozenset(["0", "1", "2", "3"])


def spore_fuel_game(max_atp: int, step_cost: int, *, replenish_delta: int = 0, env_can_deny_replenish: bool = True):
    """Finite ATP fuel-viability game connecting `spore.py` budgets with strategic viability.

    States are `atp_0 .. atp_{max_atp}`, safe region is `{atp_k | k >= step_cost}` (enough ATP to act).
    - Action `work`: burns `step_cost` ATP.
    - Action `harvest` (if `replenish_delta > 0`): gains `replenish_delta` ATP (capped at `max_atp`)
      when environment cooperates (`grant`), or burns `step_cost` when environment denies (`deny`).
    """
    if max_atp < 1 or step_cost < 1 or step_cost > max_atp:
        raise ValueError("require 1 <= step_cost <= max_atp")
    states = [f"atp_{k}" for k in range(max_atp + 1)]
    safe = frozenset(f"atp_{k}" for k in range(step_cost, max_atp + 1))
    act_ok = {}
    env_ok = {}
    step = {}
    envs = ["grant", "deny"] if env_can_deny_replenish else ["grant"]
    for k in range(max_atp + 1):
        s = f"atp_{k}"
        acts = ["work"]
        if replenish_delta > 0:
            acts.append("harvest")
        act_ok[s] = acts
        env_ok[s] = envs
        after_work = f"atp_{max(0, k - step_cost)}"
        for e in envs:
            step[(s, "work", e)] = [after_work]
        if replenish_delta > 0:
            step[(s, "harvest", "grant")] = [f"atp_{min(max_atp, k + replenish_delta)}"]
            if env_can_deny_replenish:
                step[(s, "harvest", "deny")] = [after_work]
    return make_game(states, act_ok, env_ok, step), safe


def viability_certificate(game: Game, safe, *, label="unnamed", require_live=True):
    """Produce a deterministic, content-addressed SHA-256 viability & anti-capture certificate."""
    safe = frozenset(safe)                      # read once: synthesis, verification and the body all use it
    live, dead = check_live_env(game)
    bp = blocking_power(game, safe, require_live=require_live)
    pol = synthesize_survival_policy(game, safe, require_live=require_live)
    pol_ok, pol_info = verify_survival_policy(game, safe, pol, require_live=require_live)
    body = {
        "schema": "vars1-coalition-viability@1",
        "label": label,
        "live_env": live,
        "dead_pairs": [list(x) for x in dead],
        "safe": _sorted(frozenset(safe) & game.states),
        "angelic_viability": bp["angelic_viability"],
        "controllable_viability": bp["controllable_viability"],
        "blocked_states": bp["blocked_states"],
        "sovereign_ratio": bp["sovereign_ratio"],
        "policy": pol,
        "policy_verified": pol_ok,
        "policy_info": pol_info,
    }
    canon = json.dumps(_canon(body), sort_keys=True, separators=(",", ":")).encode("utf-8")
    digest = hashlib.sha256(canon).hexdigest()
    return {"digest": digest, "certificate": body}
