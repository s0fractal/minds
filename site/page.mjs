// The release check page: fetch the published bundles (index.json names them), let the reader pin keys, and run the
// verifier's own command line on them here (minds_verify.mjs, held to minds_verify.py by verify/vectors.json). Every
// word of a verdict below is the verifier's: its exit code, its `explain` fields, its refusal. Text is set as text.
import { compareProjections, readBundle, runCommand, sha256, toHex } from "./minds_verify.mjs";

const $ = (id) => document.getElementById(id);
const el = (tag, text, cls) => {
  const e = document.createElement(tag);
  if (text !== undefined) e.textContent = text;
  if (cls) e.className = cls;
  return e;
};
const store = {
  get(k) { try { return localStorage.getItem(k); } catch { return null; } },
  set(k, v) { try { localStorage.setItem(k, v); } catch { /* a private window keeps nothing */ } },
};
const HEX64 = /^[0-9a-f]{64}$/;
const indexUrl = new URL(new URLSearchParams(location.search).get("index") ?? "index.json", location.href);
const state = { index: null, files: {}, names: new Map() };

function status(text) { $("status").textContent = text; }

async function fetchBytes(url, sha) {
  const r = await fetch(url, { cache: "no-cache" });
  if (!r.ok) throw new Error(`${url} answered ${r.status}`);
  const bytes = new Uint8Array(await r.arrayBuffer());
  if (sha && toHex(await sha256(bytes)) !== sha) throw new Error(`${url} does not hash to what the index names`);
  return bytes;
}

const short = (k) => `${k.slice(0, 12)}…`;
const nameOf = (k) => (state.names.has(k) ? `${state.names.get(k)} (${short(k)})` : k);

function fact(dl, term, value) {
  dl.append(el("dt", term), el("dd", value));
}

async function load() {
  const index = JSON.parse(new TextDecoder().decode(await fetchBytes(indexUrl)));
  if (index.format !== "minds.published-bundles@1") throw new Error("the index is not minds.published-bundles@1");
  state.index = index;
  for (const m of index.roster) state.names.set(m.key, m.name);
  const base = indexUrl;
  state.files["attestation.json"] = await fetchBytes(new URL(index.attestation.file, base), index.attestation.sha256);
  state.files["projection.json"] = await fetchBytes(new URL(index.projection.file, base), index.projection.sha256);

  const dl = $("release-facts");
  fact(dl, "Release", index.attestation.statement ?? index.attestation.decision);
  fact(dl, "Decision", index.attestation.decision);
  fact(dl, "Projection", `${index.projection.id} at chain commit ${index.projection.tip}`);
  fact(dl, "Chain", `refs/vars/heads/minds at ${index.chain_tip}`);
  fact(dl, "Published", index.published);
  fact(dl, "Verifier", `minds_verify.mjs of main@${index.verifier.main.slice(0, 12)}, SHA-256 ${short(index.verifier.sha256)}`);
  $("release").hidden = false;

  const saved = (store.get("minds.pins") ?? "").split("\n").filter((k) => HEX64.test(k));
  const endorsed = new Set(index.attestation.endorsers ?? []);
  const witnessed = new Set(index.projection.witnesses ?? []);
  const roster = $("roster");
  for (const m of index.roster) {
    const box = el("input");
    box.type = "checkbox";
    box.value = m.key;
    box.checked = saved.length ? saved.includes(m.key) : endorsed.has(m.key) && witnessed.has(m.key);
    const said = [endorsed.has(m.key) ? "endorsed this release" : "has not endorsed this release",
      witnessed.has(m.key) ? "witnessed the projection" : "has not witnessed the projection"];
    const label = el("label");
    label.append(box, el("span", m.name), el("span", m.key, "key"), el("span", `${said.join(", ")}, says the index`, "small"));
    roster.append(label);
  }
  $("extra").value = saved.filter((k) => !state.names.has(k)).join("\n");
  $("pins").hidden = false;
  status("Bundles fetched. Choose the keys you trust and check.");
}

function pinned() {
  const keys = [...document.querySelectorAll("#roster input:checked")].map((b) => b.value);
  for (const line of $("extra").value.split("\n").map((s) => s.trim().toLowerCase()).filter(Boolean)) {
    if (!HEX64.test(line)) throw new Error(`not a key of 64 hex digits: ${line.slice(0, 80)}`);
    keys.push(line);
  }
  return [...new Set(keys)];
}

function reasonsOf(cmd, r) {
  const out = [];
  if (cmd === "verify-attestation") {
    for (const row of r.explain.required) {
      out.push(`${nameOf(row.key)}: ${row.reasons.length ? row.reasons.join("; ")
        : "endorses the cell at the projection's tip and witnessed the projection"}`);
    }
    if (r.rules_status === "unsupported") out.push(`rules: ${r.explain.rules.reason}`);
    if (r.evidence !== "complete_at_tip") out.push(`evidence: ${r.evidence} (the projection does not hold the cell)`);
    if (r.attested_at_tip === false) out.push(`not settled at the projection's tip: ${r.explain.at_tip.endorsers.length} of ${r.threshold} policy keys endorse it`);
    if (r.contradicted_after_tip) {
      for (const w of r.explain.after_tip.withdrawn) out.push(`withdrawn after the tip: ${w.verifier}, ${nameOf(w.key)}`);
    }
    if (r.grounded_after_tip === false) out.push(`not grounded; ungrounded: ${r.explain.grounded.ungrounded.join(", ") || "none named"}`);
    if (r.grounded_after_tip === null) out.push(`grounded turns on a replay: ${r.explain.grounded.needs_replay.join(", ")}`);
    if (r.projection_witnessed === false) {
      out.push(`the projection is not witnessed under its own policy; missing: ${r.explain.projection.witnesses_missing.map(nameOf).join(", ")}`);
    }
  } else {
    for (const k of r.required_missing) out.push(`${nameOf(k)}: did not witness the projection`);
    if (!r.witnessed) out.push(`not witnessed under its own policy; missing: ${r.explain.witnesses_missing.map(nameOf).join(", ")}`);
    if (r.rules_status === "unsupported") out.push(`rules: ${r.explain.rules.reason}`);
  }
  const k = cmd === "verify-attestation" ? r.explain.projection?.kernel : r.explain.kernel;
  if (k) {
    out.push(k.status === "verified_here" ? "kernel: verified_here: the rules module ran here and gave the bundle's output"
      : `kernel: witnessed: the output is the witnesses' word (${k.reason})`);
  }
  return out;
}

async function check() {
  let pins;
  try {
    pins = pinned();
  } catch (e) {
    status(e.message);
    return;
  }
  if (!pins.length) {
    status("Pin at least one key: verify needs keys you chose, not the bundle's own policy.");
    return;
  }
  store.set("minds.pins", pins.join("\n"));
  const files = { ...state.files };
  const chosen = $("file").files[0];
  let name = "attestation.json";
  if (chosen) {
    files["chosen.json"] = new Uint8Array(await chosen.arrayBuffer());
    name = "chosen.json";
  }
  let cmd = "verify-attestation";
  try {
    if (readBundle(files[name]).format === "vars-1.projection-bundle@1") cmd = "verify-projection";
  } catch { /* the verifier refuses it below, in its own words */ }
  const argv = [cmd, name, ...pins.flatMap((k) => ["--require", k])];
  if ($("kernel").checked) {
    status("Fetching the rules modules…");
    for (const [i, m] of state.index.rules.entries()) {
      files[`rules-${i}.wasm`] = await fetchBytes(new URL(m.file, indexUrl), m.id);
      argv.push("--kernel", `rules-${i}.wasm`);
    }
  }
  status("Checking…");
  const read = async (f) => files[f];
  const r = await runCommand(argv, read);
  render(cmd, argv, r, files[name]);
  status("");
}

async function render(cmd, argv, r, bundleBytes) {
  $("verdict").hidden = false;
  $("verdict-head").textContent = cmd === "verify-attestation" ? "The release, for the keys you pinned" : "The projection, for the keys you pinned";
  const word = $("verdict-word");
  const list = $("reasons");
  const counted = $("counted");
  list.replaceChildren();
  counted.replaceChildren();
  $("history").textContent = "";
  $("command").textContent = `node minds_verify.mjs ${argv.join(" ")}   (exit ${r.code})`;
  $("raw").textContent = r.stdout || r.stderr;
  if (r.code === 2 || r.code === 3) {
    word.textContent = r.code === 2 ? "Refused" : "The verifier failed (exit 3, never a verdict)";
    word.className = "word refused";
    list.append(el("li", r.stderr.trim()));
    return;
  }
  const result = JSON.parse(r.stdout);
  word.textContent = r.code === 0 ? "Accepted" : "Not accepted";
  word.className = r.code === 0 ? "word ok" : "word no";
  for (const line of reasonsOf(cmd, result)) list.append(el("li", line));
  if (cmd === "verify-attestation") {
    const ex = result.explain;
    fact(counted, "Policy", `${ex.policy.threshold} of ${ex.policy.keys.length} (${ex.policy.source})`);
    for (const row of ex.at_tip?.counted ?? []) fact(counted, row.verifier, row.endorsers.map(nameOf).join(", "));
    if (ex.scope_epoch) fact(counted, "Scope epoch", ex.scope_epoch);
    fact(counted, "Witnesses", result.explain.projection.witness_seals.map((s) => `${nameOf(s.key)}${s.counted ? "" : " (not counted)"}`).join(", "));
  } else {
    fact(counted, "Witness policy", `${result.threshold} of ${result.explain.witness_policy.keys.length}`);
    fact(counted, "Witnesses", result.witnesses.map(nameOf).join(", "));
  }
  if (r.code === 0) await history(cmd, bundleBytes);
}

// verify-extends against the last projection this browser accepted: one history, or a fork to see
async function history(cmd, bundleBytes) {
  const projection = cmd === "verify-attestation" ? readBundle(bundleBytes).projection : readBundle(bundleBytes);
  const last = store.get("minds.last-accepted");
  if (last) {
    try {
      const c = await compareProjections(JSON.parse(last), projection);
      $("history").textContent = c.relation === "same" || c.relation === "extends"
        ? `Since the last projection this browser accepted (${c.a.tip.slice(0, 12)}, ${c.a.commits} commits): ${c.relation}.`
        : `Since the last projection this browser accepted: ${c.relation}${c.equivocation ? `; sealed both: ${c.sealed_both.map(nameOf).join(", ")}` : ""}.`;
      if (c.relation === "behind") return;
    } catch (e) {
      $("history").textContent = `The last accepted projection could not be compared: ${e.message}`;
    }
  }
  store.set("minds.last-accepted", JSON.stringify(projection));
}

$("check").addEventListener("click", () => { check().catch((e) => status(`Error: ${e.message}`)); });
load().catch((e) => status(`Could not load the published bundles: ${e.message}`));
