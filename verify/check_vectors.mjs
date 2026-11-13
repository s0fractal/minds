// Holds verify/minds_verify.mjs to verify/minds_verify.py: every vector of verify/vectors.json, answered here, must
// be the bytes the Python file answered (tools/verify_vectors.py). A command line: its exit code, stdout and stderr.
// A call: its result as Python's json.dumps(result, indent=2, sort_keys=True), or its exception's class and words.
//
//     node verify/check_vectors.mjs verify/vectors.json
//
// Prints one JSON line: the vectors read, the answers compared, and every difference (index, source, what differs).
// Exit 0 only when every vector of the file was answered and none differs: a short or empty run is a failure.
import { readFile } from "node:fs/promises";
import * as MV from "./minds_verify.mjs";

const doc = JSON.parse(await readFile(process.argv[2] ?? new URL("./vectors.json", import.meta.url), "utf8"));
if (doc.format !== "minds.verify-vectors@1") throw new Error("not a minds.verify-vectors@1 file");
const blobs = new Map();
for (const [h, v] of Object.entries(doc.blobs)) {
  const bytes = v.startsWith("hex:") ? MV.fromhex(v.slice(4)) : new TextEncoder().encode(v);
  if (MV.toHex(await MV.sha256(bytes)) !== h) throw new Error(`blob ${h.slice(0, 12)} does not hash to its name`);
  blobs.set(h, bytes);
}

async function answer(v) {
  if (v.kind === "command") {
    const read = async (name) => {
      if (!Object.hasOwn(v.files, name)) throw new MV.VarsError(`no file ${name} in the vector`);
      return blobs.get(v.files[name]);
    };
    return MV.runCommand(v.argv, read);
  }
  if (v.kind === "parse") {
    try {
      const ki = MV.parseKernelInput(blobs.get(v.input), v.encoding);
      return { result: MV.pyDumps({ ...ki, pols: Object.fromEntries(ki.pols) }, { indent: 2 }) };
    } catch (e) {
      return { raised: e.name, message: e.message };
    }
  }
  const text = (h) => new TextDecoder().decode(blobs.get(h));
  const bundles = v.bundles.map((h) => MV.pyLoads(text(h)));
  try {
    const opts = { require: v.require.map(MV.fromhex), kernels: v.kernels.map((h) => blobs.get(h)) };
    const result = v.function === "compare_projections" ? await MV.compareProjections(...bundles)
      : v.function === "verify_projection" ? await MV.verifyProjection(bundles[0], opts)
        : await MV.verifyAttestation(bundles[0], opts);
    return { result: MV.pyDumps(result, { indent: 2 }) };
  } catch (e) {
    return { raised: e.name, message: e.message };
  }
}

const differences = [];
let answered = 0;
for (const [i, v] of doc.vectors.entries()) {
  const got = await answer(v);
  answered += 1;
  const want = v.answer;
  const fields = Object.keys(want).filter((k) => got[k] !== want[k]);
  if (Object.keys(got).length !== Object.keys(want).length || fields.length) {
    differences.push({ index: i, source: v.source, argv: v.argv ?? v.function, fields,
      got: Object.fromEntries(fields.map((k) => [k, String(got[k]).slice(0, 300)])),
      want: Object.fromEntries(fields.map((k) => [k, String(want[k]).slice(0, 300)])) });
  }
}
const ok = answered === doc.vectors.length && answered > 0 && !differences.length;
console.log(JSON.stringify({ vectors: doc.vectors.length, answered, differences: differences.length, first: differences.slice(0, 5) }));
process.exitCode = ok ? 0 : 1;
