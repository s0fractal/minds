// Wall time of one module over every input (experiment 6a, measure.py): argv = module file, inputs file (u32 count,
// then u32 length + bytes each, little-endian), passes, "metered" or "plain". The module is compiled once; every run
// gets a fresh instance, as the hosts do. Prints {"passes_ns": [...], "outputs": n, "refusals": n}.
import { readFileSync } from "node:fs";

const [file, inputsFile, passes, mode] = process.argv.slice(2);
const module = await WebAssembly.compile(readFileSync(file));
const buf = readFileSync(inputsFile);
const inputs = [];
for (let i = 4, k = 0; k < buf.readUInt32LE(0); k++) {
  const n = buf.readUInt32LE(i);
  inputs.push(buf.subarray(i + 4, i + 4 + n));
  i += 4 + n;
}
const times = [];
let outputs = 0;
let refusals = 0;
for (let p = 0; p < Number(passes); p++) {
  outputs = refusals = 0;
  const t0 = process.hrtime.bigint();
  for (const input of inputs) {
    const { exports } = new WebAssembly.Instance(module, {});
    if (mode === "metered") {
      exports.minds_exhausted.value = 0;
      exports.minds_fuel.value = 1n << 30n;
    }
    exports.reset();
    const ptr = exports.alloc(input.length);
    new Uint8Array(exports.memory.buffer, ptr, input.length).set(input);
    const out = exports.run(ptr, input.length);
    if (out < 0) {
      refusals++;
      continue;
    }
    const n = new DataView(exports.memory.buffer).getUint32(out, true);
    Buffer.from(new Uint8Array(exports.memory.buffer, out + 4, n));
    outputs++;
  }
  times.push(Number(process.hrtime.bigint() - t0));
}
process.stdout.write(JSON.stringify({ passes_ns: times, outputs, refusals }) + "\n");
