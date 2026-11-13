// Line host for a step-metered rules module (meter.py), as kernel/run_metered.mjs with the steps spent: the first
// stdin line is the metered module in hex; each later line is `<budget> <hex input>`, answered by one stdout line
// `<steps> <result>`, the result being the hex output, E<code> (a refusal), X (the budget ran out) or T (a trap).
// A fresh instance per run, as kernel/run_metered.mjs gives one.
import { createInterface } from "node:readline";

let module;
for await (const line of createInterface({ input: process.stdin })) {
  if (module === undefined) {
    module = await WebAssembly.compile(Buffer.from(line.trim(), "hex"));
    continue;
  }
  const { memory, reset, alloc, run, minds_fuel, minds_exhausted } = (await WebAssembly.instantiate(module, {})).exports;
  const [budget, hex] = line.trim().split(" ");
  const input = Buffer.from(hex ?? "", "hex");
  minds_exhausted.value = 0;
  minds_fuel.value = BigInt(budget);
  let out;
  try {
    reset();
    const ptr = alloc(input.length);
    new Uint8Array(memory.buffer, ptr, input.length).set(input);
    out = run(ptr, input.length);
  } catch (e) {
    if (!(e instanceof WebAssembly.RuntimeError)) throw e;
    process.stdout.write(`${BigInt(budget) - minds_fuel.value} ${minds_exhausted.value === 1 ? "X" : "T"}\n`);
    continue;
  }
  const steps = BigInt(budget) - minds_fuel.value;
  if (out < 0) {
    process.stdout.write(`${steps} E${out}\n`);
    continue;
  }
  const n = new DataView(memory.buffer).getUint32(out, true);
  process.stdout.write(`${steps} ${Buffer.from(new Uint8Array(memory.buffer, out + 4, n)).toString("hex")}\n`);
}
