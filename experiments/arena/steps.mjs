// Steps a metered rules module spends on each input (meter.py's fuel): the first stdin line is the metered module in
// hex; each later line is a hex input, answered by `<steps> <hex output | E<code> | X | T>`. A fresh instance per run,
// as kernel/run_metered.mjs does, under a budget of 2^40 steps.
import { createInterface } from "node:readline";

const BUDGET = 1n << 40n;
let module;
for await (const line of createInterface({ input: process.stdin })) {
  if (module === undefined) {
    module = await WebAssembly.compile(Buffer.from(line.trim(), "hex"));
    continue;
  }
  const { memory, reset, alloc, run, minds_fuel, minds_exhausted } = (await WebAssembly.instantiate(module, {})).exports;
  const input = Buffer.from(line.trim(), "hex");
  minds_exhausted.value = 0;
  minds_fuel.value = BUDGET;
  let out;
  try {
    reset();
    const ptr = alloc(input.length);
    new Uint8Array(memory.buffer, ptr, input.length).set(input);
    out = run(ptr, input.length);
  } catch (e) {
    if (!(e instanceof WebAssembly.RuntimeError)) throw e;
    process.stdout.write(`${BUDGET - minds_fuel.value} ${minds_exhausted.value === 1 ? "X" : "T"}\n`);
    continue;
  }
  const steps = BUDGET - minds_fuel.value;
  if (out < 0) {
    process.stdout.write(`${steps} E${out}\n`);
    continue;
  }
  const n = new DataView(memory.buffer).getUint32(out, true);
  process.stdout.write(`${steps} ${Buffer.from(new Uint8Array(memory.buffer, out + 4, n)).toString("hex")}\n`);
}
