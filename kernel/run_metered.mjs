// Line-oriented host for a step-metered rules module (meter.py). The first stdin line is the metered module in hex;
// each later line is `<budget> <hex input>`, answered by one stdout line: the hex output, E<code> (a refusal), X (the
// budget of steps was exhausted) or T (a trap: a defect of the module).
import { createInterface } from "node:readline";

let exports;
for await (const line of createInterface({ input: process.stdin })) {
  if (exports === undefined) {
    exports = (await WebAssembly.instantiate(Buffer.from(line.trim(), "hex"), {})).instance.exports;
    continue;
  }
  const { memory, reset, alloc, run, minds_fuel, minds_exhausted } = exports;
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
    process.stdout.write(minds_exhausted.value === 1 ? "X\n" : "T\n");
    continue;
  }
  if (out < 0) {
    process.stdout.write(`E${out}\n`);
    continue;
  }
  const n = new DataView(memory.buffer).getUint32(out, true);
  process.stdout.write(Buffer.from(new Uint8Array(memory.buffer, out + 4, n)).toString("hex") + "\n");
}
