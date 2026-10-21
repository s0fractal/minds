// Line-oriented host for a step-metered rules module (meter.py). The first stdin line is the metered module in hex;
// each later line is `<budget> <hex input>`, answered by one stdout line: the hex output, E<code> (a refusal), X (the
// budget of steps was exhausted) or T (a trap: a defect of the module).
//
// The module is compiled once and every run gets a fresh instance: an exhausted or trapping run stops mid-function and
// leaves the instance's state (its stack pointer, its memory) as it was there, so a reused instance would make a result
// depend on the runs before it.
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
