// Line-oriented host for the lens kernel: each stdin line is a hex input, each stdout line the hex output or E<code>.
import { readFileSync } from "node:fs";
import { createInterface } from "node:readline";

const { instance } = await WebAssembly.instantiate(readFileSync(process.argv[2]), {});
const { memory, reset, alloc, run } = instance.exports;
for await (const line of createInterface({ input: process.stdin })) {
  const input = Buffer.from(line.trim(), "hex");
  reset();
  const ptr = alloc(input.length);
  new Uint8Array(memory.buffer, ptr, input.length).set(input);
  const out = run(ptr, input.length);
  const n = input.readUInt32LE(0);
  process.stdout.write(out < 0 ? `E${out}\n` : Buffer.from(new Uint8Array(memory.buffer, out, n)).toString("hex") + "\n");
}
