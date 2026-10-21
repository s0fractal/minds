"""Step metering for rules modules (VARS-1-SPEC.md §4.3, AMENDMENTS.md): a budget in steps, not in time.

A **step** is an entry into a function body or into a `loop` body (every iteration enters it again). Steps are a
property of the module's code and its input, so every host counts the same number, whatever its engine or speed.

`metered(module)` rewrites a rules module so that it counts its own steps: it appends two exported mutable globals,
`minds_fuel` (i64, the steps left) and `minds_exhausted` (i32), and at every step it traps after setting
`minds_exhausted` to 1 when no step is left, else takes one. The rewrite inserts only stack-neutral code at the start of
each function body and each loop body; every other byte of the code is copied. It decodes the instruction set the
rules modules use (MVP, sign extension, saturating conversions, bulk memory, multi-value blocks) and refuses any other
opcode rather than guess an immediate's length.
"""
from __future__ import annotations

from typing import List, Tuple


class MeterError(ValueError):
    """The module uses a construct this rewriter does not decode."""


def _uleb(b: bytes, i: int) -> Tuple[int, int]:
    n = s = 0
    while True:
        if i >= len(b):
            raise MeterError("truncated LEB128")
        x = b[i]
        i += 1
        n |= (x & 0x7F) << s
        s += 7
        if x < 0x80:
            return n, i


def _sleb_skip(b: bytes, i: int) -> int:
    while True:
        if i >= len(b):
            raise MeterError("truncated LEB128")
        x = b[i]
        i += 1
        if x < 0x80:
            return i


def _enc_uleb(n: int) -> bytes:
    out = bytearray()
    while True:
        x = n & 0x7F
        n >>= 7
        out.append(x | (0x80 if n else 0))
        if not n:
            return bytes(out)


def _sections(b: bytes) -> List[Tuple[int, bytes]]:
    if b[:8] != b"\x00asm\x01\x00\x00\x00":
        raise MeterError("not a wasm 1 module")
    out, i = [], 8
    while i < len(b):
        sid = b[i]
        n, i = _uleb(b, i + 1)
        out.append((sid, b[i:i + n]))
        i += n
    if i != len(b):
        raise MeterError("truncated section")
    return out


# Opcodes with no immediate: control without labels, parametric, numeric (0x45-0xC4).
_PLAIN = {0x00, 0x01, 0x05, 0x0B, 0x0F, 0x1A, 0x1B} | set(range(0x45, 0xC5))
_ONE_U32 = {0x0C, 0x0D, 0x10, 0x20, 0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0xD2}  # br br_if call local.* global.* table.get/set ref.func
_MEMARG = set(range(0x28, 0x3F))  # loads and stores: align, offset


def _blocktype(b: bytes, i: int) -> int:
    if b[i] == 0x40 or b[i] in (0x7F, 0x7E, 0x7D, 0x7C, 0x7B, 0x70, 0x6F):
        return i + 1
    return _sleb_skip(b, i)  # a type index, s33


def _step(fuel: int, flag: int) -> bytes:
    """`if fuel == 0 { exhausted = 1; unreachable } fuel -= 1`, stack-neutral."""
    g = lambda op, ix: bytes([op]) + _enc_uleb(ix)  # noqa: E731
    return (g(0x23, fuel) + b"\x50\x04\x40" + b"\x41\x01" + g(0x24, flag) + b"\x00\x0b"
            + g(0x23, fuel) + b"\x42\x01\x7d" + g(0x24, fuel))


def _instrument_body(body: bytes, step: bytes) -> bytes:
    n, i = _uleb(body, 0)  # local declarations
    for _ in range(n):
        _, i = _uleb(body, i)
        i += 1
    out = bytearray(body[:i]) + step
    depth = 1
    while i < len(body):
        op = body[i]
        start = i
        i += 1
        if op in (0x02, 0x03, 0x04):  # block loop if
            i = _blocktype(body, i)
            depth += 1
            out += body[start:i]
            if op == 0x03:
                out += step
            continue
        if op == 0x0B:
            depth -= 1
        elif op in _PLAIN:
            pass
        elif op in _ONE_U32:
            _, i = _uleb(body, i)
        elif op == 0x0E:  # br_table
            k, i = _uleb(body, i)
            for _ in range(k + 1):
                _, i = _uleb(body, i)
        elif op == 0x11:  # call_indirect
            _, i = _uleb(body, i)
            _, i = _uleb(body, i)
        elif op == 0x1C:  # select t*
            k, i = _uleb(body, i)
            i += k
        elif op in _MEMARG:
            _, i = _uleb(body, i)
            _, i = _uleb(body, i)
        elif op in (0x3F, 0x40):  # memory.size memory.grow
            _, i = _uleb(body, i)
        elif op in (0x41, 0x42):  # i32.const i64.const
            i = _sleb_skip(body, i)
        elif op == 0x43:
            i += 4
        elif op == 0x44:
            i += 8
        elif op == 0xD0:  # ref.null t
            i += 1
        elif op == 0xD1:  # ref.is_null
            pass
        elif op == 0xFC:
            sub, i = _uleb(body, i)
            if sub <= 7:
                pass
            elif sub in (8, 10, 12, 14):
                _, i = _uleb(body, i)
                _, i = _uleb(body, i)
            elif sub in (9, 11, 13, 15, 16, 17):
                _, i = _uleb(body, i)
            else:
                raise MeterError(f"unknown 0xFC opcode {sub}")
        else:
            raise MeterError(f"unknown opcode 0x{op:02x}")
        out += body[start:i]
    if depth != 0 or i != len(body):
        raise MeterError("unbalanced function body")
    return bytes(out)


def metered(module: bytes) -> bytes:
    """The module with step metering (module docstring). Its other behaviour is the original's."""
    secs = _sections(module)
    ids = [s for s, _ in secs if s != 0]
    if 6 not in ids or 7 not in ids or 10 not in ids:
        raise MeterError("a rules module has a global, an export and a code section")
    if 2 in ids:
        raise MeterError("a rules module imports nothing")
    out = bytearray(module[:8])
    fuel = flag = None
    for sid, body in secs:
        if sid == 6:
            n, i = _uleb(body, 0)
            fuel, flag = n, n + 1
            body = (_enc_uleb(n + 2) + body[i:] + b"\x7e\x01\x42\x00\x0b" + b"\x7f\x01\x41\x00\x0b")
        elif sid == 7:
            n, i = _uleb(body, 0)
            body = (_enc_uleb(n + 2) + body[i:] + _enc_uleb(10) + b"minds_fuel" + b"\x03" + _enc_uleb(fuel)
                    + _enc_uleb(15) + b"minds_exhausted" + b"\x03" + _enc_uleb(flag))
        elif sid == 10:
            step = _step(fuel, flag)
            n, i = _uleb(body, 0)
            funcs = bytearray(_enc_uleb(n))
            for _ in range(n):
                size, i = _uleb(body, i)
                f = _instrument_body(body[i:i + size], step)
                funcs += _enc_uleb(len(f)) + f
                i += size
            if i != len(body):
                raise MeterError("trailing bytes in the code section")
            body = bytes(funcs)
        out += bytes([sid]) + _enc_uleb(len(body)) + body
    return bytes(out)
