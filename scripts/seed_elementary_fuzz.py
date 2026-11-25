#!/usr/bin/env python3
"""Encode versioned fixture INPUTS and IEEE boundaries as libFuzzer seeds.

No expected values are imported: MPFR independently computes the oracle.
Output is disposable; preserve minimized failures under fuzz/regressions/.
"""
import argparse
import hashlib
import json
from pathlib import Path
import struct

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / "crates/reference/fixtures"
SOURCES = [
    ("exp", "cases"), ("exp2", "cases"), ("expm1", "cases"),
    ("ln", "ln"), ("ln", "ln_1p"),
    ("log2_log10", "log2"), ("log2_log10", "log10"),
    ("sin_cos", "cases"), ("sin_cos", "cases"), ("tan", "cases"),
    (None, None), ("asin", "asin"), ("asinh", "asinh"), ("atan2", "atan2"),
]


def boundary_pairs():
    # Both signs, signed/payload NaNs, zero, subnormal/normal boundaries,
    # binade edges, maximum finite, infinity. Integer bit operations only.
    positive = [0, 1, 2, 3, 0x000FFFFFFFFFFFFF, 0x0010000000000000,
                0x7FEFFFFFFFFFFFFF, 0x7FF0000000000000,
                0x7FF8000000000000, 0x7FF0000000000001, 0x7FFABCDE12345678]
    for exponent in range(1, 2047):
        positive.extend([(exponent << 52) - 1, exponent << 52, (exponent << 52) + 1])
    return [(b | sign, 0x3FF0000000000000)
                  for b in positive for sign in [0, 1 << 63]]


def seeds():
    boundaries = boundary_pairs()
    for op, (name, key) in enumerate(SOURCES):
        pairs = list(boundaries)
        if name is not None:
            rows = json.loads((FIXTURES / f"{name}.json").read_text())[key]
            pairs.extend((int(r["y"], 16), int(r["x"], 16)) if op == 13
                         else (int(r["x"], 16), 0) for r in rows)
        # Tiny/subnormal atan2 ratios, both argument orders and all signs.
        if op == 13:
            for a in [1, 2, 3, 0x0010000000000000, 0x3FF0000000000000]:
                for b in [0, 1, 0x4000000000000000, 0x7FEFFFFFFFFFFFFF, 0x7FF0000000000000]:
                    for sa in [0, 1 << 63]:
                        for sb in [0, 1 << 63]:
                            pairs.extend([(a | sa, b | sb), (b | sb, a | sa)])
        pairs = list(dict.fromkeys(pairs))
        # Explicit empty and short slices include remainders on each backend.
        yield bytes([op])
        for count in range(1, 16):
            yield bytes([op]) + b"".join(struct.pack("<QQ", *p) for p in pairs[:count])
        for start in range(0, len(pairs), 16):
            yield bytes([op]) + b"".join(struct.pack("<QQ", *p) for p in pairs[start:start + 16])


def fast_seeds():
    def encode(op, words):
        return bytes([op]) + b"".join(struct.pack("<QQ", b, 0) for b in words)

    # Exact bits of 704 and one, their neighbors, both signs, and exceptions.
    boundary = [0, 1 << 63, 1, 0x0010000000000000,
                0x7FEFFFFFFFFFFFFF, 0x7FF0000000000000,
                0xFFF0000000000000, 0x7FF0000000000001, 0xFFFABCDE12345678]
    for center in [0x4086000000000000, 0x3FF0000000000000]:
        boundary.extend((center + delta) | sign
                        for delta in [-1, 0, 1] for sign in [0, 1 << 63])
    common = [a for a, _ in boundary_pairs()]
    fast_rows = json.loads((FIXTURES / "fast.json").read_text())["cases"]
    ln_rows = json.loads((FIXTURES / "fast_ln.json").read_text())["cases"]
    for op in range(3):
        name, key = ("ln", "ln") if op == 2 else ("exp", "cases")
        rows = json.loads((FIXTURES / f"{name}.json").read_text())[key]
        inputs = common + boundary + [int(row["x"], 16) for row in rows]
        inputs += [int(row["x"], 16) for row in ln_rows] if op == 2 else [
            int(row["x"], 16) for row in fast_rows
            if row["primitive"] in ("exp", "exp_coarse")]
        inputs = list(dict.fromkeys(inputs))
        yield encode(op, [])
        # All-regular packets and mixed packets, including fallback boundaries
        # and NaN payloads, at every length through the 64+1 remainder.
        regular = [0x3FE0000000000000, 0x3FF0000000000001,
                   0x4000000000000000, 0x4085FFFFFFFFFFFF]
        for count in range(1, 66):
            yield encode(op, [regular[i % len(regular)] for i in range(count)])
            yield encode(op, [boundary[(i + count) % len(boundary)] for i in range(count)])
        for start in range(0, len(inputs), 65):
            yield encode(op, inputs[start:start + 65])


def fast_normal_seeds():
    def encode(op, words):
        return bytes([op]) + b"".join(struct.pack("<QQ", word, 0) for word in words)

    # Public screens and Gaussian branch regions, including adjacent encodings.
    boundary = [0, 1 << 63, 1, 0x7FEFFFFFFFFFFFFF, 0x7FF0000000000000,
                0xFFF0000000000000, 0x7FF0000000000001, 0xFFFABCDE12345678]
    for value in [2**-33, 0.5, 0.663, 8.0, 16.0, 22.5]:
        center = struct.unpack("<Q", struct.pack("<d", value))[0]
        boundary.extend((center + delta) | sign
                        for delta in [-1, 0, 1] for sign in [0, 1 << 63])
    common = [a for a, _ in boundary_pairs()]
    rows = json.loads((FIXTURES / "fast.json").read_text())["cases"]
    log_rows = json.loads((FIXTURES / "fast_log_cdf.json").read_text())["cases"]
    regular = [struct.unpack("<Q", struct.pack("<d", x))[0]
               for x in [-0.5, -0.25, 0.25, 1.0, 7.0]]
    for op, primitive in enumerate(["erfcx", "cdf", "log_cdf"]):
        inputs = common + boundary + [int(row["x"], 16) for row in rows
                                      if row["primitive"] == primitive]
        if op == 2:
            inputs += [int(row["x"], 16) for row in log_rows]
        inputs = list(dict.fromkeys(inputs))
        yield encode(op, [])
        for count in range(1, 66):
            yield encode(op, [regular[i % len(regular)] for i in range(count)])
            yield encode(op, [boundary[(i + count) % len(boundary)] for i in range(count)])
        for start in range(0, len(inputs), 65):
            yield encode(op, inputs[start:start + 65])


def strong_normal_seeds():
    def encode(op, words):
        return bytes([op]) + b"".join(struct.pack("<QQ", word, 0) for word in words)

    # Contract thresholds from docs/normal.md and docs/erfcx.md, plus oracle
    # formula joins. Inputs only; neither expected values nor runtime tables.
    centers = [0x3FE0000000000000, 0x4020000000000000, 0x4030000000000000,
               0x403AA0F4D2E063CF, 0x4040000000000000, 0x4044000000000000,
               0x4050000000000000, 0x402095B059D67C4D, 0x40433E21DC3F3BD8,
               0x5FF6A09E667F3BCD, 0x7FC20DD750429B6E,
               0x3C9C5BF891B4EF69, 0x3C8C5BF891B4EF6B]
    boundary = [0, 1 << 63, 1, 0x7FEFFFFFFFFFFFFF, 0x7FF0000000000000,
                0xFFF0000000000000, 0x7FF0000000000001, 0xFFFABCDE12345678]
    boundary += [(center + delta) | sign for center in centers
                 for delta in range(-3, 4) for sign in [0, 1 << 63]]
    common = [a for a, _ in boundary_pairs()]
    for op in range(3):
        name = "erfcx" if op == 0 else "normal"
        rows = json.loads((FIXTURES / f"{name}.json").read_text())["cases"]
        inputs = list(dict.fromkeys(common + boundary + [int(row["x"], 16) for row in rows]))
        yield encode(op, [])
        regular = [struct.unpack("<Q", struct.pack("<d", x))[0]
                   for x in [-26.0, -8.0, -0.5, 0.25, 1.0, 16.0, 64.0]]
        for count in range(1, 66):
            yield encode(op, [regular[i % len(regular)] for i in range(count)])
            yield encode(op, [boundary[(i + count) % len(boundary)] for i in range(count)])
        for start in range(0, len(inputs), 65):
            yield encode(op, inputs[start:start + 65])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    targets = {"elementary": seeds, "fast_elementary": fast_seeds,
               "fast_normal": fast_normal_seeds, "strong_normal": strong_normal_seeds}
    parser.add_argument("--target", choices=targets, default="elementary")
    args = parser.parse_args()
    args.directory.mkdir(parents=True, exist_ok=True)
    count = 0
    for data in targets[args.target]():
        (args.directory / hashlib.sha256(data).hexdigest()).write_bytes(data)
        count += 1
    print(f"wrote {count} deterministic {args.target} seeds to {args.directory}")


if __name__ == "__main__":
    main()
