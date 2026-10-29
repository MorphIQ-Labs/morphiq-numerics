"""Deterministic binary64 workloads; no previous measurement is an input."""
import struct


def bits(x):
    return struct.pack('>d', float(x)).hex()


def value(word):
    return struct.unpack('>d', bytes.fromhex(word))[0]


def active(primitive, x):
    if primitive == 'exp':
        return abs(x) < 704
    if primitive == 'erfcx':
        return -.5 <= x < 16 and abs(x) >= 2**-33
    return 2**-33 <= abs(x) <= 8


def ordinary_packets():
    # Same operation order as crates/reference/src/bin/bench-fast-primitives.rs.
    return {name: [lo + (hi-lo)*i/51.0 for i in range(52)]
            for name, lo, hi in [('exp', -.2, .2), ('erfcx', 0., 6.), ('cdf', -3., 3.)]}
