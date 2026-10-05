"""Shared by the function reference generators: a rigorous correctly rounded
oracle for binary64, built on mpmath's interval arithmetic.

`correctly_rounded(f, x)` evaluates the interval function f on the exact
binary64 x, doubling the precision from 128 bits until both ends of the
enclosure round to the same binary64 number, which is then the correctly
rounded value (to nearest, ties to even; subnormals rounded once; overflow to
infinity). Rounding is done in integer arithmetic on the endpoints' exact
(sign, mantissa, exponent) tuples, so no value depends on a tolerance.
"""
import math
import struct
import sys

import mpmath
from mpmath import iv

MASK = (1 << 64) - 1
GOLDEN_GAMMA = 0x9E3779B97F4A7C15


def to_bits(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def from_bits(b):
    return struct.unpack('<d', struct.pack('<Q', b))[0]


def round_binary64(man, exp):
    """man * 2^exp, man > 0, rounded to nearest-even binary64."""
    e = man.bit_length() - 1 + exp
    if e < -1076:
        # Below 2^-1076, under half the least subnormal: rounds to +0.
        return 0.0
    q = max(e - 52, -1074)
    shift = q - exp
    if shift <= 0:
        m = man << -shift
    else:
        m, rem = man >> shift, man & ((1 << shift) - 1)
        half = 1 << (shift - 1)
        if rem > half or (rem == half and m & 1):
            m += 1
    if m.bit_length() + q > 1024:
        return math.inf
    return math.ldexp(m, q)


def round_endpoint(raw):
    """An interval endpoint, mpmath's raw (sign, man, exp, bc) tuple, which is
    exact, rounded to nearest-even binary64. (Converting an endpoint to an mpf
    would round it to the global context's precision.)"""
    sign, man, exp, _ = raw
    if man == 0:
        return 0.0
    value = round_binary64(int(man), int(exp))
    return -value if sign else value


def correctly_rounded(f, x, start=128, limit=1 << 15):
    """f (an mpmath interval function) at the binary64 x, correctly rounded."""
    prec = start
    while True:
        iv.prec = prec
        y = f(iv.mpf(x))
        lo, hi = (round_endpoint(end) for end in y._mpi_)
        if to_bits(lo) == to_bits(hi):
            return lo
        prec *= 2
        if prec > limit:
            sys.exit(f'f({x!r}) did not settle by {limit} bits')


def binary_digits(v, count):
    """The first `count` significant binary digits of |v|, a nonzero mpf, and
    the exponent of the leading one, computed with 4 * count bits."""
    with mpmath.workprec(4 * count + 64):
        v = abs(v)
        e = int(mpmath.floor(mpmath.log(v, 2)))
        scaled = v / mpmath.mpf(2) ** e
        while scaled >= 2:
            scaled, e = scaled / 2, e + 1
        while scaled < 1:
            scaled, e = scaled * 2, e - 1
        digits = int(mpmath.floor(scaled * mpmath.mpf(2) ** (count - 1)))
    return format(digits, 'b'), e


def from_binary(sign, digits, exp2):
    """sign * (digits read as a binary fraction) * 2^exp2, exactly a binary64."""
    whole, frac = digits.split('.')
    man = int(whole + frac, 2)
    x = math.ldexp(man, exp2 - len(frac))
    assert x * 2.0 ** (len(frac) - exp2) == man, 'not exactly representable'
    return -x if sign < 0 else x


def check_worst_case(f, sign, digits, exp2, image, after, label):
    """A published worst case: f(x) must have exactly the stated digits, the
    53 significant bits `image` then the bits `after`, so a mistyped input fails.
    Returns x."""
    x = from_binary(sign, digits, exp2)
    expected = image.replace('-', '').replace('.', '') + after
    with mpmath.workprec(4 * len(expected) + 64):
        got, _ = binary_digits(f(mpmath.mpf(x)), len(expected))
    if got != expected:
        sys.exit(f'{label} {digits} x 2^{exp2}: f(x) has digits\n{got}\nnot\n{expected}')
    return x


def bisect(lo, hi, predicate):
    """For encodings lo < hi with predicate false at lo and true at hi, the
    first encoding where it is true."""
    assert not predicate(lo) and predicate(hi)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if predicate(mid):
            hi = mid
        else:
            lo = mid
    return hi


def splitmix64(seed):
    """Steele, Lea and Flood, OOPSLA 2014, Figure 16."""
    state = seed
    while True:
        state = (state + GOLDEN_GAMMA) & MASK
        z = state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK
        yield z ^ (z >> 31)
