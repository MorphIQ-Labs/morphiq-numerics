#!/usr/bin/env python3
"""Jump polynomials for the xoshiro256 linear engine.

The engine is Blackman and Vigna, "Scrambled linear pseudorandom number
generators", ACM TOMS 47(4), 2021 (arXiv:1805.01407v3), Figure 4, with A = 17
and B = 45 from Table 2. It is linear over GF(2) on its 256-bit state, so
advancing it k steps is s -> M^k s. If p is the characteristic polynomial of M,
then M^k = J(M) with J = x^k mod p, and J(M) s = sum_i j_i M^i s is computed by
stepping the engine 256 times and xoring in the states whose coefficient is set.

p is found as the minimal polynomial of one output bit's sequence, by
Berlekamp-Massey over 512 terms. The paper states the engine's period is
2^256 - 1, so p is primitive of degree 256 and every nonzero linear functional
has p as its minimal polynomial; the script checks the degree.

Prints the coefficients of x^(2^128) mod p (jump) and x^(2^192) mod p
(long_jump) as four 64-bit words each, word i holding coefficients 64i..64i+63.
Pure Python, no third-party package.
"""
import sys

MASK = (1 << 64) - 1
A, B = 17, 45


def rotl(x, k):
    return ((x << k) | (x >> (64 - k))) & MASK


def step(s):
    """Figure 4's state update, A = 17, B = 45."""
    s = list(s)
    t = (s[1] << A) & MASK
    s[2] ^= s[0]
    s[3] ^= s[1]
    s[1] ^= s[2]
    s[0] ^= s[3]
    s[2] ^= t
    s[3] = rotl(s[3], B)
    return s


def berlekamp_massey(bits):
    """Minimal connection polynomial of a GF(2) sequence, as an int bitmask."""
    c, b = 1, 1
    length, m = 0, 1
    for n, bit in enumerate(bits):
        d = bit
        for i in range(1, length + 1):
            d ^= ((c >> i) & 1) & bits[n - i]
        if d == 0:
            m += 1
        elif 2 * length <= n:
            t = c
            c ^= b << m
            length, b, m = n + 1 - length, t, 1
        else:
            c ^= b << m
            m += 1
    return c, length


def reverse(poly, degree):
    """Connection polynomial to characteristic polynomial."""
    return int(format(poly, f'0{degree + 1}b')[::-1], 2)


def mulmod(a, b, p, degree):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if (a >> degree) & 1:
            a ^= p
    return result


def x_to_two_to_the(k, p, degree):
    """x^(2^k) mod p, by k squarings."""
    r = 2  # x
    for _ in range(k):
        r = mulmod(r, r, p, degree)
    return r


def words(poly):
    return [(poly >> (64 * i)) & MASK for i in range(4)]


def main():
    s = [1, 0, 0, 0]
    bits = []
    for _ in range(512):
        bits.append(s[0] & 1)
        s = step(s)
    connection, degree = berlekamp_massey(bits)
    if degree != 256:
        sys.exit(f'minimal polynomial has degree {degree}, expected 256')
    p = reverse(connection, degree)
    for name, k in (('JUMP', 128), ('LONG_JUMP', 192)):
        print(name, ' '.join(f'0x{w:016x}' for w in words(x_to_two_to_the(k, p, degree))))


if __name__ == '__main__':
    main()
