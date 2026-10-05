#!/usr/bin/env python3
"""Reference outputs for the seeded streams, from the papers' definitions.

An implementation separate from the Rust crate, in arbitrary-precision Python
integers masked to 64 bits:
- SplitMix64: Steele, Lea and Flood, OOPSLA 2014, Figure 16 (the Weyl step with
  GOLDEN_GAMMA and the mix64variant13 mixer), as the crate specifies it.
- xoshiro256++: Blackman and Vigna, ACM TOMS 47(4), 2021 (arXiv:1805.01407v3),
  Figure 4 with A = 17, B = 45 and R = 23, seeded with four SplitMix64 words.

Writes crates/reference/fixtures/random_streams.json; with --check, fails if the
committed fixture differs from a fresh generation.
"""
import json
import pathlib
import sys

MASK = (1 << 64) - 1
GOLDEN_GAMMA = 0x9E3779B97F4A7C15
OUTPUT = pathlib.Path(__file__).resolve().parents[1] / 'crates/reference/fixtures/random_streams.json'
SEEDS = [0, 1, 42, 0x9E3779B97F4A7C15, MASK, 0x0123456789ABCDEF]


def splitmix64(seed):
    state = seed
    while True:
        state = (state + GOLDEN_GAMMA) & MASK
        z = state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK
        yield z ^ (z >> 31)


def rotl(x, k):
    return ((x << k) | (x >> (64 - k))) & MASK


def xoshiro256pp(seed):
    words = splitmix64(seed)
    s = [next(words) for _ in range(4)]
    while True:
        result = (rotl((s[0] + s[3]) & MASK, 23) + s[0]) & MASK
        t = (s[1] << 17) & MASK
        s[2] ^= s[0]
        s[3] ^= s[1]
        s[1] ^= s[2]
        s[0] ^= s[3]
        s[2] ^= t
        s[3] = rotl(s[3], 45)
        yield result


def take(stream, n):
    return [f'{next(stream):016x}' for _ in range(n)]


def document():
    return {
        'generator': 'generators/random_streams_reference.py',
        'sources': ['Steele, Lea and Flood, OOPSLA 2014, Figure 16',
                    'Blackman and Vigna, ACM TOMS 47(4), 2021, Figure 4, Tables 2 and 3'],
        'splitmix64': {f'{seed:016x}': take(splitmix64(seed), 64) for seed in SEEDS},
        'xoshiro256pp': {f'{seed:016x}': take(xoshiro256pp(seed), 64) for seed in SEEDS},
    }


def main():
    data = json.dumps(document(), indent=1) + '\n'
    if '--check' in sys.argv[1:]:
        if OUTPUT.read_text() != data:
            sys.exit(f'{OUTPUT} differs from a fresh generation')
        return
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(data)


if __name__ == '__main__':
    main()
