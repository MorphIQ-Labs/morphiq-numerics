# Seeded streams and unit uniforms

`morphiq_numerics::random` provides integer streams specified bit for bit, and
exact maps from a 64-bit word to a uniform binary64. A seed produces the same
sequence on every target and in any implementation of the same specification,
in any language.

## Sources

- G. L. Steele, D. Lea, C. H. Flood, "Fast splittable pseudorandom number
  generators", OOPSLA 2014: Figure 16 (`nextSeed`, `mix64variant13`,
  `GOLDEN_GAMMA`) and Figure 17 (`nextDouble`).
- D. Blackman, S. Vigna, "Scrambled linear pseudorandom number generators",
  *ACM TOMS* 47(4), 2021 (arXiv:1805.01407v3): Figure 4 (the xoshiro256 engine
  and its scramblers), Table 2 (`A = 17`, `B = 45`), Table 3 (`R = 23` for `++`),
  and §5 (seeding through SplitMix).

## `SplitMix64`

**Specification.**
- **State:** one 64-bit word, the seed.
- **Step:** each call adds `GOLDEN_GAMMA = 0x9e3779b97f4a7c15` modulo `2^64`,
  the Weyl step `nextSeed` of Figure 16.
- **Output:** the new state mixed by Stafford's Mix13, Figure 16's
  `mix64variant13`:
  1. `z ← (z ⊕ (z ≫ 30)) · 0xbf58476d1ce4e5b9`
  2. `z ← (z ⊕ (z ≫ 27)) · 0x94d049bb133111eb`
  3. return `z ⊕ (z ≫ 31)`

  All arithmetic is modulo `2^64`.

**The variant.** The paper's own `SplittableRandom.nextLong` mixes with its
`mix64` (the MurmurHash3 finalizer) and uses Mix13 only inside `mixGamma`. This
crate pairs the Weyl sequence with Mix13 for output. That is the generator
commonly called SplitMix64, and the variant used to seed xoshiro, so streams
pinned against it elsewhere reproduce. Every operation is from Figure 16; the
pairing is this crate's specification, chosen for that compatibility.

## `Xoshiro256PlusPlus`

**Specification.** The state is four 64-bit words, not all zero. Each call
returns the `++` scrambler of the current state, then advances the linear
engine (Figure 4, with `A = 17`, `B = 45`, `R = 23`; all arithmetic modulo `2^64`):

```text
result ← rotl(s0 + s3, 23) + s0
t ← s1 ≪ 17
s2 ← s2 ⊕ s0;  s3 ← s3 ⊕ s1;  s1 ← s1 ⊕ s2;  s0 ← s0 ⊕ s3
s2 ← s2 ⊕ t;   s3 ← rotl(s3, 45)
```

**Seeding.** `new(seed)` fills the state with four consecutive words of
`SplitMix64::new(seed)`, as §5 recommends for a 64-bit seed. The state can't be
all zero: four consecutive Weyl terms are distinct, and Mix13 is a bijection
(each line is an invertible xorshift or a multiplication by an odd constant), so
at most one of the four words is zero. `from_state` takes any nonzero state.

### Jumps

The engine is linear over GF(2) on its 256-bit state: one step is `s ↦ M s` for a
fixed matrix `M`. Let `p` be `M`'s characteristic polynomial. Cayley–Hamilton gives
`p(M) = 0`, so `M^k = J(M)` with `J = x^k mod p`, and `J(M) s = Σ_{j_i = 1} M^i s`.
`jump` and `long_jump` evaluate that sum: they step the engine through
`M^0 s, …, M^255 s` and XOR together the states whose coefficient is set.

- `jump` is `k = 2^128`. It divides the `2^256 − 1` period into `2^128`
  non-overlapping subsequences of length `2^128`, for parallel streams.
- `long_jump` is `k = 2^192`, for a second level of `2^64` blocks.

**The polynomials are generated** by `generators/xoshiro256_jump.py`, from the
engine alone:
1. Run the engine from a unit state and take its lowest output bit for 512 steps.
2. Berlekamp–Massey gives that sequence's minimal polynomial. The paper states
   the period is `2^256 − 1`, so `p` is primitive and every nonzero linear
   functional has minimal polynomial `p`; the script checks the degree is 256.
3. `x^(2^128)` and `x^(2^192)` are reduced modulo `p` by repeated squaring.

It prints the coefficient words `random.rs` embeds and writes them to
`crates/reference/fixtures/xoshiro256_jump.json`.

## Unit uniforms

| Function | Interval | Map | Source |
|---|---|---|---|
| `unit_closed_open(w)` | `[0, 1)` | `k · 2^−53`, `k = w ≫ 11` (the top 53 bits) | Figure 17, `nextDouble` |
| `unit_open(w)` | `(0, 1)` | `(2m + 1) · 2^−53`, `m = w ≫ 12` (the top 52 bits) | this crate's specification |

Both are exact: `k < 2^53` and `2m + 1 < 2^53` are integers binary64 represents,
and the scaling by `2^−53` is exact.

`unit_open`'s values are the odd multiples of `2^−53`. They never reach 0 or 1,
and they are symmetric: the complemented word gives exactly `1 − u`. The map
`(m + ½)·2^−53` from 53 bits would need 54 significant bits and so would round.
That is why the open map uses 52.

## Checked by

- **Streams:** both reproduce, word for word, the first 64 outputs from six seeds
  (including 0, `2^64 − 1` and `GOLDEN_GAMMA`). The fixture comes from
  `generators/random_streams_reference.py`, a separate Python implementation of
  the same definitions in unbounded integers masked to 64 bits.
- **Jumps:**
  - the test builds `M` column by column, as the engine's image of each unit
    state, and checks it reproduces one step on random states;
  - it then raises `M` to `2^128` and `2^192` by repeated squaring and checks that
    `jump` and `long_jump` produce `M^(2^128) s` and `M^(2^192) s`;
  - separately, it evaluates the generated polynomials, `J(M) s` as the xor of
    the states `M^i s` whose coefficient is set, and checks the jumps match them.
    So the embedded constants are the generator's.
- **Generator replay:** `scripts/check_generators.sh` (the `check / generators`
  CI job) reruns every generator with `--check`, and requires each committed
  fixture to match a fresh generation byte for byte.

  That verifies the generated polynomials independently of the generator.
- **Seeding:** never the all-zero state over 10,002 seeds; `from_state` refuses
  zero.
- **Uniforms:** exact at both ends and at `½`; `unit_open` is symmetric and never
  0 or 1 over 100,000 words.
