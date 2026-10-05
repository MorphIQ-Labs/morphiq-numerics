# ULP utilities

`morphiq_numerics::ulp` provides the unit in the last place of a binary64 number,
and a measure of the distance between two numbers in binary64 steps. Later
functions state their error bounds and test tolerances in these units, so the
definitions are fixed here once.

## Mathematics used

- **The binary64 encoding** (IEEE 754-2019 §3.4). A finite number is encoded as
  a sign bit, an 11-bit biased exponent `E` and a 52-bit trailing significand
  `T`:
  - if `0 < E < 2047`, the value is `(−1)^s · 2^(E − 1023) · (1 + T·2^−52)`;
  - if `E = 0`, it is `(−1)^s · 2^−1022 · (T·2^−52)`, a subnormal or zero.
  - `E = 2047` encodes the infinities (`T = 0`) and the NaNs.
- **The unit in the last place,** in the sense Muller (*Elementary Functions*,
  3rd ed., 2016, ch. 2) and Boldo, Jeannerod, Melquiond and Muller ("Floating-point
  arithmetic", *Acta Numerica* 32, 2023) attribute to Goldberg: the spacing of
  the floating-point numbers in the binade that contains `x`.

## `ulp`

**Contract.**
- **Finite nonzero `x`,** with `2^e ≤ |x| < 2^(e+1)`: `ulp(x) = 2^(max(e, −1022) − 52)`.
- **Zero:** `ulp(±0) = 2^−1074`.
- **Infinity:** `ulp(±∞) = +∞`.
- **NaN:** returned unchanged.

The result is an exact power of two, so no rounding is involved.

**Derivation from the encoding.**
- **A normal binade** (`0 < E < 2047`) holds `2^52` numbers, `2^(E−1023)·(1 + T·2^−52)`
  for `T = 0, …, 2^52 − 1`. Consecutive ones differ by
  `2^(E − 1023 − 52) = 2^(E − 1075)`.
- **The subnormals** (`E = 0`) are `2^−1022·T·2^−52`, spaced by `2^−1074`. That is
  also the spacing of the smallest normal binade (`E = 1`), which is why
  `max(e, −1022)` appears.

So the result depends only on `E`, and as a binary64 encoding it is:
- **`E ≥ 53`:** `2^(E − 1075)` is normal, with biased exponent `E − 52` and a
  zero significand.
- **`1 ≤ E ≤ 52`:** `2^(E − 1075) = 2^−1074 · 2^(E − 1)` is subnormal, with the
  single significand bit `E − 1` set.
- **`E = 0`:** `2^−1074`, the encoding with only bit 0 set.

**Alternative definitions not adopted.** Harrison's ulp and Muller's
`ulp`-of-the-exact-value differ from this one only at powers of two, where they
measure the spacing below `x` rather than above. This crate's bounds are stated
for the result's own binade, which is the definition above.

**Checked by:**
- every binade's least and greatest member of both signs, against the exact
  difference `next_up(|x|) − |x|` (Sterbenz: the subtraction of two neighbours
  is exact). The largest finite magnitude uses `|x| − next_down(|x|)`, since its
  successor is `+∞`;
- 100,000 seeded random finite numbers, against the same difference;
- zero, the infinities and a NaN payload.

## `ordered_bits` and `ulps_between`

**Contract.** `ordered_bits(x)` maps binary64 onto the integers so that
consecutive numbers map to consecutive integers:
- **Zero:** `+0` and `−0` both map to `0`.
- **Positive numbers:** each maps to its encoding read as an integer. The
  smallest subnormal maps to `1`, and `+∞` to one more than the largest finite
  number.
- **Negative numbers:** each maps to the negative of its magnitude's position.
- **NaNs:** a positive NaN lands above `+∞` and a negative NaN below `−∞`, which
  orders them but doesn't measure a distance.

`ulps_between(a, b)` is `|ordered_bits(b) − ordered_bits(a)|`, or `None` if
either argument is a NaN.

**Derivation.**
- **Positive magnitudes:** for non-negative numbers, the encoding with the sign
  bit cleared is `E·2^52 + T`. That is increasing in the value, and consecutive
  numbers differ by one in it. It holds within a binade, where `T` advances,
  and across a binade boundary, where `T` wraps from `2^52 − 1` to `0` as `E`
  advances by one. It also holds from the largest subnormal to the smallest
  normal, and from the largest finite number to `+∞` (`E = 2047`, `T = 0`).
- **Negative numbers:** negating the magnitude's position extends the map
  monotonically through the negative numbers.
- **Zero:** `−0` and `+0` meet at `0`, matching their IEEE equality.

**Relation to `totalOrder`.** IEEE 754-2019 §5.10's `totalOrder` agrees with this
order except that it puts `−0` below `+0`; the two zeros are deliberately one
position here, so `ulps_between(−0, +0) = 0`.

**Checked by:**
- `ordered_bits` advances by exactly one per `next_up`, and retreats by one per
  `next_down`, at every binade edge of both signs and at both zeros;
- `+∞` and `−∞` are one step beyond the extreme finite numbers;
- the NaN positions lie outside the infinities;
- `ulps_between` is symmetric, counts across the subnormal–normal boundary, and
  refuses NaNs.
