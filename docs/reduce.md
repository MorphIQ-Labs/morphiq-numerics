# Sums, dot products and sums of squares

`morphiq_numerics::reduce` reduces slices of binary64 numbers to one number:

| Function | Computes | Order and algorithm |
|---|---|---|
| `sum(x)` | `Σ x_i` | left to right, each addition rounded |
| `sum2(x)` | `Σ x_i`, compensated | Sum2 (Ogita, Rump and Oishi, Algorithm 4.1) |
| `dot(x, y)` | `Σ x_i·y_i` | each product rounded, then summed left to right |
| `dot2(x, y)` | `Σ x_i·y_i`, compensated | Dot2 (Algorithm 5.3) |
| `sum_squares(x)` | `Σ x_i²` | `dot(x, x)` |
| `sum_squares2(x)` | `Σ x_i²`, compensated | `dot2(x, x)` |
| `max_abs(x)` | `max \|x_i\|` | left to right; exact |

**The order is part of the contract.** Every function evaluates its terms in one
fixed order, so its result is the same on every target. A vectorized or parallel
evaluation is allowed only where it reproduces these bits; none exists yet.

**The compensated variants are fully specified.** Sum2 and Dot2 are stated
operation by operation in the source, and the code follows them line for line.
Their result is as accurate as if computed in twice the working precision and
rounded once.

Notation:
- `u = 2^−53` is the unit roundoff (the paper's `eps`);
- `γ_k = k·u / (1 − k·u)`, defined for `k·u < 1`;
- `s` is the exact sum or dot product;
- `S = Σ|x_i|` for a sum and `|x|ᵀ|y| = Σ|x_i·y_i|` for a dot product.

## Source

T. Ogita, S. M. Rump, S. Oishi, "Accurate sum and dot product", *SIAM J. Sci.
Comput.* 26(6), 1955–1988, 2005, doi:10.1137/030601818. The authors' copy is at
`https://www.tuhh.de/ti3/paper/rump/OgRuOi05.pdf`, SHA-256
`56e897ffce0a843ea531769d50b8466241ae4f01094b0ddf83d8fff74255cfcc`.

| Here | There |
|---|---|
| `sum` | `π_n` of Algorithm 4.1, `fl(Σ p_i)` by (4.1); bound (2.4) |
| `sum2` | Algorithm 4.1 (equivalent to Algorithm 4.4); Proposition 4.5 |
| `dot2` | Algorithm 5.3; Proposition 5.5 |
| `dot` | `p` of Algorithm 5.3, `fl(xᵀy)`; bound derived below |

The paper's TwoSum and TwoProduct (Algorithms 3.1 and 3.3) arrange their
operations differently from this crate's `two_sum` and `two_prod`
([double-word.md](double-word.md)). Both return `fl(a ∘ b)` and the exact error,
and that pair is unique, so on the exact domains the results are bit-identical.
The proofs use only that property.

## Contracts

### `sum`

`π_1 = x_1`, then `π_i = fl(π_{i−1} + x_i)`; `sum` returns `π_n`, and `0` for an
empty slice.

**Bound** (the paper's (2.4)): `|sum − s| ≤ γ_{n−1}·S`, also with underflow, when
`n·u < 1` and no operation overflows. Every sum of two binary64 numbers rounds
with relative error at most `u`, and a subnormal sum is exact.

### `sum2`

```
π_1 = x_1;  σ_1 = 0
for i = 2..n:  [π_i, q_i] = two_sum(π_{i−1}, x_i);  σ_i = fl(σ_{i−1} + q_i)
sum2 = fl(π_n + σ_n)
```

`0` for an empty slice. As the paper states it, `σ` starts at `+0`, so
`sum2([−0]) = +0`, while `sum([−0]) = −0`.

**Bound** (Proposition 4.5): `|sum2 − s| ≤ u·|s| + γ_{n−1}²·S`, also with
underflow, when `n·u < 1` and no operation overflows. The proof needs only that
each `two_sum` is exact. `two_sum` is proved exact when both operands are at most
`2^1020` in magnitude ([double-word.md](double-word.md)). Here the operands are
the running sum and a term, so `S ≤ 2^1019` keeps every `two_sum` in its domain.

The bound says the result is as accurate as twice the working precision, then
rounded. In relative terms: `|sum2 − s| / |s| ≤ u + γ_{n−1}²·cond`, with
`cond = S / |s|` (the paper's Remark 3).

### `dot`

`p_1 = fl(x_1·y_1)`, then `p_i = fl(p_{i−1} + fl(x_i·y_i))`; `dot` returns `p_n`,
and `0` for empty slices. This is the `p` of Dot2, the ordinary floating-point
dot product.

**Bound:** `|dot − xᵀy| ≤ γ_n·|x|ᵀ|y|` when no product underflows (each `x_i·y_i`
is zero or at least `2^−1022` in magnitude), `n·u < 1`, and no operation
overflows. Derivation, from the paper's (2.2) and (2.4):
- each rounded product is `h_i = x_i·y_i·(1 + ε_i)` with `|ε_i| ≤ u`, so
  `Σ|h_i − x_i·y_i| ≤ u·|x|ᵀ|y|` and `Σ|h_i| ≤ (1 + u)·|x|ᵀ|y|`;
- `p_n = fl(Σ h_i)`, so by (2.4), `|p_n − Σ h_i| ≤ γ_{n−1}·Σ|h_i|`;
- together, `|p_n − xᵀy| ≤ (γ_{n−1}·(1 + u) + u)·|x|ᵀ|y|`, and
  `γ_{n−1} + u·(1 + γ_{n−1}) ≤ γ_n`, the paper's (4.6).

### `dot2`

```
[p, s] = two_prod(x_1, y_1)
for i = 2..n:  [h, r] = two_prod(x_i, y_i);  [p, q] = two_sum(p, h);  s = fl(s + (q + r))
dot2 = fl(p + s)
```

`0` for empty slices.

**Bound** (Proposition 5.5): `|dot2 − xᵀy| ≤ u·|xᵀy| + γ_n²·|x|ᵀ|y|` when `n·u < 1`,
no operation overflows, and every `two_prod` is exact: each product `x_i·y_i` is
zero or at least `2^−969` in magnitude, `two_prod`'s domain. In relative terms,
`u + ½·γ_n²·cond`, with `cond = 2·|x|ᵀ|y| / |xᵀy|` (Corollary 5.7).

The paper also bounds Dot2 in the presence of underflow, adding `5n·eta`. That
analysis uses its own TwoProduct's behaviour on underflowing products, which this
crate's `two_prod` doesn't share outside its domain. So it isn't claimed here.

### `sum_squares`, `sum_squares2`

`dot(x, x)` and `dot2(x, x)`, bit for bit, with the bounds above. Here
`|x|ᵀ|x| = Σ x_i²` is the exact result itself, so the bounds are relative:
- `sum_squares`: at most `γ_n`;
- `sum_squares2`: at most `u + γ_n²`.

The conditions become: each `x_i²` is zero or at least `2^−1022`
(`sum_squares`) or `2^−969` (`sum_squares2`).

### `max_abs`

The largest `|x_i|`, exactly; `0` for an empty slice. A NaN anywhere makes the
result NaN: the first NaN in slice order is returned unchanged, so the result
doesn't depend on how a comparison treats NaNs. `−0` gives `+0`.

### Non-finite inputs

An infinity or NaN among the terms propagates through IEEE 754 arithmetic. The
error bounds are statements about finite inputs whose computation doesn't
overflow.

## What is checked, and how

Not machine-checked: these bounds are the paper's propositions, and the
derivation above for `dot`. The crate's own part, that `two_sum` and `two_prod`
are exact on their domains, is machine-checked ([double-word.md](double-word.md)).

`crates/reference/tests/reduce.rs` checks every bound in exact integer
arithmetic, with the denominators of `γ` cleared:
- 2,000 slices per function, of lengths 1 to 64, half of them random and half
  constructed to cancel heavily (terms paired with their negatives a few ulps
  off), so `cond` reaches about `u^−1`;
- the paper's Table 4.1: for `p = [1, θ, θ², −θ, −θ², −1]` with `θ = 2^−54`,
  `sum` returns exactly 0 and `sum2` exactly `−θ²`, as the paper shows;
- empty slices, `−0`, mismatched lengths, and `max_abs`'s NaN rule.

**The checks can fail.** With `sum2` returning `π_n` without its correction, both
`sum2` tests fail. With `dot2` dropping the products' errors `r`, the `dot2` test
fails.

The determinism digest's `reduce` section hashes every function on slices of
every length from 0 to 32 ([determinism.md](determinism.md)).
