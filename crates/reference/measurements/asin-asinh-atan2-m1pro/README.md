# `asin`, `asinh` and `atan2`: scalar loop against the batched function

Same-host timing of a loop of the scalar function against `asin_slice`,
`asinh_slice` and `atan2_slice` (paired arguments for `atan2`), by
`crates/reference/src/bin/bench-batched.rs` at commit `722bd96`:

```sh
cargo run --release --locked -p morphiq-numerics-reference --features simd,std --bin bench-batched
```

Each figure is the median over 31 rounds of the nanoseconds per element on 4,096
arguments, the loop repeated to about 10 ms per round. Three consecutive runs are
kept (`bench-batched-run1.md` to `run3.md`, the new functions' rows).

- **Host:** Apple M1 Pro, NEON (2 lanes), AC power, battery charged, 1-minute load
  average 2.4 before the first run, no other benchmark, build or container running,
  Rust 1.97.1, `--release` (2026-10-21).
- **Allocation:** none. The crate is `no_std` without `alloc`; the kernels keep
  fixed-size arrays on the stack.
- **Fallback rate** (arguments the rounding test sends to the accurate path, from
  the unit tests' sweeps of random arguments): `asin` 626 of 200,000 (1 in 320),
  `asinh` 133 of 100,000 (1 in 750), `atan2` 710 of 240,000 pairs over the four
  forms (1 in 338).

| Function | Arguments | Scalar loop (ns) | Batched, NEON (ns) | Speed-up |
|---|---|---|---|---|
| `asin` | `[−1, 1]` | 62.3 | 55.4 | 1.13× |
| `asin` | `[0.71, 1]`, the complement | 179–184 | 155–159 | 1.13–1.16× |
| `asin` | `[10^-7, 0.0078]` | 11.0 | 10.0 | 1.10× |
| `asinh` | `[10^-7, 0.0078]`, the series | 10.7 | 10.3–10.6 | 1.01–1.05× |
| `asinh` | `[2^-7, 2^28]`, log-uniform | 194–198 | 154 | 1.26–1.29× |
| `asinh` | `[2^28, 2^1018]`, log-uniform | 43–44 | 26.5 | 1.62–1.66× |
| `asinh` | `[−8, 8]` | 191 | 151–156 | 1.23–1.27× |
| `atan2` | `y, x ∈ [−1, 1]` | 40.6–41.4 | 25.2 | 1.61–1.64× |
| `atan2` | `y, x` log-uniform in `[2^-60, 2^60]` | 22.2–22.5 | 21.0–21.2 | 1.05–1.07× |

## Findings and their disposition

- **The first lane kernels were slower than the scalar loop.** `asin`'s ran at
  0.51× to 0.76× before the fix: it computed the small series, the table and the
  complement's extra operations on every chunk, and the scalar square root on every
  lane. `asin` now computes each only where some lane needs it (commit
  `perf(asin): skip unneeded work in the lane kernel`); `asinh` and `atan2` were
  written that way. The speed-ups above are after the fix.
- **The software square root dominates (before the hardware path).** These figures were taken before `exact::sqrt` and the fused `two_prod_d` replaced the integer root and Dekker's product in these kernels ([sqrt.md](../../../../docs/sqrt.md)); they have not been re-measured and the speed-ups above predate that change.
  The finding itself: The complement (`asin`, 179 ns) and the
  logarithmic region (`asinh`, 194 ns) spend most of their time in
  `crate::sqrt::sqrt`, the integer digit-by-digit square root: the crate is `no_std`
  and by design reaches no platform `sqrt` ([sqrt.md](../../../../docs/sqrt.md)). A
  hardware square root is correctly rounded and so bit-identical; `exact::sqrt` now
  uses it where the target has one, which should cut those regions several-fold in
  the scalar functions and the lanes alike. That is the expectation, not a measurement.
- **The series regions barely gain** (`asin` 1.10×, `asinh` 1.01–1.05×): the work
  is a few multiplies per element and two lanes cannot beat that by much on this
  host. A wider backend would.

## Not measured

No native x86-64 hardware (SSE2, AVX2+FMA, AVX-512F) was available for this run. The
x86 backends were checked for bit equality only, on x86-64 under Rosetta (SSE2),
and AVX-512F by CI's SDE job; neither is a timing. These measurements are still to
be taken and recorded, as the issue requires (#124 or a linked measurement issue):
every row above on an x86-64 host with each backend alone and through the
cascade, as [lanes-x86-i9-10920x-cold-paths](../lanes-x86-i9-10920x-cold-paths/README.md)
does for the earlier functions. Emulation and CI timing establish no speed claim.
