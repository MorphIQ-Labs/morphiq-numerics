//! `ln` and `ln_1p` on lanes ([`docs/lanes.md`] §5): `ln`'s screen,
//! `Reduced::of`, the reciprocal stage and shared double-word fallback,
//! and `ln_1p`'s stage H and double-word fallback, operation for operation.
//!
//! [`docs/lanes.md`]: https://github.com/MorphIQ-Labs/morphiq-numerics/blob/main/docs/lanes.md

use morphiq_numerics_arch::Simd;

use super::stage_tables::{EL, H, L0, L1, OFF, R, T};
use super::stages::{A_H, K_H, K2_H, TWO_53, TWO_M46};
use super::{FRACTION, TWO_54, ln, ln_1p};
use crate::lanes::{Cold, Kernel, cold, cold_arrays, decide_relative, lanes_mask, mask_from};

pub(crate) mod fallback;
pub(crate) mod stage_b;

/// `ln` as a lane kernel.
pub(crate) struct Ln;

/// `ln_1p` as a lane kernel.
pub(crate) struct Ln1p;

/// `1 + 53/128`: the reduced significand `m ∈ [1, 2)` has index `i ≥ 53`
/// exactly from it up.
const HIGH_INDEX: f64 = 1.0 + 53.0 / 128.0;
/// `2^52`, whose encoding's low bits hold an integer below `2^52` exactly.
const TWO_52: f64 = f64::from_bits(0x4330_0000_0000_0000);

/// `Reduced::of` on every lane of `x`, returning `(y, E)`; callers put 1 in
/// the lanes they discard. Everything but the table loads is in lanes, as
/// `Reduced::of` computes it, with its integer steps done exactly in binary64
/// (docs/lanes.md §5).
#[inline(always)]
fn reduce<K: Simd>(k: K, x: K::F) -> (K::F, K::F) {
    // Step 1: a subnormal x is scaled by 2^54, exactly.
    let tiny = k.lt(x, k.splat(f64::MIN_POSITIVE));
    let bits = k.to_bits(k.select(tiny, k.mul(x, k.splat(TWO_54)), x));
    let fraction = k.and_u(bits, k.splat_bits(FRACTION));
    // Step 2: m = 1.fraction; i is the fraction's top 7 bits, and i ≥ 53
    // exactly when m ≥ 1 + 53/128. Then y = m/2 (exact: the encoding with
    // exponent 1022), else y = m.
    let m = k.to_float(k.or_u(fraction, k.splat_bits(1023 << 52)));
    let high = k.le(k.splat(HIGH_INDEX), m);
    let y = k.select(high, k.mul(m, k.splat(0.5)), m);
    // E = biased − (1022 or 1023) − (54 if scaled): the biased exponent read
    // as the integer below 2^52 in 2^52's encoding, every step exact.
    let biased = k.sub(
        k.to_float(k.or_u(k.shr_u(bits, 52), k.splat_bits(TWO_52.to_bits()))),
        k.splat(TWO_52),
    );
    let offset = k.add(
        k.select(high, k.splat(1022.0), k.splat(1023.0)),
        k.select(tiny, k.splat(54.0), k.splat(0.0)),
    );
    let e = k.sub(biased, offset);
    (y, e)
}

/// `stage::parts`, operation for operation, after normalization.
#[inline(always)]
fn fast_value<K: Simd>(k: K, input: (K::F, K::F)) -> StageH<K> {
    fast_value_tables::<K, false>(k, input)
}

#[inline(always)]
fn fast_value_tables<K: Simd, const PACKED: bool>(k: K, (y, e): (K::F, K::F)) -> StageH<K> {
    let hb = k.to_bits(y);
    let u = k.sub_u(hb, k.splat_bits(OFF));
    let words = k.store(k.to_float(u));
    let (mut r, mut th, mut tl, mut re) = (
        K::Array::default(),
        K::Array::default(),
        K::Array::default(),
        K::Array::default(),
    );
    for (lane, word) in words.as_ref().iter().enumerate() {
        let u = word.to_bits();
        #[allow(clippy::cast_possible_truncation)] // nine bits
        let i = ((u >> 43) & 511) as usize;
        #[allow(clippy::cast_possible_wrap, clippy::cast_precision_loss)] // signed 12-bit exponent
        {
            re.as_mut()[lane] = ((u as i64) >> 52) as f64;
        }
        if PACKED {
            let [high, low] = super::bounded::PACKED[i];
            r.as_mut()[lane] = f64::from_bits((1022 << 52) | ((high & 1023) << 43));
            th.as_mut()[lane] = f64::from_bits(high & !1023);
            tl.as_mut()[lane] = f64::from_bits(low);
        } else {
            r.as_mut()[lane] = f64::from_bits(R[i]);
            (th.as_mut()[lane], tl.as_mut()[lane]) = T[i];
        }
    }
    let rs = k.to_float(k.sub_u(k.to_bits(k.load(r)), k.and_u(u, k.splat_bits(!FRACTION))));
    let hh = k.to_float(k.and_u(hb, k.splat_bits(!0x3ff)));
    let hl = k.sub(y, hh);
    let z = k.add(k.sub(k.mul(hh, rs), k.splat(1.0)), k.mul(hl, rs));
    let e = k.add(e, k.load(re));
    let ln1 = k.add(k.mul(e, k.splat(L1)), k.load(th));
    let ln0 = k.add(k.mul(e, k.splat(L0)), k.load(tl));
    let z2 = k.mul(z, z);
    let t0 = k.sub(k.mul(z, k.splat(H[0])), k.splat(0.5));
    let t1 = k.add(k.mul(z, k.splat(H[2])), k.splat(H[1]));
    let a1 = k.add(k.mul(z2, k.splat(H[3])), t1);
    let p = k.add(k.mul(z2, a1), t0);
    let q = k.mul(z2, p);
    let s = k.add(ln1, z);
    let e1 = k.sub(z, k.sub(s, ln1));
    let pre = k.add(e1, ln0);
    let lo = k.add(pre, q);
    let eps = k.add(
        k.mul(z2, k.splat(K_H)),
        k.add(k.mul(k.abs(s), k.splat(K2_H)), k.splat(A_H)),
    );
    (s, lo, eps)
}

/// Reciprocal-stage parts for the finite moderate normal tail. The caller
/// supplies 37 <= x <= 2^45; NormalLogReciprocalStage proves this direct use.
#[inline(always)]
pub(crate) fn direct_parts<K: Simd>(k: K, x: K::F) -> StageH<K> {
    fast_value(k, (x, k.splat(0.0)))
}

/// Finish the interval test and return the mask of decided lanes.
/// Keep this mask through the common branch: forming its complement on
/// every batch adds measurable overhead (docs/lanes.md §7).
#[inline(always)]
fn finish<K: Simd>(k: K, (s, lo, eps): StageH<K>, scalar_lanes: u64) -> (K::Array, u64) {
    let lb = k.add(s, k.sub(lo, eps));
    let ub = k.add(s, k.add(lo, eps));
    let decided = k.mask_bits(k.and_m(k.le(lb, ub), k.le(ub, lb))) & !scalar_lanes;
    (k.store(lb), decided)
}

impl Kernel for Ln {
    fn scalar(x: f64) -> f64 {
        ln(x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, x: K::Array) -> K::Array {
        // ln's screen: NaN, x < 0, ±0, +∞ and 1 are returned by `ln` itself.
        let (y, scalar_lanes) = fast_ln(k, &x);
        let (mut out, decided) = finish(k, y, scalar_lanes);
        let all = lanes_mask::<K>();
        if decided != all {
            for (i, o) in out.as_mut().iter_mut().enumerate() {
                if decided >> i & 1 == 0 {
                    if decided | (1 << i) != all {
                        let open = all & !decided;
                        return k.store(cold(
                            k,
                            FinishLn { open, scalar_lanes },
                            k.load(x),
                            k.load(out),
                        ));
                    }
                    *o = ln(x.as_ref()[i]);
                }
            }
        }
        out
    }
}

/// `ln`'s undecided lanes, `open`, and its screened ones.
struct FinishLn {
    open: u64,
    scalar_lanes: u64,
}

impl Cold for FinishLn {
    #[inline(always)]
    fn run<K: Simd>(self, k: K, x: K::Array, out: K::Array) -> K::Array {
        finish_ln(k, x, out, self.open, self.scalar_lanes)
    }
}

/// Complete the uncommon lanes, through `lanes::cold` so that they stay out
/// of the common stage's code but inside the backend's features.
#[inline(always)]
fn finish_ln<K: Simd>(
    k: K,
    x: K::Array,
    mut out: K::Array,
    mut open: u64,
    scalar_lanes: u64,
) -> K::Array {
    for (i, o) in out.as_mut().iter_mut().enumerate() {
        if scalar_lanes >> i & 1 != 0 {
            *o = ln(x.as_ref()[i]);
            open &= !(1 << i);
        }
    }
    if open.count_ones() >= 2 {
        let input = k.select(mask_from(k, open), k.load(x), k.splat(2.0));
        let y = fallback::ln(k, input);
        let accepted = decide_relative(k, y, super::EPS) & open;
        let values = k.store(y.0);
        for (i, o) in out.as_mut().iter_mut().enumerate() {
            if open >> i & 1 != 0 {
                *o = if accepted >> i & 1 != 0 {
                    values.as_ref()[i]
                } else {
                    let r = super::Reduced::of(x.as_ref()[i]);
                    r.accurate_value(r.z_exact()).to_f64()
                };
            }
        }
    } else if open != 0 {
        let i = open.trailing_zeros() as usize;
        out.as_mut()[i] = super::Reduced::of(x.as_ref()[i]).finish();
    }
    out
}

/// `ln`'s reciprocal stage on every lane, and the lanes (bit
/// `i` set) that `ln` screens out: NaN, `x ≤ 0`, `+∞` and 1.
#[inline(always)]
pub(super) fn fast_ln<K: Simd>(k: K, x: &K::Array) -> (StageH<K>, u64) {
    // The screen in lanes: 0 < x < +∞ and x ≠ 1 (x ≤ 1 and 1 ≤ x both
    // hold only at 1); both orderings fail on NaN, as the scalar test does.
    // Building a lane mask from per-lane bits instead stores each lane and
    // reloads them as one vector, which stalls store forwarding.
    let xv = k.load(*x);
    let one = k.splat(1.0);
    let inside = k.and_m(k.lt(k.splat(0.0), xv), k.lt(xv, k.splat(f64::INFINITY)));
    let at_one = k.and_m(k.le(xv, one), k.le(one, xv));
    let fast = k.and_m(inside, k.not_m(at_one));
    let scalar_lanes = !k.mask_bits(fast) & lanes_mask::<K>();
    (
        fast_value(k, reduce(k, k.select(fast, xv, one))),
        scalar_lanes,
    )
}

/// Rounded reciprocal stage for a packet of finite positive inputs.
/// The bounded slice screens the whole packet before entering. At one all
/// residuals and table terms are zero, so this also returns exact +0.
#[inline(always)]
pub(super) fn bounded_positive<K: Simd>(k: K, x: K::F) -> K::F {
    let (s, lo, _) = fast_value_tables::<K, true>(k, reduce(k, x));
    k.add(s, lo)
}

impl Kernel for Ln1p {
    fn scalar(x: f64) -> f64 {
        ln_1p(x)
    }

    #[inline(always)]
    fn lanes<K: Simd>(k: K, x: K::Array) -> K::Array {
        let ((s, lo, eps), scalar_lanes) = stage_h(k, &x);
        let (mut out, decided) = finish(k, (s, lo, eps), scalar_lanes);
        let all = lanes_mask::<K>();
        if decided != all {
            for (i, o) in out.as_mut().iter_mut().enumerate() {
                if decided >> i & 1 == 0 {
                    if decided | (1 << i) != all {
                        let open = all & !decided;
                        if K::LANES == 2 {
                            // NEON and SSE2 are baseline target features: keeping
                            // their scalar prefix inside the wrapper adds no
                            // feature-boundary cost and avoids another call.
                            return k.store(cold(
                                k,
                                FinishLn1p::<true> { open },
                                k.load(x),
                                k.load(out),
                            ));
                        }
                        return k.store(finish_ln_1p(k, k.load(x), k.load(out), open));
                    }
                    *o = super::ln_1p_after_h(x.as_ref()[i]);
                }
            }
        }
        out
    }
}

/// `ln_1p`'s undecided lanes, `open`.
struct FinishLn1p<const SCALAR_PREFIX: bool> {
    open: u64,
}

impl<const SCALAR_PREFIX: bool> Cold for FinishLn1p<SCALAR_PREFIX> {
    #[inline(always)]
    fn run<K: Simd>(self, k: K, x: K::Array, mut out: K::Array) -> K::Array {
        let open = if SCALAR_PREFIX {
            finish_ln_1p_scalar::<K>(&x, &mut out, self.open)
        } else {
            self.open
        };
        if open.count_ones() >= 2 {
            finish_ln_1p_fallback(k, x, out, open)
        } else {
            finish_ln_1p_single::<K>(&x, &mut out, open);
            out
        }
    }
}

/// Scalar stage B and special values need no backend re-entry. Only two or
/// more unresolved lanes enter the feature-enabled vector fallback.
#[cold]
#[inline(never)]
fn finish_ln_1p<K: Simd>(k: K, x: K::F, out: K::F, open: u64) -> K::F {
    let x = k.store(x);
    let mut out = k.store(out);
    let open = finish_ln_1p_scalar::<K>(&x, &mut out, open);
    if open.count_ones() >= 2 {
        return k.load(cold_arrays(k, FinishLn1p::<false> { open }, &x, &out));
    }
    finish_ln_1p_single::<K>(&x, &mut out, open);
    k.load(out)
}

#[inline(always)]
fn finish_ln_1p_scalar<K: Simd>(x: &K::Array, out: &mut K::Array, mut open: u64) -> u64 {
    // Stage B remains scalar. Its rare undecided lanes share the
    // double-word fallback; a single lane avoids vector setup overhead.
    for (i, o) in out.as_mut().iter_mut().enumerate() {
        if open >> i & 1 == 0 {
            continue;
        }
        let xi = x.as_ref()[i];
        if super::stages::stage_b_screen(xi)
            && let Some(y) = super::stages::stage_b(xi)
        {
            *o = y;
            open &= !(1 << i);
        } else if !(xi > -1.0 && xi < f64::INFINITY) || xi.abs() < super::TWO_M54 {
            *o = super::ln_1p_reference(xi);
            open &= !(1 << i);
        }
    }
    open
}

#[inline(always)]
fn finish_ln_1p_single<K: Simd>(x: &K::Array, out: &mut K::Array, open: u64) {
    if open != 0 {
        let i = open.trailing_zeros() as usize;
        out.as_mut()[i] = super::ln_1p_reference(x.as_ref()[i]);
    }
}

#[inline(always)]
fn finish_ln_1p_fallback<K: Simd>(k: K, x: K::Array, mut out: K::Array, open: u64) -> K::Array {
    let input = k.select(mask_from(k, open), k.load(x), k.splat(1.0));
    let y = fallback::ln_1p(k, input);
    let accepted = decide_relative(k, y, super::EPS) & open;
    let values = k.store(y.0);
    for (i, o) in out.as_mut().iter_mut().enumerate() {
        if open >> i & 1 != 0 {
            let xi = x.as_ref()[i];
            *o = if accepted >> i & 1 != 0 {
                values.as_ref()[i]
            } else if xi.abs() < super::TWO_M7 {
                super::small_accurate(xi).to_f64()
            } else {
                let (h, l) = super::split(xi);
                let r = super::Reduced::of(h);
                r.accurate_value(r.z_prime(l)).to_f64()
            };
        }
    }

    out
}

/// Stage H's `(s, lo, eps)` on lanes.
pub(super) type StageH<K> = (<K as Simd>::F, <K as Simd>::F, <K as Simd>::F);

/// `ln_1p`'s stage H on every lane, `stages::stage_h_parts` operation for
/// operation: `(s, lo, eps)`, and the lanes (bit `i` set) its screen sends
/// to `ln_1p_after_h`. The table index and loads are per lane; every
/// floating-point operation is in lanes.
#[inline(always)]
pub(super) fn stage_h<K: Simd>(k: K, x: &K::Array) -> (StageH<K>, u64) {
    let one = k.splat(1.0);
    let xv = k.load(*x);
    // The scalar stage-H screen, including its NaN semantics.
    let screen = k.and_m(
        k.and_m(k.le(k.splat(TWO_M46), k.abs(xv)), k.lt(xv, k.splat(TWO_53))),
        k.lt(k.splat(-1.0), xv),
    );
    let all = if K::LANES == 64 {
        u64::MAX
    } else {
        (1 << K::LANES) - 1
    };
    let scalar_lanes = !k.mask_bits(screen) & all;
    // Screened lanes compute on the placeholder 1, and are discarded.
    let xv = k.select(screen, xv, one);
    let s0 = k.add(one, xv);
    let l = k.sub(xv, k.sub(s0, one));
    // u = bits(s0) − OFF; E·2^52 is u with its fraction cleared, so
    // R[i]·2^−E is bits(R[i]) − (u & exponent field and sign).
    let hb = k.to_bits(s0);
    let u = k.sub_u(hb, k.splat_bits(OFF));
    let words = k.store(k.to_float(u));
    let (mut r, mut th, mut tl, mut eh, mut el) = (
        K::Array::default(),
        K::Array::default(),
        K::Array::default(),
        K::Array::default(),
        K::Array::default(),
    );
    for (lane, word) in words.as_ref().iter().enumerate() {
        let u = word.to_bits();
        #[allow(clippy::cast_possible_truncation)] // 9 bits
        let i = ((u >> 43) & 511) as usize;
        // ((E + 64) & 127), E the top 12 bits of u in two's complement.
        #[allow(clippy::cast_possible_truncation)] // 7 bits
        let e = (((u >> 52) + 64) & 127) as usize;
        r.as_mut()[lane] = f64::from_bits(R[i]);
        (th.as_mut()[lane], tl.as_mut()[lane]) = T[i];
        (eh.as_mut()[lane], el.as_mut()[lane]) = EL[e];
    }
    let rs = k.to_float(k.sub_u(k.to_bits(k.load(r)), k.and_u(u, k.splat_bits(!FRACTION))));
    let hh = k.to_float(k.and_u(hb, k.splat_bits(!0x3ff)));
    let hl = k.sub(s0, hh);
    let z = k.add(k.sub(k.mul(hh, rs), one), k.mul(hl, rs));
    let ln1 = k.add(k.load(eh), k.load(th));
    let ln0 = k.add(k.load(el), k.load(tl));
    let lr = k.mul(l, rs);
    let z2 = k.mul(z, z);
    let t0 = k.sub(k.mul(z, k.splat(H[0])), k.splat(0.5));
    let t1 = k.add(k.mul(z, k.splat(H[2])), k.splat(H[1]));
    let a1 = k.add(k.mul(z2, k.splat(H[3])), t1);
    let p = k.add(k.mul(z2, a1), t0);
    let q = k.mul(z2, p);
    let s = k.add(ln1, z);
    let e1 = k.sub(z, k.sub(s, ln1));
    let pre = k.add(e1, k.add(k.mul(lr, k.sub(one, z)), ln0));
    let lo = k.add(pre, q);
    let eps = k.add(
        k.mul(z2, k.splat(K_H)),
        k.add(k.mul(k.abs(s), k.splat(K2_H)), k.splat(A_H)),
    );
    ((s, lo, eps), scalar_lanes)
}

#[cfg(test)]
mod tests;
