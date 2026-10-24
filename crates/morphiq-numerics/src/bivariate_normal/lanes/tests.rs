//! The lane evaluation returns the scalar bits on every backend this CPU has
//! (docs/lanes.md §6): over the reference fixture's triples, every
//! correlation rule limit at adjacent doubles, saturated, NaN, infinite and
//! degenerate lanes, batches that mix regimes and rule lengths, short slices
//! and SIMD-width remainders, and random encodings.

use std::vec::Vec;

use morphiq_numerics_arch::{Simd, WithSimd};

use super::{Correlations, MAX_LANES, chunk, chunks, map};
use crate::bivariate_normal::{
    BivariateNormal, BoundedProbability, GENZ_CORRELATION_SPLIT, Regime, bivariate_norm_cdf,
    bivariate_norm_cdf_bounded, bivariate_norm_cdf_bounded_slice, bivariate_norm_cdf_slice,
};
use crate::lanes::tests::{backends, cases};
use crate::random::SplitMix64;

fn unit(rng: &mut SplitMix64) -> f64 {
    (rng.next_u64() >> 11) as f64 / (1u64 << 53) as f64
}

/// Each value of the fixture's `key` entries, in order.
fn fixture_words(fixture: &str, key: &str) -> Vec<f64> {
    let marker = std::format!("\"{key}\": \"");
    fixture
        .split(marker.as_str())
        .skip(1)
        .map(|rest| f64::from_bits(u64::from_str_radix(&rest[..16], 16).unwrap()))
        .collect()
}

/// Every `rho` that selects a different rule or regime, at the rule limits'
/// adjacent doubles, and the correlations a lane must send to the scalar
/// function.
fn correlations() -> Vec<f64> {
    let mut v = std::vec![
        0.0,
        -0.0,
        0.5,
        -0.5,
        0.786_151_377_757_423_3,
        0.99,
        -0.99,
        1e-300,
        f64::from_bits(1),
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        1.0 + f64::EPSILON,
        -1.5,
    ];
    for edge in [
        0.06,
        0.22,
        0.40,
        0.55,
        0.70,
        0.80,
        0.85,
        0.20,
        0.29,
        0.66,
        0.75,
        0.89,
        GENZ_CORRELATION_SPLIT,
        f64::EPSILON,
        1.0,
        1.0_f64.next_down(),
    ] {
        for sign in [1.0, -1.0] {
            for r in [edge, edge.next_up(), edge.next_down()] {
                v.push(sign * r);
            }
        }
    }
    v
}

/// Thresholds at every saturation and special-value edge.
fn points() -> Vec<f64> {
    let mut v = std::vec![
        0.0,
        -0.0,
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::MAX,
        f64::MIN_POSITIVE,
        f64::from_bits(1),
        1e-17,
    ];
    for p in [0.5, 1.0, 3.0, 8.0, 37.5, 39.0, 40.0] {
        v.push(p);
        v.push(-p);
    }
    for p in [39.0_f64, 38.0, 38.9] {
        for q in [p.next_up(), p.next_down()] {
            v.push(q);
            v.push(-q);
        }
    }
    v
}

/// Triples: the fixture's, every correlation at every pair of points, and
/// random ones whose correlations are drawn from the rule limits and
/// uniformly, so a chunk mixes regimes and rule lengths.
fn corpus() -> (Vec<f64>, Vec<f64>, Vec<f64>) {
    let fixture = include_str!("../../../../reference/fixtures/bivariate_normal.json");
    let cases_start = fixture.find("\"cases\"").unwrap();
    let fixture = &fixture[cases_start..];
    let mut x = fixture_words(fixture, "h");
    let mut y = fixture_words(fixture, "k");
    let mut rho = fixture_words(fixture, "rho");
    assert!(x.len() == y.len() && y.len() == rho.len() && x.len() > 2000);
    let (pts, rhos) = (points(), correlations());
    for &r in &rhos {
        for &a in &pts {
            for &b in &pts {
                x.push(a);
                y.push(b);
                rho.push(r);
            }
        }
    }
    let mut rng = SplitMix64::new(0x6269_7661_7269_6174);
    for _ in 0..cases() / 16 {
        let draw = |rng: &mut SplitMix64| match rng.next_u64() % 6 {
            0 => f64::from_bits(rng.next_u64()),
            1 => pts[(rng.next_u64() % pts.len() as u64) as usize],
            2 => (unit(rng) * 2.0 - 1.0) * 8.0,
            _ => (unit(rng) * 2.0 - 1.0) * 40.0,
        };
        x.push(draw(&mut rng));
        y.push(draw(&mut rng));
        rho.push(match rng.next_u64() % 4 {
            0 => rhos[(rng.next_u64() % rhos.len() as u64) as usize],
            1 => f64::from_bits(rng.next_u64()),
            2 => (unit(&mut rng) * 2.0 - 1.0) * 0.925,
            _ => (unit(&mut rng) * 2.0 - 1.0) * 0.999,
        });
    }
    (x, y, rho)
}

/// `chunk` on every lane group of the corpus, a correlation per lane, against
/// the scalar function.
struct PerLane<'a> {
    x: &'a [f64],
    y: &'a [f64],
    rho: &'a [f64],
}

impl WithSimd for PerLane<'_> {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let dummy = BivariateNormal::new(0.0).unwrap();
        let mut served_total = 0_usize;
        let mut lanes_total = 0_usize;
        for start in (0..self.x.len() - self.x.len() % K::LANES).step_by(K::LANES) {
            let end = start + K::LANES;
            let owned: Vec<Option<BivariateNormal>> = self.rho[start..end]
                .iter()
                .map(|&r| BivariateNormal::new(r).ok())
                .collect();
            let mut tables = [&dummy; MAX_LANES];
            for (slot, table) in tables.iter_mut().zip(&owned) {
                if let Some(table) = table {
                    *slot = table;
                }
            }
            let (mut ax, mut ay) = (K::Array::default(), K::Array::default());
            ax.as_mut().copy_from_slice(&self.x[start..end]);
            ay.as_mut().copy_from_slice(&self.y[start..end]);
            let (out, served) = chunk(k, ax, ay, &tables);
            for (lane, table) in owned.iter().enumerate() {
                let Some(table) = table else {
                    continue;
                };
                let (x, y) = (self.x[start + lane], self.y[start + lane]);
                assert_eq!(
                    out.as_ref()[lane].to_bits(),
                    table.cdf(x, y).to_bits(),
                    "P({x:e}, {y:e}; {:e}) on {}",
                    self.rho[start + lane],
                    K::NAME
                );
                served_total += usize::from(served >> lane & 1 == 1);
                lanes_total += 1;
            }
        }
        // Not vacuous: the vector code, not the fallback, served most lanes.
        assert!(
            served_total * 3 > lanes_total,
            "{served_total} of {lanes_total} lanes served on {}",
            K::NAME
        );
    }
}

#[test]
fn lanes_return_the_scalar_bits_with_a_correlation_per_lane() {
    let (x, y, rho) = corpus();
    for backend in backends() {
        backend.vectorize(PerLane {
            x: &x,
            y: &y,
            rho: &rho,
        });
    }
}

/// Every correlation at one table, every pair of points: the slice form's
/// chunks.
struct OneTable<'a> {
    table: &'a BivariateNormal,
    x: &'a [f64],
    y: &'a [f64],
}

impl WithSimd for OneTable<'_> {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        let tables = [self.table; MAX_LANES];
        for (cx, cy) in self
            .x
            .chunks_exact(K::LANES)
            .zip(self.y.chunks_exact(K::LANES))
        {
            let (mut ax, mut ay) = (K::Array::default(), K::Array::default());
            ax.as_mut().copy_from_slice(cx);
            ay.as_mut().copy_from_slice(cy);
            let (out, _) = chunk(k, ax, ay, &tables);
            for lane in 0..K::LANES {
                assert_eq!(
                    out.as_ref()[lane].to_bits(),
                    self.table.cdf(cx[lane], cy[lane]).to_bits(),
                    "P({:e}, {:e}; {:e}) on {}",
                    cx[lane],
                    cy[lane],
                    self.table.correlation(),
                    K::NAME
                );
            }
        }
    }
}

#[test]
fn lanes_return_the_scalar_bits_at_one_correlation() {
    let pts = points();
    let (mut x, mut y) = (Vec::new(), Vec::new());
    for &a in &pts {
        for &b in &pts {
            x.push(a);
            y.push(b);
        }
    }
    let mut rng = SplitMix64::new(0x6f6e_6574_6162_6c65);
    for _ in 0..4000 {
        x.push((unit(&mut rng) * 2.0 - 1.0) * 12.0);
        y.push((unit(&mut rng) * 2.0 - 1.0) * 12.0);
    }
    for rho in correlations() {
        let Ok(table) = BivariateNormal::new(rho) else {
            continue;
        };
        for backend in backends() {
            backend.vectorize(OneTable {
                table: &table,
                x: &x,
                y: &y,
            });
        }
    }
}

/// Which lanes the vector code serves: the low-correlation quadrature on a
/// pair that is not NaN and not saturated, and no others.
struct Served;

impl WithSimd for Served {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        // (x, y, rho, served by the vector code)
        let classes: [(f64, f64, f64, bool); 12] = [
            (0.3, -0.4, 0.5, true),
            (1.0, 2.0, -0.3, true),
            (0.3, -0.4, 0.95, false),
            (-1.0, 0.0, -0.97, false),
            (0.3, -0.4, 0.0, false),
            (0.3, -0.4, 1.0, false),
            (0.3, -0.4, -1.0, false),
            (f64::NAN, 0.0, 0.5, false),
            (-39.0, 0.0, 0.5, false),
            (0.0, 39.0, 0.95, false),
            (f64::NEG_INFINITY, f64::INFINITY, 0.5, false),
            (38.9, -38.9, 0.5, true),
        ];
        for rotate in 0..classes.len() {
            let owned: Vec<BivariateNormal> = (0..K::LANES)
                .map(|lane| {
                    BivariateNormal::new(classes[(lane + rotate) % classes.len()].2).unwrap()
                })
                .collect();
            let mut tables = [&owned[0]; MAX_LANES];
            for (slot, table) in tables.iter_mut().zip(&owned) {
                *slot = table;
            }
            let (mut ax, mut ay) = (K::Array::default(), K::Array::default());
            let mut expected = 0_u64;
            for lane in 0..K::LANES {
                let (x, y, _, vector) = classes[(lane + rotate) % classes.len()];
                ax.as_mut()[lane] = x;
                ay.as_mut()[lane] = y;
                expected |= u64::from(vector) << lane;
            }
            let (out, served) = chunk(k, ax, ay, &tables);
            assert_eq!(served, expected, "rotation {rotate} on {}", K::NAME);
            for (lane, table) in owned.iter().enumerate() {
                assert_eq!(
                    out.as_ref()[lane].to_bits(),
                    table.cdf(ax.as_ref()[lane], ay.as_ref()[lane]).to_bits()
                );
            }
        }
    }
}

#[test]
fn only_low_correlation_lanes_that_are_not_nan_or_saturated_are_served_by_the_vector_code() {
    for backend in backends() {
        backend.vectorize(Served);
    }
    // The classification the screen reads.
    assert_eq!(BivariateNormal::new(0.5).unwrap().regime, Regime::Low);
    assert_eq!(BivariateNormal::new(0.95).unwrap().regime, Regime::High);
}

/// A correlation repeated across lanes, valid or not, is evaluated or NaN in
/// each of them.
#[test]
fn repeated_correlations_keep_their_validity_in_every_lane() {
    for rho in [f64::NAN, 1.5, -1.0_f64.next_down(), 0.5, 0.95] {
        let rho = [rho; 40];
        let x: Vec<f64> = (0..40).map(|i| f64::from(i) / 7.0 - 2.0).collect();
        let y: Vec<f64> = (0..40).map(|i| 1.0 - f64::from(i) / 9.0).collect();
        let mut out = [0.0; 40];
        bivariate_norm_cdf_slice(&x, &y, &rho, &mut out);
        for i in 0..40 {
            assert!(
                same(out[i], bivariate_norm_cdf(x[i], y[i], rho[i])),
                "{} at {i}",
                rho[i]
            );
        }
    }
}

/// The driver on one backend: whole chunks vector, the scalar function for
/// the rest, every length 0 to 17 at every offset.
struct Driver<'a> {
    x: &'a [f64],
    y: &'a [f64],
    rho: &'a [f64],
}

impl WithSimd for Driver<'_> {
    type Output = ();
    #[inline(always)]
    fn with<K: Simd>(self, k: K) {
        for len in 0..=17 {
            for start in 0..8 {
                let (x, y, rho) = (
                    &self.x[start..start + len],
                    &self.y[start..start + len],
                    &self.rho[start..start + len],
                );
                let mut out = std::vec![f64::from_bits(0x7ff8_dead_beef_0001); len];
                let covered = chunks(k, x, y, Correlations::Each(rho), &mut out);
                let whole = if K::LANES == 1 {
                    0
                } else {
                    len - len % K::LANES
                };
                assert_eq!(covered, whole, "{} length {len}", K::NAME);
                for i in 0..covered {
                    assert_eq!(
                        out[i].to_bits(),
                        bivariate_norm_cdf(x[i], y[i], rho[i]).to_bits(),
                        "element {i} of {len} on {}",
                        K::NAME
                    );
                }
                // Beyond the covered chunks the output is untouched.
                for o in &out[covered..] {
                    assert_eq!(o.to_bits(), 0x7ff8_dead_beef_0001);
                }
            }
        }
    }
}

#[test]
fn the_driver_covers_whole_chunks_and_leaves_the_remainder() {
    let (x, y, rho) = corpus();
    // Skip the fixture's start so the windows hold a mix of regimes.
    let from = x.len() / 3;
    for backend in backends() {
        backend.vectorize(Driver {
            x: &x[from..],
            y: &y[from..],
            rho: &rho[from..],
        });
    }
}

fn same(a: f64, b: f64) -> bool {
    a.to_bits() == b.to_bits()
}

/// The public entry points, on the dispatched backend, for every length up
/// to 17 and a long batch.
#[test]
fn slice_entry_points_return_the_scalar_bits() {
    let (x, y, rho) = corpus();
    let from = x.len() / 2;
    for len in (0..=17).chain([4099]) {
        let (x, y, rho) = (
            &x[from..from + len],
            &y[from..from + len],
            &rho[from..from + len],
        );
        let mut out = std::vec![f64::NAN; len];
        bivariate_norm_cdf_slice(x, y, rho, &mut out);
        let mut bounded = std::vec![
            BoundedProbability {
                value: 0.0,
                error: 0.0
            };
            len
        ];
        bivariate_norm_cdf_bounded_slice(x, y, rho, &mut bounded);
        for i in 0..len {
            let want = bivariate_norm_cdf(x[i], y[i], rho[i]);
            assert!(
                same(out[i], want),
                "paired ({:e}, {:e}; {:e})",
                x[i],
                y[i],
                rho[i]
            );
            let want = bivariate_norm_cdf_bounded(x[i], y[i], rho[i]);
            assert!(same(bounded[i].value, want.value) && same(bounded[i].error, want.error));
        }
    }
    for r in correlations() {
        let Ok(table) = BivariateNormal::new(r) else {
            continue;
        };
        for len in [0, 1, 2, 3, 5, 8, 9, 17, 130] {
            let (x, y) = (&x[from..from + len], &y[from..from + len]);
            let mut out = std::vec![f64::NAN; len];
            table.cdf_slice(x, y, &mut out);
            let mut bounded = std::vec![
                BoundedProbability {
                    value: 0.0,
                    error: 0.0
                };
                len
            ];
            table.cdf_bounded_slice(x, y, &mut bounded);
            for i in 0..len {
                assert!(same(out[i], table.cdf(x[i], y[i])));
                let want = table.cdf_bounded(x[i], y[i]);
                assert!(same(bounded[i].value, want.value) && same(bounded[i].error, want.error));
            }
        }
    }
}

/// An invalid correlation is NaN in its own lane and disturbs no other.
#[test]
fn an_invalid_correlation_is_nan_in_its_own_lane_only() {
    let rho = [
        0.5,
        f64::NAN,
        0.95,
        1.5,
        -0.5,
        0.0,
        f64::INFINITY,
        -0.97,
        0.3,
    ];
    let x = [0.2; 9];
    let y = [-0.7; 9];
    let mut out = [0.0; 9];
    bivariate_norm_cdf_slice(&x, &y, &rho, &mut out);
    for (i, &r) in rho.iter().enumerate() {
        assert!(same(out[i], bivariate_norm_cdf(0.2, -0.7, r)), "{r}");
    }
    assert!(out[1].is_nan() && out[3].is_nan() && out[6].is_nan());
    assert!(!out[0].is_nan() && !out[2].is_nan());
}

/// A long batch at one correlation equals the one-shot function.
#[test]
fn the_slice_form_equals_the_one_shot_function() {
    let mut rng = SplitMix64::new(0x7365_7269_6573);
    let n = 1000;
    let x: Vec<f64> = (0..n).map(|_| (unit(&mut rng) * 2.0 - 1.0) * 6.0).collect();
    let y: Vec<f64> = (0..n).map(|_| (unit(&mut rng) * 2.0 - 1.0) * 6.0).collect();
    for rho in [0.1, -0.45, 0.9, 0.93, -0.999] {
        let table = BivariateNormal::new(rho).unwrap();
        let mut out = std::vec![0.0; n];
        table.cdf_slice(&x, &y, &mut out);
        for i in 0..n {
            assert!(same(out[i], bivariate_norm_cdf(x[i], y[i], rho)));
        }
    }
}

/// `map` itself, the cascade: whole chunks in lanes, the rest scalar.
#[test]
fn the_cascade_returns_the_scalar_bits() {
    let (x, y, rho) = corpus();
    let from = x.len() / 4;
    for len in 0..=40 {
        let (x, y, rho) = (
            &x[from..from + len],
            &y[from..from + len],
            &rho[from..from + len],
        );
        let mut out = std::vec![f64::NAN; len];
        map(x, y, Correlations::Each(rho), &mut out);
        for i in 0..len {
            assert!(same(out[i], bivariate_norm_cdf(x[i], y[i], rho[i])));
        }
    }
}
