//! Finite intervals and checked tridiagonal solves against exact and directed
//! MPFR values, and the contracts in docs/interval.md and docs/tridiagonal.md.
use morphiq_numerics::interval::{FiniteInterval, IntervalError};
use morphiq_numerics::linalg::tridiagonal::{
    DominantTridiagonal, Error, SignTridiagonal, UnpivotedTridiagonal,
};
use rug::{Float, float::Round};

/// Holds binary64 products and their short sums exactly.
const WIDE: u32 = 4400;
const ORDER: usize = 12;

fn exact(x: f64) -> Float {
    Float::with_val(WIDE, x)
}

fn mul(a: &Float, b: &Float) -> Float {
    Float::with_val(WIDE, a * b)
}

fn add(a: &Float, b: &Float) -> Float {
    Float::with_val(WIDE, a + b)
}

fn sub(a: &Float, b: &Float) -> Float {
    Float::with_val(WIDE, a - b)
}

fn magnitude(x: f64) -> Float {
    exact(x).abs()
}

/// One binary64 operation, rounded to nearest from a wide result.
fn round(x: Float) -> f64 {
    x.to_f64_round(Round::Nearest)
}

fn quotient(a: f64, b: f64) -> f64 {
    round(Float::with_val(WIDE, &exact(a) / &exact(b)))
}

/// Within a factor `1 - 2^-40` of the overflow threshold.
fn near_overflow(x: &Float) -> bool {
    let limit = sub(&exact(f64::MAX), &(exact(f64::MAX) >> 40));
    x.clone().abs() >= limit
}

/// The enclosure must contain every value in `[low, high]` given as exact
/// bounds of the true image.
fn contains(result: FiniteInterval, low: &Float, high: &Float) -> bool {
    exact(result.lower()) <= *low && exact(result.upper()) >= *high
}

fn check_algebraic(
    name: &str,
    result: Result<FiniteInterval, IntervalError>,
    corners: &[Float],
    inputs: (FiniteInterval, FiniteInterval),
) {
    let low = corners
        .iter()
        .skip(1)
        .fold(corners[0].clone(), |a, b| a.min(b));
    let high = corners
        .iter()
        .skip(1)
        .fold(corners[0].clone(), |a, b| a.max(b));
    match result {
        Ok(z) => assert!(contains(z, &low, &high), "{name} enclosure {inputs:?}"),
        Err(IntervalError::Range) => assert!(
            near_overflow(&low) || near_overflow(&high),
            "{name} range refusal {inputs:?}"
        ),
        Err(error) => panic!("{name}: unexpected {error:?} for {inputs:?}"),
    }
}

fn check_binary(x: FiniteInterval, y: FiniteInterval) {
    let [l, u, a, b] = [x.lower(), x.upper(), y.lower(), y.upper()].map(exact);
    check_algebraic("add", x.checked_add(y), &[add(&l, &a), add(&u, &b)], (x, y));
    check_algebraic("sub", x.checked_sub(y), &[sub(&l, &b), sub(&u, &a)], (x, y));
    let products = [mul(&l, &a), mul(&l, &b), mul(&u, &a), mul(&u, &b)];
    check_algebraic("mul", x.checked_mul(y), &products, (x, y));
    let spans_zero = y.lower() <= 0.0 && y.upper() >= 0.0;
    match x.checked_div(y) {
        Err(IntervalError::Domain) => assert!(spans_zero, "division domain {y:?}"),
        Ok(z) => {
            assert!(!spans_zero, "division by an interval holding zero");
            // lower <= p/q <= upper, multiplied through by q.
            for p in [&l, &u] {
                for q in [&a, &b] {
                    let low = mul(&exact(z.lower()), q);
                    let high = mul(&exact(z.upper()), q);
                    let inside = if *q > 0 {
                        low <= *p && *p <= high
                    } else {
                        high <= *p && *p <= low
                    };
                    assert!(inside, "division enclosure {x:?} {y:?}");
                }
            }
        }
        // The intermediate reciprocal or a corner may overflow.
        Err(IntervalError::Range) => {
            assert!(!spans_zero);
            let smallest = a.clone().abs().min(&b.clone().abs());
            let reciprocal = Float::with_val(WIDE, 1 / &smallest);
            let largest = l.clone().abs().max(&u.clone().abs());
            let image = mul(&largest, &add(&reciprocal, &(reciprocal.clone() >> 50)));
            assert!(
                near_overflow(&reciprocal) || near_overflow(&image),
                "division range refusal {x:?} {y:?}"
            );
        }
        Err(error) => panic!("division: unexpected {error:?}"),
    }
}

/// An increasing function's image of `[lower, upper]`, enclosed at 512 bits.
fn check_increasing(
    name: &str,
    result: FiniteInterval,
    x: FiniteInterval,
    f: fn(&mut Float, Round) -> std::cmp::Ordering,
) {
    let end = |value: f64, direction| {
        let mut y = Float::with_val(512, value);
        f(&mut y, direction);
        y
    };
    assert!(
        exact(result.lower()) <= end(x.lower(), Round::Up),
        "{name} lower end {x:?}"
    );
    assert!(
        exact(result.upper()) >= end(x.upper(), Round::Down),
        "{name} upper end {x:?}"
    );
}

fn check_unary(x: FiniteInterval) {
    let (l, u) = (x.lower(), x.upper());
    let negated = x.negated();
    assert_eq!([negated.lower(), negated.upper()], [-u, -l]);
    let abs = x.abs();
    let expected_low = if l > 0.0 {
        l
    } else if u < 0.0 {
        -u
    } else {
        0.0
    };
    assert_eq!([abs.lower(), abs.upper()], [expected_low, (-l).max(u)]);
    assert!(!abs.lower().is_sign_negative() && !abs.upper().is_sign_negative());
    for v in [l, u, 0.0, f64::NAN, f64::INFINITY] {
        assert_eq!(x.contains(v), v.is_finite() && l <= v && v <= u);
    }
    let squares = [
        mul(&exact(abs.lower()), &exact(abs.lower())),
        mul(&exact(abs.upper()), &exact(abs.upper())),
    ];
    match x.checked_square() {
        Ok(z) => assert!(
            z.lower() >= 0.0 && contains(z, &squares[0], &squares[1]),
            "square {x:?}"
        ),
        Err(IntervalError::Range) => assert!(near_overflow(&squares[1]), "square range {x:?}"),
        Err(error) => panic!("square: unexpected {error:?}"),
    }
    match x.checked_ln() {
        Ok(z) => {
            assert!(l > 0.0);
            check_increasing("ln", z, x, Float::ln_round);
        }
        Err(error) => assert!(
            error == IntervalError::Domain && l <= 0.0,
            "ln {x:?} {error:?}"
        ),
    }
    match x.checked_sqrt() {
        Ok(z) => {
            assert!(l >= 0.0 && z.lower() >= 0.0);
            check_increasing("sqrt", z, x, Float::sqrt_round);
        }
        Err(error) => assert!(
            error == IntervalError::Domain && l < 0.0,
            "sqrt {x:?} {error:?}"
        ),
    }
    match x.checked_exp() {
        Ok(z) => {
            assert!(z.lower() >= 0.0);
            check_increasing("exp", z, x, Float::exp_round);
        }
        // exp(709.78) is the largest finite image.
        Err(error) => assert!(
            error == IntervalError::Range && u > 709.78,
            "exp {x:?} {error:?}"
        ),
    }
}

fn check_intervals(w: &[f64]) {
    let mut built = Vec::new();
    for pair in w.as_chunks::<2>().0.iter().take(4) {
        let [a, b] = *pair;
        let admitted = a.is_finite() && b.is_finite() && a <= b;
        match FiniteInterval::new(a, b) {
            Ok(x) => {
                assert!(admitted && x.lower() == a && x.upper() == b);
                built.push(x);
            }
            Err(error) => assert!(!admitted && error == IntervalError::InvalidBounds),
        }
        assert_eq!(FiniteInterval::point(a).is_ok(), a.is_finite());
        if a.is_finite() && b.is_finite() {
            built.push(FiniteInterval::new(a.min(b), a.max(b)).expect("ordered bounds"));
        }
    }
    for &x in &built {
        check_unary(x);
        for &y in &built {
            check_binary(x, y);
            let m = x.max(y);
            assert!(m.lower() == x.lower().max(y.lower()) && m.upper() == x.upper().max(y.upper()));
        }
    }
}

struct System {
    lower: Vec<f64>,
    diagonal: Vec<f64>,
    upper: Vec<f64>,
}

/// The documented recurrence's factorization, or its first failure.
fn reference_factor(a: &System) -> Result<(Vec<f64>, Vec<f64>), Error> {
    let n = a.diagonal.len();
    let (mut p, mut c) = (Vec::new(), Vec::new());
    for i in 0..n {
        let pivot = if i == 0 {
            a.diagonal[0]
        } else {
            let product = round(mul(&exact(a.lower[i - 1]), &exact(c[i - 1])));
            if !product.is_finite() {
                return Err(Error::Range);
            }
            round(sub(&exact(a.diagonal[i]), &exact(product)))
        };
        if pivot == 0.0 {
            return Err(Error::ZeroPivot(i));
        }
        if !pivot.is_finite() {
            return Err(Error::Range);
        }
        p.push(pivot);
        if i + 1 < n {
            let normalized = quotient(a.upper[i], pivot);
            if !normalized.is_finite() {
                return Err(Error::Range);
            }
            c.push(normalized);
        }
    }
    Ok((p, c))
}

/// The documented forward and back recurrences, with an optional obstacle.
fn reference_solve(
    a: &System,
    p: &[f64],
    c: &[f64],
    rhs: &[f64],
    obstacle: Option<&[f64]>,
) -> Option<Vec<f64>> {
    let n = p.len();
    let mut x = vec![0.0; n];
    for i in 0..n {
        let numerator = if i == 0 {
            rhs[0]
        } else {
            let product = round(mul(&exact(a.lower[i - 1]), &exact(x[i - 1])));
            round(sub(&exact(rhs[i]), &exact(product)))
        };
        if !numerator.is_finite() {
            return None;
        }
        x[i] = quotient(numerator, p[i]);
        if !x[i].is_finite() {
            return None;
        }
    }
    for i in (0..n).rev() {
        if i + 1 < n {
            let product = round(mul(&exact(c[i]), &exact(x[i + 1])));
            x[i] = round(sub(&exact(x[i]), &exact(product)));
        }
        if let Some(g) = obstacle
            && x[i] < g[i]
        {
            x[i] = g[i];
        }
        if !x[i].is_finite() {
            return None;
        }
    }
    Some(x)
}

fn residual(a: &System, rhs: &[f64], x: &[f64], i: usize) -> Float {
    let mut r = sub(&mul(&exact(a.diagonal[i]), &exact(x[i])), &exact(rhs[i]));
    if i > 0 {
        r = add(&r, &mul(&exact(a.lower[i - 1]), &exact(x[i - 1])));
    }
    if i + 1 < x.len() {
        r = add(&r, &mul(&exact(a.upper[i]), &exact(x[i + 1])));
    }
    r
}

fn largest_residual(a: &System, rhs: &[f64], x: &[f64]) -> Float {
    (0..x.len())
        .map(|i| residual(a, rhs, x, i).abs())
        .fold(exact(0.0), |m, r| m.max(&r))
}

/// A high-precision solution of a strictly dominant system.
fn accurate_solution(a: &System, rhs: &[f64]) -> Vec<Float> {
    let p = 8000;
    let n = rhs.len();
    let (mut c, mut x): (Vec<Float>, Vec<Float>) = (Vec::new(), Vec::new());
    for i in 0..n {
        let mut pivot = Float::with_val(p, a.diagonal[i]);
        let mut value = Float::with_val(p, rhs[i]);
        if i > 0 {
            let l = Float::with_val(p, a.lower[i - 1]);
            pivot -= Float::with_val(p, &l * &c[i - 1]);
            value -= Float::with_val(p, &l * &x[i - 1]);
        }
        x.push(value / &pivot);
        if i + 1 < n {
            c.push(Float::with_val(p, a.upper[i]) / &pivot);
        }
    }
    for i in (0..n.saturating_sub(1)).rev() {
        let product = Float::with_val(p, &c[i] * &x[i + 1]);
        x[i] -= product;
    }
    x
}

/// An admitted obstacle solve is the exact solution of the problem with each
/// right-hand side moved by at most `2 tau`.
fn check_complementarity(a: &System, p: &[f64], c: &[f64], rhs: &[f64], g: &[f64], x: &[f64]) {
    let n = x.len();
    let abs = |v: f64| magnitude(v);
    for i in 0..n {
        let (l, xm, cm) = if i > 0 {
            (a.lower[i - 1], x[i - 1], c[i - 1])
        } else {
            (0.0, 0.0, 0.0)
        };
        let xp = if i + 1 < n { x[i + 1] } else { 0.0 };
        let ci = if i + 1 < n { c[i] } else { 0.0 };
        let m = add(
            &mul(&abs(l), &add(&abs(xm), &mul(&abs(cm), &abs(x[i])))),
            &mul(&abs(p[i]), &add(&abs(x[i]), &mul(&abs(ci), &abs(xp)))),
        );
        let relative = mul(&add(&m, &abs(rhs[i])), &(exact(5.0) >> 52));
        let scales = mul(
            &add(
                &add(&exact(1.0), &abs(l)),
                &add(&abs(a.diagonal[i]), &abs(p[i])),
            ),
            &add(&add(&exact(1.0), &abs(xm)), &add(&abs(x[i]), &abs(xp))),
        );
        let tau = add(&relative, &mul(&scales, &(exact(8.0) >> 1074)));
        let allowed = add(&tau, &tau);
        let r = residual(a, rhs, x, i);
        assert!(x[i] >= g[i], "below the obstacle at row {i}");
        if x[i] == g[i] {
            assert!(r >= -allowed.clone(), "contact row {i} residual");
        } else {
            assert!(r.abs() <= allowed, "continuation row {i} residual");
        }
    }
}

macro_rules! solves {
    ($a:expr, $factors:expr, $p:expr, $c:expr, $rhs:expr, $obstacle:expr) => {{
        let n = $rhs.len();
        let mut out = vec![0.0; n];
        let expected = reference_solve($a, $p, $c, $rhs, None);
        match $factors.solve_into($rhs, &mut out) {
            Ok(()) => {
                let want = expected
                    .as_ref()
                    .expect("solve succeeded where the recurrence overflows");
                for (got, want) in out.iter().zip(want) {
                    assert_eq!(got.to_bits(), want.to_bits(), "solve bits");
                }
            }
            Err(error) => assert!(
                error == Error::Range && expected.is_none(),
                "solve {error:?}"
            ),
        }
        // Two columns, interleaved by row; each repeats the scalar solve.
        let two: Vec<f64> = $rhs
            .iter()
            .zip($obstacle)
            .flat_map(|(&a, &b)| [a, b])
            .collect();
        let mut many = vec![0.0; 2 * n];
        let second = reference_solve($a, $p, $c, $obstacle, None);
        match $factors.solve_many_into(2, &two, &mut many) {
            Ok(()) => {
                for (column, want) in [&expected, &second].into_iter().enumerate() {
                    let want = want
                        .as_ref()
                        .expect("batched solve of an overflowing column");
                    for i in 0..n {
                        assert_eq!(
                            many[2 * i + column].to_bits(),
                            want[i].to_bits(),
                            "batched bits"
                        );
                    }
                }
            }
            Err(error) => assert!(
                error == Error::Range && (expected.is_none() || second.is_none()),
                "batched solve {error:?}"
            ),
        }
        let swept = reference_solve($a, $p, $c, $rhs, Some($obstacle));
        match $factors.solve_obstacle_into($rhs, $obstacle, &mut out) {
            Ok(()) => {
                let want = swept.expect("obstacle solve of an overflowing sweep");
                for (got, want) in out.iter().zip(&want) {
                    assert_eq!(got.to_bits(), want.to_bits(), "obstacle bits");
                }
                check_complementarity($a, $p, $c, $rhs, $obstacle, &out);
            }
            Err(Error::NotComplementary(_)) => assert!(swept.is_some()),
            Err(error) => assert_eq!(error, Error::Range),
        }
    }};
}

fn check_residual_bound(bound: f64, a: &System, rhs: &[f64], candidate: &[f64]) {
    assert!(
        exact(bound) >= largest_residual(a, rhs, candidate),
        "residual certificate"
    );
}

fn check_system(a: &System, rhs: &[f64], obstacle: &[f64], candidate: &[f64]) {
    let n = a.diagonal.len();
    let finite = a
        .lower
        .iter()
        .chain(&a.diagonal)
        .chain(&a.upper)
        .all(|v| v.is_finite());
    let reference = finite.then(|| reference_factor(a));
    let (mut pivots, mut upper) = (vec![0.0; n], vec![0.0; n.saturating_sub(1)]);
    let vectors_finite = rhs
        .iter()
        .chain(obstacle)
        .chain(candidate)
        .all(|v| v.is_finite());

    macro_rules! factored {
        ($matrix:expr, $then:expr) => {
            match $matrix.factor_into(&mut pivots, &mut upper) {
                Ok(factors) => {
                    let (p, c) = reference
                        .clone()
                        .expect("finite input")
                        .expect("factored where the recurrence fails");
                    if vectors_finite {
                        solves!(a, factors, &p, &c, rhs, obstacle);
                        $then(factors);
                    } else if !rhs.iter().all(|v| v.is_finite()) {
                        let mut out = vec![0.25; n];
                        assert_eq!(factors.solve_into(rhs, &mut out), Err(Error::NonFinite));
                        assert!(out.iter().all(|&v| v == 0.25), "output written on refusal");
                    }
                }
                Err(error) => assert_eq!(
                    reference.clone().expect("finite input").err(),
                    Some(error),
                    "factorization failure"
                ),
            }
        };
    }

    match UnpivotedTridiagonal::new(&a.lower, &a.diagonal, &a.upper) {
        Err(error) => assert!(error == Error::NonFinite && !finite),
        Ok(matrix) => {
            assert!(finite);
            factored!(
                matrix,
                |factors: morphiq_numerics::linalg::tridiagonal::UnpivotedThomasFactors| {
                    if let Ok(c) = factors.certify_residual(rhs, candidate) {
                        check_residual_bound(c.max_residual(), a, rhs, candidate);
                    }
                }
            );
        }
    }

    let sign_admitted = finite
        && a.diagonal.iter().all(|&d| d > 0.0)
        && a.lower
            .iter()
            .zip(&a.upper)
            .all(|(&l, &u)| l == 0.0 || u == 0.0 || (l > 0.0) != (u > 0.0));
    match SignTridiagonal::new(&a.lower, &a.diagonal, &a.upper) {
        Err(error) => assert!(!sign_admitted, "sign domain refused: {error:?}"),
        Ok(matrix) => {
            assert!(sign_admitted, "sign domain admitted outside its conditions");
            factored!(
                matrix,
                |factors: morphiq_numerics::linalg::tridiagonal::SignThomasFactors| {
                    if let Ok(c) = factors.certify_residual(rhs, candidate) {
                        check_residual_bound(c.max_residual(), a, rhs, candidate);
                    }
                }
            );
        }
    }

    if let Ok(matrix) = DominantTridiagonal::new(&a.lower, &a.diagonal, &a.upper) {
        assert!(finite);
        let margin = matrix.dominance_margin();
        if n > 0 {
            let exact_margin = (0..n)
                .map(|i| {
                    let mut m = magnitude(a.diagonal[i]);
                    if i > 0 {
                        m = sub(&m, &magnitude(a.lower[i - 1]));
                    }
                    if i + 1 < n {
                        m = sub(&m, &magnitude(a.upper[i]));
                    }
                    m
                })
                .reduce(|x, y| x.min(&y))
                .expect("a row");
            assert!(
                margin > 0.0 && exact(margin) <= exact_margin,
                "dominance margin"
            );
        } else {
            assert_eq!(margin, 0.0);
        }
        factored!(
            matrix,
            |factors: morphiq_numerics::linalg::tridiagonal::ThomasFactors| {
                if let Ok(c) = factors.certify(rhs, candidate) {
                    check_residual_bound(c.max_residual(), a, rhs, candidate);
                    // The 8000-bit solution's own error is far below this slack.
                    let slack = exact(f64::from_bits(1)) >> 4000;
                    for (x, solution) in candidate.iter().zip(accurate_solution(a, rhs)) {
                        let distance = Float::with_val(8000, *x - &solution).abs();
                        let allowed = Float::with_val(8000, c.max_solution_error() + &slack);
                        assert!(distance <= allowed, "solution error certificate");
                    }
                }
            }
        );
    }
}

/// Byte 0 selects intervals or tridiagonal systems. For a system, byte 1 holds
/// the order and how coefficients are shaped; words follow, cycled to length.
pub fn check_input(data: &[u8]) {
    let [selector, shape, data @ ..] = data else {
        return;
    };
    let words: Vec<f64> = data
        .as_chunks::<8>()
        .0
        .iter()
        .take(64)
        .map(|w| f64::from_bits(u64::from_le_bytes(*w)))
        .collect();
    if words.is_empty() {
        return;
    }
    if selector % 2 == 0 {
        check_intervals(&words);
        return;
    }
    let n = usize::from(shape % (ORDER as u8 + 1));
    let mut next = words.iter().copied().cycle();
    let mut take = |count: usize| -> Vec<f64> { next.by_ref().take(count).collect() };
    let mut a = System {
        lower: take(n.saturating_sub(1)),
        diagonal: take(n),
        upper: take(n.saturating_sub(1)),
    };
    // Optionally shape the matrix so the admitted domains are reachable.
    if shape / 16 % 2 == 1 {
        for i in 0..n {
            let mut sum = 1.0 + a.diagonal[i].abs();
            if i > 0 {
                sum += a.lower[i - 1].abs();
            }
            if i + 1 < n {
                sum += a.upper[i].abs();
            }
            a.diagonal[i] = sum;
        }
    }
    if shape / 32 % 2 == 1 {
        for (l, u) in a.lower.iter_mut().zip(&mut a.upper) {
            *l = -l.abs();
            *u = if shape / 64 % 2 == 1 {
                -u.abs()
            } else {
                u.abs()
            };
        }
    }
    let rhs = take(n);
    let obstacle = take(n);
    let candidate = take(n);
    check_system(&a, &rhs, &obstacle, &candidate);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn packet(selector: u8, shape: u8, words: &[f64]) -> Vec<u8> {
        let mut data = vec![selector, shape];
        data.extend(words.iter().flat_map(|x| x.to_bits().to_le_bytes()));
        data
    }

    #[test]
    fn boundary_intervals_satisfy_their_contracts() {
        let tiny = f64::from_bits(1);
        let values = [
            0.0,
            -0.0,
            tiny,
            -tiny,
            0.5,
            1.0,
            -1.0,
            2.0,
            709.782712893384,
            710.0,
            -1000.0,
            1.0e154,
            -1.0e155,
            f64::MIN_POSITIVE,
            f64::MAX,
            -f64::MAX,
            f64::INFINITY,
            f64::NAN,
        ];
        for a in values {
            for b in values {
                check_input(&packet(0, 0, &[a, b, b, a, a, 1.5, -2.5, b]));
            }
        }
    }

    #[test]
    fn systems_of_every_order_and_shape_satisfy_their_contracts() {
        let well = [0.25, -0.5, 3.0, 1.0, -2.0, 0.125, 5.0, -0.75, 1.0e-3, 4.0];
        let hard = [
            0.0,
            1.0,
            f64::MAX,
            1.0e-300,
            -1.0,
            5.0e-324,
            2.0,
            -0.0,
            1.0e300,
        ];
        for order in 0..=ORDER as u8 {
            for shape in 0..8 {
                check_input(&packet(1, order + 16 * shape, &well));
                check_input(&packet(1, order + 16 * shape, &hard));
            }
        }
    }

    #[test]
    fn the_oracle_rejects_planted_errors() {
        let a = System {
            lower: vec![1.0],
            diagonal: vec![4.0, 4.0],
            upper: vec![1.0],
        };
        let (p, c) = reference_factor(&a).unwrap();
        let x = reference_solve(&a, &p, &c, &[1.0, 2.0], None).unwrap();
        let bound = largest_residual(&a, &[1.0, 2.0], &x).to_f64_round(Round::Up);
        check_residual_bound(bound, &a, &[1.0, 2.0], &x);
        assert!(
            std::panic::catch_unwind(|| check_residual_bound(0.0, &a, &[1.0, 2.0], &[1.0, 1.0]))
                .is_err()
        );
        let narrow = FiniteInterval::new(1.0, 1.0).unwrap();
        assert!(
            std::panic::catch_unwind(|| check_algebraic(
                "planted",
                Ok(narrow),
                &[exact(2.0)],
                (narrow, narrow)
            ))
            .is_err()
        );
    }
}
