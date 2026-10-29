//! High-word table evaluation for the explicit bounded Gaussian APIs.
use super::{T, f, t_reduce};

#[inline]
pub(crate) fn table(x: f64) -> f64 {
    let (i, _, h, _) = t_reduce(x);
    let a = &T[i];
    let h2 = h * h;
    let p0 = f(a[0]) + h * f(a[2]);
    let p1 = f(a[4]) + h * f(a[6]);
    let p2 = f(a[7]) + h * f(a[8]);
    let p3 = f(a[9]) + h * f(a[10]);
    let p4 = f(a[11]) + h * f(a[12]);
    p0 + h2 * (p1 + h2 * (p2 + h2 * (p3 + h2 * p4)))
}

#[cfg(feature = "simd")]
#[inline(always)]
pub(crate) fn lanes<K: morphiq_numerics_arch::Simd>(k: K, input: K::F) -> K::F {
    let words = k.store(input);
    let mut coefficients = [K::Array::default(); 10];
    let mut h = K::Array::default();
    for (i, &x) in words.as_ref().iter().enumerate() {
        let (index, _, residual, _) = t_reduce(x);
        h.as_mut()[i] = residual;
        for (out, j) in coefficients
            .iter_mut()
            .zip([0, 2, 4, 6, 7, 8, 9, 10, 11, 12])
        {
            out.as_mut()[i] = f(T[index][j]);
        }
    }
    let a = |j: usize| k.load(coefficients[j]);
    let h = k.load(h);
    let h2 = k.mul(h, h);
    let p0 = k.add(a(0), k.mul(h, a(1)));
    let p1 = k.add(a(2), k.mul(h, a(3)));
    let p2 = k.add(a(4), k.mul(h, a(5)));
    let p3 = k.add(a(6), k.mul(h, a(7)));
    let p4 = k.add(a(8), k.mul(h, a(9)));
    k.add(
        p0,
        k.mul(
            h2,
            k.add(
                p1,
                k.mul(h2, k.add(p2, k.mul(h2, k.add(p3, k.mul(h2, p4))))),
            ),
        ),
    )
}
