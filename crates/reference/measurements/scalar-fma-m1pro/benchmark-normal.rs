use morphiq_numerics::normal::*;
use std::hint::black_box;
use std::time::{Duration, Instant};
fn measure(mut f: impl FnMut(), n: usize) -> f64 {
    let t = Instant::now();
    let mut r = 0;
    loop {
        f();
        r += 1;
        if t.elapsed() >= Duration::from_millis(150) {
            break;
        }
    }
    t.elapsed().as_secs_f64() * 1e9 / (r as f64 * n as f64)
}
fn bench(name: &str, f: impl Fn(f64) -> f64, b: impl Fn(&[f64], &mut [f64])) {
    let x: Vec<_> = (0..1024)
        .map(|i| 10.0 * (f64::from(i) / 1023.0) - 5.0)
        .collect();
    let mut y = vec![0.0; 1024];
    b(&x, &mut y);
    for (&v, &o) in x.iter().zip(&y) {
        assert_eq!(f(v).to_bits(), o.to_bits());
    }
    let s = measure(
        || {
            for (o, &v) in y.iter_mut().zip(black_box(&x)) {
                *o = f(v);
            }
            black_box(&y);
        },
        1024,
    );
    let v = measure(
        || {
            b(black_box(&x), &mut y);
            black_box(&y);
        },
        1024,
    );
    println!("{name},{s:.3},{v:.3}");
}
fn main() {
    for _ in 0..3 {
        bench("pdf", norm_pdf, norm_pdf_slice);
        bench("cdf", norm_cdf, norm_cdf_slice);
        bench("ccdf", norm_ccdf, norm_ccdf_slice);
        bench("centered", norm_cdf_centered, norm_cdf_centered_slice);
        bench("log_cdf", log_norm_cdf, log_norm_cdf_slice);
    }
}
