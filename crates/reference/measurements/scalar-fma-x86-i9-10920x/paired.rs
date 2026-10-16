use std::{hint::black_box, time::Instant};
fn measure(f: impl Fn(f64) -> f64, xs: &[f64], out: &mut [f64]) -> f64 {
    let t = Instant::now();
    let mut rounds = 0;
    loop {
        for (o, &x) in out.iter_mut().zip(black_box(xs)) {
            *o = f(x);
        }
        black_box(&mut *out);
        rounds += 1;
        if t.elapsed().as_millis() >= 10 {
            break;
        }
    }
    t.elapsed().as_secs_f64() * 1e9 / (rounds * xs.len()) as f64
}
fn bench(
    name: &str,
    range: &str,
    low: f64,
    width: f64,
    a: impl Fn(f64) -> f64,
    b: impl Fn(f64) -> f64,
    a_batch: fn(&[f64], &mut [f64]),
    b_batch: fn(&[f64], &mut [f64]),
) {
    let mut seed = 0x34beac_u64;
    let xs: Vec<_> = (0..4096)
        .map(|_| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            low + width * ((seed >> 11) as f64 / 9007199254740992.0)
        })
        .collect();
    let mut out = vec![0.; xs.len()];
    for &x in &xs {
        assert_eq!(a(x).to_bits(), b(x).to_bits(), "{name} {range} {x}");
    }
    let mut check = vec![0.; xs.len()];
    for f in [a_batch,b_batch] {
        f(&xs, &mut check);
        for (&x,&y) in xs.iter().zip(&check) { assert_eq!(a(x).to_bits(),y.to_bits()); }
    }
    for round in 0..34 {
        for i in 0..2 {
            let side = (i + round) % 2;
            let ns = if side == 0 {
                measure(&a, &xs, &mut out)
            } else {
                measure(&b, &xs, &mut out)
            };
            if round > 0 { println!("{name},{range},scalar,{round},{side},{ns:.5}"); }
            let f = if side==0 {a_batch} else {b_batch};
            let t=Instant::now();let mut repeats=0;
            while t.elapsed().as_millis()<10 {f(black_box(&xs),&mut out);black_box(&out);repeats+=1;}
            let batch=t.elapsed().as_secs_f64()*1e9/(repeats*xs.len()) as f64;
            if round>0 {println!("{name},{range},batch,{round},{side},{batch:.5}");}
        }
    }
}
fn main() {
    println!("function,range,mode,round,variant,ns");
    bench(
        "pdf",
        "ordinary",
        -5.,
        10.,
        before::normal::norm_pdf,
        after::normal::norm_pdf,
        before::normal::norm_pdf_slice,
        after::normal::norm_pdf_slice,
    );
    bench(
        "cdf",
        "ordinary",
        -5.,
        10.,
        before::normal::norm_cdf,
        after::normal::norm_cdf,
        before::normal::norm_cdf_slice,
        after::normal::norm_cdf_slice,
    );
    bench(
        "ccdf",
        "ordinary",
        -5.,
        10.,
        before::normal::norm_ccdf,
        after::normal::norm_ccdf,
        before::normal::norm_ccdf_slice,
        after::normal::norm_ccdf_slice,
    );
    bench(
        "centered",
        "ordinary",
        -5.,
        10.,
        before::normal::norm_cdf_centered,
        after::normal::norm_cdf_centered,
        before::normal::norm_cdf_centered_slice,
        after::normal::norm_cdf_centered_slice,
    );
    bench(
        "log_cdf",
        "ordinary",
        -5.,
        10.,
        before::normal::log_norm_cdf,
        after::normal::log_norm_cdf,
        before::normal::log_norm_cdf_slice,
        after::normal::log_norm_cdf_slice,
    );
    for (name, l, w) in [
        ("table", -0.5, 16.5),
        ("positive_common", 0., 6.),
        ("asymptotic", 16., 496.),
        ("reciprocal", 512., 4096.),
        ("negative", -26.6, 26.1),
    ] {
        bench(
            "erfcx",
            name,
            l,
            w,
            before::normal::erfcx,
            after::normal::erfcx,
        before::normal::erfcx_slice,
        after::normal::erfcx_slice,
        );
    }
}
