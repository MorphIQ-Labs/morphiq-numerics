
#[test]
#[ignore]
fn measure_accurate_negative() {
    use std::hint::black_box;
    let inputs: std::vec::Vec<f64> = (0..4096).map(|i| -0.5 - f64::from(i) * (26.6 - 0.5) / 4096.0).collect();
    let mut digest = 0_u64;
    for &x in &inputs {
        digest ^= black_box(accurate::accurate(black_box(x))).to_f64().to_bits();
    }
    let start = std::time::Instant::now();
    for &x in &inputs {
        digest ^= black_box(accurate::accurate(black_box(x))).to_f64().to_bits();
    }
    let ns = start.elapsed().as_nanos();
    std::println!("MEASUREMENT,{ns},{},{}", inputs.len(), black_box(digest));
}
