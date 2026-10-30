//! C ABI over Risk's own `log_norm_cdf` (Cody rational erfcx with the platform
//! logarithm), the declared cost comparator for the bounded log-CDF. Risk has
//! no public log-CDF slice: its packet entry is the scalar loop it would run.
#[unsafe(no_mangle)]
pub extern "C" fn prod_log_norm_cdf(x: f64) -> f64 {
    morphiq_risk::numerics::log_norm_cdf(x)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn prod_log_norm_cdf_slice(x: *const f64, y: *mut f64, n: usize) {
    let (x, y) = unsafe {
        (
            std::slice::from_raw_parts(x, n),
            std::slice::from_raw_parts_mut(y, n),
        )
    };
    for (y, &x) in y.iter_mut().zip(x) {
        *y = morphiq_risk::numerics::log_norm_cdf(x);
    }
}
