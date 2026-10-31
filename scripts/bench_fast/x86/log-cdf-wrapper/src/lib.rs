//! C ABI over the public bounded and strong log-CDF entries for the native timer.
#[unsafe(no_mangle)]
pub extern "C" fn prod_log_norm_cdf(x: f64) -> f64 {
    morphiq_numerics::fast::normal::log_norm_cdf(x)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn prod_log_norm_cdf_slice(x: *const f64, y: *mut f64, n: usize) {
    unsafe {
        morphiq_numerics::fast::normal::log_norm_cdf_slice(
            std::slice::from_raw_parts(x, n),
            std::slice::from_raw_parts_mut(y, n),
        );
    }
}
#[unsafe(no_mangle)]
pub extern "C" fn control_log_norm_cdf(x: f64) -> f64 {
    morphiq_numerics::normal::log_norm_cdf(x)
}
#[unsafe(no_mangle)]
pub unsafe extern "C" fn control_log_norm_cdf_slice(x: *const f64, y: *mut f64, n: usize) {
    unsafe {
        morphiq_numerics::normal::log_norm_cdf_slice(
            std::slice::from_raw_parts(x, n),
            std::slice::from_raw_parts_mut(y, n),
        );
    }
}
