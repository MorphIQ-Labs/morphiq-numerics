#![no_main]
libfuzzer_sys::fuzz_target!(|data: &[u8]| {
    morphiq_numerics_fuzz::bivariate::check_input(data);
});
