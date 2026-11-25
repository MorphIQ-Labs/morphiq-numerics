#![no_main]

libfuzzer_sys::fuzz_target!(|data: &[u8]| {
    morphiq_numerics_fuzz::fast_normal::check_input(data);
});
