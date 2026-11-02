#![no_main]

libfuzzer_sys::fuzz_target!(|data: &[u8]| {
    morphiq_numerics_fuzz::check_input(data);
});
