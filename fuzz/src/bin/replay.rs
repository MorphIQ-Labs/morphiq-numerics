//! Replay seeds or retained libFuzzer failures without a sanitizer/nightly.
use std::{env, fs, path::Path};

fn replay(path: &Path, check: fn(&[u8])) -> usize {
    if path.is_dir() {
        let mut files: Vec<_> = fs::read_dir(path)
            .expect("read corpus directory")
            .map(|entry| entry.expect("read corpus entry").path())
            .collect();
        files.sort();
        files.iter().map(|file| replay(file, check)).sum()
    } else {
        let bytes = fs::read(path).expect("read corpus input");
        eprintln!("replay {}", path.display());
        check(&bytes);
        1
    }
}

fn main() {
    let mut args = env::args_os().skip(1);
    let target = args
        .next()
        .expect("usage: replay TARGET FILE_OR_DIRECTORY ...");
    let check = match target.to_str() {
        Some("elementary") => morphiq_numerics_fuzz::check_input,
        Some("fast_elementary") => morphiq_numerics_fuzz::check_fast_input,
        _ => panic!("unknown fuzz target: {target:?}"),
    };
    let paths: Vec<_> = args.collect();
    assert!(
        !paths.is_empty(),
        "usage: replay TARGET FILE_OR_DIRECTORY ..."
    );
    let count: usize = paths.iter().map(|arg| replay(Path::new(arg), check)).sum();
    assert!(count > 0, "empty replay corpus");
    println!("replayed {count} {target:?} inputs");
}
