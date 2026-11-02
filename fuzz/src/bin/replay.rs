//! Replay seeds or retained libFuzzer failures without a sanitizer/nightly.
use std::{env, fs, path::Path};

fn replay(path: &Path) -> usize {
    if path.is_dir() {
        let mut files: Vec<_> = fs::read_dir(path)
            .expect("read corpus directory")
            .map(|entry| entry.expect("read corpus entry").path())
            .collect();
        files.sort();
        files.iter().map(|file| replay(file)).sum()
    } else {
        let bytes = fs::read(path).expect("read corpus input");
        eprintln!("replay {}", path.display());
        morphiq_numerics_fuzz::check_input(&bytes);
        1
    }
}

fn main() {
    let args: Vec<_> = env::args_os().skip(1).collect();
    assert!(!args.is_empty(), "usage: replay FILE_OR_DIRECTORY ...");
    let count: usize = args.iter().map(|arg| replay(Path::new(arg))).sum();
    assert!(count > 0, "empty replay corpus");
    println!("replayed {count} elementary inputs");
}
