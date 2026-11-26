//! One bounded binary64 window, using the same oracle as strong-normal fuzzing.
use std::{env, path::Path, process};

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args().skip(1).collect();
    if args.len() != 4 {
        return Err("usage: normal-sweep OP FIRST_HEX LAST_HEX FAILURE_PACKET".into());
    }
    let op = args[0]
        .parse::<u8>()
        .map_err(|e| format!("operation: {e}"))?;
    let bits = |text: &str| {
        if text.len() != 16 || !text.bytes().all(|b| b.is_ascii_hexdigit()) {
            return Err("endpoints must be exactly 16 hexadecimal digits".to_owned());
        }
        u64::from_str_radix(text, 16).map_err(|e| e.to_string())
    };
    let first = bits(&args[1])?;
    let last = bits(&args[2])?;
    let count =
        morphiq_numerics_fuzz::normal_sweep::check_window(op, first, last, Path::new(&args[3]))?;
    println!("{count}");
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        process::exit(1);
    }
}
