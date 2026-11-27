//! One bounded binary64 window, using the same oracle as the named fuzz target.
use std::{env, path::Path, process};

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args().skip(1).collect();
    if args.len() != 6 {
        return Err("usage: sweep TARGET OP FIRST_HEX LAST_HEX SECOND_HEX FAILURE_PACKET".into());
    }
    let op = args[1]
        .parse::<u8>()
        .map_err(|e| format!("operation: {e}"))?;
    let bits = |text: &str| {
        if text.len() != 16 || !text.bytes().all(|b| b.is_ascii_hexdigit()) {
            return Err("encodings must be exactly 16 hexadecimal digits".to_owned());
        }
        u64::from_str_radix(text, 16).map_err(|e| e.to_string())
    };
    let count = morphiq_numerics_fuzz::sweep::check_window(
        &args[0],
        op,
        bits(&args[2])?,
        bits(&args[3])?,
        bits(&args[4])?,
        Path::new(&args[5]),
    )?;
    println!("{count}");
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        process::exit(1);
    }
}
