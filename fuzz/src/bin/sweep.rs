//! One bounded binary64 window, using the same oracle as the named fuzz target.
use std::{env, path::Path, process};

/// `--f32 TARGET OP FIRST_HEX LAST_HEX FAILURE_PACKET`, with 8-digit encodings.
fn run_narrow(args: &[String]) -> Result<(), String> {
    let [target, op, first, last, failure] = args else {
        return Err("usage: sweep --f32 TARGET OP FIRST_HEX LAST_HEX FAILURE_PACKET".into());
    };
    let bits = |text: &str| {
        if text.len() != 8 || !text.bytes().all(|b| b.is_ascii_hexdigit()) {
            return Err("encodings must be exactly 8 hexadecimal digits".to_owned());
        }
        u32::from_str_radix(text, 16).map_err(|e| e.to_string())
    };
    let count = morphiq_numerics_fuzz::sweep::check_narrow_window(
        target,
        op.parse().map_err(|e| format!("operation: {e}"))?,
        bits(first)?,
        bits(last)?,
        Path::new(failure),
    )?;
    println!("{count}");
    Ok(())
}

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args().skip(1).collect();
    if args.first().is_some_and(|a| a == "--f32") {
        return run_narrow(&args[1..]);
    }
    if args.len() < 5 {
        return Err(
            "usage: sweep TARGET OP FIRST_HEX LAST_HEX FAILURE_PACKET [FIXED_HEX ...]".into(),
        );
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
        &args[5..]
            .iter()
            .map(|word| bits(word))
            .collect::<Result<Vec<_>, _>>()?,
        Path::new(&args[4]),
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
