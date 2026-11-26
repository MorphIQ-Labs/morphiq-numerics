//! Deterministic enumeration of bounded, contiguous binary64 encoding windows.
use std::{fs, path::Path};

/// Keep one invocation bounded independently of the caller's manifest.
const MAX_INPUTS: u64 = 1_048_576;
const LANES: usize = 65;

#[derive(Clone, Copy)]
struct Window {
    selector: u8,
    first: u64,
    last: u64,
}

impl Window {
    fn new(selector: u8, first: u64, last: u64) -> Result<Self, String> {
        if selector > 2 {
            return Err("operation must be 0 (erfcx), 1 (CDF), or 2 (log-CDF)".into());
        }
        if first > last
            || first >> 63 != last >> 63
            || !f64::from_bits(first).is_finite()
            || !f64::from_bits(last).is_finite()
        {
            return Err("window must have ordered finite encodings with one sign".into());
        }
        if last - first >= MAX_INPUTS {
            return Err(format!("window exceeds {MAX_INPUTS} inputs"));
        }
        Ok(Self {
            selector,
            first,
            last,
        })
    }

    fn visit(self, mut check: impl FnMut(&[u8]) -> Result<(), String>) -> Result<u64, String> {
        let mut next = self.first;
        let mut checked = 0;
        loop {
            let count = (self.last - next + 1).min(LANES as u64) as usize;
            let mut packet = [0_u8; 1 + 16 * LANES];
            packet[0] = self.selector;
            for i in 0..count {
                let start = 1 + 16 * i;
                packet[start..start + 8].copy_from_slice(&(next + i as u64).to_le_bytes());
            }
            check(&packet[..1 + 16 * count])?;
            checked += count as u64;
            if next + count as u64 - 1 == self.last {
                return Ok(checked);
            }
            next += count as u64;
        }
    }
}

/// Check every encoding in an inclusive window against the strong-normal
/// oracle and scalar/slice identity. On an oracle panic, retain the exact
/// packet for the existing replay tool and return failure, never partial success.
pub fn check_window(selector: u8, first: u64, last: u64, failure: &Path) -> Result<u64, String> {
    Window::new(selector, first, last)?
        .visit(|packet| check_packet(packet, failure, super::strong_normal::check_input))
}

fn check_packet(packet: &[u8], failure: &Path, check: fn(&[u8])) -> Result<(), String> {
    if std::panic::catch_unwind(|| check(packet)).is_err() {
        fs::write(failure, packet).map_err(|e| format!("retain failing packet: {e}"))?;
        return Err(format!(
            "oracle failed; replay strong_normal {}",
            failure.display()
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn every_encoding_is_visited_once_including_endpoints_and_remainders() {
        for first in [
            0,
            0x8000_0000_0000_0000,
            0x3ff0_0000_0000_0000,
            0x7fef_ffff_ffff_fe00,
            0xffef_ffff_ffff_fe00,
        ] {
            for count in [1, 2, 64, 65, 66, 130, 131, 257] {
                let mut observed = Vec::new();
                let total = Window::new(2, first, first + count - 1)
                    .unwrap()
                    .visit(|packet| {
                        assert_eq!(packet[0], 2);
                        assert!(packet.len() <= 1 + 16 * LANES);
                        for pair in packet[1..].as_chunks::<16>().0 {
                            observed.push(u64::from_le_bytes(pair[..8].try_into().unwrap()));
                            assert_eq!(&pair[8..], &[0; 8]);
                        }
                        Ok(())
                    })
                    .unwrap();
                assert_eq!(total, count);
                assert_eq!(observed, (first..first + count).collect::<Vec<_>>());
            }
        }
    }

    #[test]
    fn invalid_and_unbounded_windows_fail_before_checking_inputs() {
        for (op, first, last) in [
            (3, 0, 1),
            (0, 2, 1),
            (0, 0, MAX_INPUTS),
            (0, 0x7ff0_0000_0000_0000, 0x7ff0_0000_0000_0000),
            (0, 0xfff8_0000_0000_0001, 0xfff8_0000_0000_0001),
            (0, 0x7fef_ffff_ffff_ffff, 0x8000_0000_0000_0000),
        ] {
            assert!(Window::new(op, first, last).is_err());
        }
    }

    #[test]
    fn a_failed_packet_stops_without_reporting_a_completed_count() {
        let mut calls = 0;
        let result = Window::new(0, 0, 200).unwrap().visit(|_| {
            calls += 1;
            if calls == 2 {
                Err("planted failure".into())
            } else {
                Ok(())
            }
        });
        assert_eq!(calls, 2);
        assert_eq!(result, Err("planted failure".into()));
    }

    #[test]
    fn oracle_panics_retain_the_exact_replay_packet_and_remain_failures() {
        let path = std::env::temp_dir().join(format!(
            "morphiq-normal-sweep-{}.packet",
            std::process::id()
        ));
        let packet = [2, 1, 2, 3, 4];
        let result = check_packet(&packet, &path, |_| panic!("planted oracle failure"));
        assert!(result.is_err());
        assert_eq!(fs::read(&path).unwrap(), packet);
        fs::remove_file(path).unwrap();
    }
}
