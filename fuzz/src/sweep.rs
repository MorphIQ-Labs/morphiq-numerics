//! Deterministic enumeration of bounded, contiguous binary64 encoding windows.
use std::{fs, path::Path};

/// Keep one invocation bounded independently of the caller's manifest.
const MAX_INPUTS: u64 = 1_048_576;
const LANES: usize = 65;

/// One fuzz target's packet layout: up to `lanes` records of an input word and
/// a second word, after a one-byte operation selector.
#[derive(Clone, Copy)]
struct Target {
    name: &'static str,
    operations: u8,
    lanes: usize,
    check: fn(&[u8]),
}

const TARGETS: [Target; 5] = [
    Target {
        name: "elementary",
        operations: 14,
        lanes: 16,
        check: super::check_input,
    },
    Target {
        name: "fast_elementary",
        operations: 3,
        lanes: LANES,
        check: super::check_fast_input,
    },
    Target {
        name: "fast_normal",
        operations: 3,
        lanes: LANES,
        check: super::fast_normal::check_input,
    },
    Target {
        name: "strong_normal",
        operations: 3,
        lanes: LANES,
        check: super::strong_normal::check_input,
    },
    Target {
        name: "strong_density",
        operations: 4,
        lanes: LANES,
        check: super::strong_density::check_input,
    },
];

fn target(name: &str) -> Result<Target, String> {
    TARGETS
        .into_iter()
        .find(|t| t.name == name)
        .ok_or_else(|| format!("unknown sweep target: {name}"))
}

#[derive(Clone, Copy)]
struct Window {
    selector: u8,
    first: u64,
    last: u64,
    /// The fixed second argument; zero for one-argument functions.
    second: u64,
    lanes: usize,
}

impl Window {
    fn new(of: Target, selector: u8, first: u64, last: u64, second: u64) -> Result<Self, String> {
        if selector >= of.operations {
            return Err(format!(
                "{} has operations 0 to {}",
                of.name,
                of.operations - 1
            ));
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
            second,
            lanes: of.lanes,
        })
    }

    fn visit(self, mut check: impl FnMut(&[u8]) -> Result<(), String>) -> Result<u64, String> {
        let mut next = self.first;
        let mut checked = 0;
        loop {
            let count = (self.last - next + 1).min(self.lanes as u64) as usize;
            let mut packet = [0_u8; 1 + 16 * LANES];
            packet[0] = self.selector;
            for i in 0..count {
                let start = 1 + 16 * i;
                packet[start..start + 8].copy_from_slice(&(next + i as u64).to_le_bytes());
                packet[start + 8..start + 16].copy_from_slice(&self.second.to_le_bytes());
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

/// Check every encoding in an inclusive window against the named fuzz target's
/// oracle, including its scalar/slice identity. On an oracle panic, retain the
/// exact packet for the existing replay tool and return failure, never partial
/// success.
pub fn check_window(
    name: &str,
    selector: u8,
    first: u64,
    last: u64,
    second: u64,
    failure: &Path,
) -> Result<u64, String> {
    let of = target(name)?;
    Window::new(of, selector, first, last, second)?
        .visit(|packet| check_packet(packet, failure, of))
}

fn check_packet(packet: &[u8], failure: &Path, of: Target) -> Result<(), String> {
    if std::panic::catch_unwind(|| (of.check)(packet)).is_err() {
        fs::write(failure, packet).map_err(|e| format!("retain failing packet: {e}"))?;
        return Err(format!(
            "oracle failed; replay {} {}",
            of.name,
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
                let of = target("strong_normal").unwrap();
                let total = Window::new(of, 2, first, first + count - 1, 0)
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
    fn each_target_receives_its_lane_count_and_the_fixed_second_argument() {
        for of in TARGETS {
            let mut lanes = 0;
            Window::new(of, 0, 0, 99, 7)
                .unwrap()
                .visit(|packet| {
                    let records = packet[1..].as_chunks::<16>().0;
                    lanes = lanes.max(records.len());
                    assert!(records.iter().all(|r| r[8..] == 7_u64.to_le_bytes()));
                    Ok(())
                })
                .unwrap();
            assert_eq!(lanes, of.lanes, "{}", of.name);
            assert!(Window::new(of, of.operations, 0, 1, 0).is_err());
        }
        assert!(target("unknown").is_err());
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
            let of = target("strong_normal").unwrap();
            assert!(Window::new(of, op, first, last, 0).is_err());
        }
    }

    #[test]
    fn a_failed_packet_stops_without_reporting_a_completed_count() {
        let mut calls = 0;
        let of = target("strong_normal").unwrap();
        let result = Window::new(of, 0, 0, 200, 0).unwrap().visit(|_| {
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
        let path =
            std::env::temp_dir().join(format!("morphiq-sweep-{}.packet", std::process::id()));
        let packet = [2, 1, 2, 3, 4];
        let planted = Target {
            check: |_| panic!("planted oracle failure"),
            ..target("strong_normal").unwrap()
        };
        let result = check_packet(&packet, &path, planted);
        assert!(result.is_err());
        assert_eq!(fs::read(&path).unwrap(), packet);
        fs::remove_file(path).unwrap();
    }
}
