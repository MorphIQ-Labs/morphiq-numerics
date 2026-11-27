//! Deterministic enumeration of bounded, contiguous binary64 encoding windows.
use std::{fs, path::Path};

/// Keep one invocation bounded independently of the caller's manifest.
const MAX_INPUTS: u64 = 1_048_576;
const LANES: usize = 65;

/// What a window's encodings mean.
#[derive(Clone, Copy, PartialEq)]
enum Domain {
    /// Finite binary64 inputs of one sign.
    Float,
    /// Raw 64-bit words.
    Word,
}

/// One fuzz target's packet layout: a header, then up to `lanes` records of the
/// swept word followed by `fixed` fixed words.
#[derive(Clone, Copy)]
struct Target {
    name: &'static str,
    operations: u8,
    /// The header is the operation selector; otherwise it is `header`.
    selects_operation: bool,
    header: &'static [u8],
    fixed: usize,
    lanes: usize,
    domain: Domain,
    check: fn(&[u8]),
}

const TARGETS: [Target; 10] = [
    Target {
        name: "elementary",
        operations: 14,
        selects_operation: true,
        header: &[],
        fixed: 1,
        lanes: 16,
        domain: Domain::Float,
        check: super::check_input,
    },
    Target {
        name: "fast_elementary",
        operations: 3,
        selects_operation: true,
        header: &[],
        fixed: 1,
        lanes: LANES,
        domain: Domain::Float,
        check: super::check_fast_input,
    },
    Target {
        name: "fast_normal",
        operations: 3,
        selects_operation: true,
        header: &[],
        fixed: 1,
        lanes: LANES,
        domain: Domain::Float,
        check: super::fast_normal::check_input,
    },
    Target {
        name: "strong_normal",
        operations: 3,
        selects_operation: true,
        header: &[],
        fixed: 1,
        lanes: LANES,
        domain: Domain::Float,
        check: super::strong_normal::check_input,
    },
    Target {
        name: "strong_density",
        operations: 4,
        selects_operation: true,
        header: &[],
        fixed: 1,
        lanes: LANES,
        domain: Domain::Float,
        check: super::strong_density::check_input,
    },
    Target {
        name: "bivariate",
        operations: 1,
        selects_operation: false,
        header: &[0],
        fixed: 2,
        lanes: 8,
        domain: Domain::Float,
        check: super::bivariate::check_input,
    },
    Target {
        name: "reductions",
        operations: 1,
        selects_operation: false,
        header: &[2, 0, 0],
        fixed: 1,
        lanes: 32,
        domain: Domain::Float,
        check: super::reductions::check_input,
    },
    Target {
        name: "arithmetic",
        operations: 1,
        selects_operation: false,
        header: &[],
        fixed: 3,
        lanes: 16,
        domain: Domain::Float,
        check: super::arithmetic::check_input,
    },
    Target {
        name: "structures",
        operations: 1,
        selects_operation: false,
        header: &[0, 0],
        fixed: 1,
        lanes: 4,
        domain: Domain::Float,
        check: super::structures::check_input,
    },
    Target {
        name: "streams",
        operations: 1,
        selects_operation: false,
        header: &[],
        fixed: 1,
        lanes: LANES,
        domain: Domain::Word,
        check: super::streams::check_input,
    },
];

fn target(name: &str) -> Result<Target, String> {
    TARGETS
        .into_iter()
        .find(|t| t.name == name)
        .ok_or_else(|| format!("unknown sweep target: {name}"))
}

#[derive(Clone)]
struct Window {
    of: Target,
    selector: u8,
    first: u64,
    last: u64,
    /// The records' fixed words: zeros where the window gives none.
    fixed: Vec<u64>,
}

impl Window {
    fn new(of: Target, selector: u8, first: u64, last: u64, fixed: &[u64]) -> Result<Self, String> {
        if selector >= of.operations {
            return Err(format!(
                "{} has operations 0 to {}",
                of.name,
                of.operations - 1
            ));
        }
        if first > last
            || of.domain == Domain::Float
                && (first >> 63 != last >> 63
                    || !f64::from_bits(first).is_finite()
                    || !f64::from_bits(last).is_finite())
        {
            return Err("window must have ordered finite encodings with one sign".into());
        }
        if last - first >= MAX_INPUTS {
            return Err(format!("window exceeds {MAX_INPUTS} inputs"));
        }
        if fixed.len() > of.fixed {
            return Err(format!("{} takes {} fixed words", of.name, of.fixed));
        }
        let mut fixed = fixed.to_vec();
        fixed.resize(of.fixed, 0);
        Ok(Self {
            of,
            selector,
            first,
            last,
            fixed,
        })
    }

    fn visit(&self, mut check: impl FnMut(&[u8]) -> Result<(), String>) -> Result<u64, String> {
        let mut next = self.first;
        let mut checked = 0;
        loop {
            let remaining = (self.last - next).saturating_add(1);
            let count = remaining.min(self.of.lanes as u64) as usize;
            let mut packet = if self.of.selects_operation {
                vec![self.selector]
            } else {
                self.of.header.to_vec()
            };
            for i in 0..count {
                packet.extend_from_slice(&(next + i as u64).to_le_bytes());
                for word in &self.fixed {
                    packet.extend_from_slice(&word.to_le_bytes());
                }
            }
            check(&packet)?;
            checked += count as u64;
            if next + (count as u64 - 1) == self.last {
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
    fixed: &[u64],
    failure: &Path,
) -> Result<u64, String> {
    let of = target(name)?;
    Window::new(of, selector, first, last, fixed)?.visit(|packet| check_packet(packet, failure, of))
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
                let total = Window::new(of, 2, first, first + count - 1, &[])
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
    fn each_target_receives_its_layout_and_fixed_words() {
        for of in TARGETS {
            let fixed: Vec<u64> = (0..of.fixed as u64).map(|i| 7 + i).collect();
            let header = if of.selects_operation {
                1
            } else {
                of.header.len()
            };
            let record = 8 * (1 + of.fixed);
            let mut observed = Vec::new();
            Window::new(of, 0, 0, 99, &fixed)
                .unwrap()
                .visit(|packet| {
                    let body = &packet[header..];
                    assert!(body.len() % record == 0 && body.len() / record <= of.lanes);
                    for r in body.chunks(record) {
                        observed.push(u64::from_le_bytes(r[..8].try_into().unwrap()));
                        for (i, word) in fixed.iter().enumerate() {
                            assert_eq!(r[8 * (i + 1)..8 * (i + 2)], word.to_le_bytes());
                        }
                    }
                    Ok(())
                })
                .unwrap();
            assert_eq!(observed, (0..100).collect::<Vec<_>>(), "{}", of.name);
            assert!(Window::new(of, of.operations, 0, 1, &[]).is_err());
            assert!(Window::new(of, 0, 0, 1, &vec![0; of.fixed + 1]).is_err());
        }
        assert!(target("unknown").is_err());
    }

    #[test]
    fn word_windows_reach_the_largest_word() {
        let of = target("streams").unwrap();
        let count = Window::new(of, 0, u64::MAX - 99, u64::MAX, &[])
            .unwrap()
            .visit(|_| Ok(()));
        assert_eq!(count, Ok(100));
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
            assert!(Window::new(of, op, first, last, &[]).is_err());
        }
    }

    #[test]
    fn a_failed_packet_stops_without_reporting_a_completed_count() {
        let mut calls = 0;
        let of = target("strong_normal").unwrap();
        let result = Window::new(of, 0, 0, 200, &[]).unwrap().visit(|_| {
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
