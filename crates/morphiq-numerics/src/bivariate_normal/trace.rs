//! The library functions the kernel calls, recording each call while a
//! recording is open, for the cross-check corpus
//! (`internal_crosscheck/bivariate.rs`). The Coq transcription of the kernel
//! (`formal/bivariate/BvnKernel.v`) takes its `exp`, `sin`, `asin` and
//! `norm_cdf` from the results recorded here, so the extracted kernel is
//! compared with this code on the same library results, call for call.
//!
//! Compiled in tests only: the library's own build calls the functions
//! directly.
use std::cell::{Cell, RefCell};
use std::vec::Vec;

/// A library function the kernel calls.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Function {
    Exp,
    Sin,
    Asin,
    NormCdf,
}

/// One call: the function, its argument and its result, as encodings.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Call {
    pub(crate) function: Function,
    pub(crate) argument: u64,
    pub(crate) result: u64,
}

std::thread_local! {
    static ACTIVE: Cell<bool> = const { Cell::new(false) };
    static LOG: RefCell<Vec<Call>> = const { RefCell::new(Vec::new()) };
}

/// Run `f`, returning its result with the library calls it made, in call order.
pub(crate) fn recording<R>(f: impl FnOnce() -> R) -> (R, Vec<Call>) {
    LOG.with(|log| log.borrow_mut().clear());
    ACTIVE.with(|active| active.set(true));
    let result = f();
    ACTIVE.with(|active| active.set(false));
    (
        result,
        LOG.with(|log| core::mem::take(&mut *log.borrow_mut())),
    )
}

fn record(function: Function, argument: f64, result: f64) -> f64 {
    if ACTIVE.with(Cell::get) {
        LOG.with(|log| {
            log.borrow_mut().push(Call {
                function,
                argument: argument.to_bits(),
                result: result.to_bits(),
            });
        });
    }
    result
}

pub(super) fn exp(x: f64) -> f64 {
    record(Function::Exp, x, crate::elementary::exp(x))
}

pub(super) fn sin(x: f64) -> f64 {
    record(Function::Sin, x, crate::elementary::sin(x))
}

pub(super) fn asin(x: f64) -> f64 {
    record(Function::Asin, x, crate::elementary::asin(x))
}

pub(super) fn norm_cdf(x: f64) -> f64 {
    record(Function::NormCdf, x, crate::normal::norm_cdf(x))
}

/// A table's regime (0 independent, 1 comonotone, 2 countermonotone, 3 low,
/// 4 high), `asin(rho)` and each node's `kw`, `p` and `q`, as encodings.
pub(crate) fn table_parts(table: &super::BivariateNormal) -> (u8, u64, Vec<[u64; 3]>) {
    let code = match table.regime {
        super::Regime::Independent => 0,
        super::Regime::Comonotone => 1,
        super::Regime::Countermonotone => 2,
        super::Regime::Low => 3,
        super::Regime::High => 4,
    };
    let nodes = (0..table.nodes)
        .map(|i| {
            [
                table.kw[i].to_bits(),
                table.p[i].to_bits(),
                table.q[i].to_bits(),
            ]
        })
        .collect();
    (code, table.asr.to_bits(), nodes)
}

/// The regime and branches `bivariate_norm_cdf(x, y, rho)` takes, by name, for
/// the corpus writer's coverage account. Each condition is the kernel's own
/// (`super::high_correlation`'s), recomputed.
pub(crate) fn branches(x: f64, y: f64, rho: f64) -> Vec<std::string::String> {
    use std::string::{String, ToString};
    let mut tags: Vec<String> = Vec::new();
    let Ok(table) = super::BivariateNormal::new(rho) else {
        tags.push("invalid-correlation".to_string());
        return tags;
    };
    if rho == 0.0 && rho.is_sign_negative() {
        tags.push("signed-zero-correlation".to_string());
    }
    if (x == 0.0 && x.is_sign_negative()) || (y == 0.0 && y.is_sign_negative()) {
        tags.push("signed-zero-threshold".to_string());
    }
    // The kernel's `x <= y` is false for a NaN operand.
    if x > y || x.is_nan() || y.is_nan() {
        tags.push("swapped".to_string());
    }
    let (x, y) = if x <= y { (x, y) } else { (y, x) };
    if x.is_nan() || y.is_nan() {
        tags.push("nan-threshold".to_string());
        return tags;
    }
    if x <= -super::SATURATED_THRESHOLD {
        tags.push("saturated-lower".to_string());
        return tags;
    }
    if y >= super::SATURATED_THRESHOLD {
        tags.push("saturated-upper".to_string());
        return tags;
    }
    match table.regime {
        super::Regime::Independent => tags.push("independent".to_string()),
        super::Regime::Comonotone => tags.push("comonotone".to_string()),
        super::Regime::Countermonotone => tags.push("countermonotone".to_string()),
        super::Regime::Low => tags.push(std::format!("low-{}", table.nodes)),
        super::Regime::High => {
            let (dh, dk) = (-x, -y);
            let (k, hk) = if rho < 0.0 {
                (-dk, -(dh * dk))
            } else {
                (dk, dh * dk)
            };
            let bs = (dh - k) * (dh - k);
            tags.push(
                if rho < 0.0 {
                    "high-negative"
                } else {
                    "high-positive"
                }
                .to_string(),
            );
            if hk >= super::HK_CUTOFF {
                tags.push("hk-skip".to_string());
                return tags;
            }
            if hk >= 100.0 {
                tags.push("hk-large".to_string());
            }
            if hk >= super::HK_SPLIT {
                tags.push("hk-split".to_string());
            }
            let a = super::sqrt((1.0 - rho.abs()) * (1.0 + rho.abs()));
            let (mut s, mut panels) = (a, 0);
            while s > super::PANEL_FLOOR {
                tags.push(
                    if s > 0.095 {
                        "panel-16-nodes"
                    } else {
                        "panel-15-nodes"
                    }
                    .to_string(),
                );
                panels += 1;
                s /= 2.0;
            }
            tags.push(std::format!("panels-{panels}"));
            if super::sqrt(bs) < 20.0 * s {
                tags.push("closed-form".to_string());
                if hk >= super::HK_SPLIT {
                    tags.push("closed-remainder".to_string());
                }
            } else {
                tags.push("closed-form-skip".to_string());
            }
            if rho < 0.0 {
                tags.push(
                    if -dh > dk {
                        "negative-difference"
                    } else {
                        "negative-zero"
                    }
                    .to_string(),
                );
            }
        }
    }
    tags
}
