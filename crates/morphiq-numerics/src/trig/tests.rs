//! The reduction against 256-bit references (docs/sin_cos.md §3).

use super::reduce;
use crate::test_exact::{Exact, entries, field, word};

#[test]
fn the_reduction_is_within_its_bound_everywhere() {
    let fixture = include_str!("../../../reference/fixtures/sin_cos.json");
    let cases = entries(fixture, &["reduction"]);
    assert_eq!(cases.len(), 607);
    for c in cases {
        let x = word(c, "x");
        let v = Exact::of_hex(field(c, "m"), field(c, "e").parse().unwrap());
        let reference = if field(c, "negative") == "true" { v.neg() } else { v };
        let (k, r) = reduce(x);
        assert_eq!(k, field(c, "k").parse::<u32>().unwrap(), "k mod 4 for {x:e}");
        assert!(Exact::of_q256(r).within(&reference, 1, 199), "r for {x:e}");
    }
}
