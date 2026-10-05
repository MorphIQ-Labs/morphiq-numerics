//! The determinism digest is the committed one on this target.

use morphiq_numerics_reference::determinism::corpus_digest;

#[test]
fn every_output_matches_the_committed_digest() {
    let committed = include_str!("../determinism.sha256").trim();
    let computed = corpus_digest();
    assert_eq!(
        computed, committed,
        "this target computes a different result for some function. If the change is \
         deliberate, update crates/reference/determinism.sha256 to {computed} and say why \
         in the pull request"
    );
}
