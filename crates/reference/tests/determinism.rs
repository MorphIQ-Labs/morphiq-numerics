//! The determinism digest is the committed one on this target.

use morphiq_numerics_digest::corpus_digest_hex;

#[test]
fn every_output_matches_the_committed_digest() {
    let committed = include_str!("../determinism.sha256").trim();
    let mut buffer = [0; 64];
    let computed = corpus_digest_hex(&mut buffer);
    assert_eq!(
        computed, committed,
        "this target computes a different result for some function. If the change is \
         deliberate, update crates/reference/determinism.sha256 to {computed} and say why \
         in the pull request"
    );
}
