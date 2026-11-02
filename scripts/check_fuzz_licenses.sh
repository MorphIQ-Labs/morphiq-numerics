#!/usr/bin/env sh
# Keep the shipped graph's permissive-only policy unchanged. Only the separate,
# unpublished black-box oracle graph receives these package/version exceptions.
set -eu
cd "$(dirname "$0")/.."
mkdir -p target/fuzz
cat deny.toml > target/fuzz/deny.toml
cat >> target/fuzz/deny.toml <<'POLICY'

[[licenses.exceptions]]
name = "rug"
version = "=1.30.0"
allow = ["LGPL-3.0-or-later"]

[[licenses.exceptions]]
name = "gmp-mpfr-sys"
version = "=1.7.1"
allow = ["LGPL-3.0-or-later"]

[[licenses.exceptions]]
name = "libfuzzer-sys"
version = "=0.4.12"
allow = ["MIT", "NCSA"]
POLICY
cargo deny --manifest-path fuzz/Cargo.toml --all-features --locked \
  --config target/fuzz/deny.toml check licenses
