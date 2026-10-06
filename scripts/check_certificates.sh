#!/usr/bin/env sh
# The certificates lane: Sollya approximation bounds and Gappa rounding-error
# bounds, bound to the sources they describe.
#
#   1. formal/exp/binding.sha256 matches: a change to the derivation, the
#      generated constants or a certificate fails until the certificates are
#      rerun and the manifest is updated with them.
#   2. generators/exp_poly.sollya reproduces generators/exp_poly.out exactly.
#   3. Every Gappa certificate in formal/exp proves its goal.
#
# Runs in the pinned image of the certificates job (.github/workflows/ci.yml),
# which provides Sollya 8.0 and Gappa 1.4.1.
set -eu
cd "$(dirname "$0")/.."

sha256sum --check --quiet formal/exp/binding.sha256

sollya generators/exp_poly.sollya | grep -E '^(c[3-6]|error_bound) ' | diff -u generators/exp_poly.out -
echo "replayed: generators/exp_poly.sollya"

failed=0
for certificate in formal/exp/*.g; do
  if gappa -Eprecision=300 "$certificate" >/dev/null 2>&1; then
    echo "proved: $certificate"
  else
    echo "not proved: $certificate" >&2
    failed=1
  fi
done
[ "$failed" -eq 0 ]
echo "certificates: OK"
