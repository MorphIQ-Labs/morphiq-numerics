#!/usr/bin/env sh
# The certificates lane: Sollya approximation bounds and Gappa rounding-error
# bounds, bound to the sources they describe. For each function directory
# formal/<f> (exp, ln, exp2, log2, expm1):
#
#   1. formal/<f>/binding.sha256 matches: a change to the derivation, the
#      generated constants or a certificate fails until the certificates are
#      rerun and the manifest is updated with them.
#   2. generators/<f>_poly.sollya, where there is one, reproduces
#      generators/<f>_poly.out exactly.
#   3. Every Gappa certificate in formal/<f> proves its goal.
#
# Runs in the pinned image of the certificates job (.github/workflows/ci.yml),
# which provides Sollya 8.0 and Gappa 1.4.1.
set -eu
cd "$(dirname "$0")/.."

failed=0
for dir in formal/exp formal/ln formal/exp2 formal/log2 formal/expm1; do
  f=${dir#formal/}
  sha256sum --check --quiet "$dir/binding.sha256"
  # A function with its own polynomial replays its Sollya script.
  if [ -f "generators/${f}_poly.sollya" ]; then
    sollya "generators/${f}_poly.sollya" | grep -E '^(c[0-9]+|error_bound|relative_error_bound|remainder_bound) ' \
      | diff -u "generators/${f}_poly.out" -
    echo "replayed: generators/${f}_poly.sollya"
  fi
  for certificate in "$dir"/*.g; do
    if gappa -Eprecision=300 "$certificate" >/dev/null 2>&1; then
      echo "proved: $certificate"
    else
      echo "not proved: $certificate" >&2
      failed=1
    fi
  done
done
[ "$failed" -eq 0 ]
echo "certificates: OK"
