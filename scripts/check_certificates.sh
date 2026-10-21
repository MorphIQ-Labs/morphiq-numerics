#!/usr/bin/env sh
# The certificates lane: Sollya approximation bounds and Gappa rounding-error
# bounds, bound to the sources they describe. For each function directory
# formal/<f> (exp, ln, exp2, log2, expm1, trig, asin):
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
for dir in formal/exp formal/ln formal/exp2 formal/log2 formal/expm1 formal/trig formal/normal formal/asin; do
  f=${dir#formal/}
  binding="$dir/binding.sha256"
  # Normal compositions share the end-to-end proof manifest.
  if [ "$f" = normal ]; then binding=formal/binding.sha256; fi
  sha256sum --check --quiet "$binding"
  # A function with its own polynomial replays its Sollya script.
  for polynomial in "generators/${f}_poly.sollya" generators/${f}_*_poly.sollya; do
    [ -f "$polynomial" ] || continue
    sollya "$polynomial" | grep -E '^([a-z]+[0-9]+|[a-z_]*error_bound|[a-z_]*remainder_bound) ' \
      | diff -u "${polynomial%.sollya}.out" -
    echo "replayed: $polynomial"
  done
  for certificate in "$dir"/*.g; do
    # Q256's bounds reach 2^-260: Gappa needs the wider working precision.
    if gappa -Eprecision=400 "$certificate" >/dev/null 2>&1; then
      echo "proved: $certificate"
    else
      echo "not proved: $certificate" >&2
      failed=1
    fi
  done
done


[ "$failed" -eq 0 ]
./scripts/check_erfcx_certificates.sh
echo "certificates: OK"
