#!/usr/bin/env sh
# Writes each Gappa certificate's Coq proof, gappa -Bcoq at the precision the
# certificates are proved at, to formal/<f>/coq/<certificate>.v, or with
# --into DIR to DIR/<f>/<certificate>.v (scripts/check_certificates.sh replays
# it that way). Needs Gappa 1.4.1, as the certificates job pins it.
set -eu
cd "$(dirname "$0")/.."

into=""
if [ "${1:-}" = "--into" ]; then
  into=$2
fi
for dir in formal/exp formal/ln formal/exp2 formal/log2 formal/expm1 formal/trig; do
  f=${dir#formal/}
  out=${into:+$into/$f}
  out=${out:-$dir/coq}
  mkdir -p "$out"
  for certificate in "$dir"/*.g; do
    name=$(basename "$certificate" .g)
    gappa -Bcoq -Eprecision=400 "$certificate" > "$out/$name.v"
  done
done
