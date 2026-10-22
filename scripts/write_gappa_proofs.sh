#!/usr/bin/env sh
# Writes each Gappa certificate's Coq proof (gappa -Bcoq, at the precision the
# certificates are proved at) to DIR/<f>/<certificate>.v, for the formal lane
# (scripts/check_formal.sh). Gappa's proof search can take a different, equally
# valid route on a different host, so the proofs are written where they are
# checked rather than committed; the theorem each states comes from the bound
# certificate. Needs Gappa 1.4.1, as the certificates and formal jobs pin it.
set -eu
if [ $# -ne 1 ]; then
  echo "usage: $0 <output directory>" >&2
  exit 2
fi
out=$1
cd "$(dirname "$0")/.."

for dir in formal/exp formal/ln formal/exp2 formal/log2 formal/expm1 formal/trig formal/erfcx formal/normal formal/asin formal/asinh formal/atan2; do
  f=${dir#formal/}
  mkdir -p "$out/$f"
  # Reusing an output directory must not retain proofs of removed certificates.
  for proof in "$out/$f"/*.v; do
    [ -f "$proof" ] || continue
    if [ ! -f "$dir/$(basename "$proof" .v).g" ]; then
      rm "$proof"
    fi
  done
  for certificate in "$dir"/*.g; do
    gappa -Bcoq -Eprecision=400 "$certificate" > "$out/$f/$(basename "$certificate" .g).v"
  done
done
