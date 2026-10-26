#!/usr/bin/env sh
# Writes each Gappa certificate's Coq proof (gappa -Bcoq, at the precision the
# certificates are proved at) to DIR/<f>/<certificate>.v, for the formal lane
# (scripts/check_formal.sh). Gappa's proof search can take a different, equally
# valid route on a different host, so the proofs are written where they are
# checked rather than committed; the theorem each states comes from the bound
# certificate. Needs Gappa 1.4.1, as the certificates and formal jobs pin it.
#
# Its route can differ between two runs on one host, so a proof is rewritten
# only when its certificate's bytes (or the Gappa invocation) differ from those
# it was written from, recorded in DIR/.stamps. A directory restored from CI's
# cache then keeps the proofs of unchanged certificates byte for byte, and the
# proof build reuses what it compiled from them. Coq checks every proof it
# compiles, so which valid route a proof takes is not what the lane rests on.
set -eu
if [ $# -ne 1 ]; then
  echo "usage: $0 <output directory>" >&2
  exit 2
fi
out=$1
cd "$(dirname "$0")/.."

for dir in formal/exp formal/ln formal/exp2 formal/log2 formal/expm1 formal/trig formal/erfcx formal/normal formal/asin formal/asinh formal/atan2; do
  f=${dir#formal/}
  mkdir -p "$out/$f" "$out/.stamps/$f"
  # Reusing an output directory must not retain proofs of removed certificates.
  for proof in "$out/$f"/*.v; do
    [ -f "$proof" ] || continue
    if [ ! -f "$dir/$(basename "$proof" .v).g" ]; then
      rm "$proof" "$out/.stamps/$f/$(basename "$proof" .v)"
    fi
  done
  for certificate in "$dir"/*.g; do
    name=$(basename "$certificate" .g)
    stamp=$(printf '%s\n' "-Bcoq -Eprecision=400" | cat - "$certificate" | sha256sum | cut -d' ' -f1)
    if [ -f "$out/$f/$name.v" ] && [ "$(cat "$out/.stamps/$f/$name" 2>/dev/null)" = "$stamp" ]; then
      continue
    fi
    # Written whole or not at all: an interrupted run must not leave a proof
    # that a later run takes for the certificate's.
    rm -f "$out/.stamps/$f/$name"
    gappa -Bcoq -Eprecision=400 "$certificate" > "$out/$f/$name.v.tmp"
    mv "$out/$f/$name.v.tmp" "$out/$f/$name.v"
    printf '%s\n' "$stamp" > "$out/.stamps/$f/$name"
  done
done
