#!/usr/bin/env sh
# Build the unpublished LAPACK diagnostic comparator. Requires curl, gcc and
# gfortran; all downloaded source stays in PREFIX with its BSD license.
set -eu
cd "$(dirname "$0")/.."
prefix=${1:?usage: build_tridiagonal_lapack.sh PREFIX}
mkdir -p "$prefix/src"
prefix=$(realpath "$prefix")
revision=6ec7f2bc4ecf4c4a93496aa2fa519575bc0e39ca # Reference LAPACK v3.12.1
for path in SRC/dgttrf.f SRC/dgttrs.f SRC/dgtts2.f SRC/xerbla.f INSTALL/lsame.f \
    SRC/ilaenv.f SRC/iparmq.f SRC/ieeeck.f SRC/iparam2stage.F LICENSE; do
  curl --fail --silent --show-error --location --retry 3 \
    "https://raw.githubusercontent.com/Reference-LAPACK/lapack/$revision/$path" \
    -o "$prefix/src/$(basename "$path")"
done
cp scripts/tridiagonal_lapack.sha256 "$prefix/src/source.sha256"
(cd "$prefix/src" && sha256sum --check source.sha256 && \
  gfortran -O3 -ffp-contract=off -c dgttrf.f dgttrs.f dgtts2.f xerbla.f lsame.f \
    ilaenv.f iparmq.f ieeeck.f iparam2stage.F)
gcc -O3 -ffp-contract=off -c scripts/bench_tridiagonal_lapack.c -o "$prefix/src/bench.o"
gfortran -o "$prefix/bench-lapack" "$prefix/src/bench.o" "$prefix/src/dgttrf.o" \
  "$prefix/src/dgttrs.o" "$prefix/src/dgtts2.o" "$prefix/src/xerbla.o" \
  "$prefix/src/lsame.o" "$prefix/src/ilaenv.o" "$prefix/src/iparmq.o" \
  "$prefix/src/ieeeck.o" "$prefix/src/iparam2stage.o"
{ gcc --version; gfortran --version; sha256sum "$prefix/bench-lapack"; } > "$prefix/build.txt"
