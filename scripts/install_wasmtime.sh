#!/usr/bin/env sh
# Installs the pinned wasmtime (.cargo/wasmtime-version) into $1/bin, after
# checking the release archive against the pinned SHA-256 (.cargo/wasmtime-sha256),
# which equals the digest GitHub records for the release asset. Linux x86_64 and
# aarch64 only; it is the runner for the wasm32-wasip1 digest.
set -eu
cd "$(dirname "$0")/.."
prefix=${1:?usage: install_wasmtime.sh PREFIX}
version=$(cat .cargo/wasmtime-version)
arch=$(uname -m)
case "$arch" in
  x86_64 | aarch64) ;;
  arm64) arch=aarch64 ;;
  *) echo "no pinned wasmtime for $arch" >&2; exit 1 ;;
esac
expected=$(awk -v a="$arch" '$1 == a { print $2 }' .cargo/wasmtime-sha256)
name="wasmtime-v$version-$arch-linux"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
curl --fail --silent --show-error --location --retry 3 \
  "https://github.com/bytecodealliance/wasmtime/releases/download/v$version/$name.tar.xz" \
  --output "$work/$name.tar.xz"
actual=$(sha256sum "$work/$name.tar.xz" | cut -d' ' -f1)
if [ "$actual" != "$expected" ]; then
  echo "wasmtime archive checksum $actual does not match the pin $expected" >&2
  exit 1
fi
tar -xJf "$work/$name.tar.xz" -C "$work"
mkdir -p "$prefix/bin"
cp "$work/$name/wasmtime" "$prefix/bin/wasmtime"
"$prefix/bin/wasmtime" --version
