#!/usr/bin/env sh
# Installs the pinned Intel Software Development Emulator (.cargo/sde-version:
# Intel's mirror directory and archive name) into $1, after checking the archive
# against the pinned SHA-256 (.cargo/sde-sha256), which equals the digest Intel
# publishes on the SDE download page. Linux x86_64 only; it runs the AVX-512F
# lane tests (docs/lanes.md §6). SDE is free to use under the Intel Simplified
# Software License; it is downloaded for CI and never redistributed.
set -eu
cd "$(dirname "$0")/.."
prefix=${1:?usage: install_sde.sh PREFIX}
pin=$(cat .cargo/sde-version)
name=${pin#*/}
expected=$(cat .cargo/sde-sha256)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
curl --fail --silent --show-error --location --retry 3 \
  "https://downloadmirror.intel.com/$pin.tar.xz" --output "$work/$name.tar.xz"
actual=$(sha256sum "$work/$name.tar.xz" | cut -d' ' -f1)
if [ "$actual" != "$expected" ]; then
  echo "SDE archive checksum $actual does not match the pin $expected" >&2
  exit 1
fi
mkdir -p "$prefix"
tar -xJf "$work/$name.tar.xz" -C "$prefix" --strip-components=1
"$prefix/sde64" -version | head -n 3
