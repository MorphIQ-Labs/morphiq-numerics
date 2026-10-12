#!/usr/bin/env sh
# Installs the release workflow's tools into $1/bin: release-plz
# (.cargo/release-plz-version) and cargo-semver-checks
# (.cargo/semver-checks-version), each after checking its release archive
# against the pinned SHA-256 (.cargo/*-sha256), which equals the digest GitHub
# records for the release asset. Linux x86_64 only; it is the release runner.
set -eu
cd "$(dirname "$0")/.."
prefix=${1:?usage: install_release_tools.sh PREFIX}
arch=$(uname -m)
[ "$arch" = x86_64 ] || { echo "no pinned release tools for $arch" >&2; exit 1; }
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir -p "$prefix/bin"

# install NAME PIN URL BINARY
install() {
  expected=$(awk -v a="$arch" '$1 == a { print $2 }' ".cargo/$2-sha256")
  curl --fail --silent --show-error --location --retry 3 "$3" --output "$work/$1.tar.gz"
  actual=$(sha256sum "$work/$1.tar.gz" | cut -d' ' -f1)
  if [ "$actual" != "$expected" ]; then
    echo "$1 archive checksum $actual does not match the pin $expected" >&2
    exit 1
  fi
  mkdir "$work/$1"
  tar -xzf "$work/$1.tar.gz" -C "$work/$1"
  cp "$work/$1/$4" "$prefix/bin/$4"
}

version=$(cat .cargo/release-plz-version)
install release-plz release-plz \
  "https://github.com/release-plz/release-plz/releases/download/release-plz-v$version/release-plz-$arch-unknown-linux-gnu.tar.gz" \
  release-plz
version=$(cat .cargo/semver-checks-version)
install cargo-semver-checks semver-checks \
  "https://github.com/obi1kenobi/cargo-semver-checks/releases/download/v$version/cargo-semver-checks-$arch-unknown-linux-gnu.tar.gz" \
  cargo-semver-checks

"$prefix/bin/release-plz" --version
"$prefix/bin/cargo-semver-checks" semver-checks --version
