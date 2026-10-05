#!/usr/bin/env sh
# RustSec advisories over the locked dependency graph: vulnerabilities,
# unsound, yanked and unmaintained crates all fail. The pin in
# .cargo/audit-version is asserted so local and CI runs use one cargo-audit.
set -eu
cd "$(dirname "$0")/.."
required=$(cat .cargo/audit-version)
installed=$(cargo audit --version 2>/dev/null | sed -n 's/^cargo-audit-audit //p; s/^cargo-audit //p')
if [ "$installed" != "$required" ]; then
  echo "cargo-audit $required is required; install it with:" >&2
  echo "  cargo install --locked cargo-audit --version $required" >&2
  exit 127
fi
cargo audit --deny warnings --deny unsound --deny yanked --deny unmaintained
echo "advisory gate: OK"
