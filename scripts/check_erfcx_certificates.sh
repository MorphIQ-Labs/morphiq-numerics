#!/usr/bin/env sh
# Component certificates for the erfcx table evaluator. The remaining regions
# and the end-to-end proof must be supplied before this draft can ship.
set -eu
cd "$(dirname "$0")/.."
sha256sum --check --quiet formal/erfcx/binding.sha256
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
sollya generators/erfcx/tables.sollya > "$work/tables.out"
diff -u generators/erfcx/tables.out "$work/tables.out"
for certificate in formal/erfcx/*.g; do
    gappa -Eprecision=400 "$certificate" >/dev/null 2>&1
    echo "proved: $certificate"
done
