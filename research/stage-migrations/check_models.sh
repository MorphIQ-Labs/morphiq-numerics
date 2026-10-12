#!/usr/bin/env sh
# Conditional Gappa models only; this does not prove the Rust candidates.
# Run from the repository root with Python 3 and Gappa 1.4.1 on PATH.
# The certificates job's pinned Debian image/package can supply Gappa.
set -eu
cd "$(dirname "$0")/../.."
case "$(gappa --version)" in
  'Gappa 1.4.1') ;;
  *) echo 'Gappa 1.4.1 is required' >&2; exit 1 ;;
esac
sha256sum --check --quiet research/stage-migrations/binding.sha256
python3 research/stage-migrations/certificates.py --check
for model in research/stage-migrations/certificates/*.g; do
  gappa -Eprecision=400 "$model"
  echo "conditional model proved: $model"
done
