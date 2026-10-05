#!/usr/bin/env sh
# Generator replay: every generator in generators/ that writes a committed
# fixture is rerun, and the fixture must match a fresh generation byte for
# byte, so a fixture can't drift from the generator that justifies it.
#
# A generator joins this list in the change that adds it. Each is pure Python
# with integer-exact output, so the result doesn't depend on the Python version.
set -eu
cd "$(dirname "$0")/.."

for generator in generators/random_streams_reference.py generators/xoshiro256_jump.py; do
  python3 "$generator" --check
  echo "replayed: $generator"
done

# Every generator is listed above.
listed=2
present=$(ls generators/*.py | wc -l | tr -d ' ')
if [ "$present" -ne "$listed" ]; then
  echo "generators/ holds $present generators, but $listed are replayed" >&2
  exit 1
fi
echo "generators: OK"
