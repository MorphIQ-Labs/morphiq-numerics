#!/usr/bin/env sh
# Generator replay: every generator in generators/ that writes a committed
# fixture is rerun, and the fixture must match a fresh generation byte for
# byte, so a fixture can't drift from the generator that justifies it.
#
# Generators run in a virtual environment holding exactly
# generators/requirements.txt, installed by hash. A generator joins this list in
# the change that adds it. Their outputs are integer-exact, so they don't
# depend on the Python version.
set -eu
cd "$(dirname "$0")/.."

venv=target/generators-venv
if [ ! -x "$venv/bin/python" ]; then
  python3 -m venv "$venv"
fi
"$venv/bin/python" -m pip install --quiet --require-hashes -r generators/requirements.txt

generators="generators/random_streams_reference.py generators/xoshiro256_jump.py generators/exp_reference.py generators/ln_reference.py generators/exp_constants.py"
for generator in $generators; do
  "$venv/bin/python" "$generator" --check
  echo "replayed: $generator"
done

# Every generator is listed above.
listed=$(echo "$generators" | wc -w | tr -d ' ')
present=$(ls generators/*.py | wc -l | tr -d ' ')
if [ "$present" -ne "$listed" ]; then
  echo "generators/ holds $present generators, but $listed are replayed" >&2
  exit 1
fi
echo "generators: OK"
