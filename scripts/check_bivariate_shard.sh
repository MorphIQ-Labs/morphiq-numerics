#!/usr/bin/env sh
# Replays one shard of the bivariate-normal reference fixture: the cases whose
# index is congruent to $1 modulo $2. CI runs every shard 0..$2-1, so every row
# is replayed against the committed fixture; BVN_FULL_REPLAY=1 scripts/check_generators.sh
# replays them all on one host.
set -eu
cd "$(dirname "$0")/.."
[ "$#" -eq 2 ] || { echo "usage: $0 <shard> <shards>" >&2; exit 2; }

venv=target/generators-venv
if [ ! -x "$venv/bin/python" ]; then
  python3 -m venv "$venv"
fi
"$venv/bin/python" -m pip install --quiet --require-hashes -r generators/requirements.txt
BVN_WORKERS="${BVN_WORKERS:-$(nproc 2>/dev/null || sysctl -n hw.ncpu)}" \
  "$venv/bin/python" generators/bivariate_normal_reference.py --shard "$1/$2"
