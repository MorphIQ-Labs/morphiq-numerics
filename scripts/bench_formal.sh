#!/usr/bin/env bash
# Measure cold/warm formal gates in the pinned Coq image, on the same host.
# OUT must be new: never silently turn a requested cold run into a warm one.
# Raw logs and failed attempts are retained; no proof/audit result is cached.
set -euo pipefail
family=()
if [[ ${1:-} == --family ]]; then
  family=(--family "$2")
  shift 2
fi
if [[ $# != 5 ]]; then
  echo "usage: $0 [--family NAME] DEPS PUBLIC-CORPUS INTERNAL-CORPUS GAPPA-PROOFS OUT" >&2
  exit 2
fi
deps=$(realpath "$1")
public=$(realpath "$2")
internal=$(realpath "$3")
proofs=$(realpath "$4")
out=$(realpath -m "$5")
mkdir -p "$(dirname "$out")"
if ! mkdir "$out"; then
  echo "cold measurement requires a new output directory: $out" >&2
  exit 2
fi
mkdir "$out/build"
cd "$(dirname "$0")/.."
{
  git -c safe.directory="$PWD" rev-parse HEAD
  uname -a
  lscpu
  coqc --version
  sha256sum formal/binding.sha256 .cargo/coq-image .cargo/coq-packages "$deps" "$public" "$internal"
  printf 'family=%s\n' "${family[*]:-full}"
} > "$out/environment.txt"
printf 'phase\tstep\tseconds\texit\n' > "$out/timings.tsv"
common=(--deps "$deps" --build "$out/build" "${family[@]}")
measure() {
  local phase=$1 step=$2 started status=0
  shift 2
  started=$(date +%s)
  ./scripts/check_formal.sh "${common[@]}" "$@" "$public" "$internal" "$proofs" \
    2>&1 | tee "$out/$phase-$step.log" || status=$?
  printf '%s\t%s\t%s\t%s\n' "$phase" "$step" "$(( $(date +%s) - started ))" "$status" >> "$out/timings.tsv"
  return "$status"
}
# Match CI's build-only/cache boundary followed by the complete gate. The warm
# pass reuses compiled proofs but reruns every selected audit and extraction.
for phase in cold warm; do
  measure "$phase" build --build-only
  measure "$phase" audit
done
