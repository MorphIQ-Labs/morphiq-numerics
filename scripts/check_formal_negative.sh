#!/usr/bin/env sh
# Run one mutation against a COPY of a previously validated proof build.
# Run inside .cargo/coq-image, after check_formal.sh has passed with --build.
# Neither the checkout nor the reusable build is changed. A case passes only
# when the formal gate exits nonzero AND reports the intended rejection.
set -eu
if [ "$#" -ne 6 ]; then
  echo "usage: $0 <binding|admitted|axiom|certificate|crosscheck|internal-crosscheck> <deps.tar.gz> <build> <corpus> <internal corpus> <gappa proofs>" >&2
  exit 2
fi
mutation=$1
deps=$(realpath "$2")
build=$(realpath "$3")
corpus=$(realpath "$4")
icorpus=$(realpath "$5")
proofs=$(realpath "$6")
case "$mutation" in
  binding|admitted|axiom|certificate|crosscheck|internal-crosscheck) ;;
  *) echo "unknown mutation: $mutation" >&2; exit 2 ;;
esac
test -f "$build/.built"
cd "$(dirname "$0")/.."
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir "$work/repo"
cp -r .cargo crates formal scripts "$work/repo/"
cp -a "$build" "$work/build"
cp "$corpus" "$work/crosscheck.txt"
cp "$icorpus" "$work/internal-crosscheck.txt"
cp -r "$proofs" "$work/proofs"
cd "$work/repo"
# Validate the clean fixture first: unrelated missing or stale bound sources
# must not masquerade as a successful rejection in the binding case.
sha256sum --check --quiet formal/binding.sha256

rebind() {
  sed -i "s|^[0-9a-f]*  $1\$|$(sha256sum "$1")|" formal/binding.sha256
  sha256sum --check --quiet formal/binding.sha256
}
expected_status=1
case "$mutation" in
  binding)
    printf '(* edited *)\n' >> formal/exp/ExpReduction.v
    expected='formal/exp/ExpReduction.v: FAILED'
    ;;
  admitted)
    file=formal/ln/Ln1pScreen.v
    line=$(grep -n '^Qed\.$' "$file" | tail -1 | cut -d: -f1)
    test -n "$line"
    sed -i "${line}s/^Qed\.\$/Admitted./" "$file"
    rebind "$file"
    expected='a proof admits a goal'
    ;;
  axiom)
    printf 'Axiom sabotage_axiom : 0 = 0.\nDefinition uses_sabotage := sabotage_axiom.\nPrint Assumptions uses_sabotage.\n' >> formal/audit/Audit.v
    rebind formal/audit/Audit.v
    expected="the relied-on theorems' axioms differ from formal/axioms.expected"
    ;;
  certificate)
    file="$work/proofs/exp/reduction.v"
    line=$(grep -n '^Qed\.$' "$file" | tail -1 | cut -d: -f1)
    test -n "$line"
    sed -i "$((line - 1))d" "$file"
    expected='Attempt to save an incomplete proof'
    expected_status=2
    ;;
  crosscheck|internal-crosscheck)
    file="$work/$mutation.txt"
    # Change an expected result by one bit, keeping the corpus well formed.
    # The first expected result is finite; don't mutate a NaN payload that
    # the cross-check intentionally treats as equivalent.
    awk 'NR == 1 && match($0, /: [0-9a-f]/) {
      pos = RSTART + 2
      digit = index("0123456789abcdef", substr($0, pos, 1))
      $0 = substr($0, 1, pos - 1) substr("1032547698badcfe", digit, 1) substr($0, pos + 1)
    } { print }' "$file" > "$file.changed"
    if cmp -s "$file" "$file.changed"; then
      echo "$mutation: mutation did not change the corpus" >&2
      exit 1
    fi
    mv "$file.changed" "$file"
    expected='mismatch:'
    ;;
esac

started=$(date +%s)
status=0
./scripts/check_formal.sh --deps "$deps" --build "$work/build" \
  "$work/crosscheck.txt" "$work/internal-crosscheck.txt" "$work/proofs" \
  > "$work/result.log" 2>&1 || status=$?
cat "$work/result.log"
if [ "$status" -ne "$expected_status" ]; then
  echo "negative ($mutation): FAIL: expected exit $expected_status, got $status" >&2
  exit 1
fi
if ! grep -qF "$expected" "$work/result.log"; then
  echo "negative ($mutation): FAIL: exited $status without the intended rejection: $expected" >&2
  exit 1
fi
case "$mutation" in
  crosscheck) grep -qxF 'crosscheck failed' "$work/result.log" ;;
  internal-crosscheck) grep -qxF 'internal_crosscheck failed' "$work/result.log" ;;
esac
echo "negative ($mutation): PASS: intended rejection (exit $status, $(($(date +%s) - started)) seconds)"
