#!/usr/bin/env sh
# The formal lane: machine-checked proofs, bound to the source they describe.
#
#   1. formal/binding.sha256 matches: a change to a covered source or proof file
#      fails until the proofs are rerun and the manifest is updated with them.
#   2. No proof file admits a goal.
#   3. The double-word development (formal/double-word), the two_prod binding
#      proof (formal/two-prod) and the binary64 bindings (formal/binary64) build.
#   4. The global axioms the relied-on theorems (formal/audit/Audit.v) rest on
#      are exactly those listed in formal/axioms.expected.
#   5. The proved IEEE 754 definitions, extracted to OCaml (formal/extraction),
#      reproduce the Rust library's results bit for bit on the cross-check
#      corpus, the file given as the only argument. Write it first with
#        cargo run --locked -p morphiq-numerics-reference --bin crosscheck-corpus > target/crosscheck.txt
#
# Runs inside the pinned Coq image (see the formal job in .github/workflows/ci.yml),
# which provides coqc, coq_makefile and opam; Flocq and math-comp are pinned here.
set -eu
if [ $# -ne 1 ]; then
  echo "usage: $0 <cross-check corpus>" >&2
  exit 2
fi
corpus=$(realpath "$1")
cd "$(dirname "$0")/.."

sha256sum --check --quiet formal/binding.sha256

if grep -n -w -E 'Admitted|admit' formal/double-word/*.v formal/two-prod/*.v formal/binary64/*.v formal/extraction/*.v; then
  echo "a proof admits a goal" >&2
  exit 1
fi

opam install --yes coq-flocq.3.4.3 coq-mathcomp-ssreflect.1.14.0 >/dev/null

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -r formal/double-word formal/two-prod formal/binary64 formal/audit formal/extraction "$work/"
(cd "$work/double-word" && coq_makefile -f _CoqProject -o Makefile && make -j"$(nproc)")
(cd "$work/two-prod" && coqc TwoProdBinary64.v)
(cd "$work/binary64" && for proof in Binary64Add Instances Binary64Mul Grid Binary64Div \
    IEEE64 IEEE64Add IEEE64Mul IEEE64Div IEEE64Eft IEEE64Sqrt \
    Isqrt SqrtRound SqrtAlgorithm; do
  coqc -R ../double-word Double -R . Binary64 -R ../two-prod "" "$proof.v" || exit 1
done)

(cd "$work/audit" && coqc -R ../double-word Double -I ../two-prod -R ../two-prod "" -R ../binary64 Binary64 Audit.v) > "$work/audit.log"
# Each axiom entry starts unindented; its type follows on the same line or on
# indented lines after it, depending on its length.
grep -E '^[^[:space:]]' "$work/audit.log" \
  | grep -v -E '^(Axioms:|Closed under the global context)' \
  | sed 's/ :.*//' | sort -u > "$work/axioms"
# Equality, not inclusion: an axiom the audit failed to parse fails here too.
sort -u formal/axioms.expected > "$work/expected"
if ! diff -u "$work/expected" "$work/axioms" >&2; then
  echo "the relied-on theorems' axioms differ from formal/axioms.expected (- expected, + found)" >&2
  exit 1
fi
# One report per audited theorem, so a theorem the audit failed to reach fails here.
# grep -c exits 1 on a zero count, which set -e would treat as a failure.
with_axioms=$(grep -c '^Axioms:' "$work/audit.log" || true)
closed=$(grep -c 'Closed under the global context' "$work/audit.log" || true)
reports=$((with_axioms + closed))
if [ "$reports" -ne "$(grep -c '^Print Assumptions' formal/audit/Audit.v)" ]; then
  echo "the audit reported on $reports theorems, not every one in formal/audit/Audit.v" >&2
  exit 1
fi
(cd "$work/extraction" \
  && coqc -R ../double-word Double -R ../binary64 Binary64 -R ../two-prod "" Crosscheck.v \
  && ocamlfind ocamlopt -o crosscheck crosscheck.mli crosscheck.ml driver.ml \
  && ./crosscheck "$corpus")
echo "formal: OK"
