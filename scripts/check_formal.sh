#!/usr/bin/env sh
# The formal lane: machine-checked proofs, bound to the source they describe.
#
#   1. formal/binding.sha256 matches: a change to a covered source or proof file
#      fails until the proofs are rerun and the manifest is updated with them.
#   2. No proof file admits a goal.
#   3. The double-word development (formal/double-word) and the two_prod binding
#      proof (formal/two-prod) build.
#   4. Every theorem the library relies on (formal/audit/Audit.v) rests only on
#      global axioms listed in formal/axioms.expected (Coq's classical reals).
#
# Runs inside the pinned Coq image (see the formal job in .github/workflows/ci.yml),
# which provides coqc, coq_makefile and opam; Flocq and math-comp are pinned here.
set -eu
cd "$(dirname "$0")/.."

sha256sum --check --quiet formal/binding.sha256

if grep -n -w -E 'Admitted|admit' formal/double-word/*.v formal/two-prod/*.v; then
  echo "a proof admits a goal" >&2
  exit 1
fi

opam install --yes coq-flocq.3.4.3 coq-mathcomp-ssreflect.1.14.0 >/dev/null

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
cp -r formal/double-word formal/two-prod formal/audit "$work/"
(cd "$work/double-word" && coq_makefile -f _CoqProject -o Makefile && make -j"$(nproc)")
(cd "$work/two-prod" && coqc TwoProdBinary64.v)

(cd "$work/audit" && coqc -R ../double-word Double -I ../two-prod -R ../two-prod "" Audit.v) > "$work/audit.log"
grep -E '^[A-Za-z_][A-Za-z0-9_.]* :' "$work/audit.log" | sed 's/ :.*//' | sort -u > "$work/axioms"
unexpected=$(sort -u formal/axioms.expected | comm -13 - "$work/axioms")
if [ -n "$unexpected" ]; then
  echo "a relied-on theorem rests on axioms outside formal/axioms.expected:" >&2
  echo "$unexpected" >&2
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
echo "formal: OK"
