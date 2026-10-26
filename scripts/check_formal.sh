#!/usr/bin/env sh
# The formal lane: machine-checked proofs, bound to the source they describe.
#
#   1. formal/binding.sha256 matches: a change to a covered source or proof file
#      fails until the proofs are rerun and the manifest is updated with them.
#   2. No proof file admits a goal.
#   3. The double-word development (formal/double-word), the two_prod binding
#      proof (formal/two-prod), the binary64 bindings (formal/binary64) and the
#      Q128/Q256 contracts (formal/q) build.
#   4. The global axioms the relied-on theorems (formal/audit/Audit.v) rest on
#      are exactly those listed in formal/axioms.expected.
#   5. Every Gappa certificate's Coq proof (gappa -Bcoq, written into the
#      directory given as the third argument by scripts/write_gappa_proofs.sh)
#      builds with each rewriting hint proved as a lemma by
#      formal/gappa/Hints.v, so no hypothesis is left; and each final theorem's
#      global axioms are among formal/axioms.expected.
#   6. The kernels' transcriptions and proofs (formal/exp/*.v, formal/ln/*.v) and
#      asin's analytic facts (formal/asin/AsinFacts.v: the Taylor remainders, the
#      argument ranges, sin t / t),
#      which apply the certificates' theorems, build (formal/exp/ExpStageTables.v
#      checks exp's 512-entry table by one reflective computation); and the global axioms the
#      theorems in formal/audit/KernelAudit.v (audited in parallel chunks of its
#      Print Assumptions lines, one coqc each) rest on are among
#      formal/axioms.expected, formal/axioms.int63.expected and formal/axioms.float.expected. The second
#      list is Coq's primitive 63-bit integers: CoqInterval, which proves the kernels' constants,
#      computes with them through Bignums. The third is Coq's primitive floats (FloatAxioms), which
#      CoqInterval's bisection and Taylor tactics (i_bisect, i_taylor) reach even at high precision;
#      they are Coq's own specified primitives, as the integers are, and only asin's segment
#      certificates (formal/asin/AsinApprox.v) and what composes them rest on them.
#   7. The proved IEEE 754 definitions and the Q128/Q256 transcriptions,
#      extracted to OCaml (formal/extraction), reproduce the Rust library's
#      results bit for bit on the cross-check corpora given as the first two
#      arguments; the bivariate normal's scalar kernel (formal/bivariate/BvnKernel.v)
#      is extracted separately (formal/extraction/BvnCrosscheck.v, bvndriver.ml) and
#      runs on the bvn lines of the internal corpus, with the library functions it
#      calls given by the results the Rust recorded. Write the arguments first with
#        cargo run --locked -p morphiq-numerics-reference --bin crosscheck-corpus > target/crosscheck.txt
#        MORPHIQ_INTERNAL_CORPUS=$PWD/target/internal-crosscheck.txt cargo test --locked -p morphiq-numerics --lib internal_crosscheck -- --ignored
#        ./scripts/write_gappa_proofs.sh target/gappa-proofs   (in the certificates image)
#
# The builds of 3, 5 and 6 are one parallel make over a generated _CoqProject.
# The audits of 4, 5 and 6 and the extraction of 7 are compiled afresh on every
# run, against the build's .vo files, all at once.
#
# Options:
#   --build-only  prepare a retained --build tree for caching, then exit before
#                 the audits and cross-checks. This is not a passing formal
#                 gate; CI follows it with the complete invocation below.
#   --deps TAR   restore the Coq libraries from TAR (scripts/formal_deps.sh)
#                and check their pinned versions, instead of installing them.
#   --build DIR  build in DIR and keep it, so a later run reuses it (CI caches
#                it). A .vo file is reused only if its source file's bytes, the
#                generated _CoqProject and the Coq toolchain's fingerprint (the
#                compiler, its library and plugin files, and every installed
#                package's version) are unchanged; make rebuilds everything
#                downstream of a rebuilt file, and Coq refuses a .vo compiled
#                against a different version of a library it requires.
#                It marks the tree with DIR/.built once make succeeds.
#                Without it, the build is in a fresh temporary directory.
#
# Runs inside the pinned Coq image (.cargo/coq-image; see the formal jobs in
# .github/workflows/ci.yml), which provides coqc, coq_makefile and opam; the
# Coq libraries are pinned by version in .cargo/coq-packages.
set -eu
deps=
build=
build_only=0
while [ $# -gt 0 ]; do
  case $1 in
    --build-only) build_only=1; shift ;;
    --deps) deps=$(realpath "$2"); shift 2 ;;
    --build) mkdir -p "$2"; build=$(realpath "$2"); shift 2 ;;
    --) shift; break ;;
    -*) echo "unknown option $1" >&2; exit 2 ;;
    *) break ;;
  esac
done
if [ $# -ne 3 ]; then
  echo "usage: $0 [--deps <tar>] [--build <dir>] [--build-only] <cross-check corpus> <internal cross-check corpus> <Gappa proofs directory>" >&2
  exit 2
fi
if [ "$build_only" -eq 1 ] && [ -z "$build" ]; then
  echo "--build-only requires a retained --build directory" >&2
  exit 2
fi
corpus=$(realpath "$1")
icorpus=$(realpath "$2")
proofs=$(realpath "$3")
cd "$(dirname "$0")/.."

sha256sum --check --quiet formal/binding.sha256

if grep -n -w -E 'Admitted|admit' formal/double-word/*.v formal/two-prod/*.v formal/binary64/*.v formal/extraction/*.v formal/q/*.v \
    formal/exp/*.v formal/ln/*.v formal/erfcx/*.v formal/normal/*.v formal/asin/*.v formal/asinh/*.v formal/atan2/*.v formal/bivariate/*.v formal/gappa/*.v "$proofs"/*/*.v; then
  echo "a proof admits a goal" >&2
  exit 1
fi

packages=$(grep -v -E '^(#|$)' .cargo/coq-packages)
if [ -n "$deps" ]; then
  tar -C "$(opam var prefix)" -xzf "$deps"
  installed=$(opam list --installed --short --columns=package)
  for package in $packages; do
    if ! printf '%s\n' "$installed" | grep -qxF "$package"; then
      echo "$deps does not provide $package (.cargo/coq-packages)" >&2
      exit 1
    fi
  done
else
  # shellcheck disable=SC2086 # one package per word
  opam install --yes $packages >/dev/null
fi

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

# The source tree: the developments, each Gappa certificate's proof with its
# hints proved, and the kernels beside the certificates they apply.
src="$work/src"
mkdir "$src"
cp -r formal/double-word formal/two-prod formal/binary64 formal/q formal/audit formal/extraction "$src/"
rm "$src/double-word/_CoqProject"
mkdir "$src/gappa"
cp formal/gappa/Hints.v "$src/gappa/"
# The Gappa certificates: each hint hypothesis becomes a lemma proved by [hint].
printf '' > "$src/gappa/CertificateAudit.v"
for proof in "$proofs"/*/*.v; do
  f=$(basename "$(dirname "$proof")")
  module="${f}_$(basename "$proof" .v)"
  if ! grep -q '^Lemma l1 : s1 -> False\.$' "$proof"; then
    echo "$proof: no final theorem l1" >&2
    exit 1
  fi
  { echo 'From Coq Require Import Reals. Require Import Hints.'
    sed -E 's/^Hypothesis (a[0-9]+) : (.*)\.$/Lemma \1 : \2.\nProof. hint. Qed./' "$proof"
  } > "$src/gappa/$module.v"
  if grep -q '^Hypothesis' "$src/gappa/$module.v"; then
    echo "$proof: a hypothesis is left" >&2
    exit 1
  fi
  printf 'Require %s.\nPrint Assumptions %s.l1.\n' "$module" "$module" >> "$src/gappa/CertificateAudit.v"
done
cp formal/exp/*.v formal/ln/*.v formal/erfcx/*.v formal/normal/*.v formal/asin/*.v formal/asinh/*.v formal/atan2/*.v formal/bivariate/*.v formal/audit/KernelAudit.v "$src/gappa/"
# Everything but the audits and the extraction, which are compiled below. The
# mappings are those each directory's proofs are written against.
(cd "$src" && {
  echo '-R double-word Double'
  echo '-R two-prod ""'
  echo '-R binary64 Binary64'
  echo '-R q Q'
  echo '-R gappa ""'
  find double-word two-prod binary64 q gappa -name '*.v' \
    ! -name CertificateAudit.v ! -name KernelAudit.v | LC_ALL=C sort
} > _CoqProject)

# The build tree. A kept one is reused only where nothing it was built from
# has changed.
if [ -z "$build" ]; then
  build="$work/build"
  mkdir "$build"
fi
toolchain=$({
  coqc --version
  ocamlfind ocamlopt -version
  opam list --installed --short --columns=package
  cd "$(opam var prefix)"
  find bin/coqc lib/coq lib/coq-core/plugins -type f -print0 | LC_ALL=C sort -z | xargs -0 sha256sum
} | sha256sum | cut -d' ' -f1)
# .built marks a tree whose last make succeeded, so every .vo in it is complete;
# CI saves the tree only then.
rm -f "$build/.built"
if [ "$(cat "$build/.toolchain" 2>/dev/null)" != "$toolchain" ] || ! cmp -s "$build/_CoqProject" "$src/_CoqProject"; then
  find "$build" -mindepth 1 -delete
fi
# A source file that's new or changed is copied, with a new modification time,
# and its compiled files are removed; one that's gone is removed with them.
compiled() {
  echo "${1%.v}.vo ${1%.v}.vos ${1%.v}.vok ${1%.v}.glob $(dirname "$1")/.$(basename "$1" .v).aux"
}
(cd "$src" && find . -type f) | while read -r f; do
  if ! cmp -s "$src/$f" "$build/$f"; then
    mkdir -p "$(dirname "$build/$f")"
    cp "$src/$f" "$build/$f"
    # shellcheck disable=SC2046 # the names have no spaces
    case $f in *.v) (cd "$build" && rm -f $(compiled "$f")) ;; esac
  fi
done
(cd "$build" && find . -name '*.v') | while read -r f; do
  if [ ! -e "$src/$f" ]; then
    # shellcheck disable=SC2046
    (cd "$build" && rm -f "$f" $(compiled "$f"))
  fi
done
echo "$toolchain" > "$build/.toolchain"

(cd "$build" && coq_makefile -f _CoqProject -o Makefile && make -j"$(nproc)" TIMED=1)
touch "$build/.built"
if [ "$build_only" -eq 1 ]; then
  echo "proof build prepared; audits and cross-checks have not run"
  exit 0
fi

# The pinned OCaml Flambda compiler recursively walks the extracted module's
# top-level expressions. The complete erfcx entry exceeds even 32 MiB on
# Linux; reserve 60 MiB, verified with the pinned compiler and below macOS's
# 64 MiB hard limit. This applies to both extractions
# and is scoped to the compiler, not the proof auditors or corpus executables.
compile_extraction() (
  echo "extraction: compiling $*"
  ulimit -s 61440 || exit 1
  exec ocamlfind ocamlopt "$@"
)

# The audits and the cross-checks are independent, so they run at once; each is
# then judged in turn, and the first to fail fails the lane.
(cd "$build/audit" && coqc -R ../double-word Double -I ../two-prod -R ../two-prod "" -R ../binary64 Binary64 -R ../q Q Audit.v) \
  > "$work/audit.log" 2> "$work/audit.err" &
audit=$!
(cd "$build/gappa" && coqc -R . "" CertificateAudit.v) \
  > "$work/certificate_audit.log" 2> "$work/certificate_audit.err" &
certificate_audit=$!
# The kernel audit is one serial coqc, which took 47 of a 91 minute run, so its
# Print Assumptions lines are dealt round-robin to as many files as the machine
# has cores (at most 6), each with the file's whole header, and checked by one
# coqc each at once. The checks below read the chunks' concatenated reports, so
# they are the checks of one file: the same entries, the same expected axioms,
# the same report count.
kernel_chunks=$(nproc)
[ "$kernel_chunks" -gt 6 ] && kernel_chunks=6
[ "$kernel_chunks" -lt 1 ] && kernel_chunks=1
kernel_entries=$(grep -c '^Print Assumptions ' "$build/gappa/KernelAudit.v")
if [ "$kernel_entries" -ne "$(grep -c '^Print Assumptions .*\.$' "$build/gappa/KernelAudit.v")" ]; then
  echo "a Print Assumptions line of KernelAudit.v is not a single statement" >&2
  exit 1
fi
kernel_pids=
i=0
while [ "$i" -lt "$kernel_chunks" ]; do
  chunk="$build/gappa/KernelAuditPart$i.v"
  awk -v n="$kernel_chunks" -v part="$i" '
    /^Print Assumptions / { if (count++ % n == part) print; next }
    { print }
  ' "$build/gappa/KernelAudit.v" > "$chunk"
  (cd "$build/gappa" && coqc -R ../double-word Double -R ../binary64 Binary64 -R ../two-prod "" -R ../q Q -R . "" "KernelAuditPart$i.v") \
    > "$work/kernel_audit$i.log" 2> "$work/kernel_audit$i.err" &
  kernel_pids="$kernel_pids $!"
  i=$((i + 1))
done
(cd "$build/extraction" \
  && coqc -R ../double-word Double -R ../binary64 Binary64 -R ../two-prod "" Crosscheck.v \
  && compile_extraction -o crosscheck crosscheck.mli crosscheck.ml driver.ml \
  && echo "extraction: running crosscheck" \
  && ./crosscheck "$corpus") > "$work/crosscheck.log" 2> "$work/crosscheck.err" &
crosscheck=$!
(cd "$build/extraction" \
  && coqc -R ../double-word Double -R ../binary64 Binary64 -R ../two-prod "" -R ../q Q -R ../gappa "" InternalCrosscheck.v \
  && compile_extraction -o internalcrosscheck internalcrosscheck.mli internalcrosscheck.ml internaldriver.ml \
  && echo "extraction: running internalcrosscheck" \
  && ./internalcrosscheck "$icorpus") > "$work/internal_crosscheck.log" 2> "$work/internal_crosscheck.err" &
internal_crosscheck=$!
(cd "$build/extraction" \
  && coqc -R ../double-word Double -R ../binary64 Binary64 -R ../two-prod "" -R ../gappa "" BvnCrosscheck.v \
  && compile_extraction -o bvncrosscheck bvncrosscheck.mli bvncrosscheck.ml bvndriver.ml \
  && echo "extraction: running bvncrosscheck" \
  && ./bvncrosscheck "$icorpus") > "$work/bvn_crosscheck.log" 2> "$work/bvn_crosscheck.err" &
bvn_crosscheck=$!
# finish NAME PID: waits for the step, shows its errors, and fails if it did.
finish() {
  status=0
  wait "$2" || status=$?
  cat "$work/$1.err" >&2
  if [ "$status" -ne 0 ]; then
    tail -n 20 "$work/$1.log" >&2
    echo "$1 failed" >&2
    exit "$status"
  fi
}

finish audit "$audit"
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

finish certificate_audit "$certificate_audit"
grep -E '^[^[:space:]]' "$work/certificate_audit.log" \
  | grep -v -E '^(Axioms:|Closed under the global context)' \
  | sed 's/ :.*//' | sort -u > "$work/certificate-axioms"
if ! comm -23 "$work/certificate-axioms" "$work/expected" | diff /dev/null - >&2; then
  echo "a certificate's theorem rests on an axiom outside formal/axioms.expected" >&2
  exit 1
fi
certificates=$(grep -c '^Print Assumptions' "$build/gappa/CertificateAudit.v")
reports=$(( $(grep -c '^Axioms:' "$work/certificate_audit.log" || true) + $(grep -c 'Closed under the global context' "$work/certificate_audit.log" || true) ))
if [ "$reports" -ne "$certificates" ]; then
  echo "the certificate audit reported on $reports theorems, not $certificates" >&2
  exit 1
fi
echo "certificates in Coq: $certificates proved"

i=0
for pid in $kernel_pids; do
  finish "kernel_audit$i" "$pid"
  i=$((i + 1))
done
cat "$work"/kernel_audit[0-9]*.log > "$work/kernel_audit.log"
grep -E '^[^[:space:]]' "$work/kernel_audit.log" \
  | grep -v -E '^(Axioms:|Closed under the global context)' \
  | sed 's/ :.*//' | sort -u > "$work/kernel-axioms"
sort -u formal/axioms.expected formal/axioms.int63.expected formal/axioms.float.expected > "$work/kernel-expected"
if ! comm -23 "$work/kernel-axioms" "$work/kernel-expected" | diff /dev/null - >&2; then
  echo "a kernel theorem rests on an axiom outside formal/axioms.expected, formal/axioms.int63.expected and formal/axioms.float.expected" >&2
  exit 1
fi
kernels=$(grep -c '^Print Assumptions' formal/audit/KernelAudit.v)
reports=$(( $(grep -c '^Axioms:' "$work/kernel_audit.log" || true) + $(grep -c 'Closed under the global context' "$work/kernel_audit.log" || true) ))
if [ "$reports" -ne "$kernels" ]; then
  echo "the kernel audit reported on $reports theorems, not $kernels" >&2
  exit 1
fi
echo "kernel proofs: $kernels proved"

finish crosscheck "$crosscheck"
cat "$work/crosscheck.log"
finish internal_crosscheck "$internal_crosscheck"
cat "$work/internal_crosscheck.log"
finish bvn_crosscheck "$bvn_crosscheck"
cat "$work/bvn_crosscheck.log"
echo "formal: OK"
