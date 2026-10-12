#!/usr/bin/env sh
# Installs the formal lane's Coq libraries, pinned by exact version in
# .cargo/coq-packages, into the opam switch of the pinned Coq image
# (.cargo/coq-image), and writes everything the install added or changed in the
# switch to $1 as a gzipped tar. scripts/check_formal.sh --deps restores it in
# the same image instead of building the libraries again, which takes about a
# quarter of an hour.
#
# The tar is exact: it holds every path under the switch whose status changed
# after the install began (its ctime, which neither a copy nor an archive
# extraction can preserve), so a file opam wrote is never missed. A tar can't
# delete, so the script fails if the install removed a path from the switch.
#
# Runs inside the pinned Coq image, as its default user.
set -eu
if [ $# -ne 1 ]; then
  echo "usage: $0 <output .tar.gz>" >&2
  exit 2
fi
out=$(realpath "$1")
cd "$(dirname "$0")/.."
packages=$(grep -v -E '^(#|$)' .cargo/coq-packages)
prefix=$(opam var prefix)

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
(cd "$prefix" && find . | LC_ALL=C sort) > "$work/before"
touch "$work/marker"
# A status change in the same clock tick as the marker would not be newer.
sleep 1

opam update --quiet >/dev/null 2>&1 || true
# shellcheck disable=SC2086 # one package per word
opam install --yes $packages >/dev/null

(cd "$prefix" && find . | LC_ALL=C sort) > "$work/after"
if LC_ALL=C comm -23 "$work/before" "$work/after" | grep . >&2; then
  echo "the install removed the paths above from the switch, which the tar can't express" >&2
  exit 1
fi
(cd "$prefix" && find . -cnewer "$work/marker" | LC_ALL=C sort) > "$work/changed"
tar -C "$prefix" --no-recursion -czf "$out" -T "$work/changed"
echo "coq dependencies: $(wc -l < "$work/changed") paths, $(wc -c < "$out") bytes"
