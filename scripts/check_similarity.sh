#!/usr/bin/env sh
# The similarity gate (docs/PROVENANCE.md, "Similarity gate"): fetches the
# pinned corpora in provenance/similarity/corpora.tsv into
# target/similarity-corpora, then compares the library's design-choice source
# against them (crates/similarity). It prints only our files, lines and
# fingerprints, and the corpus paths matched, never corpus text.
#
# A git corpus is fetched shallow and sparse at its ref, and must resolve to
# its pinned commit; a tarball must match its pinned SHA-256. An unpinned
# corpus fails the gate: a person pins it.
set -eu
cd "$(dirname "$0")/.."

dir=target/similarity-corpora
mkdir -p "$dir"

grep -v '^#' provenance/similarity/corpora.tsv | grep -v '^[[:space:]]*$' |
while IFS="$(printf '\t')" read -r name kind url ref pin paths license; do
  dest="$dir/$name"
  if [ -f "$dest/.pinned" ] && [ "$(cat "$dest/.pinned")" = "$pin" ]; then
    echo "cached: $name"
    continue
  fi
  rm -rf "$dest"
  case "$kind" in
    git)
      git init -q "$dest"
      git -C "$dest" remote add origin "$url"
      if [ "$paths" != "-" ]; then
        # shellcheck disable=SC2086
        git -C "$dest" sparse-checkout set $paths
      fi
      if printf '%s' "$ref" | grep -Eq '^[0-9a-f]{40}$'; then
        git -C "$dest" fetch -q --depth 1 --filter=blob:none origin "$ref"
      else
        git -C "$dest" fetch -q --depth 1 --filter=blob:none origin "refs/tags/$ref:refs/tags/$ref"
        git -C "$dest" update-ref FETCH_HEAD "refs/tags/$ref^{commit}"
      fi
      git -C "$dest" -c advice.detachedHead=false checkout -q FETCH_HEAD
      got=$(git -C "$dest" rev-parse 'HEAD^{commit}')
      if [ "$got" != "$pin" ]; then
        echo "corpus $name: $ref resolves to $got, not the pinned $pin" >&2
        exit 1
      fi
      ;;
    tarball)
      if [ "$pin" = "unpinned" ]; then
        echo "corpus $name: no SHA-256 pin. A person downloads $url, checks it, and records its SHA-256 in provenance/similarity/corpora.tsv" >&2
        exit 1
      fi
      mkdir -p "$dest"
      curl -fsSL "$url" -o "$dest.download"
      got=$(sha256sum "$dest.download" | cut -d' ' -f1)
      if [ "$got" != "$pin" ]; then
        echo "corpus $name: SHA-256 $got, not the pinned $pin" >&2
        exit 1
      fi
      tar -xzf "$dest.download" -C "$dest"
      rm "$dest.download"
      ;;
    *)
      echo "corpus $name: unknown kind $kind" >&2
      exit 1
      ;;
  esac
  printf '%s' "$pin" > "$dest/.pinned"
  echo "fetched: $name"
done

cargo run --locked --release -q -p morphiq-numerics-similarity -- --corpora "$dir"
