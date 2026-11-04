#!/usr/bin/env bash
# Run after release-plz release-pr -o json, using the existing release identity
# and remote credentials. Update only the PRs returned by that invocation.
set -euo pipefail

branches=$(jq -er '.prs | map(.head_branch) | .[]' "$1") || {
  # An empty array means release-plz had nothing to open or update.
  jq -e '.prs == []' "$1" >/dev/null
  exit 0
}
while IFS= read -r branch; do
  case "$branch" in
    release-plz-*) git check-ref-format "refs/heads/$branch" ;;
    *) echo "Unexpected release branch: $branch" >&2; exit 1 ;;
  esac
  git fetch origin "refs/heads/$branch"
  git checkout --detach FETCH_HEAD
  # --workspace preserves the locked third-party versions. Do not use a
  # general cargo update or drop --locked from the license/fuzz checks.
  cargo update --manifest-path fuzz/Cargo.toml --workspace
  cargo metadata --manifest-path fuzz/Cargo.toml --all-features --locked \
    --format-version 1 >/dev/null
  if ! git diff --quiet -- fuzz/Cargo.lock; then
    git add fuzz/Cargo.lock
    git commit -m "fix(release): synchronize fuzz workspace lockfile"
    # No force push: fail if another writer has advanced the release branch.
    git push origin "HEAD:refs/heads/$branch"
  fi
done <<< "$branches"
