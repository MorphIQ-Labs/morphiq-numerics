#!/usr/bin/env bash
# Run after release-plz release-pr -o json, with GH_TOKEN set to the release
# token and GITHUB_REPOSITORY to owner/name. Update only the PRs returned by
# that invocation.
#
# The commit is created through GitHub's API, not git push: GitHub signs the
# commits it creates, and the "Main branch protection" ruleset admits only
# verified signatures, so a pushed, unsigned commit would block the release
# pull request's merge.
set -euo pipefail
: "${GITHUB_REPOSITORY:?GITHUB_REPOSITORY must name owner/repo}"

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
    lock=$(mktemp)
    cp fuzz/Cargo.lock "$lock"
    # expectedHeadOid refuses the commit if another writer has advanced the
    # release branch since the fetch, as a non-force push would.
    oid=$(jq -n --arg repo "$GITHUB_REPOSITORY" --arg branch "$branch" \
        --arg head "$(git rev-parse HEAD)" --rawfile contents <(base64 -w0 "$lock") '{
      query: "mutation($input: CreateCommitOnBranchInput!) { createCommitOnBranch(input: $input) { commit { oid } } }",
      variables: {input: {
        branch: {repositoryNameWithOwner: $repo, branchName: $branch},
        expectedHeadOid: $head,
        message: {headline: "fix(release): synchronize fuzz workspace lockfile"},
        fileChanges: {additions: [{path: "fuzz/Cargo.lock", contents: $contents}]}
      }}
    }' | gh api graphql --input - | jq -er '.data.createCommitOnBranch.commit.oid')
    # The branch must now hold exactly that commit, carrying this lockfile.
    git checkout -- fuzz/Cargo.lock
    git fetch origin "refs/heads/$branch"
    git checkout --detach FETCH_HEAD
    [ "$(git rev-parse HEAD)" = "$oid" ] || {
      echo "Release branch $branch is not at the created commit $oid" >&2; exit 1
    }
    cmp -s fuzz/Cargo.lock "$lock" || {
      echo "Commit $oid does not carry the synchronized fuzz lockfile" >&2; exit 1
    }
    rm -f "$lock"
  fi
done <<< "$branches"
