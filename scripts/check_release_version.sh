#!/usr/bin/env sh
# Release tags equal the Cargo version. A tag vX.Y.Z must point at a commit
# whose workspace version ([workspace.package] in Cargo.toml) is exactly X.Y.Z,
# and every released crate takes that version, so a consumer pinning the tag
# gets the version the tag names. release-plz.toml makes this the intended
# outcome (one workspace version, tag v{{ version }}); this script checks it.
#
# Always:
#   - each released crate inherits the workspace version;
#   - every tag vX.Y.Z already in the repository has workspace version X.Y.Z.
# On a release pull request (head branch release-plz-*), for the tag its merge
# will create, v{version}:
#   - that tag does not exist yet;
#   - CHANGELOG.md's newest release section is that version;
#   - a version named in the pull request title (PR_TITLE) is that version.
# On a tag push (GITHUB_REF_TYPE=tag), the pushed tag is checked as above.
#
# Needs full history and tags (fetch-depth: 0). Depends on git and awk only.
set -eu

VERSION=1
for arg in "$@"; do
  case "$arg" in
    -h | --help)
      echo "usage: check_release_version.sh"
      echo "Fails when a release tag, or the tag a release pull request proposes,"
      echo "differs from the workspace version in Cargo.toml."
      exit 0
      ;;
    -V | --version)
      echo "check_release_version $VERSION"
      exit 0
      ;;
    --) break ;;
    *)
      echo "check_release_version: unexpected argument: $arg" >&2
      exit 2
      ;;
  esac
done

cd "$(dirname "$0")/.."

# The packages release-plz.toml releases.
released="morphiq-numerics morphiq-numerics-arch"

# workspace_version: [workspace.package] version of the Cargo.toml on stdin.
workspace_version() {
  awk -F'"' '/^\[/ { f = ($0 == "[workspace.package]"); next } f && /^version = / { print $2; exit }'
}

fail=0
err() { echo "check_release_version: $*" >&2; fail=1; }

version=$(workspace_version < Cargo.toml)
if ! printf '%s\n' "$version" | grep -qE '^[0-9]+\.[0-9]+\.[0-9]+$'; then
  echo "check_release_version: no X.Y.Z [workspace.package] version in Cargo.toml (found '$version')" >&2
  exit 1
fi
echo "workspace version: $version"

for crate in $released; do
  grep -qx 'version.workspace = true' "crates/$crate/Cargo.toml" \
    || err "crates/$crate does not inherit the workspace version"
done

# Every release tag names its commit's workspace version.
tags=$(git tag --list 'v*')
for tag in $tags; do
  printf '%s\n' "$tag" | grep -qE '^v[0-9]+\.[0-9]+\.[0-9]+$' \
    || { err "tag $tag is not v{major}.{minor}.{patch}"; continue; }
  at=$(git show "$tag:Cargo.toml" | workspace_version)
  if [ "$at" = "${tag#v}" ]; then
    echo "tag $tag: workspace version $at"
  else
    err "tag $tag points at $(git rev-parse --short "$tag^{commit}"), whose workspace version is '$at'"
  fi
done

if [ "${GITHUB_REF_TYPE:-}" = tag ]; then
  tag=${GITHUB_REF_NAME:?}
  case "$tag" in
    v*) [ "$tag" = "v$version" ] || err "pushed tag $tag does not equal the workspace version $version at $(git rev-parse --short HEAD)" ;;
  esac
fi

case "${GITHUB_HEAD_REF:-}" in
  release-plz-*)
    proposed="v$version"
    echo "release pull request proposes $proposed"
    if git rev-parse -q --verify "refs/tags/$proposed" > /dev/null; then
      err "the release pull request's version $version is already tagged $proposed; it would release nothing"
    fi
    newest=$(sed -n 's/^## \[\([0-9][0-9.]*\)\].*/\1/p' CHANGELOG.md | head -n 1)
    [ "$newest" = "$version" ] \
      || err "CHANGELOG.md's newest release section is '$newest', not $version"
    named=$(printf '%s\n' "${PR_TITLE:-}" | grep -oE 'v?[0-9]+\.[0-9]+\.[0-9]+' || true)
    for v in $named; do
      [ "${v#v}" = "$version" ] || err "the pull request title names $v, not $version"
    done
    ;;
esac

[ "$fail" -eq 0 ] || exit 1
echo "check_release_version: tags and version agree"
