"""Exercise release synchronization against a local remote and real Cargo locks.

A fake gh stands in for GitHub's createCommitOnBranch: it commits the request's
files onto the local remote's branch, refusing a stale expectedHeadOid as
GitHub does.
"""

import base64
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("sync_release_fuzz_lock.sh").resolve()
REPOSITORY = "MorphIQ-Labs/release-test"
FAKE_GH = r'''#!/usr/bin/env python3
import base64, json, os, subprocess, sys, tempfile

assert sys.argv[1:] == ["api", "graphql", "--input", "-"], sys.argv
request = json.load(sys.stdin)
with open(os.environ["FAKE_GH_LOG"], "a") as log:
    log.write(json.dumps(request) + "\n")
assert "createCommitOnBranch(input: $input)" in request["query"], request["query"]
change = request["variables"]["input"]
ref = "refs/heads/" + change["branch"]["branchName"]
identity = dict(os.environ, GIT_AUTHOR_NAME="GitHub", GIT_AUTHOR_EMAIL="noreply@github.com",
                GIT_COMMITTER_NAME="GitHub", GIT_COMMITTER_EMAIL="noreply@github.com")

def git(*args, env=identity, data=None):
    return subprocess.run(["git", "--git-dir", os.environ["FAKE_GH_REMOTE"], *args], env=env,
                          input=data, check=True, capture_output=True).stdout.decode().strip()

head = git("rev-parse", ref)
if os.environ.get("FAKE_GH_ADVANCE"):
    head_tree = git("rev-parse", head + "^{tree}")
    advanced = git("commit-tree", head_tree, "-p", head, "-m", "another writer")
    git("update-ref", ref, advanced, head)
    head = advanced
if head != change["expectedHeadOid"]:
    print(json.dumps({"errors": [{"message": "Expected branch to point to "
                                  + change["expectedHeadOid"] + " but it did not"}]}))
    sys.exit(1)
with tempfile.TemporaryDirectory() as scratch:
    index = dict(identity, GIT_INDEX_FILE=os.path.join(scratch, "index"))
    git("read-tree", head, env=index)
    for addition in change["fileChanges"]["additions"]:
        blob = git("hash-object", "-w", "--stdin", data=base64.b64decode(addition["contents"]))
        git("update-index", "--add", "--cacheinfo", "100644," + blob + "," + addition["path"], env=index)
    tree = git("write-tree", env=index)
commit = git("commit-tree", tree, "-p", head, "-m", change["message"]["headline"])
git("update-ref", ref, commit, head)
print(json.dumps({"data": {"createCommitOnBranch": {"commit": {"oid": commit}}}}))
'''


class ReleaseFuzzLockTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        bin_dir = self.root / "bin"
        bin_dir.mkdir()
        (bin_dir / "gh").write_text(FAKE_GH)
        (bin_dir / "gh").chmod(0o755)
        self.log = self.root / "gh-requests.jsonl"
        self.env = dict(os.environ, CARGO_NET_OFFLINE="true", GITHUB_REPOSITORY=REPOSITORY,
                        FAKE_GH_REMOTE=str(self.root / "remote.git"), FAKE_GH_LOG=str(self.log),
                        PATH=f"{bin_dir}{os.pathsep}{os.environ['PATH']}")
        self.env.pop("FAKE_GH_ADVANCE", None)
        self.run_command("git", "init", "--bare", str(self.root / "remote.git"))
        self.run_command("git", "init", "-b", "main")
        self.run_command("git", "config", "user.name", "Release test")
        self.run_command("git", "config", "user.email", "release@example.invalid")
        self.run_command("git", "config", "commit.gpgsign", "false")
        self.run_command("git", "remote", "add", "origin", str(self.root / "remote.git"))
        self.write("Cargo.toml", '[workspace]\nmembers = ["library"]\nresolver = "2"\n')
        self.manifest = '[package]\nname = "release-test-library"\nversion = "0.0.24"\nedition = "2021"\n'
        self.write("library/Cargo.toml", self.manifest)
        self.write("library/src/lib.rs", "")
        self.write("fuzz/Cargo.toml", '[package]\nname = "release-test-fuzz"\nversion = "0.0.0"\nedition = "2021"\n[workspace]\n[dependencies]\nrelease-test-library = { path = "../library" }\n')
        self.write("fuzz/src/lib.rs", "")
        self.run_command("cargo", "generate-lockfile", "--manifest-path", "fuzz/Cargo.toml")
        self.write("library/Cargo.toml", self.manifest.replace("0.0.24", "0.0.25"))
        self.run_command("git", "add", ".")
        self.run_command("git", "commit", "-m", "release fixture with stale fuzz lock")
        self.branch = "release-plz-test"
        self.run_command("git", "push", "origin", f"HEAD:refs/heads/{self.branch}")
        self.output = self.root / "release-pr.json"

    def write(self, name, text):
        path = self.repo / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def run_command(self, *args, check=True):
        result = subprocess.run(args, cwd=self.repo, env=self.env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if check and result.returncode:
            self.fail(result.stdout)
        return result

    def remote_head(self):
        return self.run_command("git", "ls-remote", "origin", f"refs/heads/{self.branch}").stdout.split()[0]

    def requests(self):
        return [json.loads(line) for line in self.log.read_text().splitlines()] if self.log.exists() else []

    def sync(self, prs, check=True):
        self.output.write_text(json.dumps({"prs": prs}))
        return self.run_command("bash", str(SCRIPT), str(self.output), check=check)

    def test_repairs_stale_lock_through_the_api_and_is_idempotent(self):
        command = ("cargo", "metadata", "--manifest-path", "fuzz/Cargo.toml",
                   "--all-features", "--locked", "--format-version", "1")
        self.assertNotEqual(self.run_command(*command, check=False).returncode, 0)
        before = self.remote_head()
        self.sync([{"head_branch": self.branch}])
        self.run_command(*command)
        after = self.remote_head()
        self.assertNotEqual(before, after)
        self.assertEqual(self.run_command("git", "rev-parse", "HEAD").stdout.strip(), after)
        self.assertEqual(self.run_command("git", "rev-parse", f"{after}^").stdout.strip(), before)
        self.assertEqual(self.run_command("git", "diff", "--name-only", before, after).stdout.strip(),
                         "fuzz/Cargo.lock")
        [request] = self.requests()
        change = request["variables"]["input"]
        self.assertEqual(change["branch"], {"repositoryNameWithOwner": REPOSITORY,
                                            "branchName": self.branch})
        self.assertEqual(change["expectedHeadOid"], before)
        self.assertEqual(change["message"], {"headline": "fix(release): synchronize fuzz workspace lockfile"})
        [addition] = change["fileChanges"]["additions"]
        self.assertEqual(addition["path"], "fuzz/Cargo.lock")
        self.assertEqual(base64.b64decode(addition["contents"]),
                         (self.repo / "fuzz/Cargo.lock").read_bytes())
        self.sync([{"head_branch": self.branch}])
        self.assertEqual(self.remote_head(), after)
        self.assertEqual(len(self.requests()), 1)
        self.assertEqual(self.run_command("git", "status", "--porcelain").stdout, "")

    def test_refuses_a_release_branch_another_writer_advanced(self):
        before = self.remote_head()
        self.env["FAKE_GH_ADVANCE"] = "1"
        self.assertNotEqual(self.sync([{"head_branch": self.branch}], check=False).returncode, 0)
        # The other writer's commit stands; nothing was committed over it.
        self.run_command("git", "fetch", "origin", f"refs/heads/{self.branch}")
        self.assertEqual(self.run_command("git", "log", "-1", "--format=%s", "FETCH_HEAD").stdout.strip(),
                         "another writer")
        self.assertEqual(self.run_command("git", "rev-parse", "FETCH_HEAD^").stdout.strip(), before)

    def test_requires_the_repository(self):
        del self.env["GITHUB_REPOSITORY"]
        self.assertNotEqual(self.sync([{"head_branch": self.branch}], check=False).returncode, 0)
        self.assertEqual(self.requests(), [])
        self.assertEqual(self.remote_head(), self.run_command("git", "rev-parse", "HEAD").stdout.strip())

    def test_no_release_is_noop(self):
        self.sync([])
        self.assertEqual(self.run_command("git", "branch", "--show-current").stdout.strip(), "main")

    def test_rejects_non_release_branch(self):
        self.assertNotEqual(self.sync([{"head_branch": "main"}], check=False).returncode, 0)

    def test_rejects_malformed_output(self):
        self.output.write_text("{}")
        result = self.run_command("bash", str(SCRIPT), str(self.output), check=False)
        self.assertNotEqual(result.returncode, 0)


if __name__ == "__main__":
    unittest.main()
