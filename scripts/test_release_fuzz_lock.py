"""Exercise release synchronization against a local remote and real Cargo locks."""

import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPT = Path(__file__).with_name("sync_release_fuzz_lock.sh").resolve()


class ReleaseFuzzLockTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.env = dict(os.environ, CARGO_NET_OFFLINE="true")
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

    def sync(self, prs, check=True):
        self.output.write_text(json.dumps({"prs": prs}))
        return self.run_command("bash", str(SCRIPT), str(self.output), check=check)

    def test_repairs_stale_lock_and_is_idempotent(self):
        command = ("cargo", "metadata", "--manifest-path", "fuzz/Cargo.toml",
                   "--all-features", "--locked", "--format-version", "1")
        self.assertNotEqual(self.run_command(*command, check=False).returncode, 0)
        before = self.run_command("git", "rev-parse", "HEAD").stdout.strip()
        self.sync([{"head_branch": self.branch}])
        self.run_command(*command)
        after = self.run_command("git", "rev-parse", "HEAD").stdout.strip()
        self.assertNotEqual(before, after)
        self.assertEqual(self.run_command("git", "diff", "--name-only", before, after).stdout.strip(),
                         "fuzz/Cargo.lock")
        remote = self.run_command("git", "ls-remote", "origin", f"refs/heads/{self.branch}").stdout
        self.assertEqual(remote.split()[0], after)
        self.sync([{"head_branch": self.branch}])
        self.assertEqual(self.run_command("git", "rev-parse", "HEAD").stdout.strip(), after)
        self.assertEqual(self.run_command("git", "status", "--porcelain").stdout, "")

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
