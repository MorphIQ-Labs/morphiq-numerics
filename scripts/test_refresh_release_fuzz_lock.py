"""Exercise release lock refresh against real temporary Git/Cargo workspaces."""
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("refresh_release_fuzz_lock.py").resolve()
BRANCH = "release-plz-test"


class ReleaseLockTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="release-lock-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.remote = self.root / "remote.git"
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.git("init", "--bare", str(self.remote))
        self.git("init", "-b", "main")
        self.git("config", "user.name", "Release test")
        self.git("config", "user.email", "release@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.git("remote", "add", "origin", str(self.remote))
        (self.repo / "Cargo.toml").write_text('''[workspace]
members = ["lib", "arch"]
exclude = ["fuzz"]
resolver = "2"
[workspace.package]
version = "0.0.24"
''')
        for directory, name, dependency in [
            ("arch", "morphiq-numerics-arch", ""),
            ("lib", "morphiq-numerics", 'morphiq-numerics-arch = { path = "../arch" }'),
        ]:
            path = self.repo / directory
            (path / "src").mkdir(parents=True)
            (path / "src/lib.rs").write_text("")
            (path / "Cargo.toml").write_text(f'''[package]
name = "{name}"
version.workspace = true
edition = "2021"
[dependencies]
{dependency}
''')
        fuzz = self.repo / "fuzz"
        (fuzz / "src").mkdir(parents=True)
        (fuzz / "src/lib.rs").write_text("")
        (fuzz / "Cargo.toml").write_text('''[workspace]
[package]
name = "release-fuzz-test"
version = "0.0.0"
edition = "2021"
[dependencies]
morphiq-numerics = { path = "../lib" }
''')
        self.command("cargo", "generate-lockfile", "--manifest-path", "fuzz/Cargo.toml", "--offline")
        self.git("add", ".")
        self.git("commit", "-m", "initial")
        self.git("push", "origin", "main")
        self.git("checkout", "-b", BRANCH)
        manifest = self.repo / "Cargo.toml"
        manifest.write_text(manifest.read_text().replace("0.0.24", "0.0.25"))
        self.git("commit", "-am", "release")
        self.git("push", "origin", BRANCH)
        self.before = self.remote_head()
        self.git("checkout", "main")
        self.output = self.root / "release.json"
        self.output.write_text(json.dumps({"prs": [{"head_branch": BRANCH, "base_branch": "main"}]}))

    def command(self, *args):
        return subprocess.check_output(args, cwd=self.repo, stderr=subprocess.STDOUT, text=True).strip()

    def git(self, *args):
        return self.command("git", *args)

    def remote_head(self):
        return self.git("ls-remote", "origin", f"refs/heads/{BRANCH}").split()[0]

    def refresh(self, env=None):
        return subprocess.run([sys.executable, str(SCRIPT), str(self.output)], cwd=self.repo,
                              env=env, text=True, capture_output=True, timeout=60)

    def test_refreshes_existing_release_and_is_idempotent(self):
        result = self.refresh()
        self.assertEqual(result.returncode, 0, result.stderr)
        after = self.remote_head()
        self.assertNotEqual(after, self.before)
        self.assertEqual(self.git("diff", "--name-only", self.before, after), "fuzz/Cargo.lock")
        self.command("cargo", "metadata", "--manifest-path", "fuzz/Cargo.toml", "--locked", "--offline", "--format-version", "1")
        result = self.refresh()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.remote_head(), after)
        self.assertEqual(self.git("rev-parse", "main"), self.git("rev-parse", "origin/main"))

    def test_empty_release_output_is_a_noop(self):
        self.output.write_text('{"prs": []}')
        result = self.refresh()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(self.git("branch", "--show-current"), "main")
        self.assertEqual(self.remote_head(), self.before)

    def test_non_release_branch_is_rejected(self):
        self.output.write_text('{"prs": [{"head_branch": "main", "base_branch": "main"}]}')
        self.assertNotEqual(self.refresh().returncode, 0)
        self.assertEqual(self.remote_head(), self.before)

    def test_dirty_checkout_is_preserved(self):
        path = self.repo / "owner-work"
        path.write_text("preserve me")
        self.assertNotEqual(self.refresh().returncode, 0)
        self.assertEqual(path.read_text(), "preserve me")
        self.assertEqual(self.remote_head(), self.before)

    def test_cargo_failure_does_not_push(self):
        self.fake_cargo("exit 23\n")

    def test_unexpected_lockfile_change_does_not_push(self):
        self.fake_cargo("sed 's/0.0.24/0.0.99/g' fuzz/Cargo.lock > fuzz/new.lock\nmv fuzz/new.lock fuzz/Cargo.lock\n")

    def test_concurrent_branch_update_is_preserved(self):
        tree = self.git("rev-parse", f"{self.before}^{{tree}}")
        concurrent = self.git("commit-tree", tree, "-p", self.before, "-m", "concurrent owner work")
        # Make the owner update after refresh has fetched its starting commit.
        body = (f'{shlex.quote(shutil.which("cargo"))} "$@"\n'
                f'git push origin {concurrent}:refs/heads/{BRANCH}\n')
        self.fake_cargo(body, expected_head=concurrent)

    def fake_cargo(self, body, expected_head=None):
        directory = self.root / "bin"
        directory.mkdir()
        cargo = directory / "cargo"
        cargo.write_text("#!/bin/sh\n" + body)
        cargo.chmod(0o755)
        env = dict(os.environ, PATH=str(directory) + os.pathsep + os.environ["PATH"])
        self.assertNotEqual(self.refresh(env).returncode, 0)
        self.assertEqual(self.remote_head(), expected_head or self.before)


if __name__ == "__main__":
    unittest.main()
