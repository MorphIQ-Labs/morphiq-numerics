import os
import tempfile
import subprocess
from pathlib import Path
import unittest

from scripts import formal_relevant as fr

BOUND = {"crates/morphiq-numerics/src/exp/mod.rs", "docs/exp.md"}


def first(*paths):
    return fr.first_affecting(list(paths), BOUND)


class FormalRelevantTest(unittest.TestCase):
    def test_a_proof_is_affected(self):
        self.assertEqual(first("formal/exp/ExpKernel.v"), "formal/exp/ExpKernel.v")

    def test_a_bound_file_is_affected(self):
        self.assertEqual(first("docs/exp.md"), "docs/exp.md")
        self.assertEqual(first("README.md", "docs/exp.md"), "docs/exp.md")

    def test_library_source_is_affected_unless_it_is_a_test(self):
        self.assertIsNotNone(first("crates/morphiq-numerics/src/random.rs"))
        self.assertIsNone(first("crates/morphiq-numerics/src/random/tests.rs"))
        self.assertIsNone(first("crates/morphiq-numerics/src/log_space/normalize_tests.rs"))
        self.assertIsNone(first("crates/morphiq-numerics/src/lanes/tests/bench.rs"))

    def test_the_lane_and_the_workspace_are_affected(self):
        for path in (
            "scripts/check_formal.sh",
            "scripts/formal_affected.py",
            "scripts/write_gappa_proofs.sh",
            ".cargo/coq-image",
            ".github/workflows/ci.yml",
            "Cargo.lock",
            "Cargo.toml",
            "rust-toolchain.toml",
            "crates/reference/src/lib.rs",
        ):
            self.assertEqual(first(path), path, path)

    def test_known_prose_paths_are_not_affected(self):
        self.assertIsNone(first("README.md", "AGENTS.md", "docs/adr/0002-fma.md", ""))

    def test_unclassified_paths_select_the_full_gate(self):
        for path in ["CHANGELOG.md", "docs/unbound.md", "crates/reference/fixtures/exp.json",
                     "generators/unbound.py", ".github/workflows/release.yml", "unknown.file", "README.md "]:
            self.assertEqual(first(path), path)

    def test_renaming_a_proof_to_prose_keeps_the_removed_source_in_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            previous = os.getcwd()
            try:
                os.chdir(directory)
                def git(*args):
                    return subprocess.check_output(["git", "-c", "commit.gpgsign=false", *args], text=True, stderr=subprocess.DEVNULL).strip()
                git("init"); git("config", "user.name", "fixture"); git("config", "user.email", "fixture@example.invalid")
                Path("formal/exp").mkdir(parents=True)
                Path("formal/exp/Old.v").write_text("(* proof fixture *)\n")
                git("add", "."); git("commit", "-m", "fixture: original")
                base = git("rev-parse", "HEAD")
                git("mv", "formal/exp/Old.v", "README.md"); git("commit", "-m", "fixture: rename")
                paths = fr.changed_paths(base, "HEAD")
                self.assertEqual(set(paths), {"formal/exp/Old.v", "README.md"})
                self.assertEqual(fr.first_affecting(paths, set()), "formal/exp/Old.v")
            finally:
                os.chdir(previous)

    def test_the_bindings_are_read_from_every_manifest(self):
        with tempfile.TemporaryDirectory() as root:
            for directory, line in (("formal", "0  docs/a.md\\n"), ("formal/exp", "0  docs/b.md\\n")):
                os.makedirs(os.path.join(root, directory), exist_ok=True)
                with open(os.path.join(root, directory, "binding.sha256"), "w") as handle:
                    handle.write(line.replace("\\n", "\n"))
            self.assertEqual(fr.bound_files(root), {"docs/a.md", "docs/b.md"})


if __name__ == "__main__":
    unittest.main()
