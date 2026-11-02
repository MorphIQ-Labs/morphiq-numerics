"""Exercise the real runner's shell control flow without building or fuzzing.

On macOS /bin/bash is Bash 3.2; PATH may instead select a newer Homebrew Bash.
Both must preserve the scalar/SIMD argument vectors and propagate failures.
Cargo is replaced at its CLI boundary; no production source text is asserted.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SHELLS = sorted({str(Path(p).resolve()) for p in ["/bin/bash", shutil.which("bash")]
                 if p and Path(p).is_file()})


class FuzzRunnerTests(unittest.TestCase):
    def run_runner(self, shell, fail_test=False):
        with tempfile.TemporaryDirectory(prefix="fuzz-runner-") as temp:
            root = Path(temp)
            for directory in ["scripts", ".cargo", "fuzz", "bin"]:
                (root / directory).mkdir()
            shutil.copyfile(ROOT / "scripts/check_fuzz.sh", root / "scripts/check_fuzz.sh")
            for pin in ["fuzz-version", "fuzz-nightly-version"]:
                shutil.copyfile(ROOT / ".cargo" / pin, root / ".cargo" / pin)
            (root / "fuzz/Cargo.lock").write_text("test lockfile\n")
            (root / "scripts/seed_elementary_fuzz.py").write_text(
                "import pathlib, sys\npathlib.Path(sys.argv[1]).mkdir(parents=True, exist_ok=True)\n")
            cargo = root / "bin/cargo"
            cargo.write_text(f"#!{sys.executable}\n" + '''import json, os, pathlib, sys
args = sys.argv[1:]
with open(os.environ["FUZZ_RUNNER_CALLS"], "a") as log:
    log.write(json.dumps(args) + "\\n")
if args == ["fuzz", "--version"]:
    print("cargo-fuzz " + pathlib.Path(".cargo/fuzz-version").read_text().strip())
if os.environ["FUZZ_RUNNER_FAIL_TEST"] == "1" and args[0] == "test":
    sys.exit(23)
''')
            cargo.chmod(0o755)
            log = root / "calls.jsonl"
            env = dict(os.environ, PATH=str(root / "bin") + os.pathsep + os.environ["PATH"],
                       FUZZ_RUNNER_CALLS=str(log), FUZZ_RUNNER_FAIL_TEST=str(int(fail_test)))
            result = subprocess.run([shell, str(root / "scripts/check_fuzz.sh"), "1"],
                                    env=env, text=True, capture_output=True, timeout=30)
            calls = [json.loads(line) for line in log.read_text().splitlines()]
            return result, calls

    def test_scalar_and_simd_arguments_work_on_each_installed_bash(self):
        self.assertTrue(SHELLS)
        for shell in SHELLS:
            with self.subTest(shell=shell):
                result, calls = self.run_runner(shell)
                self.assertEqual(result.returncode, 0, result.stderr)
                tests = [args for args in calls if args[0] == "test"]
                self.assertEqual(len(tests), 2)
                self.assertIn("--no-default-features", tests[0])
                self.assertNotIn("--features", tests[0])
                self.assertIn("--no-default-features", tests[1])
                self.assertEqual(tests[1][tests[1].index("--features") + 1], "simd")
                replay = [args for args in calls if args[0] == "run"]
                self.assertGreaterEqual(len(replay), 2)
                for args in replay:
                    self.assertIn("--no-default-features", args)
                campaigns = [args for args in calls if args[0].startswith("+")]
                self.assertGreaterEqual(len(campaigns), 2)
                self.assertEqual({args[args.index("--features") + 1] for args in campaigns},
                                 {"fuzzing", "fuzzing,simd"})

    def test_a_failed_oracle_test_stops_before_fuzzing(self):
        for shell in SHELLS:
            with self.subTest(shell=shell):
                result, calls = self.run_runner(shell, fail_test=True)
                self.assertEqual(result.returncode, 23, result.stderr)
                self.assertFalse(any(args[0] == "run" or args[0].startswith("+") for args in calls))


if __name__ == "__main__":
    unittest.main()
