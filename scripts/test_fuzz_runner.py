"""Exercise the real runner's shell control flow without building or fuzzing.

On macOS /bin/bash is Bash 3.2; PATH may instead select a newer Homebrew Bash.
Both must preserve the scalar/SIMD argument vectors and propagate failures.
Cargo is replaced at its CLI boundary; no production source text is asserted.
"""
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SHELLS = sorted({str(Path(p).resolve()) for p in ["/bin/bash", shutil.which("bash")]
                 if p and Path(p).is_file()})


class FuzzRunnerTests(unittest.TestCase):
    def run_runner(self, shell, fail_test=False, arguments=("1",)):
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
            result = subprocess.run([shell, str(root / "scripts/check_fuzz.sh"), *arguments],
                                    env=env, text=True, capture_output=True, timeout=30)
            calls = [json.loads(line) for line in log.read_text().splitlines()] if log.exists() else []
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
                self.assertEqual(len(replay), 12)
                expected_targets = {"elementary", "fast_elementary", "fast_normal", "strong_normal",
                                    "strong_density", "arithmetic"}
                self.assertEqual({args[args.index("--") + 1] for args in replay}, expected_targets)
                for args in replay:
                    self.assertIn("--no-default-features", args)
                campaigns = [args for args in calls if args[0].startswith("+")]
                self.assertEqual(len(campaigns), 12)
                self.assertEqual({args[3] for args in campaigns}, expected_targets)
                for args in campaigns:
                    self.assertIn("-max_len=" + ("257" if args[3] == "elementary" else "1041"), args)
                self.assertEqual({args[args.index("--features") + 1] for args in campaigns},
                                 {"fuzzing", "fuzzing,simd"})

    def test_named_targets_run_alone_and_unknown_names_fail_before_any_work(self):
        for shell in SHELLS:
            with self.subTest(shell=shell):
                result, calls = self.run_runner(shell, arguments=("1", "strong_normal"))
                self.assertEqual(result.returncode, 0, result.stderr)
                replay = [args for args in calls if args[0] == "run"]
                campaigns = [args for args in calls if args[0].startswith("+")]
                self.assertEqual([args[args.index("--") + 1] for args in replay], ["strong_normal"] * 2)
                self.assertEqual([args[3] for args in campaigns], ["strong_normal"] * 2)
                result, calls = self.run_runner(shell, arguments=("1", "strong_normal", "missing"))
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("unknown fuzz target: missing", result.stderr)
                self.assertEqual(calls, [])

    def test_the_listing_names_every_declared_fuzz_binary(self):
        listed = subprocess.run(["bash", str(ROOT / "scripts/check_fuzz.sh"), "--list"],
                                text=True, capture_output=True, check=True).stdout.split()
        binaries = sorted(path.stem for path in (ROOT / "fuzz/fuzz_targets").glob("*.rs"))
        self.assertEqual(sorted(listed), binaries)

    def test_a_failed_oracle_test_stops_before_fuzzing(self):
        for shell in SHELLS:
            with self.subTest(shell=shell):
                result, calls = self.run_runner(shell, fail_test=True)
                self.assertEqual(result.returncode, 23, result.stderr)
                self.assertFalse(any(args[0] == "run" or args[0].startswith("+") for args in calls))


class FastNormalSeeds(unittest.TestCase):
    def test_packets_cover_all_operations_lengths_and_domain_neighbors(self):
        from scripts.seed_elementary_fuzz import fast_normal_seeds

        inputs = {op: set() for op in range(3)}
        lengths = {op: set() for op in range(3)}
        for data in fast_normal_seeds():
            op = data[0]
            self.assertEqual((len(data) - 1) % 16, 0)
            count = (len(data) - 1) // 16
            self.assertLessEqual(count, 65)
            lengths[op].add(count)
            inputs[op].update(struct.unpack_from("<Q", data, i)[0]
                              for i in range(1, len(data), 16))
        for op in range(3):
            self.assertEqual(lengths[op], set(range(66)))
            for edge in [2**-33, 0.5, 8.0, 16.0, 22.5]:
                center = struct.unpack("<Q", struct.pack("<d", edge))[0]
                for delta in [-1, 0, 1]:
                    for sign in [0, 1 << 63]:
                        self.assertIn((center + delta) | sign, inputs[op])
            for word in [0, 1 << 63, 0x7FF0000000000000, 0xFFF0000000000000,
                         0x7FF0000000000001, 0xFFFABCDE12345678]:
                self.assertIn(word, inputs[op])


class StrongNormalSeeds(unittest.TestCase):
    def test_full_domain_inputs_and_all_slice_lengths_are_retained(self):
        from scripts.seed_elementary_fuzz import strong_normal_seeds

        inputs = {op: set() for op in range(3)}
        lengths = {op: set() for op in range(3)}
        for data in strong_normal_seeds():
            op = data[0]
            self.assertEqual((len(data) - 1) % 16, 0)
            lengths[op].add((len(data) - 1) // 16)
            inputs[op].update(struct.unpack_from("<Q", data, i)[0]
                              for i in range(1, len(data), 16))
        for op in range(3):
            self.assertEqual(lengths[op], set(range(66)))
            for center in [0x403AA0F4D2E063CF, 0x40433E21DC3F3BD8,
                           0x402095B059D67C4D, 0x5FF6A09E667F3BCD,
                           0x7FC20DD750429B6E]:
                for delta in range(-3, 4):
                    for sign in [0, 1 << 63]:
                        self.assertIn((center + delta) | sign, inputs[op])
            for exponent in range(1, 2047):
                for sign in [0, 1 << 63]:
                    self.assertIn((exponent << 52) | sign, inputs[op])
            for word in [0, 1 << 63, 1, 0x7FEFFFFFFFFFFFFF,
                         0x7FF0000000000001, 0xFFFABCDE12345678]:
                self.assertIn(word, inputs[op])


class StrongDensitySeeds(unittest.TestCase):
    def test_regime_joins_and_all_slice_lengths_are_retained(self):
        from scripts.seed_elementary_fuzz import strong_density_seeds

        inputs = {op: set() for op in range(4)}
        lengths = {op: set() for op in range(4)}
        for data in strong_density_seeds():
            op = data[0]
            self.assertEqual((len(data) - 1) % 16, 0)
            lengths[op].add((len(data) - 1) // 16)
            inputs[op].update(struct.unpack_from("<Q", data, i)[0]
                              for i in range(1, len(data), 16))
        for op in range(4):
            self.assertEqual(lengths[op], set(range(66)))
            for center in [0x402095B059D67C4D, 0x40434A429AC2A6BC,
                           0x5FF6A09E667F3BCD]:
                for delta in range(-3, 4):
                    for sign in [0, 1 << 63]:
                        self.assertIn((center + delta) | sign, inputs[op])


if __name__ == "__main__":
    unittest.main()
