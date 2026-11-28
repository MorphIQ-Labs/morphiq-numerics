"""Behavioral checks for enumeration plans and fail-closed coverage receipts."""
import json
from pathlib import Path
import tempfile
import unittest

from scripts import check_f32_sweeps as f32
from scripts.check_sweeps import MANIFESTS, OPERATIONS, load_windows, run_windows


def window(name="one", first="3feffffffffffffe", last="3ff0000000000002", anchor="3ff0000000000000"):
    return dict(name=name, operation="erfcx", first=first, last=last, anchor=anchor, source="test")


class NormalSweepTests(unittest.TestCase):
    def load(self, rows, profile="full"):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "manifest.json"
            path.write_text(json.dumps(dict(schema_version=1, windows=rows)))
            return load_windows(path, profile, "strong_normal")

    def test_counts_include_both_endpoints_and_smoke_stays_inside_declared_windows(self):
        rows = [window(first="0000000000000000", last="0000000000001000", anchor="0000000000000000")]
        self.assertEqual(self.load(rows)[0]["expected"], 4097)
        smoke = self.load(rows, "smoke")[0]
        self.assertEqual(smoke["first"], "0000000000000000")
        self.assertEqual(smoke["last"], "0000000000000002")
        self.assertEqual(smoke["expected"], 3)
    def test_every_declared_manifest_loads_and_covers_each_operation(self):
        self.assertEqual({path.stem for path in MANIFESTS.glob("*.json")}, set(OPERATIONS))
        for target, operations in OPERATIONS.items():
            with self.subTest(target=target):
                path = MANIFESTS / f"{target}.json"
                full = load_windows(path, "full", target)
                short = load_windows(path, "smoke", target)
                self.assertEqual({row["operation"] for row in full}, set(operations))
                self.assertEqual(len(short), len(full))
                for complete, sample in zip(full, short):
                    self.assertLessEqual(int(complete["first"], 16), int(sample["first"], 16))
                    self.assertLessEqual(int(sample["last"], 16), int(complete["last"], 16))
                    self.assertLessEqual(sample["expected"], 5)

    def test_invalid_empty_duplicate_overlapping_and_unbounded_plans_are_rejected(self):
        cases = [[], [window(), window()], [window(), window(name="overlap")],
                 [window(first="3ff0000000000001", last="3ff0000000000000")],
                 [window(first="7fefffffffffffff", last="8000000000000000", anchor="8000000000000000")],
                 [window(first="7ff0000000000000", last="7ff0000000000000", anchor="7ff0000000000000")],
                 [window(first="0000000000000000", last="0000000000100000", anchor="0000000000000000")],
                 [window(name="../outside")], [dict(window(), operation="unknown")],
                 [window(first="0")]]
        for rows in cases:
            with self.subTest(rows=rows), self.assertRaises(ValueError):
                self.load(rows)

    def run_fake(self, behavior):
        # Replace only the enumerator process boundary. Exercise real logs,
        # receipt writes and count validation without building or doing math.
        with tempfile.TemporaryDirectory() as temp:
            output = Path(temp)
            binary = output / "enumerator"
            binary.write_text("#!/usr/bin/env python3\nimport sys\n" + behavior)
            binary.chmod(0o755)
            rows = self.load([window()])
            receipt = dict(status="running", checked=0, windows=[])
            try:
                run_windows(binary, output, "scalar", rows, receipt)
                error = None
            except RuntimeError as exc:
                error = str(exc)
            saved = json.loads((output / "coverage.json").read_text())
            logs = [p.name for p in (output / "scalar").iterdir()]
            return error, saved, logs

    def test_exact_count_is_required_even_after_a_successful_process_exit(self):
        for behavior in ["print(4)\n", "print('5 extra')\n", "print('')\n", "sys.exit(23)\n"]:
            with self.subTest(behavior=behavior):
                error, saved, logs = self.run_fake(behavior)
                self.assertIsNotNone(error)
                self.assertEqual(saved["checked"], 0)
                self.assertEqual(saved["windows"][0]["status"], "failed")
                self.assertIn("strong_normal-one.stderr.log", logs)
                self.assertIn("strong_normal-one.stdout.log", logs)

    def test_completed_counts_are_recorded_with_the_exact_range_and_mode(self):
        error, saved, _ = self.run_fake("print(int(sys.argv[4], 16) - int(sys.argv[3], 16) + 1)\n")
        self.assertIsNone(error)
        self.assertEqual(saved["checked"], 5)
        self.assertEqual(saved["windows"][0]["checked"], 5)
        self.assertEqual(saved["windows"][0]["mode"], "scalar")
        self.assertEqual(saved["windows"][0]["status"], "passed")
        self.assertEqual(saved["windows"][0]["first"], "3feffffffffffffe")


class NarrowSweepTests(unittest.TestCase):
    def test_shards_partition_every_binary32_encoding_exactly(self):
        next_first = 0
        for shard in range(f32.SHARDS):
            first, last = f32.shard_range(shard, f32.SHARDS)
            self.assertEqual(first, next_first)
            pieces = f32.chunks(first, last)
            self.assertEqual((pieces[0][0], pieces[-1][1]), (first, last))
            self.assertTrue(all(b[0] == a[1] + 1 for a, b in zip(pieces, pieces[1:])))
            self.assertTrue(all(end - start < 1_048_576 for start, end in pieces))
            next_first = last + 1
        self.assertEqual(next_first, 2 ** 32)
        for shard, shards in [(-1, 64), (64, 64), (0, 0), (0, 3)]:
            with self.assertRaises(ValueError):
                f32.shard_range(shard, shards)

    def test_the_weekly_rotation_reaches_every_unit_once_per_cycle(self):
        total = len(f32.operations()) * f32.SHARDS
        weeks = -(-total // f32.WEEKLY)
        seen = [tuple(u.values()) for week in range(weeks) for u in f32.schedule(week)]
        self.assertEqual(len(set(seen)), total)
        self.assertNotIn(("elementary", "atan2"), f32.operations())

    def test_a_chunk_passes_only_with_its_exact_count(self):
        for behavior, expected in [("print(int(sys.argv[5], 16) - int(sys.argv[4], 16) + 1)\n", True),
                                   ("print(1)\n", False), ("sys.exit(3)\n", False)]:
            with self.subTest(behavior=behavior), tempfile.TemporaryDirectory() as temp:
                binary = Path(temp) / "enumerator"
                binary.write_text("#!/usr/bin/env python3\nimport sys\n" + behavior)
                binary.chmod(0o755)
                results = []
                f32.run_chunks(binary, Path(temp), "strong_normal", 0, [(0, 9), (10, 19)], 2,
                               lambda first, last, passed: results.append((first, last, passed)))
                self.assertEqual(results, [(0, 9, expected), (10, 19, expected)])


if __name__ == "__main__":
    unittest.main()
