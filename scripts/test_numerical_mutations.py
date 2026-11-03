"""Negative controls for mutation receipts and inventory floors."""
import unittest

from scripts.check_numerical_mutations import REQUIRED_FAULTS, catalog_entries, check_inventory, qualifies


class CatalogTests(unittest.TestCase):
    def test_controls_cannot_replace_required_faults(self):
        entries = [{"id": kind, "category": kind, "failure_contains": "oracle differs"}
                   for kind in sorted(REQUIRED_FAULTS)]
        self.assertEqual(catalog_entries({"schema": 1, "mutations": entries}), entries)
        entries[0] = dict(entries[0], expectation="equivalent-control",
                          category="equivalent-control", derivation="equivalence argument")
        with self.assertRaisesRegex(ValueError, "missing required numerical fault"):
            catalog_entries({"schema": 1, "mutations": entries})

    def test_ambiguous_catalogs_fail(self):
        entry = {"id": "fault", "category": "perturbed-constant", "failure_contains": "oracle differs"}
        for catalog in [
            {"schema": 2, "mutations": [entry]},
            {"schema": 1, "mutations": []},
            {"schema": 1, "mutations": [entry, entry]},
            {"schema": 1, "mutations": [dict(entry, id="")]},
            {"schema": 1, "mutations": [dict(entry, expectation="unknown")]},
            {"schema": 1, "mutations": [dict(entry, expectation="equivalent-control")]},
        ]:
            with self.subTest(catalog=catalog), self.assertRaises(ValueError):
                catalog_entries(catalog)


class ReceiptTests(unittest.TestCase):
    entry = {"test": "kernel::rounding_is_correct", "failure_contains": "a neighbour is nearer"}
    failure = """running 1 test
test kernel::rounding_is_correct ... FAILED
thread 'kernel::rounding_is_correct' panicked: a neighbour is nearer
test result: FAILED. 0 passed; 1 failed; 0 ignored; 0 measured; 7 filtered out;
"""
    baseline = """running 1 test
test kernel::rounding_is_correct ... ok
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 7 filtered out;
"""

    def test_only_the_named_numerical_assertion_is_a_kill(self):
        self.assertTrue(qualifies(self.failure, 101, self.entry, False))
        for log, code in [
            ("error: could not compile kernel", 101),
            (self.failure, 0),
            (self.failure, None),
            (self.failure, -9),
            (self.failure.replace("kernel::rounding_is_correct", "another_test"), 101),
            (self.failure.replace("a neighbour is nearer", "index out of bounds"), 101),
            (self.failure.replace("running 1 test", "running 0 tests"), 101),
            (self.failure.replace("1 failed; 0 ignored", "0 failed; 1 ignored"), 101),
            (self.baseline, 0),
        ]:
            with self.subTest(log=log, code=code):
                self.assertFalse(qualifies(log, code, self.entry, False))

    def test_baseline_must_run_and_pass_exactly_one_named_test(self):
        self.assertTrue(qualifies(self.baseline, 0, self.entry, True))
        for log, code in [
            (self.failure, 101),
            (self.baseline, 101),
            ("test result: ok. 0 passed; 0 failed; 0 ignored;", 0),
            (self.baseline.replace("kernel::rounding_is_correct", "another_test"), 0),
            (self.baseline.replace("1 passed; 0 failed; 0 ignored", "0 passed; 0 failed; 1 ignored"), 0),
        ]:
            with self.subTest(log=log, code=code):
                self.assertFalse(qualifies(log, code, self.entry, True))

    def test_equivalent_control_is_explicit_and_never_counts_as_a_kill(self):
        control = dict(self.entry, expectation="equivalent-control")
        self.assertTrue(qualifies(self.baseline, 0, control, False))
        self.assertFalse(qualifies(self.failure, 101, control, False))
        self.assertFalse(qualifies(self.baseline, 0, self.entry, False))


class InventoryTests(unittest.TestCase):
    floors = {"packages": {"library": 2}, "files": {"a.rs": 1, "b.rs": 1}}

    def test_new_mutants_cannot_hide_a_missing_module(self):
        rows = [{"package": "library", "file": "a.rs"}] * 10
        with self.assertRaisesRegex(ValueError, "b.rs: 0 < 1"):
            check_inventory(rows, self.floors)

    def test_package_and_file_floors_accept_growth_and_reject_disappearance(self):
        rows = [{"package": "library", "file": "a.rs"}, {"package": "library", "file": "b.rs"}]
        self.assertEqual(check_inventory(rows, self.floors)["packages"], {"library": 2})
        self.assertEqual(check_inventory(rows + rows, self.floors)["packages"], {"library": 4})
        with self.assertRaises(ValueError):
            check_inventory([], self.floors)


if __name__ == "__main__":
    unittest.main()
