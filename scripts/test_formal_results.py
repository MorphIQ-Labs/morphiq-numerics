import copy
import unittest

from scripts.formal_results import aggregate, receipt, check_status


class FormalResultsTests(unittest.TestCase):
    def setUp(self):
        self.plan = dict(selected=["a", "b"], base_entries=1, inputs=dict(binding="bind", public="pub", internal="int"),
                         families={name: dict(cache_key=name, kernel_entries=[name + ".ok"],
                                              certificates=[], base_audit=False, extractions=[])
                                   for name in ["a", "b", "c"]})
        self.results = [receipt(self.plan, name, 1, 0) for name in ["a", "b"]]

    def test_exact_successful_selected_set_passes(self):
        self.assertEqual(aggregate(self.plan, self.results)["kernel_entries"], 2)

    def test_missing_duplicate_and_extra_results_fail(self):
        for results in [[], self.results[:1], self.results + self.results[:1],
                        self.results + [receipt(self.plan, "c", 1, 0)]]:
            with self.subTest(results=results), self.assertRaises(ValueError):
                aggregate(self.plan, results)

    def test_stale_source_input_or_missing_check_fails(self):
        for field in ["cache_key", "inputs", "kernel_entries", "certificates", "base_audit", "base_entries", "extractions"]:
            results = copy.deepcopy(self.results)
            results[0][field] = "tampered"
            with self.subTest(field=field), self.assertRaises(ValueError):
                aggregate(self.plan, results)

    def test_empty_duplicate_and_unknown_selections_fail(self):
        for selected in [[], ["a", "a"], ["unknown"]]:
            plan = copy.deepcopy(self.plan); plan["selected"] = selected
            with self.subTest(selected=selected), self.assertRaises(ValueError):
                aggregate(plan, self.results)

    def test_report_count_mismatch_refuses_receipt(self):
        with self.assertRaises(ValueError):
            receipt(self.plan, "a", 0, 0)
        with self.assertRaises(ValueError):
            receipt(self.plan, "a", 1, 1)

    def test_failed_cancelled_skipped_or_missing_required_job_fails(self):
        for value in ["failure", "cancelled", "skipped", ""]:
            for field in range(4):
                args = ["success", "success", "true", "success"]
                args[field] = value
                with self.subTest(value=value, field=field), self.assertRaises(ValueError):
                    check_status(*args)

    def test_only_explicit_unaffected_selection_allows_skipped_family_job(self):
        check_status("success", "success", "true", "success")
        check_status("success", "success", "false", "skipped")
        with self.assertRaises(ValueError):
            check_status("success", "skipped", "false", "skipped")


if __name__ == "__main__":
    unittest.main()
