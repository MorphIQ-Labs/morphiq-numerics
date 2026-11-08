import copy
import unittest

from scripts.formal_results import aggregate, receipt, full_receipt, matrix, check_status


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
            with self.subTest(selected=selected), self.assertRaises(ValueError):
                matrix(plan)

    def test_full_selection_runs_one_unsplit_gate_regardless_of_order(self):
        self.plan["selected"] = ["c", "b", "a"]
        jobs = matrix(self.plan)["include"]
        self.assertEqual(len(jobs), 1)
        self.assertEqual(jobs[0]["family"], "")
        self.assertEqual(jobs[0]["cache"], "formal-build")
        self.plan["selected"].reverse()
        self.assertEqual(matrix(self.plan)["include"], jobs)
        self.plan["families"]["c"]["cache_key"] = "changed"
        self.assertNotEqual(matrix(self.plan)["include"][0]["key"], jobs[0]["key"])

    def test_proper_subset_runs_only_its_family_gates(self):
        jobs = matrix(self.plan)["include"]
        self.assertEqual([j["family"] for j in jobs], ["a", "b"])
        self.assertEqual([j["cache"] for j in jobs], ["formal-family-a", "formal-family-b"])
        self.assertEqual([j["key"] for j in jobs], ["a", "b"])

    def test_full_receipt_covers_all_obligations_and_keeps_duplicate_entries(self):
        self.plan["selected"] = list(self.plan["families"])
        unit = self.plan["families"]["c"]
        unit.update(kernel_entries=["c.ok", "c.ok"], certificates=["cert"],
                    base_audit=True, extractions=["public", "internal", "bvn"])
        result = full_receipt(self.plan, 4, 1)
        self.assertEqual(aggregate(self.plan, [result]),
                         dict(execution="full", families=3, kernel_entries=4, certificates=1,
                              base_entries=1, extractions=3))
        for counts in [(3, 1), (4, 0), (5, 1), (4, 2)]:
            with self.subTest(counts=counts), self.assertRaises(ValueError):
                full_receipt(self.plan, *counts)

    def test_full_selection_rejects_family_missing_duplicate_and_mixed_evidence(self):
        self.plan["selected"] = list(self.plan["families"])
        result = full_receipt(self.plan, 3, 0)
        families = list(result["families"].values())
        for results in [[], families, [result, result], [result] + families]:
            with self.subTest(results=results), self.assertRaises(ValueError):
                aggregate(self.plan, results)

    def test_full_receipt_rejects_stale_sources_inputs_and_missing_checks(self):
        self.plan["selected"] = list(self.plan["families"])
        result = full_receipt(self.plan, 3, 0)
        for field in result["families"]["a"]:
            stale = copy.deepcopy(result)
            stale["families"]["a"][field] = "tampered"
            with self.subTest(field=field), self.assertRaises(ValueError):
                aggregate(self.plan, [stale])
        del result["families"]["c"]
        with self.assertRaises(ValueError):
            aggregate(self.plan, [result])

    def test_subset_rejects_full_completion_or_mixed_evidence(self):
        with self.assertRaises(ValueError):
            full_receipt(self.plan, 2, 0)
        full_plan = copy.deepcopy(self.plan)
        full_plan["selected"] = list(full_plan["families"])
        result = full_receipt(full_plan, 3, 0)
        for results in [[result], self.results + [result]]:
            with self.subTest(results=results), self.assertRaises(ValueError):
                aggregate(self.plan, results)

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
