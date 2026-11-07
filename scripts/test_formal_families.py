import copy
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).parent))
import formal_families as ff  # noqa: E402


class FamilyPlanTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "repo"
        self.src = Path(self.temp.name) / "assembled"
        self.graph = {
            "binary64/Base": set(), "gappa/Hints": {"binary64/Base"},
            "gappa/LnKernel": {"binary64/Base", "gappa/ln_bound"},
            "gappa/ln_bound": {"gappa/Hints"},
            "gappa/FastEntry": {"gappa/LnKernel"},
            "gappa/BvnKernel": {"binary64/Base"},
            "audit/Audit": {"binary64/Base"},
            "gappa/KernelAudit": {"gappa/LnKernel", "gappa/FastEntry", "gappa/BvnKernel"},
            "gappa/CertificateAudit": {"gappa/ln_bound"},
            "extraction/Crosscheck": {"binary64/Base"},
            "extraction/InternalCrosscheck": {"gappa/FastEntry"},
            "extraction/BvnCrosscheck": {"gappa/BvnKernel"},
        }
        files = {
            "formal/binary64/Base.v": "", "formal/gappa/Hints.v": "",
            "formal/ln/LnKernel.v": "", "formal/ln/bound.g": "",
            "formal/fast/FastEntry.v": "", "formal/bivariate/BvnKernel.v": "",
            "formal/audit/Audit.v": "From Binary64 Require Base.\nPrint Assumptions Base.ok.\n",
            "formal/audit/KernelAudit.v": "Require LnKernel FastEntry BvnKernel.\n"
            "Print Assumptions LnKernel.ok.\nPrint Assumptions FastEntry.ok.\n"
            "Print Assumptions BvnKernel.ok.\n",
        }
        for module, (_, driver) in ff.EXTRACTIONS.items():
            files[f"formal/extraction/{module}.v"] = ""
            files[f"formal/extraction/{driver}"] = ""
        for name in ["scripts/check_formal.sh", "scripts/formal_families.py", "scripts/formal_affected.py",
                     ".cargo/coq-image", ".cargo/coq-packages", "scripts/formal_deps.sh", "formal/axioms.expected"]:
            files[name] = "pinned"
        for name, contents in files.items():
            self.write(self.root / name, contents)
        for key in self.graph:
            self.write(self.src / (key + ".v"), "")
        self.write(self.src / "audit/Audit.v", files["formal/audit/Audit.v"])
        self.write(self.src / "gappa/KernelAudit.v", files["formal/audit/KernelAudit.v"])
        self.write(self.src / "gappa/CertificateAudit.v", "Require ln_bound.\nPrint Assumptions ln_bound.l1.\n")
        self.write(self.src / "_CoqProject", '-R binary64 Binary64\n-R gappa ""\n')

    @staticmethod
    def write(path, text):
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def plan(self):
        return ff.make_plan(self.root, self.src, self.graph)

    def test_bivariate_selection_excludes_unrelated_kernels_and_extractions(self):
        plan = self.plan()
        self.assertEqual(ff.select(plan, ["formal/bivariate/BvnKernel.v"]), ["bivariate"])
        unit = plan["families"]["bivariate"]
        self.assertEqual(set(unit["closure"]), {"binary64/Base", "gappa/BvnKernel", "extraction/BvnCrosscheck"})
        self.assertEqual([e["module"] for e in unit["extractions"]], ["BvnCrosscheck"])

    def test_change_selects_every_dependent_family_and_extraction(self):
        plan = self.plan()
        self.assertEqual(ff.select(plan, ["formal/ln/LnKernel.v"]), ["fast", "internal-crosscheck", "ln"])
        self.assertEqual(ff.select(plan, ["formal/ln/bound.g"]), ["fast", "internal-crosscheck", "ln"])

    def test_shared_unknown_renamed_and_gate_changes_select_everything(self):
        plan = self.plan()
        for path in ["formal/binary64/Base.v", "formal/axioms.expected", "scripts/check_formal.sh",
                     "formal/ln/Removed.v", "crates/morphiq-numerics/src/ln/stage.rs", ".cargo/coq-image",
                     ".github/workflows/ci.yml", "unfamiliar.file", "formal/binding.sha256"]:
            with self.subTest(path=path):
                self.assertEqual(ff.select(plan, [path]), sorted(plan["families"]))

    def test_union_preserves_every_audit_certificate_and_extraction(self):
        plan = self.plan()
        units = plan["families"].values()
        self.assertCountEqual([x for u in units for x in u["kernel_entries"]],
                              ["LnKernel.ok", "FastEntry.ok", "BvnKernel.ok"])
        self.assertEqual(sum(len(u["certificates"]) for u in units), 1)
        self.assertCountEqual([e["module"] for u in units for e in u["extractions"]], ff.EXTRACTIONS)
        self.assertEqual(sum(u["base_audit"] for u in units), 1)

    def test_unowned_entry_module_and_extraction_fail_closed(self):
        original = copy.deepcopy(self.graph)
        for mode in ["entry", "module", "extraction"]:
            with self.subTest(mode=mode):
                self.graph = copy.deepcopy(original)
                if mode == "entry":
                    p = self.src / "gappa/KernelAudit.v"
                    old = p.read_text(); p.write_text(old + "Print Assumptions Missing.ok.\n")
                elif mode == "module":
                    self.graph["gappa/Unowned"] = set()
                else:
                    p = self.root / "formal/extraction/Other.v"; p.write_text("")
                with self.assertRaises(ValueError):
                    self.plan()
                if mode == "entry": p.write_text(old)
                if mode == "extraction": p.unlink()

    def test_missing_dependency_and_certificate_report_are_rejected(self):
        self.graph["gappa/LnKernel"].add("gappa/Missing")
        with self.assertRaisesRegex(ValueError, "did not resolve"):
            self.plan()
        self.graph["gappa/LnKernel"].remove("gappa/Missing")
        (self.src / "gappa/CertificateAudit.v").write_text("")
        with self.assertRaisesRegex(ValueError, "every generated certificate"):
            self.plan()

    def test_cache_keys_follow_dependency_content_not_unrelated_families(self):
        before = self.plan()
        (self.src / "gappa/LnKernel.v").write_text("changed")
        after = self.plan()
        changed = {n for n in before["families"] if before["families"][n]["cache_key"] != after["families"][n]["cache_key"]}
        self.assertEqual(changed, {"ln", "fast", "internal-crosscheck"})
        (self.root / "formal/axioms.expected").write_text("changed allowlist")
        latest = self.plan()
        self.assertTrue(all(after["families"][n]["cache_key"] != latest["families"][n]["cache_key"] for n in after["families"]))

    def test_apply_family_keeps_only_owned_audits_and_extraction_roots(self):
        plan = self.plan()
        ff.apply_family(plan, "bivariate", self.src)
        self.assertEqual(ff.audit_entries((self.src / "gappa/KernelAudit.v").read_text()), ["BvnKernel.ok"])
        self.assertEqual(ff.audit_entries((self.src / "gappa/CertificateAudit.v").read_text()), [])
        self.assertFalse((self.src / "audit/Audit.v").exists())
        self.assertEqual({p.stem for p in (self.src / "extraction").glob("*.v")}, {"BvnCrosscheck"})

    def test_audit_parser_preserves_repeated_reports_and_rejects_executable_commands(self):
        self.assertEqual(ff.audit_entries("(* nested (* comment *) *)\nRequire A\n B.\nPrint Assumptions A.ok."), ["A.ok"])
        self.assertEqual(ff.audit_entries("Print Assumptions A.ok.\nPrint Assumptions A.ok."), ["A.ok", "A.ok"])
        for text in ["Axiom escape : True.", "(* unterminated"]:
            with self.assertRaises(ValueError): ff.audit_entries(text)


if __name__ == "__main__":
    unittest.main()
