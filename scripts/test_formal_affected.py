import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(__file__))
import formal_affected as fa  # noqa: E402

# Four kernel modules: B uses A, C uses B and exp-cert, D is alone.
COQDEP = """\
gappa/A.vo gappa/A.glob: gappa/A.v binary64/Base.vo
gappa/B.vo gappa/B.glob: gappa/B.v gappa/A.vo
gappa/exp_cert.vo gappa/exp_cert.glob: gappa/exp_cert.v gappa/Hints.vo
gappa/C.vo gappa/C.glob: gappa/C.v gappa/B.vo \\
 gappa/exp_cert.vo
gappa/D.vo gappa/D.glob: gappa/D.v
gappa/A.vio: gappa/A.v
"""
AUDIT = [
    "(** header *)",
    "Require A B C D.",
    "Print Assumptions A.one.",
    "Print Assumptions B.two.",
    "Print Assumptions C.three.",
    "Print Assumptions D.four.",
    "Print Assumptions Binary64.D.five.",
]


class FormalAffected(unittest.TestCase):
    def setUp(self):
        self.graph = fa.parse_coqdep(COQDEP)

    def test_graph(self):
        self.assertEqual(self.graph["gappa/C"], {"gappa/B", "gappa/exp_cert"})
        self.assertEqual(self.graph["gappa/A"], {"binary64/Base"})
        self.assertNotIn("gappa/A.vio", self.graph)

    def test_dependents_include_the_roots_and_their_users(self):
        self.assertEqual(
            fa.dependents_closure(self.graph, {"gappa/A"}), {"gappa/A", "gappa/B", "gappa/C"}
        )
        self.assertEqual(fa.dependents_closure(self.graph, {"gappa/D"}), {"gappa/D"})

    def test_a_kernel_file_is_its_module(self):
        self.assertEqual(fa.changed_modules(["formal/exp/A.v"], self.graph), {"gappa/A"})

    def test_a_certificate_is_the_module_of_its_proof(self):
        self.assertEqual(
            fa.changed_modules(["formal/exp/cert.g"], self.graph), {"gappa/exp_cert"}
        )

    def test_unknown_or_shared_paths_select_everything(self):
        for path in (
            "formal/binary64/Foo.v",
            "formal/exp/Missing.v",
            "formal/exp/notes.txt",
            "formal/unknown/A.v",
            "formal/axioms.expected",
            "formal/audit/Audit.v",
            "scripts/check_formal.sh",
            "scripts/formal_affected.py",
            ".cargo/coq-image",
            ".github/workflows/ci.yml",
        ):
            self.assertIsNone(fa.changed_modules([path], self.graph), path)

    def test_other_paths_do_not_touch_the_proofs(self):
        self.assertEqual(
            fa.changed_modules(
                ["docs/exp.md", "crates/morphiq-numerics/src/lib.rs", "formal/binding.sha256", ""],
                self.graph,
            ),
            set(),
        )

    def test_an_entry_is_kept_if_its_module_is_affected(self):
        kept = fa.select(AUDIT, AUDIT, self.graph, {"gappa/A"})
        prints = [line for line in kept if line.startswith("Print")]
        self.assertEqual(
            prints,
            ["Print Assumptions A.one.", "Print Assumptions B.two.", "Print Assumptions C.three."],
        )
        self.assertEqual(kept[:2], AUDIT[:2])

    def test_a_new_or_edited_entry_is_kept(self):
        base = [line for line in AUDIT if "D.four" not in line]
        kept = fa.select(AUDIT, base, self.graph, set())
        self.assertIn("Print Assumptions D.four.", kept)
        self.assertNotIn("Print Assumptions A.one.", kept)

    def test_a_qualified_entry_resolves_to_its_module(self):
        self.assertEqual(fa.entry_module("Print Assumptions Binary64.D.five."), "D")

    def test_an_entry_in_no_module_selects_everything(self):
        audit = AUDIT + ["Print Assumptions Ghost.x."]
        self.assertIsNone(fa.select(audit, audit, self.graph, {"gappa/A"}))

    def test_no_change_keeps_only_the_header(self):
        kept = fa.select(AUDIT, AUDIT, self.graph, set())
        self.assertEqual(kept, AUDIT[:2])


if __name__ == "__main__":
    unittest.main()
