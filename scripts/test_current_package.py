"""Independent small packages exercise cross-target binding and proof isolation."""
import json
from pathlib import Path
import tempfile
import unittest

from current_package import build_index, check_sources, check_proof_sources, digest, encoded
from print_axioms import parse_axioms


class CurrentPackageTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        for name in ("AronowAudit", "release-evidence", "tools", "catalog/works", "package"):
            (self.root / name).mkdir(parents=True)
        self.write("SAP/P001a/Defs.lean", "def SAP.P001a.T1Statement : Prop := True\n")
        self.write("SAP/P001a/Challenge.lean", "import SAP.P001a.Defs\ntheorem SAP.P001a.T1 : SAP.P001a.T1Statement := by sorry\n")
        self.write("SAP/P001a/Solution.lean", "import SAP.P001a.Defs\ntheorem SAP.P001a.T1 : SAP.P001a.T1Statement := by trivial\n")
        self.json("SAP/INDEX.json", {"P001a": {"work": "P001", "targets": 1, "theorems": 1, "decisions": {"whole": 1}}})
        row = {"target_id": "P001-T1", "decision": "whole", "theorem": "SAP.P001a.T1",
               "restriction": None, "axioms": [], "statement_definition": "SAP.P001a.T1Statement"}
        self.json("SAP/P001a/manifest.json", [row])
        self.json("SAP/P001a/comparator.json", {"theorem_names": ["SAP.P001a.T1"], "permitted_axioms": []})
        self.json("SAP/Works/INDEX.json", {"P001": {"title": "A paper", "citation": "An author.", "target_count": 1,
                                                   "decisions": {"whole": 1}, "unit_ids": ["P001a"]}})
        self.json("SAP/Works/P001/TARGET-MAP.json", [{**row, "unit_id": "P001a"}])
        self.json("catalog/works/P001.json", {"targets": [{"id": "P001-T1"}]})
        files = {p.relative_to(self.root).as_posix(): digest(p.read_bytes())
                 for p in self.root.rglob("*") if p.is_file() and not p.is_relative_to(self.root / "catalog")}
        catalog = {p.relative_to(self.root).as_posix(): digest(p.read_bytes())
                   for p in (self.root / "catalog").rglob("*") if p.is_file()}
        self.json("package/source-manifest.json", {"source_package": {"commit": "a" * 40},
                  "files": files, "historical_catalog": {"files": catalog}})

    def write(self, path, data):
        p = self.root / path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(data)

    def json(self, path, value):
        self.write(path, encoded(value).decode())

    def test_statement_and_proof_resolve_to_different_correct_sources(self):
        check_sources(self.root)
        check_proof_sources(self.root)
        row = build_index(self.root)["targets"][0]
        self.assertEqual(row["challenge"]["path"], "SAP/P001a/Challenge.lean")
        self.assertEqual(row["solution"]["path"], "SAP/P001a/Solution.lean")
        self.assertEqual(row["challenge"]["line"], 2)
        self.assertEqual(row["definitions"][0]["line"], 1)

    def test_changed_imported_source_rejected(self):
        self.write("SAP/P001a/Defs.lean", "def SAP.P001a.T1Statement : Prop := False\n")
        with self.assertRaisesRegex(ValueError, "bytes changed"):
            check_sources(self.root)

    def test_unrecorded_proof_source_rejected(self):
        self.write("SAP/P001a/Extra.lean", "theorem unrelated : True := by trivial\n")
        with self.assertRaisesRegex(ValueError, "inventory changed"):
            check_sources(self.root)

    def test_wrong_target_mapping_rejected(self):
        self.json("SAP/Works/P001/TARGET-MAP.json", [{"target_id": "P001-T2"}])
        with self.assertRaisesRegex(ValueError, "missing/extra targets"):
            build_index(self.root)

    def test_solution_cannot_import_challenge_indirectly(self):
        self.write("SAP/P001a/Bridge.lean", "import SAP.P001a.Challenge\n")
        self.write("SAP/P001a/Solution.lean", "import SAP.P001a.Bridge\n")
        with self.assertRaisesRegex(ValueError, "Solution imports Challenge"):
            check_proof_sources(self.root)

    def test_proof_placeholder_rejected_in_solution(self):
        self.write("SAP/P001a/Solution.lean", "theorem SAP.P001a.T1 : True := by sorry\n")
        with self.assertRaisesRegex(ValueError, "Forbidden proof token"):
            check_proof_sources(self.root)

    def test_challenge_cannot_import_library_proof(self):
        self.write("AronowAudit/Proof.lean", "theorem example_proof : True := by trivial\n")
        self.write("SAP/P001a/Challenge.lean", "import AronowAudit.Proof\n")
        with self.assertRaisesRegex(ValueError, "Challenge imports proof"):
            check_proof_sources(self.root)

    def test_retained_unused_stub_requires_live_axiom_check(self):
        self.write("AronowAudit/Unused.lean", "theorem unused : False := by sorry\n")
        check_proof_sources(self.root)
        with self.assertRaisesRegex(ValueError, "Non-standard axioms"):
            parse_axioms("'SAP.P001a.T1' depends on axioms: [sorryAx]", {"SAP.P001a.T1"})

    def test_missing_axiom_output_is_not_success(self):
        with self.assertRaisesRegex(ValueError, "Missing axiom output"):
            parse_axioms("", {"SAP.P001a.T1"})


if __name__ == "__main__":
    unittest.main()
