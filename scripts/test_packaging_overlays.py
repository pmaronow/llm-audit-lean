"""Packaging annotations must never authorize changed formal sources or evidence."""

from pathlib import Path
import tempfile
import unittest

from current_package import check_packaging, digest, historical_notice


class PackagingTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def overlay(self, path="SAP/Works/P001/README.md"):
        original = b"# Original preparation record\n\nPending at preparation.\n"
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        content = historical_notice(path) + original
        target.write_bytes(content)
        return {"files": {path: digest(content)}, "documentation_overlays": {
            path: {"original_sha256": digest(original), "reason": "Historical notice."}}}

    def test_notice_preserves_original_document_body(self):
        for path in ("SAP/Works/README.md", "SAP/Works/BUILD.md", "SAP/Works/P001/README.md"):
            check_packaging(self.root, self.overlay(path))

    def test_document_body_edit_is_rejected_even_with_updated_current_hash(self):
        manifest = self.overlay()
        path = "SAP/Works/P001/README.md"
        target = self.root / path
        target.write_bytes(target.read_bytes() + b"Changed claim.\n")
        manifest["files"][path] = digest(target.read_bytes())
        with self.assertRaisesRegex(ValueError, "body changed"):
            check_packaging(self.root, manifest)

    def test_formal_source_cannot_be_a_documentation_overlay(self):
        path = "SAP/Works/P001/Solution.lean"
        target = self.root / path
        target.parent.mkdir(parents=True)
        target.write_bytes(b"changed proof")
        manifest = {"files": {path: digest(target.read_bytes())}, "documentation_overlays": {
            path: {"original_sha256": "a" * 64, "reason": "Not a permitted document."}}}
        with self.assertRaisesRegex(ValueError, "Unsupported documentation overlay"):
            check_packaging(self.root, manifest)

    def test_exclusions_cannot_remove_verification_tools_or_leave_operational_files(self):
        for path in ("tools/palomar/palomar.py", "tools/sap/sap_pipeline.py"):
            manifest = {"files": {}, "excluded_files": {
                path: {"original_sha256": "a" * 64, "reason": "Operational file omitted."}}}
            if path.endswith("sap_pipeline.py"):
                check_packaging(self.root, manifest)
                target = self.root / path
                target.parent.mkdir(parents=True)
                target.write_bytes(b"unexpected launcher")
            with self.assertRaisesRegex(ValueError, "Invalid operational exclusion"):
                check_packaging(self.root, manifest)


if __name__ == "__main__":
    unittest.main()
