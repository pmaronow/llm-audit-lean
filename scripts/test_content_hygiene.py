"""Publication hygiene must cover current files without rewriting sealed records."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from check_repository import check_repository
from content_hygiene import check_hygiene, hygiene_hits


class ContentHygieneTest(unittest.TestCase):
    def test_current_docs_allow_honest_ai_and_verification_explanations(self):
        files = {"README.md": b"Produced with AI agents. A formal proof and paper fidelity are distinct.\n",
                 "docs/VERIFICATION.md": b"The validator checks hashes; retained referee reports are evidence.\n",
                 ".github/workflows/check.yml": b"uses: actions/checkout@v4\n"}
        self.assertEqual(hygiene_hits(files, {}), [])

    def test_local_paths_emails_and_account_instructions_are_detected(self):
        files = {"docs/guide.md": ("Use /" + "home/alice/private-result\n").encode(),
                 "scripts/extra.py": ("# Yale " + "account\n# author " + "2026-11-03: \"launch more\"\n").encode(),
                 "CITATION.cff": ("email: private" + "@example.org\n").encode()}
        hits = hygiene_hits(files, {})
        self.assertEqual({h["kind"] for h in hits},
                         {"local-path", "internal-account-detail", "internal-author-instruction", "email-address"})
        self.assertIn({"file": "scripts/extra.py", "line": 2, "kind": "internal-author-instruction"}, hits)

    def test_only_exact_bound_archive_bytes_are_exempt(self):
        data = ("Historical result at /" + "home/alice/sap\n").encode()
        path = "release-evidence/old-report.md"
        manifest = {"files": {path: hashlib.sha256(data).hexdigest()}}
        self.assertEqual(hygiene_hits({path: data}, manifest), [])
        self.assertEqual(hygiene_hits({path: data + b"Changed."}, manifest)[0]["kind"], "local-path")
        self.assertEqual(hygiene_hits({"release-evidence/unregistered.md": data}, manifest)[0]["kind"], "local-path")

    def test_manifest_cannot_exempt_current_docs_or_scripts(self):
        data = ("# copied /" + "Users/alice/internal-work\n").encode()
        for path in ("README.md", "docs/guide.md", "scripts/helper.py", ".github/workflows/check.yml"):
            manifest = {"files": {path: hashlib.sha256(data).hexdigest()}}
            self.assertEqual(hygiene_hits({path: data}, manifest)[0]["kind"], "local-path")

    def test_removed_launcher_cannot_return_as_an_archived_tool(self):
        path = "tools/sap/" + "run_" + "pipeline.sh"
        manifest = {"files": {path: hashlib.sha256(b"#!/bin/bash\n").hexdigest()}}
        self.assertEqual(hygiene_hits({path: b"#!/bin/bash\n"}, manifest)[0]["kind"], "excluded-operational-script")

    def test_hash_bound_evidence_copy_of_removed_script_remains_evidence(self):
        path = "release-evidence/old/" + "sap_" + "pipeline.py"
        data = ("# author " + "2026-11-03: \"historical instruction\"\n").encode()
        manifest = {"files": {path: hashlib.sha256(data).hexdigest()}}
        self.assertEqual(hygiene_hits({path: data}, manifest), [])

    def test_credentials_are_redacted_in_all_diagnostics(self):
        credential = "ghp_" + "A" * 32
        files = {"scripts/helper.py": ("key = '" + credential + "'\n").encode()}
        with self.assertRaisesRegex(ValueError, "scripts/helper.py:1: credential") as caught:
            check_hygiene(files, {})
        self.assertNotIn(credential, str(caught.exception))
        self.assertNotIn("text", hygiene_hits(files, {})[0])

    def test_private_key_and_literal_secret_assignments_are_detected(self):
        files = {"extra.txt": ("-----BEGIN " + "PRIVATE KEY-----\n").encode(),
                 "scripts/helper.py": ("api_" + "key = '" + "B" * 32 + "'\n").encode()}
        self.assertEqual(len([h for h in hygiene_hits(files, {}) if h["kind"] == "credential"]), 2)

    def test_current_package_routine_path_enforces_hygiene(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "package").mkdir()
            (root / "package/source-manifest.json").write_text(json.dumps({"files": {}}))
            (root / "LICENSE").write_bytes((Path(__file__).resolve().parents[1] / "LICENSE").read_bytes())
            (root / "README.md").write_text("Draft at /" + "Users/alice/private-work\n")
            # Isolate the already separate source/index validator, not the
            # repository entry point or the hygiene scan that it must invoke.
            with patch("current_package.check_current", return_value={"counts": {"targets": 1, "theorems": 1}}):
                with self.assertRaisesRegex(ValueError, "README.md:1: local-path"):
                    check_repository(root)


if __name__ == "__main__":
    unittest.main()
