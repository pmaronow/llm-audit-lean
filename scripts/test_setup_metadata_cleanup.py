"""Protect proof outputs and active or unfinished compiler inputs during cleanup."""
import contextlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import build_current
from prune_setup_metadata import compiler_activity, prune_completed


class SetupCleanupTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.build = self.root / ".lake/build"

    def write(self, relative, content):
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(content)
        return path

    def complete(self, name="Example"):
        setup = self.write(f".lake/build/ir/{name}.setup.json", b'{"compiler":"input"}')
        olean = self.write(f".lake/build/lib/lean/{name}.olean", b"proved artifact")
        trace = self.write(f".lake/build/lib/lean/{name}.trace", json.dumps({
            "schemaVersion": "2025-09-10", "synthetic": False,
            "outputs": {"o": ["hash.olean"]}, "inputs": [], "log": []}).encode())
        os.utime(setup, ns=(10_000, 10_000))
        for path in (olean, trace):
            os.utime(path, ns=(20_000, 20_000))
        return setup, olean, trace

    def test_only_completed_setup_deleted_proof_outputs_and_sources_unchanged(self):
        setup, olean, trace = self.complete()
        source = self.write("SAP/Example/Solution.lean", b"theorem result : True := by trivial\n")
        evidence = self.write("release-evidence/replay.json", b'{"accepted":true}')
        ir = self.write(".lake/build/ir/Example.c", b"generated C output")
        before = {path: path.read_bytes() for path in (olean, trace, source, evidence, ir)}
        result = prune_completed(self.root, activity_probe=lambda: "")
        self.assertEqual(result.files, 1)
        self.assertFalse(setup.exists())
        self.assertEqual({path: path.read_bytes() for path in before}, before)

    def test_incomplete_and_current_rebuild_metadata_retained(self):
        setup, _, trace = self.complete()
        os.utime(setup, ns=(30_000, 30_000))
        pending = self.write(".lake/build/ir/Pending.setup.json", b"new compiler input")
        result = prune_completed(self.root, activity_probe=lambda: "")
        self.assertEqual(result.files, 0)
        self.assertTrue(setup.exists())
        self.assertTrue(pending.exists())
        trace.unlink()
        self.assertEqual(prune_completed(self.root, activity_probe=lambda: "").files, 0)

    def test_live_compiler_or_unknown_process_state_skips_cleanup(self):
        setup, _, _ = self.complete()
        for reason in ("live lean process 123", "process inspection unavailable"):
            result = prune_completed(self.root, activity_probe=lambda: reason)
            self.assertEqual(result.files, 0)
            self.assertEqual(result.skipped, reason)
            self.assertTrue(setup.exists())

    def test_compiler_appearing_before_delete_is_detected(self):
        setup, _, _ = self.complete()
        answers = iter(("", "live lake process 456"))
        result = prune_completed(self.root, activity_probe=lambda: next(answers))
        self.assertEqual(result.files, 0)
        self.assertTrue(setup.exists())

    def test_symlink_and_declared_trace_input_are_not_deleted(self):
        setup, _, trace = self.complete()
        original = setup.read_bytes()
        outside = self.write("outside.setup.json", original)
        setup.unlink()
        setup.symlink_to(outside)
        self.assertEqual(prune_completed(self.root, activity_probe=lambda: "").files, 0)
        self.assertEqual(outside.read_bytes(), original)
        setup.unlink()
        setup.write_bytes(original)
        os.utime(setup, ns=(10_000, 10_000))
        record = json.loads(trace.read_bytes())
        record["inputs"] = ["Example.setup.json"]
        trace.write_text(json.dumps(record))
        self.assertEqual(prune_completed(self.root, activity_probe=lambda: "").files, 0)
        self.assertTrue(setup.exists())

    def test_invalid_or_error_trace_does_not_certify_completion(self):
        setup, _, trace = self.complete()
        valid = {"schemaVersion": "2025-09-10", "synthetic": False, "outputs": {"o": ["x.olean"]},
                 "inputs": [], "log": []}
        invalid = [{**valid, "log": [{"level": "error"}]}, {**valid, "schemaVersion": "unknown"},
                   {**valid, "log": ["malformed"]}, {**valid, "inputs": None},
                   {**valid, "outputs": {"o": "malformed"}}]
        for content in (b"not JSON", *(json.dumps(record).encode() for record in invalid)):
            trace.write_bytes(content)
            self.assertEqual(prune_completed(self.root, activity_probe=lambda: "").files, 0)
            self.assertTrue(setup.exists())

    def test_dry_run_preserves_eligible_metadata(self):
        setup, _, _ = self.complete()
        self.assertEqual(prune_completed(self.root, dry_run=True, activity_probe=lambda: "").files, 1)
        self.assertTrue(setup.exists())

    def test_zombie_is_not_a_live_compiler_but_running_lean_is(self):
        proc = self.root / "proc"
        self.write("proc/123/comm", b"lean\n")
        status = self.write("proc/123/stat", b"123 (lean) Z 1 2 3\n")
        self.assertEqual(compiler_activity(proc), "")
        status.write_text("123 (lean) R 1 2 3\n")
        self.assertIn("live lean process", compiler_activity(proc))
        self.assertIn("unavailable", compiler_activity(self.root / "missing-proc"))


class PriorityBuildTest(unittest.TestCase):
    def test_priority_work_checks_axioms_early_and_retains_full_gate(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            index = {"works": [{"work_id": "P001", "target_count": 1},
                               {"work_id": "P003", "target_count": 1}]}
            commands = []
            with patch.object(build_current, "__file__", str(root / "scripts/build_current.py")), \
                 patch.object(build_current, "check_current", return_value=index), \
                 patch.object(build_current, "prune_completed"), \
                 patch.object(build_current, "report"), \
                 patch.object(build_current.subprocess, "run", side_effect=lambda args, **kwargs: commands.append(args)), \
                 patch("sys.argv", ["build_current.py", "--priority-work", "P003"]), \
                 contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(build_current.main(), 0)
            self.assertEqual(commands[0], ["lake", "build", "SAP.Works.P003.Challenge"])
            self.assertEqual(commands[1], ["lake", "build", "SAP.Works.P003.Solution"])
            self.assertEqual(commands[2][-2:], ["--work", "P003"])
            self.assertEqual(commands[3], ["lake", "build", "AronowAudit.All"])
            self.assertIn(["lake", "build", "SAP.Works.P001.Solution"], commands)
            self.assertTrue(commands[-1][1].endswith("print_axioms.py"))
            self.assertNotIn("--work", commands[-1])


if __name__ == "__main__":
    unittest.main()
