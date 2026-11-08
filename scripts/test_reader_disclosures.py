"""Reader wording must never silently outlive its bound source explanation."""

import json
from pathlib import Path
import unittest

from reader_disclosures import DISCLOSURES, reader_disclosure


class ReaderDisclosureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        root = Path(__file__).resolve().parents[1]
        index = json.loads((root / "package/current-results.json").read_text())
        cls.targets = {row["target_id"]: row for row in index["targets"]}

    def source(self, target_id):
        row = self.targets[target_id]
        return row["restriction"] or row["omission_reason"]

    def test_every_reworded_explanation_is_bound_to_the_actual_source(self):
        for target_id in DISCLOSURES:
            with self.subTest(target_id=target_id):
                self.assertTrue(reader_disclosure(target_id, self.source(target_id)))

    def test_changed_or_missing_source_requires_new_reader_review(self):
        for target_id in DISCLOSURES:
            for changed in (self.source(target_id) + " Changed qualification.", None):
                with self.subTest(target_id=target_id, missing=changed is None):
                    with self.assertRaisesRegex(ValueError, "source changed"):
                        reader_disclosure(target_id, changed)

    def test_unedited_explanations_pass_through(self):
        target_id = "P001-T3"
        original = self.source(target_id)
        self.assertEqual(reader_disclosure(target_id, original), original)
        self.assertIsNone(reader_disclosure("P001-T2", None))


if __name__ == "__main__":
    unittest.main()
