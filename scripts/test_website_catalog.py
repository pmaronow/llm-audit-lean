"""Exercise cross-repository publication checks with small independent fixtures."""
import json
from pathlib import Path
import tempfile
import unittest

from check_repository import check_website_catalog


class WebsiteCatalogTest(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / 'data' / 'works').mkdir(parents=True)
        self.target = {'id': 'P001-T1', 'text': {
            'headline': 'A finite mean', 'body': 'Under independent selection.', 'location': 'p. 1'}}
        self.files = {'catalog/works/P001.json': json.dumps({
            'work_id': 'P001', 'targets': [self.target]}).encode()}
        self.write_work('P001', [self.target])

    def write_work(self, work_id, targets):
        path = self.root / 'data' / 'works' / (work_id + '.json')
        path.write_text(json.dumps({'work': {'id': work_id}, 'lean': {'targets': targets}}))

    def test_matching_catalog_and_nonformal_work(self):
        self.write_work('P002', [])
        self.assertEqual(check_website_catalog(self.files, self.root), 1)

    def test_changed_description(self):
        for field in ('headline', 'body', 'location'):
            with self.subTest(field=field):
                target = {**self.target, 'text': {**self.target['text'], field: 'Changed'}}
                self.write_work('P001', [target])
                with self.assertRaisesRegex(ValueError, 'text differs: P001-T1'):
                    check_website_catalog(self.files, self.root)

    def test_missing_target(self):
        self.write_work('P001', [])
        with self.assertRaisesRegex(ValueError, 'missing: P001-T1'):
            check_website_catalog(self.files, self.root)

    def test_unexpected_target(self):
        self.write_work('P002', [{**self.target, 'id': 'P002-T1'}])
        with self.assertRaisesRegex(ValueError, 'unexpected: P002-T1'):
            check_website_catalog(self.files, self.root)

    def test_duplicate_website_target(self):
        self.write_work('P001', [self.target, self.target])
        with self.assertRaisesRegex(ValueError, 'duplicate target P001-T1'):
            check_website_catalog(self.files, self.root)

    def test_duplicate_catalog_target(self):
        self.files['catalog/works/P001.json'] = json.dumps({
            'work_id': 'P001', 'targets': [self.target, self.target]}).encode()
        with self.assertRaisesRegex(ValueError, 'duplicate target P001-T1'):
            check_website_catalog(self.files, self.root)

    def test_target_moved_to_another_work(self):
        self.write_work('P001', [])
        self.write_work('P002', [self.target])
        with self.assertRaisesRegex(ValueError, 'invalid target identifier'):
            check_website_catalog(self.files, self.root)

    def test_missing_website_directory(self):
        with self.assertRaisesRegex(ValueError, 'Website work directory does not exist'):
            check_website_catalog(self.files, self.root / 'missing')


if __name__ == '__main__':
    unittest.main()
