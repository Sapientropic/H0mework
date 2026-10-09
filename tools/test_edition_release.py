import unittest
from unittest.mock import patch

import edition_release as edition


class EditionSelectionTests(unittest.TestCase):
    def data(self):
        return {"schema": edition.EDITIONS['second'][1], "proof_packages": [
            {"id": "one", "paper": "core"}, {"id": "two", "paper": "core"},
            {"id": "three", "paper": "physics"}]}

    def invoke(self, arguments):
        with patch.object(edition.first_release, 'read_json', return_value=self.data()), \
             patch.object(edition.first_release, 'packages', side_effect=lambda data: data['proof_packages']), \
             patch.object(edition.first_release, 'main', return_value=0) as run:
            result = edition.main(arguments)
            return result, run.call_args.args[0]

    def test_paper_selects_its_independent_epoch_packages(self):
        result, arguments = self.invoke(['--edition', 'second', '--paper', 'core', 'build', '--output', '.local/new'])
        self.assertEqual(result, 0)
        self.assertEqual(arguments[-4:], ['--package', 'one', '--package', 'two'])

    def test_explicit_package_retains_the_requested_subset(self):
        arguments = ['--edition', 'second', '--paper', 'core', 'trust', '--package', 'two', '--output', '.local/new']
        _, forwarded = self.invoke(arguments)
        self.assertEqual(forwarded, arguments[4:])

    def test_other_paper_and_unknown_paper_are_rejected(self):
        for extra in (['--paper', 'core', 'build', '--package', 'three'], ['--paper', 'corelike', 'build']):
            with patch.object(edition.first_release, 'read_json', return_value=self.data()), \
                 patch.object(edition.first_release, 'packages', side_effect=lambda data: data['proof_packages']), \
                 patch.object(edition.first_release, 'main') as run, self.assertRaises(SystemExit):
                edition.main(['--edition', 'second', *extra])
            run.assert_not_called()

    def test_default_passes_through_and_restores_first_release_defaults(self):
        original = edition.first_release.MAP, edition.first_release.SCHEMA
        _, forwarded = self.invoke(['--edition', 'second', 'verify-map'])
        self.assertEqual(forwarded, ['verify-map'])
        self.assertEqual((edition.first_release.MAP, edition.first_release.SCHEMA), original)


if __name__ == '__main__':
    unittest.main()
