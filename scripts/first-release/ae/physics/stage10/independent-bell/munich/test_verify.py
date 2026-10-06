import copy
import json
from fractions import Fraction
from pathlib import Path
import tempfile
import unittest

import verify


class EmpiricalCrossTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.primary = json.loads((verify.HERE / 'primary-first-mu0001.1.json').read_text())
        cls.independent = json.loads((verify.HERE / 'independent-first-mu0001.1.json').read_text())

    def test_two_frozen_firsts_and_all_prefixes_agree(self):
        verdict, runs = verify.validate_firsts(copy.deepcopy(self.primary), copy.deepcopy(self.independent))
        self.assertIn(verdict, ('rejected', 'not_rejected'))
        self.assertEqual(len(runs), 2)
        self.assertGreater(sum(r['trials'] for r in runs), 0)

    def test_missing_run_or_duplicate_context_rejected(self):
        for change in ('missing_run', 'duplicate_context'):
            p, i = copy.deepcopy(self.primary), copy.deepcopy(self.independent)
            if change == 'missing_run':
                i['runs'].pop()
            else:
                for receipt in (p, i):
                    rows = receipt['runs'][0]['contexts']
                    rows[1] = copy.deepcopy(rows[0])
            with self.subTest(change=change), self.assertRaises(ValueError):
                verify.validate_firsts(p, i)

    def test_same_wrong_terminal_in_both_outputs_rejected(self):
        p, i = copy.deepcopy(self.primary), copy.deepcopy(self.independent)
        for receipt in (p, i):
            receipt['runs'][0]['terminal_e'] = verify.exact_summary(Fraction(12345, 7))
        with self.assertRaises(ValueError):
            verify.validate_firsts(p, i)

    def test_changed_prefix_or_pair_denominator_rejected(self):
        for change in ('prefix', 'denominator', 'selection', 'budget'):
            p, i = copy.deepcopy(self.primary), copy.deepcopy(self.independent)
            if change == 'prefix':
                i['runs'][0]['prefix_e_sha256'] = '0' * 64
            elif change == 'denominator':
                for receipt in (p, i):
                    receipt['runs'][0]['local_audit']['pair_records'] += 1
            elif change == 'selection':
                for receipt in (p, i):
                    receipt['runs'][0]['local_audit']['additional_outcome_selection'] = True
            else:
                p['familywise_alpha'] = i['familywise_alpha'] = '1/10'
            with self.subTest(change=change), self.assertRaises(ValueError):
                verify.validate_firsts(p, i)

    def test_boolean_counts_cannot_look_like_integer_counts(self):
        p, i = copy.deepcopy(self.primary), copy.deepcopy(self.independent)
        for receipt in (p, i):
            receipt['runs'][0]['contexts'][0]['counts'][0] = True
        with self.assertRaises(ValueError):
            verify.validate_firsts(p, i)

    def test_scope_promotion_or_shared_first_breaks_independence(self):
        for change in ('scope', 'primary_read'):
            p, i = copy.deepcopy(self.primary), copy.deepcopy(self.independent)
            if change == 'scope':
                p['scope']['full_joint_validated'] = True
            else:
                i['checks']['primary_receipt_read'] = True
            with self.subTest(change=change), self.assertRaises(ValueError):
                verify.validate_firsts(p, i)

    def test_incomplete_program_inventory_rejected(self):
        for report, inventory in ((self.primary, verify.PRIMARY_PATHS),
                                  (self.independent, verify.INDEPENDENT_PATHS)):
            changed = copy.deepcopy(report)
            changed['provenance']['scientific_path_git_blobs'] = {}
            with self.assertRaises(ValueError):
                verify.validate_provenance(changed, inventory)

    def test_copy_override_and_promoted_lookalike(self):
        actual = verify.consume()
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'verification.json'
            path.write_text(json.dumps(actual))
            self.assertEqual(verify.consume(path), actual)
            promoted = copy.deepcopy(actual)
            promoted['full_joint_model_certified'] = True
            path.write_text(json.dumps(promoted))
            with self.assertRaises(ValueError):
                verify.consume(path)

    def test_duplicate_json_key_rejected(self):
        with self.assertRaises(ValueError):
            verify.strict_json('{"run_count":2,"run_count":1}')


if __name__ == '__main__':
    unittest.main()
