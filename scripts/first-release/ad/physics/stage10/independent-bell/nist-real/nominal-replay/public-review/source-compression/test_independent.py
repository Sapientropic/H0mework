#!/usr/bin/env python3
"""Focused controls for independent conditional exposure and full-trial inversion."""
import copy
from fractions import Fraction as F
import json
from pathlib import Path
import tempfile
import unittest

import independent as sci


class IndependentControls(unittest.TestCase):
    def test_joint_budget(self):
        cfg, _, _ = sci.configuration()
        b = sci.budget(cfg)
        self.assertEqual(F(b['old_CI_failure_upper']), F(3, 80 * 32767))
        self.assertEqual(sum(F(b[k]) for k in ('old_CI_failure_upper', 'alpha_contrast', 'alpha_conditional')), F(1, 20))
        self.assertEqual(F(b['conditional_inverse_delta']) * F(b['alpha_conditional']), 24 * 4 * 6 * 40)

    def test_public_counts_and_prior_exposure(self):
        _, inputs, _ = sci.configuration()
        prior = json.loads((sci.MW / 'primary-first.json').read_text())
        records = sci.extract_records(inputs, prior)
        self.assertEqual(len(records), 24)
        row = next(r for r in records if r['identity'] == {'workbook': 'diag-xor3.xlsx', 'pulse_count': 5,
                                                         'pulse_indices': [4, 5, 6, 7, 8]})
        self.assertEqual(row['total_trials'], 182137032)
        self.assertEqual(row['setting_trials'], [45544445, 45538661, 45527107, 45526819])
        changed = copy.deepcopy(inputs)
        book = next(b for b in changed['diagnostic_workbooks'] if b['file'] == 'diag-xor3.xlsx')
        next(g for g in book['groups'] if g['pulse_count'] == 5)['counts'][0][3] += 1
        with self.assertRaisesRegex(ValueError, 'prior_full_count_or_exposure_mismatch'):
            sci.extract_records(changed, prior)

    def test_byte_copy_override_and_lookalike(self):
        with tempfile.TemporaryDirectory() as folder:
            p = Path(folder) / 'inputs.json'
            p.write_bytes(sci.INPUTS.read_bytes())
            self.assertEqual(sci.configuration(p)[1], sci.configuration()[1])
            p.write_bytes(p.read_bytes() + b'\n')
            with self.assertRaisesRegex(ValueError, 'lookalike_or_changed_public_input_override'):
                sci.configuration(p)

    def test_log_and_exponential_directions(self):
        self.assertEqual(sci.packet(sci.logarithm(1)), {'exact_lower': '0', 'exact_upper': '0'})
        e = sci.exp_small(F(1, 2))
        inverse = sci.exp_small(F(-1, 2))
        product = e * inverse
        self.assertLessEqual(product.lo, 1)
        self.assertGreaterEqual(product.hi, 1)
        log2 = sci.logarithm(2)
        reciprocal = sci.logarithm(F(1, 2))
        self.assertLessEqual((log2 + reciprocal).lo, 0)
        self.assertGreaterEqual((log2 + reciprocal).hi, 0)

    def test_full_exposure_in_normalizer_and_monotonicity(self):
        _, base = sci.fixed_base_bets(40, 30)
        a = sci.log_e_value(F(1, 10000), 1000, base)
        b = sci.log_e_value(F(1, 10000), 2000, base)
        c = sci.log_e_value(F(2, 10000), 1000, base)
        self.assertGreater(a.lo, b.hi)
        self.assertGreater(a.lo, c.hi)

    def test_conditional_uses_setting_exposure_and_all_directions(self):
        a = sci.conditional_interval(50, 1000, F(1000000))
        b = sci.conditional_interval(50, 2000, F(1000000))
        self.assertEqual(len(a['grid40']), 40)
        self.assertEqual({F(r['lambda']) for r in a['grid40']},
                         {F(sign, 2 ** power) for power in range(1, 21) for sign in (-1, 1)})
        for edge in ('exact_lower', 'exact_upper'):
            self.assertLessEqual(abs(F(a['interval'][edge]) - 2 * F(b['interval'][edge])), F(1, 10 ** 60))
        with self.assertRaisesRegex(ValueError, 'invalid_conditional_count_or_exposure'):
            sci.conditional_interval(1, 0, F(1000000))


if __name__ == '__main__':
    unittest.main()
