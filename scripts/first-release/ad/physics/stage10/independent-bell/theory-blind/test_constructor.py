import builtins
import copy
import os
from pathlib import Path
import unittest
from unittest.mock import patch

import capabilities
import constructor as c


class ConstructorTests(unittest.TestCase):
    def test_complete_positive_law_and_source_herald_reindexing(self):
        data = c.build_prediction()
        self.assertEqual(len(data['records']), 32)
        probabilities = {}
        for record in data['records']:
            key = tuple(record[k] for k in ('herald', 'setting_a', 'setting_b', 'outcome_a', 'outcome_b'))
            self.assertNotIn(key, probabilities)
            p = c.Q2(c.Fraction(record['probability']['r']), c.Fraction(record['probability']['s']))
            self.assertGreaterEqual(p.sign(), 0)
            self.assertGreaterEqual((c.Q2(c.Fraction(1)) - p).sign(), 0)
            probabilities[key] = p
        for herald in (False, True):
            for a in (0, 1):
                for b in (0, 1):
                    self.assertEqual(sum(probabilities[herald, a, b, x, y]
                                         for x in (False, True) for y in (False, True)), c.Q2(c.Fraction(1)))
                    for x in (False, True):
                        self.assertEqual(sum(probabilities[herald, a, b, x, y]
                                             for y in (False, True)), c.Q2(c.Fraction(1, 2)))
                    for y in (False, True):
                        self.assertEqual(sum(probabilities[herald, a, b, x, y]
                                             for x in (False, True)), c.Q2(c.Fraction(1, 2)))
        for record in data['aligned_records']:
            herald, a, b, x, y = (record[k] for k in
                ('herald', 'setting_a', 'setting_b', 'outcome_a', 'outcome_b'))
            self.assertEqual(record['probability'], probabilities[False, a, b, x, y].encode())
            self.assertEqual(record['probability'], probabilities[herald, a, b, record['source_outcome_a'], y].encode())
        for score in data['chsh']:
            actual = c.Q2(c.Fraction(score['value']['r']), c.Fraction(score['value']['s']))
            self.assertEqual(actual, c.Q2(c.Fraction(0), c.Fraction(2)))
            self.assertGreater((actual - 2).sign(), 0)

    def test_constructor_has_no_reading_capability_or_external_arguments(self):
        source = Path(c.__file__).read_text()
        self.assertEqual(capabilities.certify_constructor(source)['external_resources'], 0)
        capabilities.require_nullary(c.build_prediction)
        expected = copy.deepcopy(c.build_prediction())
        with patch.object(builtins, 'open', side_effect=AssertionError('file capability attempted')):
            with patch.dict(os.environ, {'BLIND_PUBLIC_TABLE': '/forbidden/public-table.csv', 'BLIND_FITTED_VISIBILITY': '0'}):
                self.assertEqual(c.build_prediction(), expected)
        with self.assertRaises(TypeError):
            c.build_prediction('/forbidden/public-table.csv')

    def test_lookalike_data_derived_or_dynamic_constructor_rejected(self):
        source = Path(c.__file__).read_text()
        mutants = [source+'\nimport os\n',
                   source+'\ndef empirical():\n    return open("public-table.csv").read()\n',
                   source+'\ndef empirical():\n    return globals()["counts"]\n',
                   source+'\ndef empirical():\n    return theoretical_axes.__globals__\n',
                   source.replace('def build_prediction():', 'def build_prediction(counts=None):'),
                   source+'\ncoefficient = 0.98\n']
        for mutant in mutants:
            with self.subTest(mutant=mutant[-100:]):
                with self.assertRaises((ValueError, SyntaxError)):
                    capabilities.certify_constructor(mutant)

    def test_exact_field_boundary_order_and_zero_division(self):
        for r in range(-4, 5):
            for s in range(-4, 5):
                value = c.Q2(c.Fraction(r, 3), c.Fraction(s, 5))
                self.assertEqual((-value).sign(), -value.sign())
                if value != c.Q2():
                    self.assertEqual(value / value, c.Q2(c.Fraction(1)))
        with self.assertRaises(ZeroDivisionError):
            c.Q2(c.Fraction(1)) / c.Q2()


if __name__ == '__main__':
    unittest.main()
