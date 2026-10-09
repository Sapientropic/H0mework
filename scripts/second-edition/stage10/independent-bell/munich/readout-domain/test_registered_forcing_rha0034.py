from fractions import Fraction as Q
from types import SimpleNamespace
import unittest

import registered_forcing_rha0034 as primary
import registered_forcing_independent_rha0034 as independent


class RegisteredForcingControls(unittest.TestCase):
    def test_independent_raw_bath_compiles_every_first_update_row(self):
        from test_retarded_gaussian_trajectory_source import fixture
        original = fixture()
        operators, programs, _ = primary._programs(original, (True, True))
        other, expected = independent.raw_programs(original._law.record())
        self.assertEqual(operators, other)
        actual = {p['component'] if type(p['component']) is str else tuple(p['component']): p['rows'] for p in programs}
        self.assertEqual(set(actual), set(expected))
        for component in actual:
            self.assertEqual(sorted(map(primary.source.channel._canonical, actual[component])),
                             sorted(map(primary.source.channel._canonical, expected[component])))

    def test_free_defect_excludes_old_input_but_central_tail_keeps_it(self):
        a = primary.prices(2, 3, Q(1, 7), Q(1, 11), Q(5, 13), 17, Q(1, 19))
        self.assertEqual(Q(a['new_free_bank_forcing_integral_price']), primary.source.upper(Q(12, 7)))
        self.assertEqual(Q(a['signed_central_initial_tail_mass_upper']), Q(1, 11)+Q(5, 13))
        b = primary.prices(2, 3, Q(1, 7), 0, Q(5, 13), 17, 0)
        self.assertEqual(a['new_free_bank_forcing_integral_price'], b['new_free_bank_forcing_integral_price'])

    def test_empty_time_override_and_outward_arithmetic(self):
        value = primary.prices(0, 9, 8, 7, 6, 5, 4)
        self.assertEqual(value['whole_new_forcing_integral_price'], '0')
        for q in (Q(0), Q(1, 3), Q(1, 1 << 250), Q(23, 7)):
            self.assertEqual(primary.source.upper(q), independent.upper(q))

    def test_negative_prices_and_source_callback_rejected(self):
        with self.assertRaises(ValueError): primary.prices(1, 2, -Q(1, 1 << 250), 4, 5, 6, 7)
        with self.assertRaises(ValueError): primary.generate(SimpleNamespace(record=lambda: {}))


if __name__ == '__main__': unittest.main()
