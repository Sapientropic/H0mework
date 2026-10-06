"""Focused controls for exact tails, direction, printed precision and source roles."""

from fractions import Fraction as F
from itertools import product
import unittest
import audit


def bounds(receipt):
    return tuple(F(receipt["interval"][k]) for k in ["exact_lower", "exact_upper"])


class TailControls(unittest.TestCase):
    def test_small_independent_binary_path_enumeration(self):
        for n in range(1, 8):
            for q in [F(1, 3), F(1, 2), F(3, 5)]:
                for h in range(n + 1):
                    truth = F(0)
                    for path in product([0, 1], repeat=n):
                        if sum(path) >= h:
                            truth += q ** sum(path) * (1 - q) ** (n - sum(path))
                    lo, hi = bounds(audit.binomial_tail(n, h, q, 30))
                    self.assertLessEqual(lo, truth)
                    self.assertGreaterEqual(hi, truth)
                    self.assertLessEqual(hi - lo, F(100, 10 ** 30))

    def test_known_symmetry_and_inclusive_endpoint(self):
        lo, hi = bounds(audit.binomial_tail(5, 3, F(1, 2)))
        self.assertLessEqual(lo, F(1, 2))
        self.assertGreaterEqual(hi, F(1, 2))
        lo, hi = bounds(audit.binomial_tail(2, 1, F(1, 2)))
        self.assertLessEqual(lo, F(3, 4))
        self.assertGreaterEqual(hi, F(3, 4))

    def test_zero_and_unit_probability_boundaries(self):
        self.assertEqual(bounds(audit.binomial_tail(0, 0, F(0))), (F(1), F(1)))
        self.assertEqual(bounds(audit.binomial_tail(9, 1, F(0))), (F(0), F(0)))
        self.assertEqual(bounds(audit.binomial_tail(9, 9, F(1))), (F(1), F(1)))
        self.assertEqual(bounds(audit.binomial_tail(9, 0, F(1, 3))), (F(1), F(1)))

    def test_all_successes_retains_exact_mass(self):
        lo, hi = bounds(audit.binomial_tail(8, 8, F(2, 3)))
        self.assertLessEqual(lo, F(2, 3) ** 8)
        self.assertGreaterEqual(hi, F(2, 3) ** 8)

    def test_invalid_counts_and_probability(self):
        for n, h, q in [(-1, 0, F(1, 2)), (1, 2, F(1, 2)), (1, -1, F(1, 2)),
                        (True, 1, F(1, 2)), (1, 1, F(2)), (1, 1, F(-1))]:
            with self.assertRaises(ValueError):
                audit.binomial_tail(n, h, q)

    def test_S4_equals_setting_ratio(self):
        for e in [F(0), F(1, 10000), F(1, 1000), F(3, 1000), F(1, 100), F(1)]:
            r_num, r_den = (1 + e) ** 2, (1 - e) ** 2
            self.assertEqual(audit.q_from_epsilon(e), r_num / (r_num + r_den))
        for e in [F(-1, 10), F(11, 10)]:
            with self.assertRaises(ValueError):
                audit.q_from_epsilon(e)

    def test_printed_decimal_precision_is_not_fixed_tolerance(self):
        self.assertEqual(audit.print_interval("5.85e-9"), (F(1169, 200000000000), F(1171, 200000000000)))
        self.assertNotEqual(audit.print_interval(".0020"), audit.print_interval(".002"))

    def test_positive_discrepancy_and_unresolved(self):
        self.assertEqual(audit.compare_printed({"interval":{"exact_lower":"1/2","exact_upper":"1/2"}}, ".500")['outcome'], "PRINTED_PRECISION_COMPATIBLE")
        self.assertEqual(audit.compare_printed({"interval":{"exact_lower":"1/2","exact_upper":"1/2"}}, ".100")['outcome'], "CERTIFIED_PRINTED_TAIL_DISCREPANCY")
        self.assertEqual(audit.compare_printed({"interval":{"exact_lower":"2/5","exact_upper":"3/5"}}, ".500")['outcome'], "ROUNDING_DOMAIN_UNRESOLVED")

    def test_closed_printing_boundary(self):
        self.assertEqual(audit.compare_printed({"interval":{"exact_lower":"99/200","exact_upper":"101/200"}}, ".50")['outcome'], "PRINTED_PRECISION_COMPATIBLE")

    def test_sum_covers_every_tail_term_once(self):
        r = audit.binomial_tail(100, 43, F(53, 100), 30)
        p = r['proof']
        self.assertEqual(p['summed_terms'], 100 - 43 + 1)
        self.assertLessEqual(p['sum_grid_before_probability_bound'][1] - p['sum_grid_before_probability_bound'][0], p['rounding_width_budget_grid'])


if __name__ == "__main__":
    unittest.main()
