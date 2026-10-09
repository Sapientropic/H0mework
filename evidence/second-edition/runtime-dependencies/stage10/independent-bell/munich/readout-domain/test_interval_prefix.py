import copy
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from itertools import product
import unittest

from likelihood import CONTEXTS, ORDER, PrefixChecker
from interval_prefix import IntervalPrefixChecker, check_prefixes


def boxes(table, radius=Q(0)):
    return {key: tuple((max(Q(0), value - radius), min(Q(1), value + radius)) for value in row)
            for key, row in table.items()}


def uniform():
    return dict.fromkeys(CONTEXTS, (Q(1, 4),) * 4)


class IntervalPrefixTests(unittest.TestCase):
    def test_zero_width_every_prefix_matches_original_logs_counts_and_digests(self):
        table = {context: (Q(1, 8), Q(1, 4), Q(3, 8), Q(1, 4)) for context in CONTEXTS}
        old, new = PrefixChecker(table), IntervalPrefixChecker(boxes(table))
        for bits in product(range(2), repeat=5):
            self.assertEqual(old.step(*bits), new.step(*bits))
            self.assertEqual(old.logs, new.logs)
            left, right = old.result(), new.result()
            for key in ("status", "trials", "terminal_log_e", "maximum_log_e", "maximum_upper_prefix",
                        "first_rejection", "uncertain_prefixes", "component_terminal_log_e",
                        "factor_sequence_sha256", "trial_bit_sequence_sha256", "counts", "pooled_counts"):
                self.assertEqual(left[key], right[key])

    def test_finite_width_encloses_true_factor_and_every_component_prefix(self):
        point = uniform()
        wide = boxes(point, Q(1, 100))
        checked, exact = IntervalPrefixChecker(wide), IntervalPrefixChecker(boxes(point))
        for bits in product(range(2), repeat=5):
            a, b = checked.step(*bits), exact.step(*bits)
            self.assertLessEqual(a.lower, b.lower)
            self.assertGreaterEqual(a.upper, b.upper)
            for name in ORDER:
                lo, hi = checked.last_factors[name], exact.last_factors[name]
                self.assertLessEqual(Q(lo["lower"]), Q(hi["lower"]))
                self.assertGreaterEqual(Q(lo["upper"]), Q(hi["upper"]))
            for interval, true_log in zip(checked.logs, exact.logs):
                self.assertLessEqual(interval.lower, true_log.lower)
                self.assertGreaterEqual(interval.upper, true_log.upper)
        self.assertTrue(checked.result()["all_prefixes_below_threshold_certified"])
        self.assertIsNone(checked.result()["factor_sequence_sha256"])

    def test_complement_cancels_shared_event_and_uses_linked_ratio(self):
        table = {key: ((Q(1, 4), Q(1, 2)), (Q(1, 4), Q(1, 4)),
                       (Q(1, 4), Q(1, 4)), (Q(0), Q(0))) for key in CONTEXTS}
        checker = IntervalPrefixChecker(table)
        checker.step(0, 0, 0, 0, 0)
        self.assertEqual(checker.last_factors["complement"], {"lower": "1/2", "upper": "1/2"})
        self.assertNotEqual(checker.last_factors["full"]["lower"], checker.last_factors["full"]["upper"])
        table[0, 0, 0] = ((Q(0), Q(1, 2)), (Q(1, 4), Q(1, 2)),
                         (Q(1, 4), Q(1, 2)), (Q(0), Q(0)))
        boundary = IntervalPrefixChecker(table)
        boundary.step(0, 0, 0, 0, 0)
        self.assertEqual(boundary.last_factors["complement"], {"lower": "1/2", "upper": "1/2"})
        self.assertIsNone(boundary.last_factors["full"]["upper"])

    def test_own_context_marginals_and_forecasts_use_only_past_counts(self):
        table = uniform()
        table[1, 1, 1] = (Q(1, 10), Q(1, 5), Q(3, 10), Q(2, 5))
        checker = IntervalPrefixChecker(boxes(table))
        checker.step(0, 0, 0, 0, 0)
        checker.step(1, 1, 1, 1, 1)
        self.assertEqual(checker.last_forecasts["alice"], "1/4")
        self.assertEqual(checker.last_forecasts["bob"], "1/4")
        self.assertEqual(checker.last_forecasts["full"], "1/4")
        self.assertEqual(checker.last_factors["alice"], {"lower": "5/14", "upper": "5/14"})
        self.assertEqual(checker.last_factors["bob"], {"lower": "5/12", "upper": "5/12"})
        self.assertEqual(checker.last_step_record["q_event"], {"lower": "2/5", "upper": "2/5"})
        self.assertEqual(checker.last_step_record["alice_marginal"], {"lower": "7/10", "upper": "7/10"})

    def test_zero_lower_is_unresolved_without_smoothing_or_midpoint(self):
        table = boxes(uniform())
        table[0, 0, 0] = ((Q(0), Q(1, 2)),) + ((Q(1, 5), Q(2, 5)),) * 3
        checker = IntervalPrefixChecker(table)
        result = checker.step(0, 0, 0, 0, 0)
        self.assertEqual(result.upper, Decimal("Infinity"))
        self.assertIsNone(checker.last_factors["full"]["upper"])
        receipt = checker.result()
        self.assertEqual(receipt["status"], "numerical_boundary_unresolved")
        self.assertFalse(receipt["all_prefixes_below_threshold_certified"])
        self.assertEqual(receipt["zero_lower_probability_prefixes"], [1])

    def test_certified_zero_is_rejected_and_entire_order_is_retained(self):
        table = dict.fromkeys(CONTEXTS, ((Q(1), Q(1)),) + ((Q(0), Q(0)),) * 3)
        checker = IntervalPrefixChecker(table)
        checker.step(0, 0, 0, 0, 1)
        checker.step(1, 1, 1, 0, 0)
        receipt = checker.result()
        self.assertEqual(receipt["status"], "point_excluded")
        self.assertEqual(receipt["first_rejection"], 1)
        self.assertEqual(receipt["trials"], 2)
        self.assertEqual(receipt["zero_support_prefixes"], [1])
        self.assertIsNone(receipt["component_terminal_log_e"])
        self.assertEqual(receipt["terminal_log_e"]["lower"], "Infinity")

    def test_bad_envelopes_partial_tables_and_target_lookalikes_are_rejected(self):
        good = boxes(uniform())
        bad = []
        partial = dict(good)
        partial.pop((0, 0, 0))
        bad.append(partial)
        for row in (((Q(0), Q(1, 10)),) * 4, ((Q(3, 10), Q(1)),) * 4,
                    ((Q(-1), Q(1)),) * 4, ((Q(1), Q(0)),) * 4, (Q(1, 4),) * 4):
            table = dict(good)
            table[0, 0, 0] = row
            bad.append(table)
        bool_context = dict(good)
        bool_context.pop((0, 0, 0))
        bool_context[False, 0, 0] = good[0, 0, 0]
        bad.extend((bool_context, {"J": good[0, 0, 0]}))
        for table in bad:
            with self.assertRaises(ValueError):
                IntervalPrefixChecker(table)
        for endpoint in (0.25, True):
            table = dict(good)
            table[0, 0, 0] = ((endpoint, Q(1, 4)),) * 4
            with self.assertRaises(ValueError):
                IntervalPrefixChecker(table)

    def test_positive_refusal_empty_and_precision_override(self):
        table = boxes(uniform())
        self.assertEqual(check_prefixes([], table)["status"], "inconclusive")
        positive = check_prefixes(list(product(range(2), repeat=5)), table)
        self.assertTrue(positive["all_prefixes_below_threshold_certified"])
        refused = check_prefixes([(0, 0, 0, 0, 0)] * 40, table)
        self.assertEqual(refused["status"], "point_excluded")
        self.assertLess(refused["first_rejection"], 40)
        high = check_prefixes(list(product(range(2), repeat=5)), table, precision=120)
        self.assertEqual(high["numerical_precision"], 120)
        self.assertEqual(positive["factor_sequence_sha256"], high["factor_sequence_sha256"])
        self.assertTrue(high["all_prefixes_below_threshold_certified"])
        for precision in (True, 20):
            with self.assertRaises(ValueError):
                IntervalPrefixChecker(table, precision)

    def test_order_identity_and_rejected_bits_have_no_state_update(self):
        table = boxes(uniform())
        first = [(0, 0, 0, 0, 0), (0, 0, 0, 1, 1), (0, 0, 0, 0, 1)]
        a, b = check_prefixes(first, table), check_prefixes(list(reversed(first)), table)
        self.assertEqual(a["counts"], b["counts"])
        self.assertNotEqual(a["trial_bit_sequence_sha256"], b["trial_bit_sequence_sha256"])
        self.assertNotEqual(a["factor_interval_sequence_sha256"], b["factor_interval_sequence_sha256"])
        checker = IntervalPrefixChecker(table)
        before = copy.deepcopy(checker.result())
        for trial in ((True, 0, 0, 0, 0), (0, 0, 0, 2, 0), (0, 0, 0, "0", 0)):
            with self.assertRaises(ValueError):
                checker.step(*trial)
            self.assertEqual(checker.result(), before)

    def test_global_decimal_context_cannot_change_bounds_or_cp_scope(self):
        table = boxes(uniform(), Q(1, 1000))
        trials = list(product(range(2), repeat=5))
        expected = check_prefixes(trials, table)
        with localcontext() as context:
            context.prec = 6
            found = check_prefixes(trials, table)
        self.assertEqual(expected, found)
        self.assertFalse(found["quantum_source_binding_verified"])
        self.assertFalse(found["complete_positivity_claimed"])
        self.assertTrue(found["q_source_proof_required"])
        self.assertFalse(found["new_confidence_budget_spent"])
        self.assertEqual(found["threshold"], "40")
        self.assertEqual(found["per_run_alpha"], "1/40")


if __name__ == "__main__":
    unittest.main()
