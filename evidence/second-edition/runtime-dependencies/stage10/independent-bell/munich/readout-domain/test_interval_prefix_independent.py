import copy
from decimal import localcontext
from fractions import Fraction as Q
import hashlib
from itertools import product
from types import SimpleNamespace
import unittest

from independent import Arithmetic, Bounds, Prefixes
from interval_prefix import IntervalPrefixChecker
from interval_prefix_independent import (
    CONTEXTS, IntervalPrefixes, check_run, denominator_bounds, iter_prefixes,
)


def trials(bits):
    return tuple(SimpleNamespace(row=i, h=h, a=a, b=b, x=x, y=y)
                 for i, (h, a, b, x, y) in enumerate(bits, 1))


def boxes(table=None, radius=Q(0)):
    if table is None:
        table = dict.fromkeys(CONTEXTS, (Q(1, 4),) * 4)
    return {key: tuple((value - radius, value + radius) for value in row)
            for key, row in table.items()}


def flattened(table):
    return {context + (x, y): row[2 * x + y] for context, row in table.items()
            for x, y in product((0, 1), repeat=2)}


class IndependentIntervalPrefixTests(unittest.TestCase):
    def assert_intersection(self, integer, decimal, scale):
        lo, hi = Q(integer.lo, scale), Q(integer.hi, scale)
        self.assertLessEqual(max(lo, Q(decimal.lower)), min(hi, Q(decimal.upper)))

    def test_zero_width_every_prefix_matches_old_integer_and_intersects_primary(self):
        point = dict.fromkeys(CONTEXTS, (Q(1, 8), Q(1, 4), Q(3, 8), Q(1, 4)))
        new = IntervalPrefixes(boxes(point))
        old = Prefixes(flattened(point), Arithmetic())
        primary = IntervalPrefixChecker(boxes(point))
        for trial in trials(product((0, 1), repeat=5)):
            value = new.step(trial)
            self.assertEqual(value, old.step(trial))
            self.assert_intersection(value, primary.step(trial.h, trial.a, trial.b, trial.x, trial.y),
                                     new.arithmetic.scale)
        left, right = new.result(), primary.result()
        for key in ("status", "trials", "all_prefixes_below_threshold_certified", "counts",
                    "pooled_counts", "trial_bit_sequence_sha256", "probability_table_sha256"):
            self.assertEqual(left[key], right[key])
        self.assertEqual(left["prefix_interval_sha256"], old.interval_digest.hexdigest())
        self.assertEqual(len(left["prefix_log_e"]), 32)

    def test_nonzero_width_encloses_point_and_intersects_primary_each_prefix(self):
        wide = boxes(radius=Q(1, 100))
        new = IntervalPrefixes(wide)
        midpoint = IntervalPrefixes(boxes())
        primary = IntervalPrefixChecker(wide)
        for trial in trials(product((0, 1), repeat=5)):
            broad, narrow = new.step(trial), midpoint.step(trial)
            self.assertLessEqual(broad.lo, narrow.lo)
            self.assertGreaterEqual(broad.hi, narrow.hi)
            for name in new.components:
                self.assertLessEqual(new.components[name].lo, midpoint.components[name].lo)
                self.assertGreaterEqual(new.components[name].hi, midpoint.components[name].hi)
            self.assert_intersection(broad, primary.step(trial.h, trial.a, trial.b, trial.x, trial.y),
                                     new.arithmetic.scale)
        self.assertTrue(new.result()["all_prefixes_below_threshold_certified"])

    def test_linked_complement_ratio_and_normalized_marginal_cap(self):
        row = ((Q(1, 4), Q(1, 2)), (Q(1, 8), Q(3, 8)),
               (Q(1, 8), Q(3, 8)), (Q(1, 8), Q(1, 4)))
        checker = IntervalPrefixes(dict.fromkeys(CONTEXTS, row))
        checker.step(trials([(0, 0, 0, 0, 0)])[0])
        self.assertEqual(checker.last_denominators["complement"], {"lower": "1/2", "upper": "4/5"})
        self.assertNotEqual(checker.last_denominators["complement"],
                            {"lower": "1/3", "upper": "4/3"})
        broad = ((Q(1, 5), Q(3, 5)),) * 4
        bounds = denominator_bounds(broad, 0, 0)
        self.assertEqual(bounds["alice"], (Q(2, 5), Q(1)))
        self.assertEqual(bounds["bob"], (Q(2, 5), Q(1)))

    def test_own_context_marginals_and_closed_forecasters(self):
        point = dict.fromkeys(CONTEXTS, (Q(1, 4),) * 4)
        point[1, 1, 1] = (Q(1, 10), Q(1, 5), Q(3, 10), Q(2, 5))
        new, old = IntervalPrefixes(boxes(point)), Prefixes(flattened(point), Arithmetic())
        sequence = trials([(0, 0, 0, 0, 0), (1, 1, 1, 1, 1)])
        for trial in sequence:
            self.assertEqual(new.step(trial), old.step(trial))
        self.assertEqual(new.last_denominators["alice"], {"lower": "7/10", "upper": "7/10"})
        self.assertEqual(new.last_denominators["bob"], {"lower": "3/5", "upper": "3/5"})
        self.assertEqual(new.alice, [1, 1])
        self.assertEqual(new.bob, [1, 1])

    def test_positive_rejection_empty_stream_and_precision_override(self):
        ordered = trials(product((0, 1), repeat=5))
        positive = check_run(ordered, boxes())
        self.assertTrue(positive["all_prefixes_below_threshold_certified"])
        self.assertEqual(check_run([], boxes())["status"], "inconclusive")
        refused = check_run(trials([(0, 0, 0, 0, 0)] * 40), boxes())
        self.assertEqual(refused["status"], "point_excluded")
        self.assertLess(refused["first_rejection"], 40)
        self.assertEqual(refused["prefixes_checked"], 40)
        lower = check_run(ordered, boxes(), bits=96)
        higher = check_run(ordered, boxes(), bits=320)
        self.assertEqual(lower["precision_bits"], 96)
        self.assertEqual(higher["precision_bits"], 320)
        self.assertEqual(higher["trial_bit_sequence_sha256"], lower["trial_bit_sequence_sha256"])
        checker = IntervalPrefixes(boxes())
        self.assertEqual(list(iter_prefixes(ordered, boxes())), [checker.step(t) for t in ordered])

    def test_zero_lower_and_zero_denominator_are_explicitly_unsupported(self):
        for row in (((Q(0), Q(1, 2)),) + ((Q(1, 5), Q(2, 5)),) * 3,
                    ((Q(1), Q(1)),) + ((Q(0), Q(0)),) * 3):
            table = boxes()
            table[0, 0, 0] = row
            with self.assertRaisesRegex(ValueError, "unsupported-unresolved"):
                check_run(trials([(0, 0, 0, 0, 0)]), table)
        with self.assertRaisesRegex(ValueError, "unsupported-unresolved"):
            denominator_bounds(((Q(0), Q(0)),) * 4, 0, 0)

    def test_bad_table_endpoint_precision_and_target_lookalikes(self):
        partial = boxes()
        partial.pop((0, 0, 0))
        malformed = [partial, {"J": ((Q(1, 4), Q(1, 4)),) * 4}]
        for row in (((Q(1, 10), Q(1, 10)),) * 4, ((Q(3, 10), Q(1)),) * 4,
                    ((Q(1), Q(0)),) * 4, (Q(1, 4),) * 4):
            bad = boxes()
            bad[0, 0, 0] = row
            malformed.append(bad)
        bool_context = boxes()
        bool_context.pop((0, 0, 0))
        bool_context[False, 0, 0] = ((Q(1, 4), Q(1, 4)),) * 4
        malformed.append(bool_context)
        for endpoint in (True, 0.25):
            bad = boxes()
            bad[0, 0, 0] = ((endpoint, Q(1, 4)),) * 4
            malformed.append(bad)
        for table in malformed:
            with self.assertRaises(ValueError):
                IntervalPrefixes(table)
        for precision in (True, 95, "240"):
            with self.assertRaises(ValueError):
                IntervalPrefixes(boxes(), precision)

    def test_original_order_and_invalid_trials_preserve_state(self):
        checker = IntervalPrefixes(boxes())
        before = copy.deepcopy(checker.result())
        for trial in (SimpleNamespace(row=2, h=0, a=0, b=0, x=0, y=0),
                      SimpleNamespace(row=1, h=True, a=0, b=0, x=0, y=0),
                      SimpleNamespace(row=1, h=0, a=0, b=0, x=2, y=0),
                      SimpleNamespace(row=1, h=0, a=0, b=0, x="0", y=0),
                      {"row": 1, "h": 0, "a": 0, "b": 0, "x": 0, "y": 0}):
            with self.assertRaises(ValueError):
                checker.step(trial)
            self.assertEqual(checker.result(), before)
        sequence = [(0, 0, 0, 0, 0), (0, 0, 0, 1, 1), (0, 0, 0, 0, 1)]
        first, reverse = check_run(trials(sequence), boxes()), check_run(trials(reversed(sequence)), boxes())
        self.assertEqual(first["counts"], reverse["counts"])
        self.assertNotEqual(first["trial_bit_sequence_sha256"], reverse["trial_bit_sequence_sha256"])
        self.assertEqual(first["trial_bit_sequence_sha256"],
                         hashlib.sha256(b"".join(bytes(bits) for bits in sequence)).hexdigest())

    def test_integer_arithmetic_is_context_independent_and_retains_q_source_obligation(self):
        sequence = trials(product((0, 1), repeat=5))
        expected = check_run(sequence, boxes(radius=Q(1, 1000)))
        with localcontext() as context:
            context.prec = 6
            self.assertEqual(check_run(sequence, boxes(radius=Q(1, 1000))), expected)
        self.assertFalse(expected["quantum_source_binding_verified"])
        self.assertFalse(expected["complete_positivity_claimed"])
        self.assertTrue(expected["q_source_proof_required"])
        self.assertFalse(expected["new_confidence_budget_spent"])
        self.assertEqual(expected["threshold"], "40")
        self.assertEqual(expected["per_run_alpha"], "1/40")


if __name__ == "__main__":
    unittest.main()
