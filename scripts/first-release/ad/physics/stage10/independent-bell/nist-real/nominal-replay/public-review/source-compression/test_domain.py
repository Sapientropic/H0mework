"""Exact outer-cover, common-phase and qualification controls."""
from fractions import Fraction as F
import copy
import unittest

import domain as d


class DomainControls(unittest.TestCase):
    def test_scaled_integer_intervals_are_converted_from_exact_packets(self):
        value = d.value({"exact_lower": "1/7", "exact_upper": "2/7"})
        self.assertLessEqual(F(value.lo, d.SCALE), F(1, 7))
        self.assertGreaterEqual(F(value.hi, d.SCALE), F(2, 7))
        self.assertGreater(value.lo, 1)

    def test_single_roots_enclose_exact_rational_target(self):
        for n in (1, 3, 5, 7):
            for target in (F(0), F(1), F(9, 10), F(27, 64), F(1, 10 ** 80)):
                v = d.root_interval(target, n)
                self.assertLessEqual(F(v.lo, d.SCALE) ** n, target)
                self.assertGreaterEqual(F(v.hi, d.SCALE) ** n, target)

    def test_root_rejects_invalid_domains(self):
        for q, n in ((-1, 3), (2, 3), (F(1, 2), 0)):
            with self.assertRaises(ValueError): d.root_interval(q, n)

    def test_single_inverse_matches_known_mean(self):
        mean, background = F(1, 100), F(1, 1000)
        for n in (1, 3, 5, 7):
            p = 1 - ((1 - background) / (1 + mean)) ** n
            interval, _ = d.mean_from_single({"exact_lower": str(p), "exact_upper": str(p)}, n, background, d.I(0, 1))
            self.assertTrue(interval.contains(mean))

    def test_single_no_click_zero_boundary_is_preserved(self):
        interval, witness = d.mean_from_single({"exact_lower": "0", "exact_upper": "1"}, 7, F(0), d.I(0, 3))
        self.assertEqual(interval, d.I(0, 3))
        self.assertFalse(witness["finite_upper_boundary"])

    def test_phase_partition_covers_shared_boundaries(self):
        interval = d.I(-F(1, 13), F(3, 17))
        parts = d.phase_parts(interval, 8)
        self.assertEqual(parts[0].lo, interval.lo)
        self.assertEqual(parts[-1].hi, interval.hi)
        self.assertTrue(all(a.hi == b.lo for a, b in zip(parts, parts[1:])))
        self.assertEqual(len(d.phase_parts(d.I(0), 8)), 8)

    def test_bernstein_outer_contains_full_polynomial_grid(self):
        coefficients = [d.I(-F(2, 7), F(1, 9)), d.I(3), d.I(-4), d.I(F(1, 3))]
        interval = d.I(-F(1, 5), F(2, 3))
        bound, _ = d.bernstein(coefficients, interval)
        for i in range(101):
            k = F(interval.lo, d.SCALE) + F(i, 100) * F(interval.width, d.SCALE)
            evaluated = d.geometry.pvalue(coefficients, d.I(k))
            self.assertTrue(evaluated.contained(bound))

    def test_h_is_max_of_same_source_three_branches(self):
        epsilon, ch = F(3, 1000), F(1, 20)
        losses = list(map(d.I, (F(1, 7), F(1, 11), F(1, 13))))
        h, branches = d.h_ranges(d.I(ch), losses, epsilon)
        expected = ((1 - epsilon) / 2) ** 2 * ch - epsilon * (1 - epsilon) * F(1, 13)
        self.assertTrue(h.contains(expected))
        self.assertEqual(h.hi, max(v.hi for v in branches))

    def test_probability_shape_lookalike_not_conditional_schema(self):
        report = {"schema": "p23-source-compression-statistics/v1", "version": d.VERSION, "records": []}
        with self.assertRaises(ValueError): d.new_records(report)

    def test_no_sig_same_source_feature_order_fixed(self):
        self.assertEqual(d.FEATURES, ("both", "onlyA", "onlyB", "neither", "singleA", "singleB"))
        self.assertEqual(d.geometry.AXES, ("m", "z", "x", "r", "e"))

    def test_statistical_cross_requires_exact_bound_first(self):
        binding = {"path": "primary.json.xz", "sha256": "fixed", "commit": "one"}
        cross = {"schema": "p23-source-compression-statistical-cross/v1", "version": d.VERSION,
                 "evidence_valid": True, "bindings": [binding], "original_CI_modified": False,
                 "source_tree_or_Fock_producers_executed": 0}
        for key in ("all_23040_direction_bets_verified", "all_24_complete_records_verified",
                    "all_24_support_cut_brackets_verified", "all_480_original_contrast_bets_verified",
                    "all_576_conditional_intervals_verified", "all_72_original_CI_preserved",
                    "joint_95_coverage_budget_paid"):
            cross[key] = True
        d.validate_statistics_cross(cross, binding)
        forged = copy.deepcopy(cross)
        forged["bindings"][0]["sha256"] = "foreign"
        with self.assertRaises(ValueError): d.validate_statistics_cross(forged, binding)
        disabled = copy.deepcopy(cross)
        disabled["all_576_conditional_intervals_verified"] = False
        with self.assertRaises(ValueError): d.validate_statistics_cross(disabled, binding)
        lookalike = copy.deepcopy(cross)
        lookalike["schema"] = "p23-other-statistical-cross/v1"
        with self.assertRaises(ValueError): d.validate_statistics_cross(lookalike, binding)


if __name__ == "__main__":
    unittest.main()
