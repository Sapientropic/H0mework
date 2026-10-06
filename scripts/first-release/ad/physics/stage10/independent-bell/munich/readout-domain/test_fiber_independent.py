"""Analytic rational controls for the independent fiber checker; no optimizer or data."""
import copy
from fractions import Fraction
import itertools
import unittest

import fiber_independent as checker


def point(alice="1/4", bob="1/4"):
    return {side: [{"mu": "0", "u": coordinate, "z": coordinate} for _ in (0, 1)]
            for side, coordinate in (("alice", alice), ("bob", bob))}


def endpoint(primitive, side, kind):
    upper, reciprocal, _ = checker.geometry(primitive, side)
    if kind == "maximum":
        return {"multipliers": {"upper": ["1", "0"], "reciprocal": ["0", "0"]},
                "sqrt_lower": ["0", "0"],
                "primal_squared_scales": [str(1 / (2 * upper[0][0]))] * 2}
    a, p = upper[0][0], reciprocal[0][0]
    return {"multipliers": {"upper": ["0", "0"], "reciprocal": [str(4 * a * p), "0"]},
            "sqrt_lower": [str(2 * a * p)] * 2,
            "primal_squared_scales": [str(2 * p)] * 2}


def report_fixture():
    primitive = point()
    witness = {"runs": [{"run": run, "primitive": primitive} for run in checker.RUNS]}
    runs = []
    for run in checker.RUNS:
        rows = []
        for side, setting in itertools.product(("alice", "bob"), (0, 1)):
            proposed, checked = {}, {}
            for kind in ("minimum", "maximum"):
                certificate = endpoint(primitive, side, kind)
                checked[kind] = checker.verify_endpoint(primitive, side, setting, kind, certificate)
                proposed[kind] = {"certificate": certificate, "checked": {key: checked[kind][key] for key in
                    ("gain_squared_bound", "attained_gain_squared", "optimality_gap", "all_continuous_members_covered")},
                    "proposal_solver_success": False, "proposal_iterations": 0}
            rows.append({"side": side, "setting": setting, **proposed,
                         "ranges": checker.channel_ranges(primitive, side, setting, checked["minimum"], checked["maximum"])})
        runs.append({"run": run, "primitive": primitive, "hardware_ranges": rows})
    return {"schema": checker.PRIMARY_SCHEMA, "version": checker.VERSION,
            "status": "certified_complete_fiber_hardware_ranges", "scope": "complete_regular_fiber_of_each_frozen_generated_joint_law",
            "gain_squared_optimality_gap": str(checker.GAP), "uniform_fiber_coverage": True,
            "geometric_optimizer_executed": True, "finite_grid_used_as_coverage": False,
            "new_confidence_budget_spent": False, "whole_empirical_confidence_set_bounds": False,
            "actual_hardware_uniquely_identified": False, "trial_event_files_read": 0,
            "new_statistical_fit_executed": False, "runs": runs}, witness


class RootControls(unittest.TestCase):
    def test_integer_newton_and_exact_fraction_roots(self):
        for n in range(257):
            r = checker.integer_square_root(n)
            self.assertLessEqual(r * r, n)
            self.assertGreater((r + 1) ** 2, n)
        self.assertEqual(checker.sqrt_bracket(Fraction(4, 9)), (Fraction(2, 3), Fraction(2, 3)))
        for value in (Fraction(2), Fraction(2, 3), Fraction(1, 10 ** 70), Fraction(10 ** 70, 3)):
            lo, hi = checker.sqrt_bracket(value)
            self.assertLessEqual(lo * lo, value)
            self.assertGreaterEqual(hi * hi, value)
            self.assertLessEqual(hi - lo, Fraction(1, 1 << checker.ROOT_BITS))

    def test_negative_and_boolean_root_inputs_reject(self):
        for value in (-1, True, 0.5):
            with self.assertRaises(ValueError):
                checker.sqrt_bracket(value)


class EndpointControls(unittest.TestCase):
    def test_exact_attained_minimum_and_maximum(self):
        primitive = point()
        for side, setting in itertools.product(("alice", "bob"), (0, 1)):
            for kind, bound in (("minimum", Fraction(1, 64)), ("maximum", Fraction(1))):
                result = checker.verify_endpoint(primitive, side, setting, kind, endpoint(primitive, side, kind))
                self.assertEqual(Fraction(result["gain_squared_bound"]), bound)
                self.assertEqual(result["optimality_gap"], "0")

    def test_bob_uses_reciprocal_objective_coordinates(self):
        primitive = point(bob="1/8")
        first = checker.verify_endpoint(primitive, "alice", 0, "minimum", endpoint(primitive, "alice", "minimum"))
        second = checker.verify_endpoint(primitive, "bob", 0, "minimum", endpoint(primitive, "bob", "minimum"))
        self.assertEqual(first["primal_squared_scales"], ["1/32", "1/32"])
        self.assertEqual(second["primal_squared_scales"], ["1/8", "1/8"])
        self.assertEqual(second["coordinates"], "bob_reciprocal_squared_scales")
        self.assertEqual(Fraction(second["gain_squared_bound"]), Fraction(1, 256))

    def test_negative_multiplier_and_overshot_root_reject(self):
        primitive = point()
        certificate = endpoint(primitive, "alice", "minimum")
        certificate["multipliers"]["upper"][0] = "-1"
        with self.assertRaisesRegex(ValueError, "nonnegative_dual"):
            checker.verify_endpoint(primitive, "alice", 0, "minimum", certificate)
        certificate = endpoint(primitive, "alice", "minimum")
        certificate["sqrt_lower"][0] = "1/127"
        with self.assertRaisesRegex(ValueError, "root_lower"):
            checker.verify_endpoint(primitive, "alice", 0, "minimum", certificate)

    def test_illegal_or_not_near_attaining_primal_rejects(self):
        primitive = point()
        for coordinates, reason in ((["0", "1"], "positive_primal"), (["16", "16"], "upper_cone"),
                                    (["1/16", "1/16"], "reciprocal_cone"), (["1", "1"], "primal_gap")):
            certificate = endpoint(primitive, "alice", "minimum")
            certificate["primal_squared_scales"] = coordinates
            with self.assertRaisesRegex(ValueError, reason):
                checker.verify_endpoint(primitive, "alice", 0, "minimum", certificate)

    def test_target_fields_float_and_boolean_setting_reject(self):
        primitive = point()
        certificate = endpoint(primitive, "alice", "minimum")
        certificate["target_bound"] = "1/64"
        with self.assertRaises(ValueError):
            checker.verify_endpoint(primitive, "alice", 0, "minimum", certificate)
        certificate = endpoint(primitive, "alice", "minimum")
        certificate["sqrt_lower"][0] = 0.01
        with self.assertRaises(ValueError):
            checker.verify_endpoint(primitive, "alice", 0, "minimum", certificate)
        with self.assertRaises(ValueError):
            checker.verify_endpoint(primitive, "alice", False, "minimum", endpoint(primitive, "alice", "minimum"))


class ReportControls(unittest.TestCase):
    def test_complete_sixteen_endpoints_and_eight_channel_ranges(self):
        primary, witness = report_fixture()
        result = checker.verify_report(primary, witness)
        self.assertEqual((result["endpoints_checked"], result["hardware_ranges_checked"]), (16, 8))
        self.assertFalse(result["source_optimizer_executed"])
        self.assertEqual(result["runs"][0]["hardware_ranges"][0]["ranges"]["canonical_gain"], ["1/8", "1"])

    def test_scope_wrong_claim_and_inventory_reject(self):
        primary, witness = report_fixture()
        for mutate in (lambda p: p.update(whole_empirical_confidence_set_bounds=True),
                       lambda p: p["runs"].reverse(),
                       lambda p: p["runs"][0]["hardware_ranges"].pop(),
                       lambda p: p["runs"][0]["hardware_ranges"][0]["maximum"]["checked"].update(gain_squared_bound="2"),
                       lambda p: p["runs"][0]["hardware_ranges"][0]["ranges"].update(canonical_e0=["0", "1"])):
            value = copy.deepcopy(primary)
            mutate(value)
            with self.assertRaises(ValueError):
                checker.verify_report(value, witness)


if __name__ == "__main__":
    unittest.main()
