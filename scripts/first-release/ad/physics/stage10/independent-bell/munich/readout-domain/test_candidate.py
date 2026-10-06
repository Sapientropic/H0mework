"""Pure synthetic gradient and solver controls; no official counts or records."""
import math
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import candidate
from model import decode, full_joint
from primary import COMPONENT_WEIGHTS, TerminalCounts, TerminalObjective, float_source_table, polar_effects
from run import search_starts as original_starts


NONZERO = (.2, .6, .7, -.15, .72, 1.1, .08, .66, -.6, -.22, .82, 2.)
ZERO_BIASES = (0., .6, .7, 0., .72, 1.1, 0., .66, -.6, 0., .82, 2.)
NEAR_BOUNDARY = (.985, .9998, .2, -.983, .9995, .6, .984, .9997, -.3, -.982, .9996, 1.)


def varied_counts():
    return TerminalCounts(tuple((3 + number, 7 + 2 * number, 11 + number, 5 + 3 * number)
                                for number in range(8)))


def synthetic_source_counts(parameters, total=800):
    rows = []
    for q in float_source_table(polar_effects(parameters)):
        row = [math.floor(total * value) for value in q]
        residual = total - sum(row)
        order = sorted(range(4), key=lambda number: (-(total * q[number] - row[number]), number))
        for number in order[:residual]:
            row[number] += 1
        rows.append(tuple(row))
    return TerminalCounts(tuple(rows))


def from_table(objective, probabilities):
    logs = objective.component_logs(probabilities)
    peak = max(logs)
    return peak + math.log(sum(float(weight) * math.exp(value - peak)
                               for weight, value in zip(COMPONENT_WEIGHTS, logs)))


class CandidateControls(unittest.TestCase):
    def test_fixed_starts_are_identical_and_inside_declared_finder(self):
        self.assertEqual(candidate.search_starts(), original_starts())
        self.assertEqual(len(candidate.search_starts()), 35)
        self.assertEqual(candidate.SEARCH_DECLARATION["starts_count"], 35)
        for point in candidate.search_starts():
            self.assertEqual(candidate._point(point), point)

    def test_value_is_the_original_four_component_objective(self):
        counts = varied_counts()
        original, analytic = TerminalObjective(counts), candidate.AnalyticObjective(counts)
        for point in (NONZERO, ZERO_BIASES, NEAR_BOUNDARY):
            self.assertEqual(analytic.value_gradient(point)[0], original(point))

    def test_probability_derivative_includes_parity_and_own_marginal_terms(self):
        original = TerminalObjective(varied_counts())
        analytic = candidate.AnalyticObjective(varied_counts())
        table = float_source_table(polar_effects(NONZERO))
        value, gradients = analytic.probability_gradient(table)
        self.assertEqual(value, from_table(original, table))
        for row in range(8):
            for event in range(4):
                plus, minus = [list(q) for q in table], [list(q) for q in table]
                step = 1e-7
                plus[row][event] += step
                minus[row][event] -= step
                numerical = (from_table(original, plus) - from_table(original, minus)) / (2 * step)
                self.assertAlmostEqual(gradients[row][event], numerical,
                                       delta=3e-6 * max(1., abs(numerical)))

    def test_full_source_jacobian_matches_frozen_source_and_sums_to_zero(self):
        for point in (NONZERO, ZERO_BIASES, NEAR_BOUNDARY):
            table, jacobian = candidate.source_jacobian(point)
            self.assertEqual(table, float_source_table(polar_effects(point)))
            for coordinate in range(12):
                step = 1e-7
                plus, minus = list(point), list(point)
                plus[coordinate] += step
                minus[coordinate] -= step
                upper = float_source_table(polar_effects(plus))
                lower = float_source_table(polar_effects(minus))
                for row in range(8):
                    self.assertAlmostEqual(sum(jacobian[row][event][coordinate] for event in range(4)), 0., delta=2e-15)
                    for event in range(4):
                        numerical = (upper[row][event] - lower[row][event]) / (2 * step)
                        self.assertAlmostEqual(jacobian[row][event][coordinate], numerical, delta=2e-7)

    def test_all_twelve_objective_derivatives_at_nonzero_zero_and_near_boundary(self):
        original = TerminalObjective(varied_counts())
        analytic = candidate.AnalyticObjective(varied_counts())
        for point in (NONZERO, ZERO_BIASES, NEAR_BOUNDARY):
            gradient = analytic.value_gradient(point)[1]
            for coordinate in range(12):
                # The frozen probability polynomial suffers cancellation at tiny q;
                # a larger central step there separates that roundoff from truncation.
                step = 1e-5 if point == NEAR_BOUNDARY else 1e-7
                plus, minus = list(point), list(point)
                plus[coordinate] += step
                minus[coordinate] -= step
                numerical = (original(plus) - original(minus)) / (2 * step)
                self.assertAlmostEqual(gradient[coordinate], numerical,
                                       delta=5e-6 * max(1., abs(numerical)))

    def test_extreme_internal_bounds_remain_positive_without_epsilon(self):
        point = (.99, .999999, 0., -.99, .999999, math.pi / 2,
                 .99, .999999, 0., -.99, .999999, math.pi / 2)
        table, _ = candidate.source_jacobian(point)
        minimum = min(q for row in table for q in row)
        self.assertGreater(minimum, 4.9e-11)
        value, gradient = candidate.AnalyticObjective(varied_counts()).value_gradient(point)
        self.assertTrue(math.isfinite(value) and all(math.isfinite(number) for number in gradient))

    def test_true_zero_source_or_nonfinite_coordinate_is_rejected(self):
        objective = candidate.AnalyticObjective(varied_counts())
        with self.assertRaisesRegex(ValueError, "strictly positive"):
            objective.value_gradient((0., 1., 0.) * 4)
        for bad in (math.inf, math.nan):
            with self.assertRaises(ValueError):
                candidate.source_jacobian((bad, 0., 0.) * 4)
        with self.assertRaises(ValueError):
            candidate._point((1., .5, .3) * 4)

    def test_projected_gradient_accounts_for_active_bounds(self):
        point = (.99, 0., 0.) * 4
        outward = (-2., 1., 0.) * 4
        inward = (2., -1., 0.) * 4
        self.assertEqual(candidate.projected_gradient(point, outward), (0.,) * 12)
        self.assertGreater(max(map(abs, candidate.projected_gradient(point, inward))), 0.)

    def test_mock_solver_must_receive_analytic_jac_and_reports_unmoved_failure(self):
        start = candidate.search_starts()[0]
        result = SimpleNamespace(x=start, success=True, status=0, nit=0, nfev=1)
        with patch("scipy.optimize.minimize", return_value=result) as solve:
            records = candidate.search_terminal(varied_counts(), (start,), max_iterations=23)
        self.assertEqual(len(records), 1)
        self.assertTrue(solve.call_args.kwargs["jac"])
        self.assertEqual(solve.call_args.kwargs["bounds"], candidate.BOUNDS)
        self.assertEqual(solve.call_args.kwargs["options"]["maxiter"], 23)
        self.assertEqual(records[0]["optimizer_iteration_limit"], 23)
        self.assertFalse(records[0]["optimizer_moved"])
        self.assertFalse(records[0]["optimizer_stationary_before_search"])
        self.assertEqual(records[0]["candidate_generation_status"], "unmoved_nonstationary_result")
        self.assertFalse(records[0]["numerical_verdict_certified"])

    def test_solver_version_and_iteration_override_are_checked(self):
        with patch("scipy.__version__", "synthetic-wrong-version"):
            with self.assertRaisesRegex(ValueError, "frozen scipy"):
                candidate.search_terminal(varied_counts(), (NONZERO,))
        with self.assertRaises(ValueError):
            candidate.search_terminal(varied_counts(), (NONZERO,), max_iterations=0)

    def test_synthetic_bias_gain_and_angle_target_causes_actual_solver_movement(self):
        target = (.14, .62, .45, -.11, .72, 1.23, .09, .69, -.38, -.13, .74, .91)
        counts = synthetic_source_counts(target)
        start = candidate.search_starts()[0]
        records = candidate.search_terminal(counts, (start,))
        result = records[0]
        self.assertTrue(result["analytic_gradient_used"])
        self.assertTrue(result["optimizer_moved"])
        self.assertGreater(result["optimizer_iterations"], 0)
        self.assertGreater(result["terminal_objective_improvement"], 20.)
        self.assertEqual(result["candidate_generation_version"], candidate.VERSION)
        self.assertFalse(result["all_prefix_checked"])
        for coordinate in range(3):
            self.assertGreater(max(abs(result["parameter_displacement"][index])
                                   for index in range(coordinate, 12, 3)), 1e-3)
        point = decode(result["primitive"])
        for row in full_joint(point):
            self.assertEqual(sum(row["probabilities"]), 1)
            self.assertTrue(all(q >= 0 for q in row["probabilities"]))
        self.assertAlmostEqual(result["approximate_terminal_log_e"], TerminalObjective(counts)(result["final_parameters"]), delta=1e-10)

    def test_stationary_empty_synthetic_objective_is_identified_without_forced_motion(self):
        counts = TerminalCounts(((0, 0, 0, 0),) * 8)
        result = candidate.search_terminal(counts, (NONZERO,))[0]
        self.assertTrue(result["optimizer_stationary_before_search"])
        self.assertFalse(result["optimizer_moved"])
        self.assertEqual(result["candidate_generation_status"], "stationary_start")
        self.assertEqual(result["final_gradient"], [0.] * 12)


if __name__ == "__main__":
    unittest.main()
