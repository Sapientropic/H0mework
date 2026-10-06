"""Pure synthetic controls for the source model and candidate-generation algebra."""
import math
import unittest
from fractions import Fraction
from itertools import product

from model import Effect, Instrument, MAPPINGS, decode, effect_from_axis_errors, encode, full_joint, orbit, raw_joint, source_joint
from primary import TerminalCounts, TerminalObjective, float_source_table, polar_effects, rational_candidate


class ReadoutDomainTests(unittest.TestCase):
    def setUp(self):
        self.model = Instrument((Effect("1/5", "1/3", "1/5"), Effect("-1/7", "1/4", "-2/5")),
                                (Effect("-1/8", "1/2", "1/4"), Effect("1/10", "-1/3", "1/6")))

    def test_complete_joint_positive_normalized_and_shared_margins(self):
        table = full_joint(self.model)
        self.assertEqual(len(table), 8)
        for record in table:
            q = record["probabilities"]
            self.assertEqual(sum(q), 1)
            self.assertTrue(all(0 <= value <= 1 for value in q))
            self.assertEqual(q[0] + q[1], (1 + self.model.alice[record["a"]].mu) / 2)
            self.assertEqual(q[0] + q[2], (1 + self.model.bob[record["b"]].mu) / 2)

    def test_asymmetric_readout_exact_full_joint(self):
        first = effect_from_axis_errors(0, 1, "1/10", "3/10")
        second = effect_from_axis_errors(0, 1, "1/4", "1/8")
        model = Instrument((first, first), (second, second))
        self.assertEqual(full_joint(model)[0]["probabilities"], tuple(Fraction(number, 160) for number in (27, 69, 43, 21)))

    def test_zero_error_source_and_south_pole_boundary(self):
        north, south = effect_from_axis_errors(0, 1, 0, 0), effect_from_axis_errors(0, -1, 0, 0)
        model = Instrument((north, south), (north, south))
        self.assertEqual(full_joint(model)[0]["probabilities"], (Fraction(0), Fraction(1, 2), Fraction(1, 2), Fraction(0)))
        self.assertEqual(source_joint(model, 0, 0, 1, 0, 0), Fraction(1, 2))
        self.assertEqual(Effect(1, 0, 0), effect_from_axis_errors(0, 1, 0, 1))

    def test_rank_one_source_sum_and_difference(self):
        correlations = {}
        for h, a, b in product(range(2), repeat=3):
            correlations[h, a, b] = sum((1 - 2 * x) * (1 - 2 * y) * source_joint(self.model, h, a, b, x, y)
                                        for x, y in product(range(2), repeat=2))
        difference, centered_sum = {}, {}
        for a, b in product(range(2), repeat=2):
            difference[a, b] = (correlations[1, a, b] - correlations[0, a, b]) / 2
            centered_sum[a, b] = self.model.alice[a].mu * self.model.bob[b].mu - (correlations[0, a, b] + correlations[1, a, b]) / 2
            self.assertEqual(difference[a, b], self.model.alice[a].u * self.model.bob[b].u)
            self.assertEqual(centered_sum[a, b], self.model.alice[a].z * self.model.bob[b].z)
        for matrix in (difference, centered_sum):
            self.assertEqual(matrix[0, 0] * matrix[1, 1] - matrix[0, 1] * matrix[1, 0], 0)

    def test_all_32_maps_have_generated_same_raw_joint_witness(self):
        self.assertEqual(len(MAPPINGS), 32)
        for mapping, witness in orbit(self.model):
            for h, a, b, x, y in product(range(2), repeat=5):
                self.assertEqual(raw_joint(witness, mapping, h, a, b, x, y), source_joint(self.model, h, a, b, x, y))

    def test_illegal_effect_float_target_table_and_visibility_rejected(self):
        for parameters in ((2, 0, 0), ("1/2", 1, 0), (0, 1, 1)):
            with self.assertRaises(ValueError):
                Effect(*parameters)
        with self.assertRaises(TypeError):
            Effect(.1, 0, 0)
        document = encode(self.model)
        self.assertEqual(decode(document), self.model)
        with self.assertRaises(ValueError):
            decode({**document, "probabilities": []})
        with self.assertRaises(ValueError):
            decode({**document, "visibility": "1/2"})

    def test_search_chart_and_rationalization_only_emit_legal_primitives(self):
        parameters = (.4, 1., .7, -.2, .9, 1.2, .1, 1., -2.1, .9, .7, -.3)
        effects = polar_effects(parameters)
        candidate = rational_candidate(parameters)
        for source_effect, exact_effect in zip(effects, candidate.alice + candidate.bob):
            self.assertLess(abs(float(exact_effect.mu) - source_effect[0]), 1e-9)
        for probabilities in float_source_table(effects):
            self.assertAlmostEqual(sum(probabilities), 1.)

    def test_full_likelihood_uses_all_cells_and_source_zero_has_no_epsilon(self):
        counts = TerminalCounts(tuple((3, 5, 7, 9) for _ in range(8)))
        objective = TerminalObjective(counts)
        probabilities = tuple(row["probabilities"] for row in full_joint(self.model))
        logs = objective.component_logs(probabilities)
        self.assertEqual(len(logs), 4)
        self.assertTrue(all(math.isfinite(value) for value in logs))
        impossible = tuple((0., .25, .25, .5) for _ in range(8))
        self.assertTrue(all(math.isinf(value) for value in objective.component_logs(impossible)))
        with self.assertRaises(ValueError):
            TerminalCounts(tuple((1, 2, 3, -1) for _ in range(8)))


if __name__ == "__main__":
    unittest.main()
