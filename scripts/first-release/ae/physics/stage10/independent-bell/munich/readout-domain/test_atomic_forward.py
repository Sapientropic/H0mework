"""Theory-only controls of the primitive twelve-state response producer."""
from decimal import Decimal, localcontext
from fractions import Fraction as Q
import unittest

import atomic_forward as a


def bounds(row):
    return tuple(map(Q, row))


class GeneratorTests(unittest.TestCase):
    def test_complete_invariant_hermitian_space_and_source_decay_totals(self):
        self.assertEqual(len(a.COORDINATES), 32)
        self.assertEqual(sorted(state for block in a.BLOCKS for state in block), list(range(1, 13)))
        self.assertEqual(len(a.DIAGONALS), 12)
        self.assertEqual(len(a.NATURAL_JUMPS), 18)
        for excited in a.EXCITED:
            outgoing = sum(rate for _, source, rate in a.NATURAL_JUMPS if source == excited)
            self.assertEqual(outgoing, a.GAMMA2 if excited == 6 else 1)

    def test_exact_generator_preserves_trace_for_primitive_controls(self):
        for pulse in (a.Pulse(1, 0, 0, 0), a.Pulse(1, 2, 3, Q(1, 2)),
                      a.Pulse(1, 7, 0, 3), a.Pulse(1, 0, 11, 4)):
            self.assertTrue(a.trace_preserving(a.generator_coefficients(pulse)))

    def test_hamiltonian_is_skew_in_the_frobenius_metric(self):
        full = tuple(map(dict, a.generator_coefficients(a.Pulse(1, 2, 3, 0))))
        base = tuple(map(dict, a.generator_coefficients(a.Pulse(1, 0, 0, 0))))
        weights = [1 if i == j else 2 for i, j, _ in a.COORDINATES]
        for i in range(32):
            for j in range(32):
                left = tuple(x - y for x, y in zip(full[i].get(j, a.ZERO), base[i].get(j, a.ZERO)))
                right = tuple(x - y for x, y in zip(full[j].get(i, a.ZERO), base[j].get(i, a.ZERO)))
                self.assertEqual(tuple(weights[i] * x + weights[j] * y for x, y in zip(left, right)), a.ZERO)

    def test_short_time_ionization_third_derivative_from_all_coherent_edges(self):
        pulse = a.Pulse(1, 2, 3, Q(1, 2))
        arithmetic = a.Arithmetic(80)
        generator = a.build_generator(pulse)
        for initial in (1, 4):
            vector = [(Decimal(0), Decimal(0))] * 32
            vector[a.COORDINATES.index((initial, initial, "real"))] = (Decimal(1), Decimal(1))
            for _ in range(3):
                vector = a.apply_generator(arithmetic, generator.rows, vector)
            low, high = map(Q, vector[a.ION_COORDINATE])
            self.assertLessEqual(low, 7 * pulse.ion_rate * pulse.omega_r ** 2 / 2)
            self.assertGreaterEqual(high, 7 * pulse.ion_rate * pulse.omega_r ** 2 / 2)

    def test_angular_rate_and_nanosecond_unit_mapping_is_exact(self):
        pulse = a.Pulse.from_angular_rates(250000000, 18, 12, 6, 6)
        self.assertEqual(pulse, a.Pulse(Q(3, 2), 3, 2, 1))
        self.assertEqual(a.DETUNING, Q(8145, 10) / Q(575, 100))
        self.assertEqual(a.GAMMA2, Q(60666, 10000) / Q(575, 100))

    def test_invalid_controls_do_not_enter_the_source_generator(self):
        for operation in (lambda: a.Pulse(1, .1, 2, 1), lambda: a.Pulse(1, True, 2, 1),
                          lambda: a.Pulse(-1, 2, 3, 1), lambda: a.Pulse(1, 2, 3, -1),
                          lambda: a.Pulse.from_angular_rates(1, 2, 3, 4, 0),
                          lambda: a.build_generator({"duration": 1, "omega_r": 2, "omega_c": 3, "ion_rate": 1})):
            with self.assertRaises((ValueError, TypeError)):
                operation()


class EnclosureTests(unittest.TestCase):
    def test_zero_duration_and_no_ionization_control_enclose_exact_zero(self):
        for pulse in (a.Pulse(0, 2, 3, 1), a.Pulse(Q(1, 20), 2, 3, 0)):
            report = a.propagate([pulse])
            for key in ("p_bright", "p_dark"):
                low, high = bounds(report[key])
                self.assertTrue(low <= 0 <= high)
                self.assertLess(high - low, Q(1, 10 ** 55))
            self.assertTrue(report["generator_trace_preserving"])
            for name in ("bright", "dark"):
                low, high = bounds(report[name]["trace_interval"])
                self.assertLessEqual(low, 1)
                self.assertGreaterEqual(high, 1)

    def test_cycling_only_lookalike_cannot_ionize_the_original_initial_states(self):
        report = a.propagate([a.Pulse(Q(1, 20), 0, 20, 4)])
        for key in ("p_bright", "p_dark"):
            low, high = bounds(report[key])
            self.assertTrue(low <= 0 <= high)
            self.assertLess(high - low, Q(1, 10 ** 55))

    def test_two_legitimate_raw_pulses_generate_distinct_nonzero_responses(self):
        low = a.propagate([a.Pulse(Q(1, 10), 2, 3, Q(1, 2))])
        high = a.propagate([a.Pulse(Q(1, 10), 4, 3, Q(1, 2))])
        for name in ("bright", "dark"):
            interval = bounds(low[name]["ionization_interval"])
            self.assertTrue(0 < interval[0] < interval[1] < 1)
            self.assertLess(interval[1], bounds(high[name]["ionization_interval"])[0])
            self.assertLess(Q(low[name]["trace_norm_error_upper"]), Q(1, 10 ** 55))
            trace = bounds(low[name]["trace_interval"])
            self.assertTrue(trace[0] <= 1 <= trace[1])
        self.assertLess(bounds(low["p_dark"])[1], bounds(low["p_bright"])[0])

    def test_rounding_and_taylor_override_enclosures_agree(self):
        pulse = a.Pulse(Q(1, 20), 2, 3, Q(1, 2))
        default = a.propagate([pulse])
        alternate = a.propagate([pulse], precision=100, order=48, norm_cap=Q(1, 2))
        for key in ("p_bright", "p_dark", "trace_j"):
            left, right = bounds(default[key]), bounds(alternate[key])
            self.assertLessEqual(max(left[0], right[0]), min(left[1], right[1]))
        self.assertGreater(alternate["total_steps"], default["total_steps"])

    def test_piecewise_windows_preserve_natural_decay_and_total_trace(self):
        pulses = [a.Pulse(Q(1, 20), 3, 0, 0), a.Pulse(Q(1, 20), 0, 0, 2),
                  a.Pulse(Q(1, 20), 0, 4, 2)]
        report = a.propagate(pulses)
        for name in ("bright", "dark"):
            self.assertGreater(bounds(report[name]["ionization_interval"])[0], 0)
            self.assertTrue(bounds(report[name]["trace_interval"])[0] <= 1 <=
                            bounds(report[name]["trace_interval"])[1])
        self.assertEqual(len(report["segments"]), 3)

    def test_default_decimal_context_does_not_change_the_enclosure(self):
        pulse = a.Pulse(Q(1, 100), 2, 3, Q(1, 2))
        baseline = a.propagate([pulse])
        with localcontext() as context:
            context.prec = 6
            alternate = a.propagate([pulse])
        self.assertEqual(baseline, alternate)

    def test_source_target_and_step_budget_inputs_are_rejected(self):
        for operation in (lambda: a.propagate([]), lambda: a.propagate([a.Pulse(1, 2, 3, 1)], max_steps=1),
                          lambda: a.propagate([a.Pulse(1, 2, 3, 1)], norm_cap=5),
                          lambda: a.propagate([a.Pulse(1, 2, 3, 1)], precision=10),
                          lambda: a.propagate([a.Pulse(1, 2, 3, 1)], order=True),
                          lambda: a.propagate([{"p_bright": "9/10", "p_dark": "1/10"}])):
            with self.assertRaises((ValueError, TypeError)):
                operation()


if __name__ == "__main__":
    unittest.main()
