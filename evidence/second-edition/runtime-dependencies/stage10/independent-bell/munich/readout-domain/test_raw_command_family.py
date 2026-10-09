"""Theory-only shared-command, CEM instrument, and direct Born controls."""
from fractions import Fraction as Q
from itertools import product
import unittest

import atomic_dipole as dipole
import atomic_full_forward as full
import raw_command_family as family


TRANSFER = {-1: (Q(1, 3), (0, Q(1, 2))), 0: ((0, Q(1, 5)), Q(1, 4)),
            1: (1, (Q(1, 2), Q(1, 3)))}


def template(duration=Q(1, 100)):
    return full.Segment(duration, dict.fromkeys(dipole.Q_COMPONENTS, 0),
                        {-1: 0, 0: 0, 1: 1}, 3, 1, dict.fromkeys(dipole.MANIFOLDS, 0),
                        dict.fromkeys(full.WIDTHS, 1), dict.fromkeys(full.EXCITED, 2),
                        field_convention="absorption_amplitudes")


class RawCommandControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.alice = family.predict_side("alice", TRANSFER, [template()], Q(1, 100), Q(49, 50),
                                        command_bits=96, bits=96, order=48)
        cls.bob = family.predict_side("bob", TRANSFER, [template()], Q(1, 50), Q(19, 20),
                                      command_bits=96, bits=96, order=48)

    def test_nominal_nested_radicals_have_signed_exact_brackets(self):
        first, second = family.nominal_command("-pi/8", 96), family.nominal_command("pi/8", 96)
        self.assertEqual(first.bounds[0], second.bounds[0])
        self.assertEqual(first.bounds[1], (-second.bounds[1][1], -second.bounds[1][0]))
        self.assertIsNone(first.coefficients)
        polynomial = lambda x: 8 * x ** 4 - 8 * x ** 2 + 1
        c0, c1 = first.bounds[0]
        s0, s1 = first.bounds[1]
        self.assertTrue(polynomial(c0) <= 0 <= polynomial(c1))
        self.assertTrue(polynomial(s1) <= 0 <= polynomial(s0))
        self.assertTrue(c0 * c0 + s0 * s0 <= 1 <= c1 * c1 + s1 * s1)
        quarter = family.nominal_command("pi/4", 96)
        self.assertEqual(sum((value * value for value in quarter.coefficients), dipole.Radical()), dipole.Radical(1))

    def test_commands_generate_fields_from_one_raw_transfer_and_keep_cycle(self):
        t = family.transfer_matrix(TRANSFER)
        zero = family.compile_commands(TRANSFER, [template()], "0", 96)
        quarter = family.compile_commands(TRANSFER, [template()], "pi/4", 96)
        self.assertEqual(zero.segments[0].fields_r, {q: row[0] for q, row in zip(dipole.Q_COMPONENTS, t)})
        half_root = dipole.sqrt_rational(Q(1, 2))
        self.assertEqual(quarter.segments[0].fields_r,
                         {q: (row[0] - row[1]) * half_root for q, row in zip(dipole.Q_COMPONENTS, t)})
        for program in (zero, quarter):
            self.assertEqual(program.command_trace_norm_error, 0)
            self.assertEqual(program.segments[0].fields_c, template().fields_c)
            self.assertEqual(program.segments[0].gammas, template().gammas)
        for predicted in (self.alice, self.bob):
            self.assertEqual(predicted.programs[0].transfer, predicted.programs[1].transfer)
            for program, report in zip(predicted.programs, predicted.reports):
                self.assertTrue(full.verify_certificate(report, program.segments))

    def test_command_substitution_pays_source_hamiltonian_duhamel(self):
        first = family.compile_commands(TRANSFER, [template()], "pi/8", 64)
        second = family.compile_commands(TRANSFER, [template()], "pi/8", 128)
        self.assertTrue(0 < second.command_trace_norm_error < first.command_trace_norm_error)
        payment = first.hamiltonian_certificates[0]
        column = tuple(map(Q, payment["source_column_operator_bounds"]))
        delta = sum((radius * bound for radius, bound in zip(first.command.radii, column)), Q(0))
        self.assertEqual(Q(payment["hamiltonian_substitution_bound"]), delta)
        self.assertEqual(first.command_trace_norm_error, 2 * template().duration * delta)
        self.assertEqual(first.transfer, second.transfer)

    def test_dark_effect_uses_full_complex_ion_effect(self):
        for predicted in (self.alice, self.bob):
            for effect in predicted.effects:
                j = effect.ion_effect
                k = (1 - predicted.d) * predicted.eta
                self.assertEqual(effect.coordinates["v"], 2 * k * family.Interval.read(j["01"]["imag"]))
                self.assertEqual(effect.operator[1][0], effect.operator[0][1].conjugate())
        self.assertTrue(any(effect.coordinates["v"].lo > 0 or effect.coordinates["v"].hi < 0
                            for predicted in (self.alice, self.bob) for effect in predicted.effects))

    def test_direct_tensor_born_has_complete_32_cell_enclosures(self):
        rows = family.joint_table(self.alice, self.bob)
        self.assertEqual(len(rows), 32)
        self.assertEqual({tuple(row[key] for key in ("h", "a", "b", "x", "y")) for row in rows},
                         set(product((0, 1), repeat=5)))
        for row in rows:
            low, high = map(Q, row["probability_interval"])
            self.assertTrue(0 <= low <= high <= 1)
        for h, a, b in product((0, 1), repeat=3):
            selected = [row for row in rows if (row["h"], row["a"], row["b"]) == (h, a, b)]
            self.assertTrue(sum(Q(row["probability_interval"][0]) for row in selected) <= 1 <=
                            sum(Q(row["probability_interval"][1]) for row in selected))

    def test_complete_post_instrument_sums_to_phi_and_keeps_presence_memory(self):
        for predicted in (self.alice, self.bob):
            for instrument in predicted.instruments:
                maps = family.instrument_maps(instrument)
                for input_unit in ("00", "11", "01", "10"):
                    total = family._density(maps["Phi"][input_unit])
                    click = family._density(maps["click"][input_unit])
                    noclick = family._density(maps["noclick"][input_unit])
                    self.assertEqual(family._sum(click, noclick), total)
                for entry in instrument.values():
                    self.assertTrue(entry["source_model_sum_equals_Phi"])
                    branches = entry["branches"]
                    self.assertTrue(any(i != dipole.ION and j != dipole.ION for i, j, _, _ in branches["noclick"]["density_center"]))
                    self.assertTrue(all(i == dipole.ION and j == dipole.ION for i, j, _, _ in branches["Phi_ion"]["density_center"]))
                    self.assertGreater(Q(branches["noclick"]["bound_presence_trace_interval"][0]), 0)

    def test_matrix_unit_map_phase_matches_exact_source_bridge_at_zero_time(self):
        report = full.propagate([template(0)], bits=96, order=48)
        instrument = family.post_instrument(report, 0, Q(1, 10), Q(49, 50))
        matrix = family._density(family.instrument_maps(instrument)["Phi"]["01"])
        bridge = dipole.source_qubit_bridge()
        expected = {}
        for i, left in bridge["u_x"].items():
            for j, right in bridge["d_x"].items():
                value = left * right.conjugate()
                if value:
                    expected[i, j] = value.real.as_rational(), value.imag.as_rational()
        self.assertEqual(matrix, expected)

    def test_partial_transfer_target_injection_and_qutrit_projection_are_rejected(self):
        for operation in (lambda: family.transfer_matrix({"J": 0}),
                          lambda: family.transfer_matrix(((1, 0), (0, 1))),
                          lambda: family.nominal_command("unknown"),
                          lambda: family.predict_side("alice", TRANSFER, [template()], 0.1, 1),
                          lambda: family.joint_table(self.bob, self.alice)):
            with self.assertRaises((ValueError, TypeError)):
                operation()
        report = dict(self.alice.reports[0])
        report["tomography"] = {**report["tomography"], "m0": {}}
        with self.assertRaisesRegex(ValueError, "qutrit"):
            family.detector_effect(report, 0, 0, 1)


if __name__ == "__main__":
    unittest.main()
