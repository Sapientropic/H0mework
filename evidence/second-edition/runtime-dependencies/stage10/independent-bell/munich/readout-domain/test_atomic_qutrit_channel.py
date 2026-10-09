import copy
from dataclasses import replace
from fractions import Fraction as Q
import unittest
from unittest.mock import patch

import atomic_dipole as dipole
import atomic_full_forward as full
import atomic_qutrit_channel as channel
from test_atomic_full_forward import segment


def density(rows):
    return {(i, j): (Q(real), Q(imag)) for i, j, real, imag in rows}


class QutritChannelTests(unittest.TestCase):
    def test_nine_inputs_are_native_F1_inventory_and_normalized(self):
        self.assertEqual(len(channel.initial_densities()), 9)
        self.assertEqual(tuple(state.m for state in channel.BASIS), (-1, 0, 1))
        for matrix in channel.initial_densities():
            self.assertTrue(full._hermitian(matrix))
            self.assertEqual(sum(real for (i, j), (real, _) in matrix.items() if i == j), 1)
            self.assertTrue(all(i in channel.INDICES and j in channel.INDICES for i, j in matrix))

    def test_zero_duration_reconstructs_all_nine_identity_matrix_units(self):
        report = channel.propagate([segment(0)], bits=128, order=48, d=Q(1, 10), eta=Q(9, 10))
        self.assertEqual(len(report["matrix_units"]), 9)
        for unit in report["matrix_units"]:
            i, j = unit["input"]
            self.assertEqual(density(unit["Phi"]["density_center"]),
                             {(channel.INDICES[i], channel.INDICES[j]): (Q(1), Q(0))})
            self.assertEqual(unit["Phi_ion"]["density_center"], [])
            self.assertEqual(density(unit["click"]["density_center"]),
                             {(channel.INDICES[i], channel.INDICES[j]): (Q(1, 10), Q(0))})
        self.assertTrue(channel.verify_certificate(report, [segment(0)], d=Q(1, 10), eta=Q(9, 10)))
        self.assertFalse(report["center_complete_positivity_claimed"])
        self.assertFalse(report["controller_advance"])

    def test_general_complex_program_keeps_m0_response_and_full_output(self):
        raw = segment(Q(1, 50), general=True)
        report = channel.propagate([raw], bits=128, order=48)
        self.assertGreater(Q(report["tomography"]["diag1"]["ionization_interval"][0]), 0)
        self.assertGreater(Q(report["J"]["11"]["real"][0]), 0)
        self.assertEqual(len(report["initial_inventories"]), 9)
        self.assertTrue(channel.verify_certificate(report, [raw]))

    def test_pi_field_drives_native_m0_through_retained_hyperfine_levels(self):
        raw = replace(segment(Q(1, 20)), fields_r={-1: 0, 0: 1, 1: 0})
        report = channel.propagate([raw], bits=128, order=48)
        self.assertGreater(Q(report["tomography"]["diag1"]["ionization_interval"][0]), 0)
        self.assertTrue(channel.verify_certificate(report))

    def test_adjoint_symmetry_and_every_unit_instrument_is_complete(self):
        report = channel.propagate([segment(Q(1, 100), general=True)], bits=128, order=48,
                                   d=Q(1, 10), eta=Q(4, 5))
        units = {tuple(unit["input"]): unit for unit in report["matrix_units"]}
        for (i, j), unit in units.items():
            total = density(unit["Phi"]["density_center"])
            self.assertEqual(channel._adjoint(total), density(units[j, i]["Phi"]["density_center"]))
            click, no = density(unit["click"]["density_center"]), density(unit["no_click"]["density_center"])
            self.assertEqual(channel._linear(((click, Q(1), Q(0)), (no, Q(1), Q(0)))), total)
            ion_trace = total.get((dipole.ION, dipole.ION), (Q(0), Q(0)))
            J = report["J"][str(j) + str(i)]
            for component, bounds in zip(ion_trace, (J["real"], J["imag"])):
                self.assertTrue(Q(bounds[0]) <= component <= Q(bounds[1]))
        self.assertTrue(channel.verify_certificate(report))

    def test_zero_drive_and_precision_override_enclose_same_channel(self):
        zero = channel.propagate([segment(drive=False)], bits=128, order=48)
        self.assertEqual(Q(zero["tomography"]["diag1"]["ionization_center"]), 0)
        raw = segment(Q(1, 100))
        first = channel.propagate([raw], bits=128, order=48)
        second = channel.propagate([raw], bits=160, order=64, norm_cap=Q(1, 40))
        self.assertGreater(second["steps"], first["steps"])
        for name in channel.NAMES:
            a, b = (list(map(Q, report["tomography"][name]["ionization_interval"])) for report in (first, second))
            self.assertLessEqual(max(a[0], b[0]), min(a[1], b[1]))
        self.assertTrue(channel.verify_certificate(second))

    def test_checker_rebuilds_without_calling_producer(self):
        raw = segment(Q(1, 100))
        report = channel.propagate([raw], bits=128, order=48)
        with patch.object(channel, "propagate", side_effect=AssertionError("producer called")):
            self.assertTrue(channel.verify_certificate(report, [raw]))

    def test_projection_program_target_and_detector_lookalikes_are_rejected(self):
        raw = segment(0)
        original = channel.propagate([raw], bits=128, order=48)
        for key, value in (("tomography_inputs", 4), ("matrix_unit_inputs", 4), ("input_dimension", 2),
                           ("complex_density_coordinates", 144), ("caller_density_supplied", True)):
            altered = copy.deepcopy(original)
            altered[key] = value
            with self.assertRaises(ValueError):
                channel.verify_certificate(altered)
        target = copy.deepcopy(original)
        target["J"]["11"]["real"] = ["1", "1"]
        with self.assertRaisesRegex(ValueError, "channel/J"):
            channel.verify_certificate(target)
        with self.assertRaisesRegex(ValueError, "different raw program"):
            channel.verify_certificate(original, [segment(drive=False)])
        with self.assertRaisesRegex(ValueError, "detector binding"):
            channel.verify_certificate(original, d=Q(1, 2))
        for operation in (lambda: channel.propagate([{"rho": [[1, 0], [0, 0]]}]),
                          lambda: channel.propagate([raw], d=2),
                          lambda: channel.propagate([raw], eta=0.9),
                          lambda: channel.propagate([raw], bits=True)):
            with self.assertRaises((ValueError, TypeError)):
                operation()


if __name__ == "__main__":
    unittest.main()
