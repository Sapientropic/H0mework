from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
from types import SimpleNamespace
import gzip
import json
import tempfile
import unittest

import chebyshev_density_rha0032 as rational
import chebyshev_density_integer_rha0032_1 as integer
import chebyshev_density_proposal_rha0032 as proposal
import chebyshev_density_check_rha0032_1 as checker
from test_chebyshev_density_rha0032 import raw, NS


class ChebyshevIntegerControls(unittest.TestCase):
    def test_complex_dyadic_action_is_exact_original_source_action(self):
        source, e = raw(True); d = rational.density.dipole
        source['source_raising_operator_per_second'] = rational.density.channel._input_record({(e, 0): d.ComplexRadical(250000000)})
        source['phase_radians'] = '1/7'
        columns = rational.density._Columns(source, 192); compiled = integer.Columns(columns)
        quantum = 1 << 96
        values = {(0, e): (5, -3), (e, 0): (5, 3), (0, 0): (7, 0), (e, e): (-2, 0)}
        pairs = {key: (Q(a, quantum), Q(b, quantum)) for key, (a, b) in values.items()}
        for component in ('quiet', 'drive'):
            expected, error = columns.action(component, pairs); actual, bound = compiled.action(component, values)
            denominator = quantum*(1 << 192)
            self.assertEqual({key: (Q(a, denominator), Q(b, denominator)) for key, (a, b) in actual.items() if a or b}, expected)
            self.assertGreaterEqual(Q(bound, quantum*(1 << compiled.error_bits)), error)

    def test_integer_default_and_rational_override_check_the_same_curve(self):
        source, e = raw(True); d = rational.density.dipole
        source['source_raising_operator_per_second'] = rational.density.channel._input_record({(e, 0): d.ComplexRadical(250000000)})
        source['phase_radians'] = '1/7'
        source['complete_natural_R_per_second'] = rational.density.channel._input_record({(e, e): d.ComplexRadical(400000000)})
        source['original_physical_natural_jumps'] = [{'physical_amplitude_squared_per_second': '400000000',
            'normalized_natural_jump_operator': rational.density.channel._input_record({(0, e): d.ComplexRadical(1)})}]
        initial = {(0, 0): d.ComplexRadical(Q(1, 2)), (e, e): d.ComplexRadical(Q(1, 2)),
            (0, e): d.ComplexRadical(Q(1, 2)), (e, 0): d.ComplexRadical(Q(1, 2))}
        handoff = {'schema': 'stage10-source-issued-free-density-handoff/rha0032',
            'source_record': {'Gaussian_source': source}, 'complete_initial_matrix': rational.density.channel._input_record(initial),
            'source_interval_seconds': ['0', str(NS)], 'source_factor_id': 'synthetic-integer-price-control'}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'curve.gz'; proposal.propose(handoff, path, degree=32)
            with gzip.open(path, 'rt') as handle: next(handle); value = json.loads(next(handle))
            _, pairs, _ = rational.density._rotating_initial(source, initial, 0, 96)
            columns = rational.density._Columns(source, 192)
            a = integer.piece(columns, source, value, pairs, 0, 96, 20)
            b = rational.piece(columns, source, value, pairs, 0, 96, 20)
            self.assertEqual(a[:2], b[:2]); self.assertLessEqual(abs(a[2]-b[2]), Q(1, 1 << 120))
            self.assertLess(a[2], Q(1, 10**8))

    def test_source_callback_and_nonhermitian_shape_rejected(self):
        with self.assertRaises(ValueError): integer.Columns(SimpleNamespace(column=lambda *args: ({}, 0)))
        source, _ = raw(); columns = rational.density._Columns(source, 192)
        with self.assertRaises(ValueError): integer.piece(columns, source,
            {'duration_seconds': str(NS), 'chebyshev_coefficients': [[[0, 1, 1, 0]]]}, {}, 0, 96, 20)

    def test_stream_strategy_override_rejects_unknown_arithmetic(self):
        with self.assertRaises(ValueError): checker.certify(None, {}, 0, NS, 'missing.gz', 'unused-output', strategy='callback')


if __name__ == '__main__': unittest.main()
