from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
from types import SimpleNamespace
import cmath
import gzip
import json
import tempfile
import unittest

import chebyshev_density_rha0032 as code
import chebyshev_basis_independent_rha0032 as independent
import chebyshev_density_proposal_rha0032 as proposal
import chebyshev_density_check_rha0032 as checker

NS = Q(1, 10**9)


def raw(oscillating=False):
    d = code.density.dipole; e = d.INDEX[d.State('D2', 2, 0)]
    h = {(e, e): d.ComplexRadical(2/NS)} if oscillating else {}
    return {'complete_static_H_per_second': code.density.channel._input_record(h),
        'complete_natural_R_per_second': [], 'source_raising_operator_per_second': [],
        'carrier_angular_frequency_per_second': '0', 'phase_radians': '0', 'original_physical_natural_jumps': [],
        'sigma_squared_seconds': str(NS**2), 'centre_seconds': str(NS)}, e


def evaluate_cheb(values, u):
    p, q = Q(1), 2*u-1; result = values[0]
    if len(values) > 1: result += values[1]*q
    for n in range(2, len(values)):
        p, q = q, 2*(2*u-1)*q-p; result += values[n]*q
    return result


class ChebyshevDensityControls(unittest.TestCase):
    def test_all_registered_basis_derivatives_and_products(self):
        result = independent.check(code.derivative_weights, code.product_weights, gaussian_degree=40)
        self.assertEqual(result['derivative_columns_checked'], 65)
        self.assertEqual(result['product_columns_checked'], 2665)

    def test_bad_derivative_is_rejected(self):
        with self.assertRaises(ValueError): independent.check(lambda n: {0: 1}, code.product_weights)

    def test_exact_Gaussian_polynomial_basis_conversion(self):
        coefficients = [Q(1, n+1) for n in range(21)]; transformed = code.monomial_to_chebyshev(coefficients)
        for u in (Q(0), Q(1, 7), Q(1, 2), Q(1)):
            self.assertEqual(sum(c*u**n for n, c in enumerate(coefficients)), evaluate_cheb(transformed, u))

    def test_Gaussian_majorant_covers_late_times_without_cutting_the_field(self):
        source, _ = raw()
        for start in (Q(0), 3*NS, 8*NS):
            coefficients, tail = code.gaussian_polynomial(source, start, NS, 20, 192)
            for u in (Q(0), Q(1, 3), Q(1)):
                t = start+u*NS
                exact, error = code.density.gaussian._exponential(-(t-NS)**2/(4*NS**2), Q(0), 192)
                centre = sum(c*u**n for n, c in enumerate(coefficients))
                self.assertLessEqual(abs(centre-exact[0]), tail+error)

    def test_untrusted_oscillating_proposal_pays_complete_source_defect(self):
        source, e = raw(True); initial = {(0, 0): code.density.dipole.ComplexRadical(Q(1, 2)),
            (e, e): code.density.dipole.ComplexRadical(Q(1, 2)),
            (0, e): code.density.dipole.ComplexRadical(Q(1, 2)), (e, 0): code.density.dipole.ComplexRadical(Q(1, 2))}
        handoff = {'schema': 'stage10-source-issued-free-density-handoff/rha0032', 'source_record': {'Gaussian_source': source},
            'complete_initial_matrix': code.density.channel._input_record(initial), 'source_interval_seconds': ['0', str(NS)],
            'source_factor_id': 'synthetic-untrusted-oscillator'}
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/'curve.gz'; proposal.propose(handoff, path, degree=32)
            with gzip.open(path, 'rt') as handle: header = json.loads(next(handle)); value = json.loads(next(handle))
            _, pairs, _ = code.density._rotating_initial(source, initial, 0, 96)
            columns = code.density._Columns(source, 192)
            _, endpoint, error, record = code.piece(columns, source, value, pairs, 0, 96, 10)
            self.assertLess(error, Q(1, 10**8))
            expected = .5*cmath.exp(2j)
            self.assertLess(abs(complex(*map(float, endpoint[0, e]))-expected), 1e-10)
            changed = deepcopy(value); changed['chebyshev_coefficients'][1][0][2] += 1 << 80
            self.assertGreater(code.piece(columns, source, changed, pairs, 0, 96, 10)[2], error)
            self.assertFalse(header['writer_correctness_assumed']); self.assertFalse(record['monomial_conversion_of_quantum_curve_used'])

    def test_degree_and_nonhermitian_countercontrols(self):
        source, _ = raw(); columns = code.density._Columns(source, 192)
        with self.assertRaises(ValueError): code.piece(columns, source,
            {'duration_seconds': str(NS), 'chebyshev_coefficients': [[]]*66}, {}, 0, 96, 10)
        with self.assertRaises(ValueError): code.piece(columns, source,
            {'duration_seconds': str(NS), 'chebyshev_coefficients': [[[0, 1, 1, 0]]]}, {}, 0, 96, 10)

    def test_callback_shape_is_not_an_authoritative_source(self):
        with self.assertRaises(ValueError): checker.certify(SimpleNamespace(record=lambda: {}), {}, 0, NS,
                                                          'missing.gz', 'unused-cheb-output')


if __name__ == '__main__': unittest.main()
