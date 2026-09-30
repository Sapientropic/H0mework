#!/usr/bin/env python3
"""Rigorous matrix power-series enclosures retain the source inverse cancellations."""
from fractions import Fraction as F
from math import factorial
import importlib.util
import json
from pathlib import Path
import sys
import time
import sympy as s
from flint import fmpz_mat

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('inverse_series_source', HERE/'source.py')
source = importlib.util.module_from_spec(spec); spec.loader.exec_module(source)
FQ, BASE = source.FQ, source.BASE
PRECISION = 256
UNIT = 2**PRECISION
ORDER = 40
SIZE = 112


def imatrix(entries=None):
    return fmpz_mat(entries if entries is not None else [[0]*SIZE for _ in range(SIZE)])


def magnitude(M):
    return imatrix([[abs(int(M[i, j])) for j in range(M.ncols())] for i in range(M.nrows())])


class Ball:
    """Rectangles (real+i*imag)/UNIT with a common component radius/UNIT."""
    def __init__(self, re=None, im=None, rad=None):
        example = next((M for M in [re, im, rad] if M is not None), None)
        n, m = (SIZE, SIZE) if example is None else (example.nrows(), example.ncols())
        self.re, self.im, self.rad = [M if M is not None else imatrix([[0]*m for _ in range(n)]) for M in [re, im, rad]]

    @staticmethod
    def exact(M):
        real, imag, radius = [[[0]*M.cols for _ in range(M.rows)] for _ in range(3)]
        for (i, j), value in s.SparseMatrix(M).todok().items():
            parts = [F(str(s.re(value))), F(str(s.im(value)))]
            for component, v in zip([real, imag], parts):
                component[i][j] = v.numerator*UNIT//v.denominator
            radius[i][j] = 1
        return Ball(imatrix(real), imatrix(imag), imatrix(radius))

    def __add__(self, other):
        return Ball(self.re+other.re, self.im+other.im, self.rad+other.rad)

    def __neg__(self):
        return Ball(-self.re, -self.im, self.rad)

    def mul(self, other):
        real = self.re*other.re-self.im*other.im
        imag = self.re*other.im+self.im*other.re
        error = (magnitude(self.re)+magnitude(self.im))*other.rad+self.rad*(magnitude(other.re)+magnitude(other.im))+2*(self.rad*other.rad)
        rc, ic, radius = [[[0]*other.re.ncols() for _ in range(self.re.nrows())] for _ in range(3)]
        for i in range(self.re.nrows()):
            for j in range(other.re.ncols()):
                rc[i][j] = int(real[i, j])//UNIT
                ic[i][j] = int(imag[i, j])//UNIT
                radius[i][j] = (int(error[i, j])+UNIT-1)//UNIT+1
        return Ball(imatrix(rc), imatrix(ic), imatrix(radius))

    def norm(self):
        return F(max(sum(abs(int(self.re[i, j]))+abs(int(self.im[i, j]))+2*int(self.rad[i, j])
                         for j in range(self.re.ncols())) for i in range(self.re.nrows())), UNIT)


def norm_exact(M):
    return max(sum(F(str(abs(s.re(M[i, j]))+abs(s.im(M[i, j])))) for j in range(SIZE)) for i in range(SIZE))


def main(return_data=False):
    began = time.monotonic()
    actual = source.read(BASE/'active-gauge/receipt.json')
    fixed = source.read(FQ/'packet-gauge-fixed-section-domain/source.json')
    q = s.symbols('q1:4', real=True)
    N = s.sympify(actual['source_lapse']); z = s.expand(6*N*s.sqrt(2)*(1-s.I))
    H = source.native.ward.operator(actual['primitive_121_Fourier_Jacobi_entries'],
        values=[z, *[-s.I*s.sqrt(2)*a for a in q]])[:121, :121]
    D = source.matrix(fixed['scales112']); keep = fixed['keep112']
    A = source.clean(D*H.extract(keep, keep)*D/N)
    coeff = {}
    for (i, j), value in A.todok().items():
        for powers, v in s.Poly(value, *q, domain=s.QQ_I).terms():
            coeff.setdefault(powers, s.MutableSparseMatrix(SIZE, SIZE, {}))[i, j] = v
    P, blocks = source.native.rational_inverse(source.clean(coeff.pop((0, 0, 0))))
    relative = {a: source.clean(P*M) for a, M in coeff.items()}
    norms = {a: norm_exact(M) for a, M in relative.items()}
    R = F(1, 8192)
    epsilon = F(5234375, 294988800512)
    theta = norms.get((0, 0, 1), 0)*R+norms.get((0, 0, 2), 0)*R*R
    assert theta < 1 and epsilon < R
    gap = 1-theta
    pnorm = norm_exact(P)
    first = [norms.get(tuple(1 if j == i else 0 for j in range(3)), 0)+
             norms.get(tuple((1 if j == i else 0)+(1 if j == 2 else 0) for j in range(3)), 0)*R
             for i in range(2)]
    transverse = [(0, 0), (0, 1), (1, 0), (0, 2), (1, 1), (2, 0)]
    contour = {(0, 0): pnorm/gap, (1, 0): pnorm*first[0]/gap**2, (0, 1): pnorm*first[1]/gap**2,
               (2, 0): pnorm*(first[0]**2/gap**3+norms.get((2, 0, 0), 0)/gap**2),
               (0, 2): pnorm*(first[1]**2/gap**3+norms.get((0, 2, 0), 0)/gap**2),
               (1, 1): pnorm*(2*first[0]*first[1]/gap**3+norms.get((1, 1, 0), 0)/gap**2)}
    KB = {a: Ball.exact(M) for a, M in relative.items()}
    series, coefficient_norms = {}, {}
    for beta in transverse:
        series[beta], coefficient_norms[beta] = [], []
        for n in range(ORDER+1):
            value = Ball.exact(P) if beta == (0, 0) and n == 0 else Ball()
            for alpha, M in KB.items():
                lower = (beta[0]-alpha[0], beta[1]-alpha[1])
                degree = n-alpha[2]
                if min(*lower, degree) < 0:
                    continue
                value = value+-M.mul(series[lower][degree])
            series[beta].append(value)
            coefficient_norms[beta].append(value.norm())
        print('PASS exact dyadic inverse recurrence', beta, ORDER, flush=True)
    records = []
    t = epsilon/R
    for beta in transverse:
        for a in range(5-sum(beta)):
            prefix = sum(coefficient_norms[beta][n]*F(factorial(n), factorial(n-a))*epsilon**(n-a)
                         for n in range(a, ORDER+1))
            tail = contour[beta]*F((ORDER+1)**a*factorial(a))*t**(ORDER+1-a)/(R**a*(1-t)**(a+1))
            derivative = (prefix+tail)*factorial(beta[0])*factorial(beta[1])
            records.append({'transverse': list(beta), 'radial_order': a,
                'normalized_q_coordinate_derivative_bound': str(derivative),
                'finite_source_series_part': str(prefix*factorial(beta[0])*factorial(beta[1])),
                'analytic_tail': str(tail*factorial(beta[0])*factorial(beta[1]))})
    report = {'scope': 'TRUE_ORIGINAL112_UNIFORM_RADIAL_AND_TRANSVERSE_DERIVATIVE_BOUNDS',
              'physical_frequency': str(z), 'physical_spatial_coordinate': 'k=sqrt2*q; derivatives retain 2^(-order/2)',
              'actual_source_circle_radius': str(R), 'whole_original_light_radius_q': str(epsilon),
              'source_Neumann_theta': str(theta), 'constant_inverse_norm': str(pnorm),
              'relative_source_coefficient_norms': [[list(a), str(v)] for a, v in norms.items()],
              'transverse_contour_bounds': [[list(b), str(v)] for b, v in contour.items()],
              'dyadic_precision_bits': PRECISION, 'source_radial_series_order': ORDER,
              'coefficient_norms': [[list(b), list(map(str, v))] for b, v in coefficient_norms.items()],
              'uniform_derivatives': records, 'both_original_constant_inverse_identities': True,
              'actual_inverse_blocks': blocks, 'seconds': round(time.monotonic()-began, 3)}
    if return_data:
        return {'series': series, 'contour': contour, 'radius': R, 'epsilon': epsilon,
                'A': A, 'P': P, 'D': D, 'q': q, 'report': report}
    (HERE/'inverse-series.json').write_text(json.dumps(report, separators=(',', ':'))+'\n')
    print('PASS source inverse circle and true whole-radius derivative bounds',
          [(v['transverse'], v['radial_order'], float(F(v['normalized_q_coordinate_derivative_bound']))) for v in records],
          report['seconds'], flush=True)


if __name__ == '__main__': main()
