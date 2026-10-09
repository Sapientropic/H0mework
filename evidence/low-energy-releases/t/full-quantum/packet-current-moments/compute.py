#!/usr/bin/env python3
"""Original filtered packet: source-generated position moments and current jets."""
from fractions import Fraction as F
import importlib.util
import json
from math import comb, factorial
from pathlib import Path
import sys
import sympy as s
from sympy.polys.matrices import DomainMatrix

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path.insert(0, str(BASE/'packet-band-kernel'))
from intervals import Box

FIELD = s.QQ.algebraic_field(s.sqrt(2), s.sqrt(15), s.I)


def inverse(matrix):
    # Generic expression-domain elimination treats the radicals as independent
    # generators and causes unnecessary polynomial-GCD growth.
    return DomainMatrix.from_Matrix(s.SparseMatrix(matrix)).convert_to(FIELD).inv().to_Matrix()


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.simplify)


def zero(matrix):
    terms = clean(matrix).todok()
    assert not terms, list(terms.items())[:3]


def encode(matrix):
    return [[int(i), int(j), str(value)] for (i, j), value in sorted(clean(matrix).todok().items())]


def minors(left, right):
    return [(i, j, s.simplify(left[i]*right[j]-left[j]*right[i]))
            for i in range(left.rows) for j in range(i+1, left.rows)
            if s.simplify(left[i]*right[j]-left[j]*right[i]) != 0]


def main():
    source = load(BASE/'packet-noise/source_kernel.py', 'current_moments_source')
    origin, data = source.exact_source()
    print('Original full252 reducing source reconstructed.', flush=True)
    N, omega, H0, Hj, Cinv, K, seed = data
    identity = s.eye(12)
    direction = [s.Rational(3, 5), 0, s.Rational(4, 5)]
    Hv = clean(sum((direction[j]*Hj[j] for j in range(3)), s.zeros(12)))
    zero(Hv*Hv-N**2*identity)
    zero(Hv.H-Hv)
    for H in [H0]+Hj:
        zero(K*H-H*K)
    zero(K.H*K-2*identity)
    # The complete two-transfer source current, before centering.
    physical, transfer = s.symbols('p1:4', real=True), s.symbols('k1:4', real=True)
    Hp = H0+sum((physical[j]*Hj[j] for j in range(3)), s.zeros(12))
    Hk = sum((transfer[j]*Hj[j] for j in range(3)), s.zeros(12))
    incoming = Hp-Hk
    zero(K*incoming+Hp*K-K*(2*incoming+Hk))
    wrong_commutator = clean(K*incoming+Hp*K-K*(2*incoming-Hk))
    assert wrong_commutator.todok()
    # The actual inverse, with C0^-1 on the original side. No Green is supplied.
    S0 = inverse(s.I*identity-H0)
    zero((s.I*identity-H0)*S0-identity)
    R0 = clean(s.I*S0*Cinv)
    R1 = clean(s.I*S0*Hv*S0*Cinv)
    R2 = clean(2*s.I*S0*Hv*S0*Hv*S0*Cinv)
    C0 = inverse(Cinv)
    theta = s.symbols('theta', real=True)
    D = -s.I*C0*(s.I*identity-H0-theta*Hv)
    inverse_jet = R0+theta*R1+theta**2*R2/2
    product = s.SparseMatrix(D*inverse_jet-identity).applyfunc(s.expand)
    for degree in range(3):
        zero(product.applyfunc(lambda value: value.coeff(theta, degree)))
    # b_hat(theta v)/b_hat(0)=1-theta^2/10+O(theta^4) for the same unit ball.
    u0, u1 = clean(R0*seed), clean(R1*seed)
    u2 = clean((R2-R0/5)*seed)
    B0 = clean(K*H0+H0*K)
    first = clean((-K*Hv*u0-B0*u1)/N**2)
    second = clean((2*K*Hv*u1+B0*u2)/N**2)
    current_jet = (K*(H0-theta*Hv)+H0*K)*(u0-theta*u1+theta**2*u2/2)/N**2
    zero(current_jet.applyfunc(lambda value: s.expand(value).coeff(theta, 1))-first)
    zero(2*current_jet.applyfunc(lambda value: s.expand(value).coeff(theta, 2))-second)
    first_minors, second_minors = minors(u0, first), minors(u0, second)
    assert first_minors and second_minors
    wrong_first = clean((K*Hv*u0-B0*u1)/N**2)
    wrong_second = clean((2*K*Hv*u1+B0*(R2*seed))/N**2)
    assert clean(first-wrong_first).todok()
    assert clean(second-wrong_second).todok()
    # Exact outward bounds: use the certified raw norm of this same source.
    baseline = json.loads((BASE/'packet-noise/kernel-audit/receipt.json').read_text())['h0']
    n2 = Box(*baseline['n_squared'])
    lapse = Box(F(54, 125)).sqrt()
    norm = n2.sqrt()
    moment_source = {m: Box(F(3, (2*m+1)*(2*m+3))).sqrt() for m in range(5)}
    response_moment = {}
    h_moment = {}
    for m in range(1, 5):
        response_moment[m] = sum((comb(m, j)*factorial(j)*lapse**(j+1)*moment_source[m-j]
                                  for j in range(m+1)), Box(0))/norm
        h_moment[m] = response_moment[m]+lapse*moment_source[m]/norm
    radius = Box(F(5234375, 294988800512))*Box(2).sqrt()
    first_bound = Box(2).sqrt()/F(54, 125)*(2*h_moment[1]+lapse*radius*response_moment[1]+lapse)
    second_bound = Box(2).sqrt()/F(54, 125)*(2*h_moment[2]+lapse*radius*response_moment[2]+2*lapse*response_moment[1])
    record = {
        'scope': 'SOURCE_CURRENT_SPATIAL_MOMENTS_AND_FIXED_TRANSFER_JETS_NOT_FULL_KINETIC_MATCHING',
        'source_sha256': origin['source_sha256'],
        'source_identity': 'same E=0 eta=1 unit-ball Dirac response; original full252 reducing 12 sector',
        'original_full_nonzero_yukawa_retained': origin['original_nonzero_Y_reducing_not_deleted'],
        'physical_current': 'B_k psi=N^-2 M_k K(2H+H(k)-H0)psi',
        'centered_current': 'z_k=(1-P_psi)B_k psi; one fixed P_psi for all k',
        'all_orders_directional_moment_bound': '||y_v^m psi|| <= n^-1 sum_j binom(m,j) j! N^(j+1) sqrt(3/((2(m-j)+1)(2(m-j)+3)))',
        'moment_bound_scope': 'unit direction v, positive integers m; normalized ||psi||=1 is used at order zero',
        'response_moment_bounds': {str(m): value.record() for m, value in response_moment.items()},
        'H_response_moment_bounds': {str(m): value.record() for m, value in h_moment.items()},
        'whole_light_ball_first_current_derivative_bound': first_bound.record(),
        'whole_light_ball_second_current_derivative_bound': second_bound.record(),
        'direction': list(map(str, direction)),
        'zero_transfer_output_p_zero': {
            'raw_packet': encode(u0), 'first_current_derivative': encode(first), 'second_current_derivative': encode(second),
            'first_centering_independent_minor': [first_minors[0][0],first_minors[0][1],str(first_minors[0][2])],
            'second_centering_independent_minor': [second_minors[0][0],second_minors[0][1],str(second_minors[0][2])],
            'first_nonzero_minors': len(first_minors), 'second_nonzero_minors': len(second_minors),
            'omitted_common_factor': 'bhat(0)/n, strictly positive',
        },
        'controls': {'wrong_commutator_symbol_nonzeros': len(wrong_commutator.todok()),
                     'wrong_commutator_first_jet_nonzeros': len(clean(first-wrong_first).todok()),
                     'omitted_ball_second_derivative_nonzeros': len(clean(second-wrong_second).todok())},
        'analytic_proof': 'README.md; all-order moment and Frechet regularity are analytic arguments, not new Lean axioms',
    }
    (HERE/'receipt.json').write_text(json.dumps(record, indent=2)+'\n')
    print('Original source current identity, inverse jets, moments and centered-jet witnesses PASS.')
    print('First derivative upper:', first_bound.decimals(24)[1])
    print('Second derivative upper:', second_bound.decimals(24)[1])


if __name__ == '__main__':
    main()
