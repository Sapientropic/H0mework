#!/usr/bin/env python3
"""Source-owned all-momentum Sylvester inverse and physical current probe jets.

Two original characteristic equations produce the inverse in a 16-dimensional
commutative quotient. The resulting matrix circuit keeps all source momenta;
it is not a finite momentum or time approximation.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
ROOT = HERE.parents[4]


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def clean(matrix):
    return s.SparseMatrix(matrix.rows, matrix.cols, {key: value for key, raw in
        s.SparseMatrix(matrix).todok().items() if (value := s.expand(raw)) != 0})


def zero(matrix):
    assert not clean(matrix).todok(), list(clean(matrix).todok().items())[:2]


def decode(record):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(v) for i, j, v in record['entries']})


def encode(matrix):
    return {'shape': [matrix.rows, matrix.cols], 'entries':
            [[i, j, str(v)] for (i, j), v in sorted(clean(matrix).todok().items())]}


def main():
    began = time.monotonic()
    source = load(FQ/'packet-noise/source_kernel.py', 'probe_laplace_original_source')
    provenance, (N, omega, H0, Hj, CI, K, seed) = source.exact_source()
    cosine_path = FQ/'packet-gauge-cosine/source.json'
    cosine = json.loads(cosine_path.read_text())
    V = decode(cosine['V'])
    c = s.expand(N*s.sqrt(2))
    zeta = 6*(1-s.I)
    frequency = c*zeta
    P = clean(V*V/N**2)
    zero(P*P-P)
    zero(P.H-P)
    assert P.rank() == 8
    for H in [H0, *Hj, V, K]:
        zero(P*H-H*P)
    zero(P*CI*seed-CI*seed)
    indices = [i for i in range(12) if P[i, i] == 1]
    assert P == s.diag(*[int(i in indices) for i in range(12)])
    signs = sorted(set(s.simplify(K[i, i]/s.sqrt(2)) for i in indices))
    assert signs == [-1, 1]
    p = list(s.symbols('p1:4', real=True))
    radius, radial = s.symbols('r x', real=True)
    u = s.symbols('u')
    FIELD = s.QQ_I.frac_field(radial)
    NUMBER = s.QQ.algebraic_field(s.sqrt(2), s.sqrt(15), s.I)
    point = [s.sqrt(2)/11, -2*s.sqrt(2)/13, 3*s.sqrt(2)/17]
    records = []
    for sign in signs:
        block = [i for i in indices if K[i, i] == sign*s.sqrt(2)]
        assert len(block) == 4
        F = s.SparseMatrix(12, 4, {(i, j): 1 for j, i in enumerate(block)})
        zero(F.H*F-s.eye(4))
        b0, bj, v, k = F.H*H0*F, [F.H*H*F for H in Hj], F.H*V*F, F.H*K*F
        for H, small in [(H0, b0), *zip(Hj, bj), (V, v), (K, k)]:
            zero(H*F-F*small)
            zero(F.H*H-small*F.H)
        h_axis = clean((b0+s.sqrt(2)*radius*bj[2])/c)
        coefficients = s.Poly(h_axis.charpoly(u).as_expr(), u).all_coeffs()
        radial_coefficients = []
        for value in coefficients:
            poly = s.Poly(s.expand(value), radius)
            assert all(power[0] % 2 == 0 for power, _ in poly.terms())
            radial_coefficients.append(s.expand(sum(coef*radial**(power[0]//2) for power, coef in poly.terms())))
        assert radial_coefficients[0] == 1
        h_full = clean((b0+sum((p[j]*bj[j] for j in range(3)), s.zeros(4)))/c)
        powers = [s.eye(4)]
        for _ in range(4):
            powers.append(clean(powers[-1]*h_full))
        equation = sum((coef.subs(radial, sum(v*v for v in p)/2)*powers[4-j]
                        for j, coef in enumerate(radial_coefficients)), s.zeros(4))
        zero(equation)
        # The companion acts on 1,u,u^2,u^3. Both matrix multiplication
        # operators obey this same source equation and commute with each other.
        companion = s.zeros(4)
        for j in range(3):
            companion[j+1, j] = 1
        for j in range(4):
            companion[j, 3] = -radial_coefficients[4-j]
        Mu, Mv = s.kronecker_product(companion, s.eye(4)), s.kronecker_product(s.eye(4), companion)
        operator = zeta*s.eye(16)-s.I*(Mu-Mv)
        dm = DomainMatrix.from_Matrix(operator).convert_to(FIELD)
        inverse = dm.inv()
        identity = DomainMatrix.eye((16, 16), FIELD)
        assert (dm.matmul(inverse)-identity).is_zero_matrix
        assert (inverse.matmul(dm)-identity).is_zero_matrix
        unit = DomainMatrix.from_Matrix(s.eye(16)[:, 0]).convert_to(FIELD)
        vector = inverse.matmul(unit).to_Matrix()
        assert s.cancel((operator*vector)[0]-1) == 0
        assert all(s.cancel(v) == 0 for v in (operator*vector)[1:])
        rational_entries = [[i//4, i % 4, str(s.factor(value))] for i, value in enumerate(vector) if value != 0]
        print('PASS source block', sign, 'all-p characteristic and actual quotient inverse', flush=True)

        Hp = clean(b0+sum((point[j]*bj[j] for j in range(3)), s.zeros(4)))
        hp = clean(Hp/c)
        hpowers = [s.eye(4)]
        for _ in range(3):
            hpowers.append(clean(hpowers[-1]*hp))
        xp = s.expand(sum(v*v for v in point)/2)
        coeff = [s.cancel(value.subs(radial, xp)) for value in vector]

        def R(A):
            return clean(sum((coeff[4*a+b]*hpowers[a]*A*hpowers[b]
                             for a in range(4) for b in range(4)), s.zeros(4))/c)

        def M(A):
            return clean(frequency*A-s.I*(Hp*A-A*Hp))

        # Every actual matrix unit is read back on both sides, independently
        # of the abstract quotient basis used to generate R.
        for a in range(4):
            for b in range(4):
                E = s.SparseMatrix(4, 4, {(a, b): 1})
                zero(M(R(E))-E)
                zero(R(M(E))-E)
        B0 = clean(2*k*Hp/(N**2*frequency))
        C0 = clean(2*k*v/(N**2*frequency))
        zero(M(B0)-2*k*Hp/N**2)
        zero(M(C0)-2*k*v/N**2-s.I*(v*B0-B0*v))
        B1, C1 = [], []
        for j in range(3):
            b1 = R(-k*bj[j]/N**2+s.I*B0*bj[j])
            c1 = R(s.I*C0*bj[j]+s.I*(v*b1-b1*v))
            B1.append(b1)
            C1.append(c1)
        B2, C2 = {}, {}
        for i in range(3):
            for j in range(i, 3):
                B2[i, j] = R(s.I*(B1[i]*bj[j]+B1[j]*bj[i]))
                C2[i, j] = R(s.I*(C1[i]*bj[j]+C1[j]*bj[i])+
                              s.I*(v*B2[i, j]-B2[i, j]*v))
        # Direct physical two-parameter equations at fixed output momentum.
        # Incoming momentum is p-k, so probe derivatives act by RIGHT H_j.
        for j in range(3):
            zero(M(B1[j])+k*bj[j]/N**2-s.I*B0*bj[j])
            zero(M(C1[j])-s.I*C0*bj[j]-s.I*(v*B1[j]-B1[j]*v))
        for i, j in B2:
            zero(M(B2[i, j])-s.I*(B1[i]*bj[j]+B1[j]*bj[i]))
            zero(M(C2[i, j])-s.I*(C1[i]*bj[j]+C1[j]*bj[i])-s.I*(v*B2[i, j]-B2[i, j]*v))
        wrong_side = [clean(R(-k*bj[j]/N**2+s.I*bj[j]*B0)-B1[j]) for j in range(3)]
        assert all(value.todok() for value in wrong_side)
        records.append({'chirality': int(sign), 'original12_indices': block,
            'source_characteristic_coefficients': list(map(str, radial_coefficients)),
            'all_three_momentum_source_equation': True,
            'quotient_basis': 'u^a v^b, index4a+b; a,b=0..3',
            'actual_inverse_polynomial_coefficients': rational_entries,
            'actual_matrix_inverse': 'R_z(A)=c^-1 sum_ab coeff_ab(|p|^2/2) (H(p)/c)^a A (H(p)/c)^b',
            'new_point_all16_matrix_units_two_sided': True,
            'new_point_B0': encode(B0), 'new_point_C0': encode(C0),
            'new_point_B_probe_first': list(map(encode, B1)), 'new_point_C_probe_first': list(map(encode, C1)),
            'new_point_B_probe_second': [{'axes': list(key), 'matrix': encode(value)} for key, value in B2.items()],
            'new_point_C_probe_second': [{'axes': list(key), 'matrix': encode(value)} for key, value in C2.items()],
            'wrong_left_Hj_instead_of_right_nonzero_entries': [len(v.todok()) for v in wrong_side]})
        print('PASS original physical B/C probe jets through second order for block', sign, flush=True)
    result = {'scope': 'STRIKE_SOURCE_ALL_MOMENTUM_CURRENT_SYLVESTER_INVERSE_AND_TRUE_PHYSICAL_PROBE_JETS',
        'source_sha256': provenance['source_sha256'],
        'input_sha256': {str(cosine_path.relative_to(ROOT)): hashlib.sha256(cosine_path.read_bytes()).hexdigest()},
        'actual_eight_dimensional_source_reducing_projection': encode(P), 'seed_in_same_projection': True,
        'original_nonzero_full_Y_retained': provenance['original_nonzero_Y_reducing_not_deleted'],
        'physical_frequency': str(frequency), 'normalized_frequency': str(zeta),
        'physical_clock': str(c), 'radial_variable': 'x=|physical p|^2/2',
        'new_physical_momentum': list(map(str, point)), 'blocks': records,
        'operator_contract': 'At fixed output p, B_k(z,p)=(z-i(H(p). - .H(p-k)))^-1[K(H(p)+H(p-k))/N^2]; C_k=R_k[2KV/N^2+i(VB_k-B_kV)].',
        'packet_contract': 'Apply B_k or C_k to the same psi(p-k); first jet G_i psi-G_0 partial_i psi, second G_ij psi-G_i partial_j psi-G_j partial_i psi+G_0 partial_ij psi.',
        'time_scope': 'Actual full-time current Laplace kernel; original Sylvester inverse from unitary conjugation, no time discretization or wave-resolvent product.',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'resolvent.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source all-momentum probe Laplace construction', result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
