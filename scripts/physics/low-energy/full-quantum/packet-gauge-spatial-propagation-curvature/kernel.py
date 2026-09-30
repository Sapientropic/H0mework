#!/usr/bin/env python3
"""All-radius original source circuit, before taking the actual inverse derivatives."""
from itertools import product
import importlib.util
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('propagation_kernel_source', HERE/'source.py')
source = importlib.util.module_from_spec(spec); spec.loader.exec_module(source)
FQ, BASE = source.FQ, source.BASE
q, U = s.symbols('q U', real=True)
e = s.symbols('e1:4', real=True)
indices = sorted([a for a in product(range(3), repeat=3) if sum(a) <= 2], key=lambda a: (sum(a), a))
zero = (0, 0, 0)


def clean(M): return source.clean(M)
def sub(a, b): return tuple(x-y for x, y in zip(a, b))
def below(a): return [b for b in indices if all(x <= y for x, y in zip(b, a))]
def choose(a, b): return s.prod(s.binomial(x, y) for x, y in zip(a, b))


def jet(M):
    result = {a: s.MutableSparseMatrix(M.rows, M.cols, {}) for a in indices}
    for (i, j), value in s.SparseMatrix(M).todok().items():
        P = s.Poly(value, *e)
        for a in indices:
            coefficient = P.coeff_monomial(a)*s.prod(s.factorial(j) for j in a)
            if coefficient: result[a][i, j] = coefficient
    return {a: clean(M) for a, M in result.items()}


def mul(A, B):
    return {a: clean(sum((choose(a, b)*A[b]*B[sub(a, b)] for b in below(a)), s.zeros(A[zero].rows, B[zero].cols))) for a in indices}


def source_matrix(record):
    r = s.Symbol('r', real=True)
    M = source.native.matrix(record, {str(v): v for v in [r, *source.d]})
    return clean(M.subs({r: s.sqrt(2)*q, **{a: s.sqrt(2)*b for a, b in zip(source.d, e)}}, simultaneous=True))


def main():
    began = time.monotonic()
    axis = source.read(HERE/'axis-source.json')
    global_data = source.read(FQ/'packet-gauge-global-transfer/source.json')
    actual = source.read(BASE/'active-gauge/receipt.json')
    fixed = source.read(FQ/'packet-gauge-fixed-section-domain/source.json')
    z = s.sympify(axis['physical_frequency']); N = s.sympify(actual['source_lapse'])
    c = s.sympify(global_data['physical_clock'])
    kx, ky, kz, T = s.symbols('kx ky kz T', real=True)
    names = dict(zip(map(str, [kx, ky, kz, U, T]), [kx, ky, kz, U, T]))
    def column(label):
        return s.SparseMatrix(289, 1, {(i, j): s.expand(s.sympify(value, locals=names).subs(
            {kx: 0, ky: 0, kz: s.sqrt(2)*q, T: q*q}))
            for i, j, value in global_data['columns'][label]['global_numerator']['entries']})
    A, B, Z = [column(label) for label in ['A', 'B', 'Z']]
    Fnum, Inum = clean(z*A+B), clean((z*z-c*c*U)*Z)
    denominator = s.expand(s.sympify(global_data['denominator_D'], locals=names).subs(T, q*q)*(z*z-c*c*U))
    Fhat = s.Poly(s.sympify(global_data['complete_Fhat'], locals=names).subs(T, q*q), U, q, extension=[s.sqrt(2), s.sqrt(15), s.I])
    pin = [z, 0, 0, -s.I*s.sqrt(2)*q]
    pout = [z, s.I*s.sqrt(2)*e[0], s.I*s.sqrt(2)*e[1], -s.I*s.sqrt(2)*(q-e[2])]
    H = jet(source.native.ward.operator(actual['Fourier_Jacobi_entries'], values=pout))
    residual = clean(source.native.ward.operator(actual['Fourier_Jacobi_entries'], values=pin)*Fnum-Inum)
    assert all(s.Poly(value, U, q, extension=[s.sqrt(2), s.sqrt(15), s.I]).rem(Fhat).is_zero for value in residual.todok().values())
    removed, keep = fixed['removed'], fixed['keep112']
    Km = jet(source_matrix(axis['original_Kminus']))
    minor = {a: M.extract(removed, range(9)).T for a, M in Km.items()}
    inverse = minor[zero].inv(method='DM')
    assert all(s.Poly(value, q) is not None for value in inverse)
    assert clean(minor[zero]*inverse) == clean(inverse*minor[zero]) == s.eye(9)
    V = [jet(source_matrix(profile['V'])) for profile in axis['profiles']]
    K1 = [jet(source_matrix(profile['K1'])) for profile in axis['profiles']]
    C1 = [jet(source_matrix(profile['C1'])) for profile in axis['profiles']]
    torque = {a: clean(s.SparseMatrix.hstack(*[-kg[a].T*Inum-cg[a].T*Fnum for kg, cg in zip(K1, C1)])) for a in indices}
    charge = {}
    for a in indices:
        remaining = torque[a]-sum((choose(a, b)*minor[b]*charge[sub(a, b)] for b in below(a) if b != zero), s.zeros(9, 9))
        charge[a] = clean(inverse*remaining)
    check = mul(minor, charge)
    assert all(check[a] == torque[a] for a in indices)
    I1 = {a: s.SparseMatrix(289, 9, {(removed[i], j): value for (i, j), value in M.todok().items()}) for a, M in charge.items()}
    rhs = {a: clean(I1[a]-s.SparseMatrix.hstack(*[va[a]*Fnum for va in V])) for a in indices}
    original_rhs = rhs
    current, fields, steps = H, list(range(289)), []
    print('PASS exact all-q/U source numerator, original Noether inverse jets and full theta root', flush=True)
    for step in actual['algebraic_Schur_steps']:
        eliminated = step['eliminated_fields']
        retained = [i for i in fields if i not in eliminated]
        erows, krows = [[fields.index(i) for i in ids] for ids in [eliminated, retained]]
        ai = s.SparseMatrix(len(eliminated), len(eliminated), {(eliminated.index(i), eliminated.index(j)): s.sympify(value)
            for i, j, value in step['algebraic_block_inverse']})
        assert clean(current[zero].extract(erows, erows)*ai) == s.eye(len(eliminated))
        assert all(current[a].extract(erows, erows) == s.zeros(len(eliminated)) for a in indices if a != zero)
        particular = {a: clean(ai*rhs[a].extract(erows, range(9))) for a in indices}
        back = {a: clean(-ai*current[a].extract(erows, krows)) for a in indices}
        left = {a: current[a].extract(krows, erows) for a in indices}
        update, correction = mul(left, back), mul(left, particular)
        rhs = {a: clean(rhs[a].extract(krows, range(9))-correction[a]) for a in indices}
        current = {a: clean(current[a].extract(krows, krows)+update[a]) for a in indices}
        steps.append({'eliminated': eliminated, 'retained': retained,
                      'particular': [[list(a), source.encode(M)] for a, M in particular.items()],
                      'back': [[list(a), source.encode(M)] for a, M in back.items()]})
        fields = retained
    D = source.matrix(fixed['scales112'])
    force = {a: clean(D*rhs[a].extract(keep, range(9))/N) for a in indices}
    normalized = {a: clean(D*current[a].extract(keep, keep)*D/N) for a in indices}
    print('PASS all168 source backwrite polynomials and all112 exact force numerators', flush=True)
    result = {'scope': 'WHOLE_RADIAL_SOURCE_CIRCUIT_FOR_ALL_NINE_NATIVE_PROPAGATION_PROFILES',
        'physical_frequency': str(z), 'spatial_convention': 'incoming k=sqrt2*q*e3; external delta=sqrt2*e; output=k-delta',
        'source_basis': [profile['direction'] for profile in axis['profiles']],
        'same_source_common_denominator': str(denominator), 'same_complete_Fhat': str(Fhat.as_expr()),
        'original_F_numerator': source.encode(Fnum), 'original_I_numerator': source.encode(Inum),
        'actual_normalization_D': source.encode(D), 'keep112': keep, 'removed': removed,
        'normalized_operator_jets': [[list(a), source.encode(M)] for a, M in normalized.items()],
        'normalized_force_jets': [[list(a), source.encode(M)] for a, M in force.items()],
        'original_rhs_jets': [[list(a), source.encode(M)] for a, M in original_rhs.items()],
        'source_I1_numerator_jets': [[list(a), source.encode(M)] for a, M in I1.items()],
        'auxiliary_backwrites': steps,
        'consumer': 'y_alpha=sum_beta binomial(alpha,beta)(-1)^|beta| D_out^beta(P)(q)*force_(alpha-beta); physical retained=D*y; reverse original auxiliary steps; divide only at end by same_source_common_denominator',
        'all_original_Noether_and_auxiliary_polynomial_identities': True,
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'kernel.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS all-radius actual propagation kernel circuit', result['seconds'], flush=True)


if __name__ == '__main__': main()
