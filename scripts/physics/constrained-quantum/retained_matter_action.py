#!/usr/bin/env python3
"""Preserve the original matter coordinates while eliminating only auxiliaries.

The 79/24 blocks are response coordinates of this same retained action. They
are not an additional inventory of bosons to place beside full matter CAR.
The first-order phase below is the classical presymplectic Legendre pullback;
its matter coordinates have not been assigned bosonic commutators.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import BASE, HERE, ROOT, ROOT_ID, SourceExchange, decode
from spectral_splice import clean, encode, equal

P = s.symbols('p0:4')
K = s.symbols('k1:4', real=True)
LAMBDA = s.Symbol('lambda')


def polynomial(entries, rows, columns):
    result = s.MutableSparseMatrix(rows, columns, {})
    for i, j, powers, value in entries:
        result[i, j] += s.sympify(value)*s.prod(p**n for p, n in zip(P, powers))
    return clean(result)


def negative(matrix):
    return clean(matrix.subs(dict(zip(P, [-p for p in P])), simultaneous=True))


def reverse_k(matrix):
    return clean(matrix.subs(dict(zip(K, [-k for k in K])), simultaneous=True))


class RetainedMatterAction:
    def __init__(self):
        self.source = SourceExchange()
        source = self.source
        self.H = polynomial(source.active['Fourier_Jacobi_entries'], 289, 289)
        indices = list(range(289))
        current = self.H
        self.lift = s.SparseMatrix(s.eye(289))
        self.contact = s.zeros(289)
        self.steps = []
        for step in source.active['algebraic_Schur_steps']:
            eliminated = step['eliminated_fields']
            kept = [i for i in indices if i not in eliminated]
            ie = [indices.index(i) for i in eliminated]
            ir = [indices.index(i) for i in kept]
            D = current.extract(ie, ie)
            assert not D.free_symbols
            inverse = s.SparseMatrix(289, 289, {
                (i, j): s.sympify(v) for i, j, v in step['algebraic_block_inverse']
            }).extract(eliminated, eliminated)
            equal(D*inverse, s.eye(len(ie)))
            equal(inverse*D, s.eye(len(ie)))
            feedback = clean(-inverse*current.extract(ie, ir))
            old_feedback = polynomial(step['write_back_auxiliary_from_retained'], 289, 289)
            equal(feedback, old_feedback.extract(eliminated, kept))
            local = s.MutableSparseMatrix(len(indices), len(kept), {})
            for j, i in enumerate(ir):
                local[i, j] = 1
            for (i, j), value in feedback.todok().items():
                local[ie[i], j] = value
            injection = s.SparseMatrix(len(indices), len(ie), {(i, j): 1 for j, i in enumerate(ie)})
            self.contact += self.lift*injection*inverse*injection.T*negative(self.lift).T
            reduced = clean(current.extract(ir, ir)+current.extract(ir, ie)*feedback)
            equal(negative(local).T*current*local, reduced)
            self.lift = clean(self.lift*local)
            current = reduced
            indices = kept
            self.steps.append({'groups': step['eliminated_groups'], 'eliminated_fields': eliminated,
                               'remaining_dimension': len(indices)})
        assert indices == list(range(121))
        self.retained = current
        self.contact = clean(self.contact)
        self.injection = s.SparseMatrix(289, 121, {(i, i): 1 for i in range(121)})

    def phase(self):
        """Actual all-spatial-momentum Legendre data, with its constraints intact."""
        symbol = clean(self.retained.subs(dict(zip(P, [LAMBDA, *[s.I*k for k in K]]))))
        coeff = [clean(symbol.diff(LAMBDA, n).subs(LAMBDA, 0)/s.factorial(n)) for n in range(3)]
        equal(symbol, sum((LAMBDA**n*c for n, c in enumerate(coeff)), s.zeros(121)))
        K0, K1, K2 = coeff
        zero = s.zeros(121)
        omega = s.SparseMatrix.vstack(s.SparseMatrix.hstack(K1, K2), s.SparseMatrix.hstack(-K2, zero))
        energy = s.diag(-K0, -K2)
        canonical_pullback = s.SparseMatrix.vstack(
            s.SparseMatrix.hstack(s.eye(121), zero), s.SparseMatrix.hstack(-K1/2, -K2))
        return symbol, coeff, clean(omega), clean(energy), clean(canonical_pullback)


def main():
    started = time.monotonic()
    action = RetainedMatterAction()
    source = action.source
    H, S, T, C, E = action.H, action.retained, action.lift, action.contact, action.injection
    equal(S, polynomial(source.active['primitive_121_Fourier_Jacobi_entries'], 121, 121))
    equal(E.T*T, s.eye(121))
    equal(H*T, E*S)
    equal(H*C+E*negative(T).T, s.eye(289))
    equal(C*H+T*E.T, s.eye(289))
    equal(E.T*C, s.zeros(121, 289))
    equal(C*E, s.zeros(289, 121))
    equal(negative(C).T, C)
    equal(negative(S).T, S)
    print('PASS all-four-momentum auxiliary-only Schur action and whole289 source reconstruction, retaining all48 original matter coordinates', flush=True)

    F = decode(source.exchange['full_polynomial_field_change'])
    Fi = decode(source.exchange['full_polynomial_inverse'])
    U, Ui = F[:121, :121], Fi[:121, :121]
    equal(U*Ui, s.eye(121)); equal(Ui*U, s.eye(121))
    equal(T*U, F[:, :121])
    canonical = decode(source.exchange['canonical_operator'])
    dual = decode(source.exchange['independent_dual_operator'])
    scalar_inverse = s.Matrix(source.active['Ward_constraint_elimination']['scalar_constraint_inverse']).applyfunc(s.sympify)
    normal = clean(negative(U).T*S*U)
    equal(normal[:9, :9]*scalar_inverse, s.eye(9))
    equal(normal, s.diag(normal[:9, :9], canonical, dual, s.zeros(9)))
    contact_full = s.zeros(289)
    full_read = negative(F).T
    for step in source.active['algebraic_Schur_steps']:
        ids = step['eliminated_fields']
        inverse = s.SparseMatrix(289, 289, {(i, j): s.sympify(v)
            for i, j, v in step['algebraic_block_inverse']}).extract(ids, ids)
        contact_full += F[:, ids]*inverse*full_read[ids, :]
    equal(contact_full, C)
    ward_contact = clean(U[:, :9]*scalar_inverse*negative(U[:, :9]).T)
    contact_full = clean(C+T*ward_contact*negative(T).T)
    equal(contact_full*source.injection, decode(source.exchange['contact_field_response']))
    for ids, key in [(list(range(9, 88)), 'canonical_field_lift'),
                     (list(range(88, 112)), 'independent_dual_field_lift')]:
        equal(T*U[:, ids], decode(source.exchange[key]))
    groups = [field['group'] for field in source.active['fields'][:121]]
    matter_ids = [i for i, group in enumerate(groups) if group in ('primal_H', 'dual_H')]
    assert matter_ids == list(range(73, 121))
    mixed = {}
    for name, port in [('canonical79', U[:, 9:88]), ('independent_dual24', U[:, 88:112]), ('scalar_Ward_contact', ward_contact)]:
        read = port[matter_ids, :]
        assert read.todok()
        mixed[name] = {'primal_original_rows': sorted({i+73 for i, j in read[:24, :].todok()}),
                       'dual_original_rows': sorted({i+97 for i, j in read[24:, :].todok()}),
                       'matter_nonzero_entries': len(read.todok())}
    print('PASS original121 congruence to scalarWard+canonical79+dual24+null9; all existing contact and retarded lifts reconstructed once', flush=True)

    symbol, coeff, omega, energy, pullback = action.phase()
    for n, matrix in enumerate(coeff):
        equal(reverse_k(matrix).T, (-1)**n*matrix)
        equal(s.conjugate(matrix), reverse_k(matrix))
    equal(reverse_k(omega).T, -omega)
    equal(reverse_k(energy).T, energy)
    canonical_omega = s.SparseMatrix.vstack(
        s.SparseMatrix.hstack(s.zeros(121), -s.eye(121)),
        s.SparseMatrix.hstack(s.eye(121), s.zeros(121)))
    equal(reverse_k(pullback).T*canonical_omega*pullback, omega)
    jet_graph = s.SparseMatrix.vstack(s.eye(121), LAMBDA*s.eye(121))
    equal((LAMBDA*omega-energy)*jet_graph, s.SparseMatrix.vstack(symbol, s.zeros(121)))
    K0, K1, K2 = coeff
    assert not K2.free_symbols
    equal(K2[matter_ids, :], s.zeros(48, 121))
    equal(K2[:, matter_ids], s.zeros(121, 48))
    kinetic_rank = K2.rank()
    print('PASS source all-momentum presymplectic Legendre pullback and first-order Euler identity; second-order kinetic rank', kinetic_rank, flush=True)

    # Omitting the actually eliminated Lorentz coupling changes matter's
    # retained operator: it is not an additional independent boson exchange.
    correction = clean(S-H[:121, :121])
    matter_correction = correction[matter_ids, matter_ids]
    assert matter_correction.todok()
    paths = [BASE/'active-gauge/receipt.json', BASE/'matter-vertices/exchange.json',
             HERE/'retained_matter_action.py', HERE/'full_jacobi_source.json',
             HERE/'independent_full_jacobi_source.json']
    out = {
        'root': ROOT_ID, 'source_sha256': source.vertices['source_sha256'],
        'scope': 'SOURCE_RETAINED121_AUXILIARY_ONLY_ACTION_AND_ALL_MOMENTUM_PRESYMPLECTIC_LEGENDRE',
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'retained_fields': source.active['fields'][:121], 'auxiliary_steps': action.steps,
        'retained_dimension': 121, 'retained_matter_real_coordinates': 48, 'retained_bosonic_coordinates': 73,
        'retained_operator': encode(S), 'retained_field_lift': encode(T),
        'auxiliary_only_contact': encode(C), 'retained_source_readback': encode(negative(T).T),
        'source_reconstruction': 'S y=T(-p)^T f implies H[T y+Caux f]=f, with E^T Caux=0 and E^T T=I121',
        'source_energy_elimination': 'Lred(y;f)=1/2 y(-p)^T S(p)y(p)-f(-p)^T T(p)y(p)-1/2 f(-p)^T Caux(p)f(p)',
        'normal_coordinate_change': encode(U), 'normal_coordinate_inverse': encode(Ui),
        'scalar_Ward_contact_on_retained': encode(ward_contact),
        'existing_retarded_response_identity': 'G289=Caux+T[CWard+U79 G79 U79(-p)^T+U24 G24 U24(-p)^T]T(-p)^T on the original compatible sources',
        'mixed_response_matter_rows': mixed,
        'physical_momentum_variables': list(map(str, K)),
        'retained_time_coefficients': [encode(v) for v in coeff],
        'second_order_kinetic_rank': kinetic_rank,
        'presymplectic_phase_dimension': 242,
        'presymplectic_form': encode(omega), 'Legendre_energy_hessian': encode(energy),
        'canonical_momentum_pullback': encode(pullback),
        'canonical_momentum': 'pi(k)=-K2(k) v(k)-K1(k)y(k)/2',
        'first_order_equation': 'Omega(k) d_t(y,v)-Energy(k)(y,v)=(f_retained,0); v=dot(y) reproduces the original retained Euler operator',
        'all_momentum_first_order_Euler_and_Legendre_checked': True,
        'matter_second_order_kinetic_zero': True,
        'omitted_auxiliary_matter_correction_nonzero_entries': len(matter_correction.todok()),
        'scalar61_scope': 'peripheral scalar61 is the separate retained original scalar phase; its eliminated exchange must not also be added when it is explicit',
        'quantum_scope': 'classical source action and presymplectic pullback with original matter retained; no assignment of bosonic CCR to the mixed121 carrier, no Dirac constraint reduction or full interacting quantum Hamiltonian claimed',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3),
    }
    (HERE/'retained_matter_action.json').write_text(json.dumps(out, separators=(',', ':'))+'\n')
    print('PASS retained original matter action and same-source Legendre interface', out['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
