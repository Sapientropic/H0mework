#!/usr/bin/env python3
"""Independent raw spatial BF/Dirac audit of the nonzero physical phase splice.

Neither spatial phase producer is imported. The full consistent carrier is
lifted through the actual289 source action, gauge parameters are solved with
the independent spatial reader, and internal realification precedes Fourier
substitution. Both momenta are checked against their original field action.
"""
from __future__ import annotations

import hashlib
import json
import time
from functools import lru_cache
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from independent_source_spatial_phase_tangent import RawSpatialPhase
from independent_source_full_linear_split import build_raw, read_matrix, P, K
from independent_source_physical_phase_splice import rectangular
from independent_retained_hamiltonian_reduction import DOMAIN
from independent_source_joint_temporal_rates import (
    HERE, BASE, ROOT, ROOT_ID, bindings, clean, rational, eq, encode, zero)
from independent_source_gauge_legendre import W, SIGMA, hodge, hodge_field_jet, realify
from independent_source_lorentz_contact import real_bilinear


@lru_cache(maxsize=None)
def field_number(value):
    value = s.sympify(value)
    if value.is_Rational: return DOMAIN.from_sympy(value)
    if value.is_Add: return sum((field_number(x) for x in value.args), DOMAIN.zero)
    if value.is_Mul:
        result = DOMAIN.one
        for x in value.args: result *= field_number(x)
        return result
    if value.is_Pow and value.exp.is_Integer:
        return field_number(value.base)**int(value.exp)
    assert not value.free_symbols
    return DOMAIN.from_sympy(value)


def exact(matrix):
    data = {}
    for (i, j), value in s.SparseMatrix(matrix).todok().items():
        coefficient = field_number(value)
        if coefficient != DOMAIN.zero: data.setdefault(i, {})[j] = coefficient
    return DM(data, matrix.shape, DOMAIN).to_sparse()


def verify_field_conversion():
    values = [s.S.Zero, s.S.One, s.Rational(1, 7), s.I, s.sqrt(2), s.sqrt(15), s.sqrt(30),
              3*s.sqrt(2)/5-s.I*s.sqrt(30)/17, (1+s.I*s.sqrt(2)+s.sqrt(15))**-1,
              (s.sqrt(30)+s.sqrt(2)+s.I)**5]
    for value in values: assert field_number(value) == DOMAIN.from_sympy(value)


def product(*matrices):
    value = exact(matrices[0])
    for matrix in matrices[1:]: value = value*exact(matrix)
    return s.SparseMatrix(value.to_Matrix())


def operator_jet(operator, field, generator, momentum):
    # Collect actual derivative monomials after evaluating the spatial jet;
    # only then use the consistent138 time generator for all time powers.
    operator = clean(operator.subs(dict(zip(P[1:], [s.I*k for k in momentum]))))
    coefficients = {}
    for (i, j), value in operator.todok().items():
        for (degree,), coefficient in s.Poly(value, P[0]).terms():
            coefficients.setdefault(degree, {})[i, j] = coefficient
    result = s.SparseMatrix.zeros(operator.rows, field.cols)
    for degree, entries in coefficients.items():
        partial = exact(s.SparseMatrix(*operator.shape, entries))*exact(field)
        for _ in range(degree): partial = partial*exact(generator)
        result += s.SparseMatrix(partial.to_Matrix())
    return clean(result)


class RawSpatialActive:
    def __init__(self):
        self.phase = RawSpatialPhase()
        self.raw, self.graph = self.phase.raw, self.phase.graph
        self.source = build_raw(self.raw)
        self.indices = {(f['group'], tuple(f['coordinate'])): i for i, f in enumerate(self.raw.active['fields'])}
        self.retained = json.loads((HERE/'retained_matter_action.json').read_text())
        catalog = json.loads((HERE/'retained_hamiltonian_reduction.json').read_text())
        self.row = next(row for row in catalog['source_momenta'] if any(s.sympify(x) != 0 for x in row['momentum']))
        self.k = tuple(map(s.sympify, self.row['momentum']))
        self.lift = read_matrix(self.retained['retained_field_lift'])
        self.ward = clean(self.lift*read_matrix(self.retained['normal_coordinate_change'])[:, 112:121])
        H = s.MutableSparseMatrix.zeros(289, 289)
        for i, j, powers, value in self.raw.active['Fourier_Jacobi_entries']:
            H[i, j] += s.sympify(value)*s.prod(p**n for p, n in zip(P, powers))
        self.original = clean(H)
        # Original coefficients, including the realified matter blocks, are
        # real before d_i=i k_i. This pays the two Fourier partner actions.
        for value in self.original.todok().values():
            for coefficient in s.Poly(value, *P).coeffs(): zero(s.im(coefficient))
        self.e = self.source['e']
        self.Gt = self.raw.geometry(self.e)[1][:, :16]
        omega0 = s.Matrix(self.raw.active['actual_background']['lowered_Lorentz_connection']).applyfunc(s.sympify).reshape(24, 1)
        self.dGt = s.zeros(16, 16); self.dE = s.zeros(252, 16)
        self.dHodge = []
        F0 = self.raw.curvature(self.raw.A)
        for j in range(16):
            self.dGt[:, j] = self.raw.Gsymbol[:, :16].diff(self.raw.eg[j]).subs(dict(zip(self.raw.eg, self.e))).T*omega0
            variation = s.zeros(4); variation[j] = 1
            Evar = s.kronecker_product(self.raw.coefficient_derivatives(self.e, variation)[1][0], s.eye(63))
            self.dE[:, j] = (self.raw.chi0*Evar).T
            star_variation = hodge_field_jet(self.e, variation, F0, s.zeros(6, 12))[1]
            self.dHodge.append(clean(-W*star_variation*self.raw.Gram/SIGMA).reshape(72, 1))
        self.Epair = real_bilinear(self.source['principal'][0].T)
        self.ecoefficient = clean(self.dE.applyfunc(s.re).col_join(-self.dE.applyfunc(s.im)))
        self.occupied_real = realify(self.source['O'])
        tail = json.loads((HERE/'source_physical_phase_splice.json').read_text())
        self.tail = clean(read_matrix(tail['original_nonlinear_chart_tangent'])*read_matrix(tail['tail_embedding_into_actual1208']))
        self.tail_form = read_matrix(tail['tail_original_symplectic_form'])
        self.tail_H = read_matrix(tail['original_tail_Hamiltonian']['original_density_Hamiltonian_hessian'])
        C = self.source['C']; Cr = realify(C)
        EC = clean(C.H*self.source['principal'][0]*C)
        ECinv = exact(EC).inv().to_Matrix()
        D = real_bilinear(EC.T)
        Dinv = clean(realify(ECinv.T)*s.diag(s.eye(240), -s.eye(240)))
        eq(Dinv*D, s.eye(480)); eq(D*Dinv, s.eye(480))
        self.tail_reader = rectangular(1082, 1214, [(0, 710, Dinv*Cr.T),
            (480, 6, s.eye(61)), (541, 613, s.eye(61)), (602, 103, Cr.T)])
        eq(self.tail_reader*self.tail, s.eye(1082))
        eq(self.tail_form*self.tail_reader, -self.tail.T*self.phase.J)
        triangular = json.loads((HERE/'source_full_linear_split.json').read_text())['triangular_tail']
        self.tail_A = rectangular(1082, 1082, [(0, 0, read_matrix(triangular['dual'])),
            (480, 480, read_matrix(triangular['scalar'])), (602, 602, read_matrix(triangular['primal'])),
            (480, 0, read_matrix(triangular['dual_to_scalar'])), (602, 480, read_matrix(triangular['scalar_to_primal']))])

    def cached(self, key, sign):
        A = read_matrix(self.row[key])
        return A if sign == 1 else A.conjugate()

    def fiber(self, sign, expected):
        k = tuple(sign*x for x in self.k)
        assert list(map(str, k)) == expected['momentum']
        get = lambda key: self.cached(key, sign)
        generator = get('consistent_generator')
        consistency = clean(get('velocity_quotient_section')*get('consistent_initial_data_embedding'))
        y = consistency[:121, :]
        at = dict(zip(K, k))
        kinetic = read_matrix(self.retained['retained_time_coefficients'][2]).subs(at)
        eq(kinetic*(consistency[121:, :]-y*generator), s.zeros(121, generator.rows))
        symplectic = read_matrix(self.retained['presymplectic_form']).subs(at)
        energy = read_matrix(self.retained['Legendre_energy_hessian']).subs(at)
        eq(symplectic*consistency*generator, energy*consistency)
        fields = operator_jet(self.lift, y, generator, k)
        fixed_coframe = (1, 2, 3, 6, 7, 11)
        coframe_reader = s.SparseMatrix(6, 289, {(j, self.indices['coframe', divmod(a, 4)]): 1 for j, a in enumerate(fixed_coframe)})
        gauge_reader = s.SparseMatrix(36, 289, {(12*i+a, self.indices['gauge_A', (i+1, a)]): 1 for i in range(3) for a in range(12)})
        orbit_reader = self.phase.spatial.at(self.phase.spatial.reader, k)
        slice_reader = coframe_reader.col_join(orbit_reader*gauge_reader)
        Wslice = clean(slice_reader*self.ward.subs(dict(zip(P[1:], [s.I*x for x in k]))))
        assert not Wslice.free_symbols and Wslice.det() != 0
        parameter, free = Wslice.gauss_jordan_solve(-slice_reader*fields)
        assert free.rows == 0
        fixed = clean(fields+operator_jet(self.ward, parameter, generator, k))
        eq(slice_reader*fixed, s.zeros(9, generator.rows))
        eq(operator_jet(self.original, fixed, generator, k), s.zeros(289, generator.rows))
        eq(Wslice, read_matrix(expected['source_Ward_slice_matrix']))
        eq(parameter, read_matrix(expected['source_Ward_parameter']))
        eq(fixed, read_matrix(expected['original289_field_map']))
        de = s.Matrix.vstack(*(fixed[self.indices['coframe', (a, mu)], :] for a in range(4) for mu in range(4)))
        dO = s.Matrix.vstack(*(fixed[self.indices['Lorentz', (mu, a)], :] for mu in range(4) for a in range(6)))
        dA = s.Matrix.vstack(*(fixed[self.indices['gauge_A', (mu, a)], :] for mu in range(4) for a in range(12)))
        dB = s.Matrix.vstack(*(fixed[self.indices['gauge_B', (pair, a)], :] for pair in range(6) for a in range(12)))
        def internal_real_fields(group):
            H = s.Matrix.vstack(*(fixed[self.indices[group, (im, spin, color)], :]
                                  for im in range(2) for spin in range(4) for color in range(3)))
            return clean(self.occupied_real*H)
        psi, chi = internal_real_fields('primal_H'), internal_real_fields('dual_H')
        momentum_matter = clean(self.Epair*chi+self.ecoefficient*de)
        Pi_e = clean(self.Gt.T*dO+self.dGt*de)
        Pi_A = clean(s.kronecker_product(W[:, :3].T, self.raw.Gram)*dB)
        scalar_rows = [j for j, f in enumerate(self.raw.active['fields']) if f['group'] == 'scalar_J']
        Jscalar = self.raw.O[:, self.raw.active['J_independent_columns']]
        phi = clean(Jscalar*fixed[scalar_rows, :])
        # Original source D0 v=0, h00=-1/N, h0i=0; actual A0 variation
        # remains in this covariant scalar velocity before its Gauss readback.
        Piphi = clean(-(phi*generator+self.raw.O*dA[:12, :])/self.source['N'])
        q = clean(s.Matrix.vstack(de[(5, 9, 10, 13, 14, 15), :], self.graph.Rd.T*phi, dA[12:, :], psi))
        mom = clean(s.Matrix.vstack(Pi_e[(5, 9, 10, 13, 14, 15), :], self.graph.R.T*Piphi, Pi_A, momentum_matter))
        whole = q.col_join(mom)
        eq(self.phase.at(self.phase.Piphi, k)*whole, Piphi)
        eq(self.phase.at(self.phase.G12, k)*whole, s.zeros(12, generator.rows))
        eq(Piphi, read_matrix(expected['momentum_readback']['original_scalar_momentum']))
        # A second original-density path differentiates the four-index Hodge
        # field. Its electric curvature retains -i k_i delta A0 explicitly.
        curvature = []
        for mu, nu in ((0, 1), (0, 2), (0, 3), (2, 3), (3, 1), (1, 2)):
            Am, An = dA[12*mu:12*(mu+1), :], dA[12*nu:12*(nu+1), :]
            left = An*generator if mu == 0 else s.I*k[mu-1]*An
            right = Am*generator if nu == 0 else s.I*k[nu-1]*Am
            curvature.append(clean(left-right+self.raw.ad(self.raw.A[mu, :])*An-self.raw.ad(self.raw.A[nu, :])*Am))
        kernel = clean(-W*hodge(self.e)/SIGMA)
        direct = clean(s.kronecker_product(kernel, self.raw.Gram)*s.Matrix.vstack(*curvature))
        direct += sum((self.dHodge[j]*de[j, :] for j in range(16)), s.zeros(72, generator.rows))
        eq(direct[:36, :], Pi_A)
        divergence = clean(sum((s.I*k[i]*Pi_A[12*i:12*(i+1), :] for i in range(3)), s.zeros(12, generator.rows)))
        eq(divergence, read_matrix(expected['momentum_readback']['original_gauge_divergence']))
        assert divergence.todok() and Piphi.todok()
        # The forbidden whole-Fourier realification loses actual coefficients.
        internal_psi = psi[:252, :]+s.I*psi[252:, :]
        wrong_psi = internal_psi.applyfunc(s.re).col_join(internal_psi.applyfunc(s.im))
        assert clean(wrong_psi-psi).todok()
        T = self.phase.projection(k)
        eq(T*whole, whole)
        for saved in self.row['original_Ward_jet_coordinates']:
            ward_jet = read_matrix(saved)
            if sign == -1: ward_jet = ward_jet.conjugate()
            eq(whole*ward_jet, s.zeros(1214, ward_jet.cols))
        active = clean(whole*get('quotient_section')); Q = get('quotient_map')
        eq(active*Q, whole); eq(whole*generator, active*get('Hamiltonian_generator')*Q)
        eq(active, read_matrix(expected['active_embedding']))
        omega = clean(-active.H*self.phase.J*active)
        eq(omega, get('nondegenerate_phase_form'))
        eq(active.H*self.phase.J*self.tail, s.zeros(126, 1082))
        eq(T*self.tail, self.tail)
        Ra = s.SparseMatrix((exact(omega).inv()*exact(-active.H)*exact(self.phase.J)).to_Matrix())
        Rt = self.tail_reader
        eq(product(omega, Ra), -active.H*self.phase.J)
        eq(Ra, read_matrix(expected['active_reader']))
        X, reader = active.row_join(self.tail), Ra.col_join(Rt)
        eq(product(reader, X), s.eye(1208)); eq(product(X, reader), T)
        Aa, Ha = get('Hamiltonian_generator'), get('Hamiltonian_energy')
        At, Ht = clean(self.tail_A.subs(at)), clean(self.tail_H.subs(at))
        eq(omega*Aa, Ha); eq(self.tail_form*At, Ht)
        split_A = rectangular(1208, 1208, [(0, 0, Aa), (126, 126, At)])
        split_H = rectangular(1208, 1208, [(0, 0, Ha), (126, 126, Ht)])
        split_form = rectangular(1208, 1208, [(0, 0, omega), (126, 126, self.tail_form)])
        eq(split_form*split_A, split_H); eq(split_H.H, split_H)
        eq(product(self.phase.J, reader.H, split_form), X)
        eq(product(reader, T), reader)
        # The exact all-column identities prove the complete canonical
        # intertwining without materializing a redundant1214-square matrix:
        # J R^* Omega_split=X and Omega_split A_split=H_split imply
        # T J T^* R^* H_split R = X A_split R, since R T=R and T X=X.
        # RX=I also gives X^* (R^* H_split R) X=H_split universally.
        datum = read_matrix(expected['actual_phase_datum']); rate = read_matrix(expected['actual_phase_rate'])
        force = product(reader.H, split_H, reader, datum)
        eq(product(T.H, force), force)
        canonical_rate = self.phase.project(k, clean(self.phase.J*force))[0]
        eq(canonical_rate, rate)
        # The actual full coordinate sample is independently regenerated.
        input_data = s.Matrix([s.Rational((5*j+1)%13-6, 17)+s.I*s.Rational((3*j+2)%11-5, 19) for j in range(1208)])
        if sign == -1: input_data = input_data.conjugate()
        eq(product(X, input_data), datum); eq(product(reader, rate), product(split_A, input_data))
        return (X, reader, split_H, split_A, fixed), {'momentum': list(map(str, k)),
            'original_consistent138_before_quotient': True, 'all_original289_rows_and_Ward_jets': True,
            'complete_raw_BF_Hodge_Dirac_and_scalar_Gauss_readback': True,
            'internal_realification_before_Fourier_negative_control': True,
            'actual126_plus1082_inverse_equals_source_spatial_projector': True,
            'paired_symplectic_energy_and_generator_intertwining': True}


def main():
    began = time.monotonic(); verify_field_conversion()
    path = HERE/'source_spatial_active_phase_splice.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid = ['independent_source_spatial_phase_tangent.json', 'independent_source_physical_phase_splice.json',
            'independent_source_full_linear_split.json', 'independent_retained_matter_action.json',
            'independent_retained_hamiltonian_reduction.json']
    for name in paid: count += bindings(json.loads((HERE/name).read_text()))
    m = RawSpatialActive(); assert m.raw.hashes == candidate['source_sha256']
    plus, plus_report = m.fiber(1, candidate['fibers'][0])
    print('PASS independent nonzero original289/consistent138 lift, raw spatial momenta and full1208 source phase/action', flush=True)
    minus, minus_report = m.fiber(-1, candidate['fibers'][1])
    for a, b in zip(plus, minus): eq(a.conjugate(), b)
    eq(-minus[0].T*m.phase.J*plus[0], rectangular(1208, 1208,
       [(0, 0, m.cached('nondegenerate_phase_form', 1)), (126, 126, m.tail_form)]))
    print('PASS actual opposite-momentum original action, transpose pairing and all source real-field partners', flush=True)
    assert candidate['uniform_all_k_active_reduction_claimed'] is False
    assert candidate['nonlinear_or_quantum_spectrum_inferred_from_linear_phase'] is False
    paths = [HERE/name for name in ('independent_source_spatial_active_phase_splice.py',
        'source_spatial_active_phase_splice.py', 'source_spatial_active_phase_splice.json',
        'independent_source_spatial_phase_tangent.py', 'independent_source_full_linear_split.py',
        'independent_source_physical_phase_splice.py', 'independent_source_joint_temporal_rates.py',
        'independent_source_gauge_legendre.py', 'independent_retained_hamiltonian_reduction.py', 'retained_matter_action.json', 'retained_hamiltonian_reduction.json')]+[HERE/name for name in paid]
    result = {'root': ROOT_ID, 'source_sha256': m.raw.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'verdict': 'CERTIFIED_ACTUAL_NONZERO_PAIRED_MOMENTUM_SOURCE_COMMON_PHASE_AND_ORIGINAL_INTERTWINING',
        'scope': candidate['scope'], 'checked_input_bindings': count, 'candidate_constructor_imported': False,
        'source_fibers': [plus_report, minus_report],
        'spatial_scope': 'Both displayed nonzero Fourier momenta are evaluated against the original field action and native spatial Gauss projection. All internal coefficients are realified before Fourier substitution; the final symplectic pairing is the -k transpose pairing.',
        'homogeneous_carrier_substitution_or_uniform_active_rank_assumption': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_spatial_active_phase_splice.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent original spatial active phase splice', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
