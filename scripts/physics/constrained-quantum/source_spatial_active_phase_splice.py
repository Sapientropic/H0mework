#!/usr/bin/env python3
"""Original nonzero Fourier action in the source spatial transverse phase.

All internal-complex coefficients are realified before Fourier evaluation.
The original consistent carrier is lifted before its Ward radical is removed;
the native orbit reader, with its actual divergence sign, fixes all fields by
the same gauge parameter. Opposite momenta are paired by transpose.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import json
import time
import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID
from source_full_linear_split import SourceFullLinearSplit, decode, P, K, real_pair
from source_coframe_live_ordering import FREE, DEPENDENT
from source_lorentz_contact import clean, equal, encode, GAMMA
from source_stabilizer_phase_reduction import SourceStabilizerPhaseReduction, block_diagonal
from retained_matter_action import polynomial
from retained_hamiltonian_reduction import DOMAIN
from sympy.polys.matrices import DomainMatrix as DM


def zero(A): equal(clean(A), s.zeros(*A.shape))


@lru_cache(maxsize=65536)
def field_element(value):
    value = s.sympify(value)
    assert not value.free_symbols and not value.has(s.Float)
    if value.is_Rational:
        return DOMAIN.convert(value)
    if value.is_Add:
        return sum((field_element(v) for v in value.args), DOMAIN.zero)
    if value.is_Mul:
        result = DOMAIN.one
        for v in value.args: result *= field_element(v)
        return result
    if value.is_Pow and value.exp.is_Integer:
        return field_element(value.base)**int(value.exp)
    # Only primitive radical/imaginary atoms require field identification;
    # the cached homomorphism evaluates every compound coefficient exactly.
    return DOMAIN.from_sympy(value)


def dm(matrix):
    entries = {}
    for (i, j), value in s.SparseMatrix(matrix).todok().items():
        element = field_element(value)
        if element: entries.setdefault(i, {})[j] = element
    return DM(entries, matrix.shape, DOMAIN).to_sparse()


def mul(*matrices):
    """Original exact QQ(sqrt2,sqrt15,i), not symbolic expression division."""
    value = dm(matrices[0])
    for matrix in matrices[1:]: value = value*dm(matrix)
    return clean(value.to_Matrix())


def operator_action(operator, field, generator, momentum):
    operator = clean(operator.subs(dict(zip(P[1:], [s.I*k for k in momentum]))))
    degree = max((s.degree(v, P[0]) for v in operator.todok().values()), default=0)
    answer = DM.zeros((operator.rows, field.cols), DOMAIN)
    jet, G = dm(field), dm(generator)
    for order in range(degree+1):
        answer += dm(operator.applyfunc(lambda x: s.expand(x).coeff(P[0], order)))*jet
        if order < degree: jet = jet*G
    return clean(answer.to_Matrix())


class FrozenSpatialTangent:
    """Consume the certified all-k matrices, then evaluate their source factors.

    Re-expanding the whole symbolic1214 projector would rerun an already paid
    producer. Its frozen E/C/F and broken momentum coefficients are the exact
    inputs; all pointwise identities are checked by the consumer below.
    """
    def __init__(self):
        record = json.loads((HERE/'source_spatial_phase_tangent.json').read_text())
        certified = json.loads((HERE/'independent_source_spatial_phase_tangent.json').read_text())
        assert record['root'] == certified['root'] == ROOT_ID
        assert certified['verdict'] == 'CERTIFIED_ALL_REAL_SPATIAL_MOMENTUM_WHOLE_SOURCE_CANONICAL_TANGENT'
        assert certified['source_sha256'] == record['source_sha256']
        for receipt in (record, certified):
            for group in ('source_sha256', 'input_sha256'):
                for name, expected in receipt[group].items():
                    assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == expected, name
        self.phase = SourceStabilizerPhaseReduction()
        self.orbit = decode(record['orbit'])
        self.Gauss = decode(record['Gauss'])
        self.slice = decode(record['slice_reader'])
        self.broken_map = decode(record['broken_scalar_map'])
        self.matter_current = decode(record['source_matter_current'])
        self.k = K
        self._projectors = {}

    def at(self, matrix, momentum):
        numeric = matrix.subs(dict(zip(self.k, momentum)))
        return clean(dm(numeric).to_Matrix())

    def projector(self, momentum):
        key = tuple(momentum)
        if key not in self._projectors:
            E, C, F = [self.at(M, momentum) for M in (self.orbit, self.Gauss, self.slice)]
            negative_F = self.at(self.slice, tuple(-k for k in momentum))
            B = mul(self.phase.J, negative_F.T)
            self._projectors[key] = clean(s.eye(self.phase.J.rows)-mul(E, F)+mul(B, C))
            zero(mul(C, self._projectors[key])); zero(mul(F, self._projectors[key]))
        return self._projectors[key]

    def broken_scalar_momentum(self, momentum, tangent):
        return mul(self.at(self.broken_map, momentum), tangent)

    def full_Gauss(self, momentum, tangent):
        base = self.at(self.matter_current, momentum)
        c = self.phase
        for i in range(3):
            base[:, c.n+67+12*i:c.n+79+12*i] = s.I*momentum[i]*s.eye(12)-c.gauge.ad(c.A0[i+1, :]).T
        return clean(mul(base, tangent)+mul(c.graph.constraints.orbit.T, self.broken_scalar_momentum(momentum, tangent)))


class SpatialActiveSplice:
    def __init__(self):
        self.model = FrozenSpatialTangent()
        self.c = self.model.phase
        self.split = SourceFullLinearSplit()
        self.retained = json.loads((HERE/'retained_matter_action.json').read_text())
        self.catalog = json.loads((HERE/'retained_hamiltonian_reduction.json').read_text())
        self.old = next(row for row in self.catalog['source_momenta'] if any(s.sympify(k) != 0 for k in row['momentum']))
        self.momentum = tuple(map(s.sympify, self.old['momentum']))
        self.lift = decode(self.retained['retained_field_lift'])
        self.ward = clean(self.lift*decode(self.retained['normal_coordinate_change'])[:, 112:121])
        fields = self.split.active['fields']
        self.index = {(row['group'], tuple(row['coordinate'])): j for j, row in enumerate(fields)}
        raw = polynomial(self.split.active['Fourier_Jacobi_entries'], len(fields), len(fields))
        self.raw_action = raw.xreplace({p: P[int(str(p)[1:])] for p in raw.free_symbols})
        c, split = self.c, self.split
        equal(c.e0, split.e); equal(c.psi0, split.psi0); equal(c.chi0, split.chi0)
        equal(c.graph.R, split.R)
        ports = json.loads((HERE/'source_physical_phase_splice.json').read_text())
        self.tail = clean(decode(ports['original_nonlinear_chart_tangent'])*decode(ports['tail_embedding_into_actual1208']))
        self.tail_omega = decode(ports['tail_original_symplectic_form'])
        self.tail_hessian = decode(ports['original_tail_Hamiltonian']['original_density_Hamiltonian_hessian'])
        entries = self.tail_omega.todok()
        assert len(entries) == self.tail_omega.rows
        assert len({i for i, _ in entries}) == len({j for _, j in entries}) == self.tail_omega.rows
        self.tail_omega_inverse = s.SparseMatrix(self.tail_omega.rows, self.tail_omega.cols,
            {(j, i): 1/value for (i, j), value in entries.items()})
        equal(self.tail_omega*self.tail_omega_inverse, s.eye(self.tail_omega.rows))
        equal(self.tail_omega_inverse*self.tail_omega, s.eye(self.tail_omega.rows))
        self.source_E = split.E
        self.current_real_frame = block_diagonal(split.O, split.O)
        cf = c.common.coframe
        self.Gt = cf.geometry(c.e0)['G'][:, :16]
        source_omega = s.Matrix(split.active['actual_background']['lowered_Lorentz_connection']).applyfunc(s.sympify).reshape(24, 1)
        self.dGt_omega = s.zeros(16, 16)
        self.dE_chi = s.zeros(252, 16)
        inv, determinant = c.e0.inv(), c.e0.det()
        for j in range(16):
            self.dGt_omega[:, j] = cf.at(cf.G[:, :16].diff(cf.e[j]), c.e0).T*source_omega
            delta = s.zeros(4); delta[j] = 1
            dd, di = determinant*s.trace(inv*delta), -inv*delta*inv
            dE4 = clean(s.I*sum(((dd*inv[0, a]+determinant*di[0, a])*GAMMA[a] for a in range(4)), s.zeros(4)))
            self.dE_chi[:, j] = (split.chi0*s.kronecker_product(dE4, s.eye(63))).T
        self.p_from_chi = real_pair(self.source_E.T)
        self.p_from_e = clean(self.dE_chi.applyfunc(s.re).col_join(-self.dE_chi.applyfunc(s.im)))
        self.curvature0 = c.common.gauge.curvature(c.A0, s.zeros(4, 48))
        self.constitutive0 = c.gauge.constitutive(c.e0)['kernel']

    def old_matrix(self, key, sign):
        A = decode(self.old[key])
        return A if sign == 1 else clean(A.conjugate())

    def native_slice_reader(self, momentum):
        rows = [self.index['coframe', (j//4, j%4)] for j in DEPENDENT]
        selector = s.SparseMatrix(6, len(self.split.active['fields']), {(j, row): 1 for j, row in enumerate(rows)})
        gauge = s.SparseMatrix(36, len(self.split.active['fields']), {
            (12*i+a, self.index['gauge_A', (i+1, a)]): 1 for i in range(3) for a in range(12)})
        return clean(selector.col_join(self.model.at(self.model.slice, momentum)[:, 67:103]*gauge))

    def momentum_readback(self, fixed, generator, momentum):
        n, c, split, index = fixed.cols, self.c, self.split, self.index
        de = s.Matrix.vstack(*(fixed[index['coframe', (a, mu)], :] for a in range(4) for mu in range(4)))
        domega = s.Matrix.vstack(*(fixed[index['Lorentz', (mu, a)], :] for mu in range(4) for a in range(6)))
        dA = s.Matrix.vstack(*(fixed[index['gauge_A', (mu, a)], :] for mu in range(4) for a in range(12)))
        matter_rows = lambda name: s.Matrix.vstack(*(fixed[index[name, (im, spin, color)], :] for im in range(2) for spin in range(4) for color in range(3)))
        psi_real = clean(self.current_real_frame*matter_rows('primal_H'))
        chi_real = clean(self.current_real_frame*matter_rows('dual_H'))
        # Only original INTERNAL matrices undergo realification. Each column
        # of psi_real/chi_real is already a complex Fourier amplitude of a
        # real original field; taking its real part would lose momentum terms.
        matter_momentum = clean(self.p_from_chi*chi_real+self.p_from_e*de)
        Pi_e = clean(self.Gt.T*domega+self.dGt_omega*de)
        Bmag = s.Matrix.vstack(*(fixed[index['gauge_B', (pair, a)], :] for pair in range(3, 6) for a in range(12)))
        Pi_A = clean(s.kronecker_product(s.eye(3), c.gauge.gram)*Bmag)
        phi = clean(split.J*fixed[:split.J.cols, :])
        Pi_phi = clean(-(phi*generator+split.orbit*dA[:12, :])/split.N)
        x, pi = clean(c.graph.dual_R.T*phi), clean(split.R.T*Pi_phi)
        q = s.Matrix.vstack(de[list(FREE), :], x, dA[12:, :], psi_real)
        canonical_P = s.Matrix.vstack(Pi_e[list(FREE), :], pi, Pi_A, matter_momentum)
        whole = clean(q.col_join(canonical_P))
        equal(self.model.broken_scalar_momentum(momentum, whole), Pi_phi)
        zero(self.model.full_Gauss(momentum, whole))
        # Direct original constitutive differentiation checks the auxiliary
        # momentum, including the spatial -ik_i A0 electric contribution.
        dF = []
        pairs = ((0, 1), (0, 2), (0, 3), (2, 3), (3, 1), (1, 2))
        for mu, nu in pairs:
            Am, An = dA[12*mu:12*(mu+1), :], dA[12*nu:12*(nu+1), :]
            derivative_m = An*generator if mu == 0 else s.I*momentum[mu-1]*An
            derivative_n = Am*generator if nu == 0 else s.I*momentum[nu-1]*Am
            dF.append(clean(derivative_m-derivative_n+c.gauge.ad(c.A0[mu, :])*An-c.gauge.ad(c.A0[nu, :])*Am))
        field = s.Matrix.vstack(*dF)
        direct = clean(s.kronecker_product(self.constitutive0, c.gauge.gram)*field)
        for j in range(16):
            delta = s.zeros(4); delta[j] = 1
            tau = s.Symbol('coframe_delta', real=True)
            e = c.e0+tau*delta
            kernel = c.gauge.constitutive(e)['kernel']
            variation = clean(kernel.diff(tau).subs(tau, 0)*self.curvature0*c.gauge.gram)
            direct += variation.reshape(72, 1)*de[j, :]
        equal(clean(direct[:36, :]), Pi_A)
        divergence = clean(sum((s.I*momentum[i]*Pi_A[12*i:12*(i+1), :] for i in range(3)), s.zeros(12, n)))
        assert divergence.todok() and Pi_phi.todok()
        return whole, {'original_scalar_momentum': encode(Pi_phi), 'original_gauge_divergence': encode(divergence),
                       'all12_original_Gauss_zero': True, 'raw_BF_equals_full_constitutive_derivative': True,
                       'internal_realification_precedes_Fourier': True,
                       'full_delta_E_and_coframe_BF_momentum_terms_retained': True}

    def fiber(self, sign):
        momentum = tuple(sign*k for k in self.momentum)
        get = lambda key: self.old_matrix(key, sign)
        generator = get('consistent_generator')
        phase = clean(get('velocity_quotient_section')*get('consistent_initial_data_embedding'))
        Y = phase[:len(self.retained['retained_fields']), :]
        kinetic = decode(self.retained['retained_time_coefficients'][2]).subs(dict(zip(K, momentum)))
        zero(kinetic*(phase[Y.rows:, :]-Y*generator))
        # Verify the conjugated cached reduction against the actual spatial
        # action, rather than treating the negative fiber as a new assumption.
        omega242 = decode(self.retained['presymplectic_form']).subs(dict(zip(K, momentum)))
        energy242 = decode(self.retained['Legendre_energy_hessian']).subs(dict(zip(K, momentum)))
        zero(omega242*phase*generator-energy242*phase)
        full = operator_action(self.lift, Y, generator, momentum)
        print('Built original auxiliary lift', momentum, flush=True)
        slice_reader = self.native_slice_reader(momentum)
        W = clean(slice_reader*self.ward.subs(dict(zip(P[1:], [s.I*k for k in momentum]))))
        assert not W.free_symbols and W.det() != 0
        parameter = -mul(dm(W).inv().to_Matrix(), slice_reader, full)
        fixed = clean(full+operator_action(self.ward, parameter, generator, momentum))
        zero(slice_reader*fixed)
        zero(operator_action(self.raw_action, fixed, generator, momentum))
        print('PASS all289 original Jacobi rows after same-parameter Ward slice', momentum, flush=True)
        whole, readback = self.momentum_readback(fixed, generator, momentum)
        print('PASS original spatial scalar/BF/gauge/full-delta-p momentum readback', momentum, flush=True)
        zero(self.model.at(self.model.Gauss, momentum)*whole)
        zero(self.model.at(self.model.slice, momentum)*whole)
        equal(self.model.projector(momentum)*whole, whole)
        for original_jet in self.old['original_Ward_jet_coordinates']:
            jet = decode(original_jet)
            if sign == -1: jet = clean(jet.conjugate())
            zero(whole*jet)
        active = clean(whole*get('quotient_section'))
        equal(whole, active*get('quotient_map'))
        equal(whole*generator, active*get('Hamiltonian_generator')*get('quotient_map'))
        expected_form = get('nondegenerate_phase_form')
        equal(-mul(active.H, self.c.J, active), expected_form)
        zero(mul(active.H, self.c.J, self.tail))
        equal(self.model.projector(momentum)*self.tail, self.tail)
        print('PASS source fiber original289 and all spatial momentum/Gauss rows', momentum, flush=True)
        active_inverse_form = clean(dm(expected_form).inv().to_Matrix())
        active_reader = -mul(active_inverse_form, active.H, self.c.J)
        tail_reader = -mul(self.tail_omega_inverse, self.tail.T, self.c.J)
        X, R = clean(active.row_join(self.tail)), clean(active_reader.col_join(tail_reader))
        equal(mul(R, X), s.eye(X.cols))
        equal(mul(X, R), self.model.projector(momentum))
        oldA, oldH = get('Hamiltonian_generator'), get('Hamiltonian_energy')
        equal(expected_form*oldA, oldH)
        tailA = self.split.tail_generator(momentum)
        tailH = clean(self.tail_hessian.subs(dict(zip(K, momentum))))
        equal(self.tail_omega*tailA, tailH)
        splitA, splitH = s.diag(oldA, tailA), s.diag(oldH, tailH)
        inverse_form = s.diag(active_inverse_form, self.tail_omega_inverse)
        # Exact source factors prove the entire1214 operator identity without
        # expanding its dense matrix product. RX=I and XR=T were checked above.
        # H=R(-k)^T Hsplit R, A=J H=X Asplit R on this very source subspace.
        equal(mul(self.c.J, R.H), mul(X, inverse_form))
        equal(mul(inverse_form, splitH), splitA)
        equal(splitH.H, splitH)
        print('PASS source fiber', momentum, 'whole289, full spatial momenta/Gauss, phase inverse and exact Hamiltonian factors', flush=True)
        datum = s.Matrix([s.Rational((5*j+1)%13-6, 17)+s.I*s.Rational((3*j+2)%11-5, 19) for j in range(X.cols)])
        if sign == -1: datum = datum.conjugate()
        actual = mul(X, datum)
        rate = mul(self.c.J, mul(R.H, mul(splitH, mul(R, actual))))
        equal(rate, mul(X, mul(splitA, datum)))
        equal(mul(R, rate), mul(splitA, datum))
        return {'momentum': list(map(str, momentum)), 'consistent_dimension': generator.rows,
            'active_dimension': active.cols, 'whole_physical_dimension': X.cols,
            'source_Ward_slice_matrix': encode(W), 'source_Ward_parameter': encode(parameter),
            'original289_field_map': encode(fixed), 'momentum_readback': readback,
            'active_embedding': encode(active), 'active_reader': encode(active_reader),
            'both_inverse_identities': 'R(k) X(k)=I; X(k) R(k)=the original spatial phase projector T(k)',
            'original_Hamiltonian_intertwining': True,
            'Hamiltonian_factor_identity': 'H(k)=R(-k)^T Hsplit(k) R(k), J R(-k)^T=X(k) Omega_split(k)^-1; hence A X=X Asplit and X(-k)^T H X=Hsplit by the checked RX=I',
            'actual_phase_datum': encode(actual), 'actual_phase_rate': encode(rate)}, (X, R, splitH, splitA, fixed)


def main():
    started = time.monotonic()
    controls = [s.Rational(7, 13), s.I, s.sqrt(30), (2+s.sqrt(2)-s.I)/(3+s.sqrt(15)),
                (s.sqrt(2)+s.sqrt(15)+s.I)**-3]
    for value in controls:
        assert field_element(value) == DOMAIN.from_sympy(value)
    m = SpatialActiveSplice()
    print('Built same-source spatial chart and original paired-fiber inputs', flush=True)
    positive, p = m.fiber(1)
    print('PASS original nonzero consistent/Ward/full289 phase with complete spatial momenta, symplectic form, projector inverse and energy dynamics', flush=True)
    negative, n = m.fiber(-1)
    for plus, minus in zip(p, n): equal(minus, plus.conjugate())
    equal(-mul(n[0].T, m.c.J, p[0]), s.diag(m.old_matrix('nondegenerate_phase_form', 1), m.tail_omega))
    print('PASS independently evaluated opposite-momentum source action, full canonical pairing and actual conjugate phase/rate', flush=True)
    paths = [HERE/name for name in ('source_spatial_active_phase_splice.py', 'source_spatial_phase_tangent.py',
        'source_spatial_phase_tangent.json', 'independent_source_spatial_phase_tangent.json', 'source_spatial_stabilizer_orbit.py', 'source_spatial_stabilizer_orbit.json',
        'independent_source_spatial_stabilizer_orbit.json', 'retained_matter_action.json',
        'independent_retained_matter_action.json', 'retained_hamiltonian_reduction.json',
        'independent_retained_hamiltonian_reduction.json', 'retained_hamiltonian_reduction.py', 'source_physical_phase_splice.json',
        'independent_source_physical_phase_splice.json', 'source_full_linear_split.py', 'source_full_linear_split.json')]
    paths += [BASE/'active-gauge/receipt.json']
    result = {'root': ROOT_ID, 'source_sha256': m.split.vertices['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'scope': 'ACTUAL_NONZERO_PLUS_MINUS_MOMENTUM_SOURCE_COMMON_PHASE_AND_ORIGINAL_ACTIVE_TAIL_INTERTWINING',
        'fibers': [positive, negative], 'minus_k_is_conjugate_checked_for_all_maps_and_energy': True,
        'spatial_tangent_consumption': 'Frozen source E/C/F and broken momentum coefficients with exact source bindings; T(k) is evaluated from I-EF+J F(-k)^T C after substitution, without re-expanding the paid all-k producer.',
        'same_source_spatial_slice': 'Native full36 gauge orbit Gram reader fixes the whole source Ward parameter; no old homogeneous three-coordinate minor is used.',
        'real_structure': 'All original matter complex matrices are realified before spatial Fourier substitution. Pairing is transpose between -k and k, not an additional Hilbert adjoint.',
        'original_constraints': 'All289 original Jacobi rows, full12 spatial Gauss and broken scalar momentum are checked before quotient. Every original Ward jet vanishes under the canonical reader, and that reader factors through the paid quotient.',
        'fiber_dimension_meaning': 'Complex Fourier-fiber dimensions. The -k amplitude is the conjugate partner of a real original field; the two fibers are not two independent real1208-dimensional carriers.',
        'uniform_all_k_active_reduction_claimed': False,
        'nonlinear_or_quantum_spectrum_inferred_from_linear_phase': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_spatial_active_phase_splice.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS original nonzero physical phase splice', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
