#!/usr/bin/env python3
"""Independent raw-source audit of the residual Gauss symplectic chart.

No stabilizer-reduction or quantum-stabilizer producer is imported. Exterior
representations, original native brackets and the independent complex matter
pair regenerate all moment maps. The graph's actual momentum solution and
pullback are checked before its phase dimension is read.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from independent_source_joint_temporal_rates import (
    RawSource, HERE, ROOT, ROOT_ID, bindings, clean, rational, zero, eq,
    decode, encode, dot, realify)


def combination(matrices, coefficients):
    return clean(sum((c*M for c, M in zip(coefficients, matrices) if c),
                     s.SparseMatrix.zeros(*matrices[0].shape)))


class RawStabilizerPhase:
    def __init__(self):
        self.raw = RawSource()
        self.S = s.Matrix.hstack(*self.raw.O.nullspace())
        self.R = self.raw.P61[:, list(self.raw.P61.rref()[1])]
        self.Rd = rational(self.R*(self.R.T*self.R).inv())
        self.rho = [combination(self.raw.rho70, self.S[:, h]) for h in range(3)]
        self.rho252 = [combination(self.raw.rho252, self.S[:, h]) for h in range(3)]
        eq(self.R.T*self.Rd, s.eye(61))
        eq(self.R.T*self.raw.Ob, s.zeros(61, 9))
        assert self.raw.S.row_join(self.S).det() != 0
        for T in self.rho:
            eq(T*self.raw.v, s.zeros(70, 1))
            eq(self.raw.Ob.T*T*self.R, s.zeros(9, 61))
            eq(T*self.R, self.R*(self.Rd.T*T*self.R))
        self.ads = [self.raw.ad(self.S[:, h]) for h in range(3)]
        self.matter = [realify(T) for T in self.rho252]
        self.generators = [clean(s.diag(s.zeros(6), self.Rd.T*T*self.R,
                                       ad, ad, ad, U))
                           for T, ad, U in zip(self.rho, self.ads, self.matter)]
        self.orbit = clean(s.Matrix.hstack(*(s.kronecker_product(s.eye(3), ad)*
                                            self.raw.A[1:, :].reshape(36, 1) for ad in self.ads)))
        self.pivots = list(self.orbit.T.rref()[1])
        assert len(self.pivots) == 3
        self.coordinates = [67+j for j in self.pivots]
        self.minor = self.orbit[self.pivots, :]
        assert self.minor.det() != 0
        self.structure = [rational((self.S.T*self.S).inv()*self.S.T*ad*self.S) for ad in self.ads]

    def source_pair(self):
        raw = self.raw
        e = s.Matrix(raw.active['actual_background']['coframe']).applyfunc(s.sympify)
        q = s.Matrix([e[j] for j in (5, 9, 10, 13, 14, 15)])
        E = s.kronecker_product(raw.principals(e)[0], s.eye(63))
        p = clean(-s.I*raw.chi0*E)
        configuration = s.Matrix.vstack(q, s.zeros(61, 1), raw.A[1:, :].reshape(36, 1),
                                       raw.psi0.applyfunc(s.re), raw.psi0.applyfunc(s.im))
        momentum = s.Matrix.vstack(s.zeros(103, 1), -p.T.applyfunc(s.im), -p.T.applyfunc(s.re))
        assert configuration.shape == momentum.shape == (607, 1)
        return configuration, momentum

    def moment(self, configuration, momentum):
        return clean(s.Matrix([dot(momentum, T*configuration) for T in self.generators]))

    def embed(self, configuration, momentum):
        """Freeze original gauge positions and solve original Gauss for Pi_A."""
        q, p = configuration.copy(), momentum.copy()
        source_q, _ = self.source_pair()
        for a in self.coordinates: q[a] = source_q[a]; p[a] = 0
        K = clean(s.Matrix.hstack(*(T*q for T in self.generators))[self.coordinates, :])
        assert K.det() != 0
        rhs = -self.moment(q, p)
        solution, parameters = K.T.gauss_jordan_solve(rhs)
        assert parameters.rows == 0
        solution = rational(solution)
        for a, value in zip(self.coordinates, solution): p[a] = value
        eq(self.moment(q, p), s.zeros(3, 1))
        return q, p, K

    def all_original_Gauss(self, q, p):
        raw = self.raw
        x, pi = q[6:67, :], p[6:67, :]
        A, PiA = q[67:103, :].reshape(3, 12), p[67:103, :].reshape(3, 12)
        psi = q[103:355, :]+s.I*q[355:607, :]
        dual = -p[355:607, :].T-s.I*p[103:355, :].T
        phi = raw.v+self.R*x
        matter = s.Matrix([s.expand(s.re((s.I*dual*T*psi)[0])) for T in raw.rho252])
        gauge = s.Matrix([sum(dot(PiA[i, :], raw.adjoint[a]*A[i, :].T) for i in range(3))
                          for a in range(12)])
        tangent = self.Rd*pi
        base = clean(gauge+matter+s.Matrix([dot(tangent, T*phi) for T in raw.rho70]))
        D = clean(raw.Ob.T*s.Matrix.hstack(*(raw.rho70[a]*phi for a in raw.broken)))
        normal, parameters = D.T.gauss_jordan_solve(-raw.S.T*base)
        assert parameters.rows == 0
        Pi = rational(tangent+raw.Ob*normal)
        full = clean(gauge+matter+s.Matrix([dot(Pi, T*phi) for T in raw.rho70]))
        return full, dict(phi=phi, Pi_phi=Pi, Pi_A=PiA, psi=psi, p=dual, D=D,
                          base_current=base, normal=normal)


def generic_graph_proof():
    K = s.MatrixSymbol('actual_orbit_minor', 3, 3)
    F = s.MatrixSymbol('actual_Gauss_brackets', 3, 3)
    Z = s.ZeroMatrix(3, 3)
    delta = s.BlockMatrix([[Z, K], [-K.T, F]])
    inverse = s.BlockMatrix([[K.T.I*F*K.I, -K.T.I], [K.I, Z]])
    identity = s.BlockMatrix([[s.Identity(3), Z], [Z, s.Identity(3)]])
    assert s.block_collapse(delta*inverse) == identity
    assert s.block_collapse(inverse*delta) == identity
    # After ordering the fixed pairs last, Q=(q,c), P=(p,Pi(q,p)).
    # The graph's arbitrary derivatives cannot alter the retained symplectic
    # form because all three fixed-coordinate differentials vanish.
    n = s.Integer(604)
    I, ZZ = s.Identity(n), s.ZeroMatrix(n, n)
    Z3n, Zn3 = s.ZeroMatrix(3, n), s.ZeroMatrix(n, 3)
    dq, dp = s.MatrixSymbol('solved_momentum_dq', 3, n), s.MatrixSymbol('solved_momentum_dp', 3, n)
    E = s.BlockMatrix([[I, ZZ], [Z3n, Z3n], [ZZ, I], [dq, dp]])
    omega = s.BlockMatrix([[ZZ, Zn3, I, Zn3], [Z3n, Z, Z3n, s.Identity(3)],
                          [-I, Zn3, ZZ, Zn3], [Z3n, -s.Identity(3), Z3n, Z]])
    expected = s.BlockMatrix([[ZZ, I], [-I, ZZ]])
    assert s.block_collapse(E.T*omega*E) == expected
    fg = s.MatrixSymbol('retained_f_Gauss_bracket', 1, 3)
    gg = s.MatrixSymbol('Gauss_retained_g_bracket', 3, 1)
    correction = s.BlockMatrix([[s.ZeroMatrix(1, 3), fg]])*inverse*s.BlockMatrix([[s.ZeroMatrix(3, 1)], [gg]])
    assert s.block_collapse(correction) == s.ZeroMatrix(1, 1)
    return {'both_constraint_Poisson_inverse_identities': True,
            'all607_pairs_graph_pullback_yields604_pairs': True,
            'arbitrary_actual_Gauss_bracket_retained': True,
            'all_retained_Dirac_brackets_original_canonical': True,
            'one_form': 'sum retained p dq + sum solved Pi_fixed d(A_fixed) = sum retained p dq, since the source gauge coordinates are fixed constants'}


def verify_raw_moment_maps(model):
    for h, T in enumerate(model.generators):
        assert T.shape == (607, 607)
        for k, U in enumerate(model.generators):
            eq(T*U-U*T, combination(model.generators, model.structure[h][:, k]))
    # All independent real matter coefficients, rather than a single state.
    u = s.Matrix(s.symbols('real_psi0:252', real=True))
    v = s.Matrix(s.symbols('imag_psi0:252', real=True))
    a = s.Matrix(s.symbols('real_p0:252', real=True))
    b = s.Matrix(s.symbols('imag_p0:252', real=True))
    psi, p = u+s.I*v, (a+s.I*b).T
    real_q, real_pi = u.col_join(v), (-b).col_join(-a)
    du = s.Matrix(s.symbols('du0:252', real=True))
    dv = s.Matrix(s.symbols('dv0:252', real=True))
    zero(s.expand(s.re((s.I*p*(du+s.I*dv))[0]))-dot(-b, du)-dot(-a, dv))
    for h in range(3):
        original = s.expand(s.re((s.I*p*model.rho252[h]*psi)[0]))
        reconstructed = s.expand(dot(real_pi, model.matter[h]*real_q))
        zero(original-reconstructed)
    return {'original_independent_matter_pair': 'q=(Re psi,Im psi), pi=(-Im p,-Re p)',
            'all504_real_matter_moment_coefficients_checked': True,
            'full607_pair_momentmap_Lie_identities_checked': True}


def native_source_momenta(model):
    raw = model.raw
    e = s.Matrix(raw.active['actual_background']['coframe']).applyfunc(s.sympify)
    H, G, inverse = raw.geometry(e)
    current = raw.current(e, raw.psi0, raw.chi0)
    Pi_e = rational(-G[:, :16].T*inverse*current)
    eq(Pi_e, s.zeros(16, 1))
    metric = raw.metric(e) if hasattr(raw, 'metric') else rational(s.Abs(e.det())*(e.T*s.diag(-1, 1, 1, 1)*e).inv())
    scalar_momentum = sum((metric[0, mu]*raw.action(raw.A[mu, :], raw.rho70)*raw.v
                           for mu in range(4)), s.zeros(70, 1))
    eq(scalar_momentum, s.zeros(70, 1))
    from independent_source_gauge_legendre import W, hodge, SIGMA
    constitutive = rational(-W*hodge(e)/SIGMA)
    gauge_momentum = clean((constitutive*raw.curvature(raw.A)*raw.Gram)[:3, :])
    eq(gauge_momentum, s.zeros(3, 12))
    return {'raw_BF_Lorentz_coframe_source_momentum_zero': True,
            'original_scalar_and_native_Hodge_source_momenta_zero': True}


def original_spin_pullback(model, q, p, data):
    from independent_source_lorentz_contact import GENERATORS
    free, dependent = (5, 9, 10, 13, 14, 15), (1, 2, 3, 6, 7, 11)
    e = s.Matrix(model.raw.active['actual_background']['coframe']).applyfunc(s.sympify)
    for j, v in zip(free, q[:6, :]): e[j] = v
    spatial = e.copy(); spatial[:, 0] = s.zeros(4, 1)
    Z = clean(s.Matrix.hstack(*((T*spatial).reshape(16, 1) for T in GENERATORS)))
    spin = s.Matrix([s.expand(s.re((s.I*data['p']*s.kronecker_product(T, s.eye(63))*data['psi'])[0]))
                     for T in model.raw.spin])
    Pi = s.zeros(16, 1)
    for j, v in zip(free, p[:6, :]): Pi[j] = v
    solution, params = Z.T[:, dependent].gauss_jordan_solve(-spin-Z.T*Pi)
    assert params.rows == 0
    for j, v in zip(dependent, solution): Pi[j] = v
    eq(Z.T*Pi+spin, s.zeros(6, 1))
    eq(Pi[[0, 4, 8, 12], :], s.zeros(4, 1))
    eq(Pi[list(free), :], p[:6, :])
    eq(model.R.T*data['Pi_phi'], p[6:67, :])
    return {'all10_original_coframe_primaries_zero': True,
            'original_coframe6_and_scalar61_momenta_read_back': True}


def verify_constraint_brackets(model, q, p):
    V = clean(s.Matrix.hstack(*(T*q for T in model.generators)))
    moment = model.moment(q, p)
    K = V[model.coordinates, :]
    F = clean(s.Matrix(3, 3, lambda a, b: dot(model.structure[a][:, b], moment)))
    # Candidate orders G first and gauge positions second. Build the same
    # bracket directly from all607 canonical pairs before comparing inverses.
    gradients = [((T.T*p).T, V[:, h].T) for h, T in enumerate(model.generators)]
    direct = s.zeros(6)
    for a in range(3):
        for b in range(3):
            direct[a, b] = dot(gradients[a][0], gradients[b][1])-dot(gradients[a][1], gradients[b][0])
            direct[a, 3+b] = -V[model.coordinates[b], a]
            direct[3+b, a] = V[model.coordinates[b], a]
    expected = F.row_join(-K.T).col_join(K.row_join(s.zeros(3)))
    eq(direct, expected)
    inverse = rational(direct.inv(method='DM'))
    eq(direct*inverse, s.eye(6)); eq(inverse*direct, s.eye(6))
    eq(inverse[:3, :3], s.zeros(3))
    return direct, inverse


def main():
    began = time.monotonic()
    candidate_path = HERE/'source_stabilizer_phase_reduction.json'
    candidate = json.loads(candidate_path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    model = RawStabilizerPhase(); assert model.raw.hashes == candidate['source_sha256']
    eq(model.S, decode(candidate['stabilizer']))
    assert model.pivots == candidate['slice']['gauge_coordinate_pivots']
    assert model.coordinates == candidate['slice']['whole_coordinate_pivots']
    eq(model.minor, decode(candidate['slice']['source_orbit_minor']))
    zero(model.minor.det()-s.sympify(candidate['slice']['source_minor_determinant']))
    q0, p0 = model.source_pair()
    eq(q0[model.coordinates, :], decode(candidate['slice']['fixed_values']))
    eq(model.moment(q0, p0), s.zeros(3, 1))
    full0, data0 = model.all_original_Gauss(q0, p0)
    eq(full0, s.zeros(12, 1))
    eq(data0['p'], decode(candidate['coordinates']['source_independent_p']))
    moments = verify_raw_moment_maps(model)
    source_momenta = native_source_momenta(model)
    source_matrix, source_inverse = verify_constraint_brackets(model, q0, p0)
    eq(source_matrix, decode(candidate['source_constraint_matrix']))
    eq(source_inverse, decode(candidate['source_constraint_inverse']))
    print('PASS independently regenerated original607-pair moment maps, source Gauss and source orbit minor', flush=True)
    # Reconstruct all607 canonical momenta solely from the retained604 and
    # solve the three raw moment equations by elimination, not the producer.
    q = decode(candidate['actual_full_configuration'])
    free = [j for j in range(607) if j not in model.coordinates]
    pf = decode(candidate['actual_free_momenta']); assert pf.shape == (604, 1)
    p = s.zeros(607, 1)
    for j, v in zip(free, pf): p[j] = v
    qnew, pnew, K = model.embed(q, p)
    eq(qnew, q); eq(pnew[free, :], pf)
    eq(pnew[model.coordinates, :], decode(candidate['actual_generated_dependent_momenta']))
    assert pnew[model.coordinates, :].todok()
    full, data = model.all_original_Gauss(qnew, pnew)
    eq(full, s.zeros(12, 1))
    spin = original_spin_pullback(model, qnew, pnew, data)
    actual_matrix, actual_inverse = verify_constraint_brackets(model, qnew, pnew)
    off = pnew.copy()
    for j, v in zip(model.coordinates, (s.Rational(1, 13), s.Rational(-2, 17), s.Rational(3, 19))): off[j] += v
    off_matrix, _ = verify_constraint_brackets(model, qnew, off)
    assert off_matrix[:3, :3].todok()
    eq(model.moment(qnew, off), decode(candidate['actual_off_level_Gauss_control']))
    print('PASS raw full12 Gauss and10 Spin/temporal-primary readback, actual momentum solve and off-level Poisson inverse', flush=True)
    # Recover the candidate's entire symbolic gauge-slice minor from original
    # native commutators, including every unfixed coordinate.
    coords = s.Matrix(s.symbols('a0:36', real=True))
    for j in model.pivots: coords[j] = q0[67+j]
    orbit = s.Matrix.hstack(*(s.kronecker_product(s.eye(3), ad)*coords for ad in model.ads))
    minor = clean(orbit[model.pivots, :])
    eq(minor, decode(candidate['slice']['generic_slice_minor'], {str(z): z for z in coords.free_symbols}))
    zero(minor.det()-s.sympify(candidate['slice']['generic_slice_minor_determinant'], locals={str(z): z for z in coords.free_symbols}))
    generic = generic_graph_proof()
    assert candidate['phase_dimension_before'] == 2*607
    assert candidate['phase_dimension_after'] == 2*604
    assert candidate['retained126_plus_tail1082_congruence_claimed'] is False
    assert candidate['quantum_Hilbert_measure_or_gauge_physical_state_claimed'] is False
    print('PASS generic complete canonical one-form/symplectic pullback and actual604-pair Dirac chart', flush=True)
    paths = [HERE/name for name in ('independent_source_stabilizer_phase_reduction.py',
        'source_stabilizer_phase_reduction.py', 'source_stabilizer_phase_reduction.json',
        'independent_source_joint_temporal_rates.py', 'independent_source_gauge_legendre.py',
        'independent_source_lorentz_contact.py', 'independent_source_constraint_preservation.py')]
    record = {'root': ROOT_ID, 'source_sha256': model.raw.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': candidate['scope'], 'verdict': 'CERTIFIED_LOCAL_CLASSICAL_SOURCE_STABILIZER_SYMPLECTIC_CHART',
        'checked_input_bindings': count, 'raw_moment_maps': moments, 'source_momenta': source_momenta,
        'source_minor': encode(model.minor), 'source_minor_determinant': str(s.factor(model.minor.det())),
        'actual_all12_Gauss_zero': True, 'actual_nonzero_dependent_momenta': encode(pnew[model.coordinates, :]),
        'original_primary_readback': spin, 'generic_graph': generic,
        'local_orbit_review': 'The actual rank3 source derivative is the infinitesimal gauge-slice map of the source native stabilizer. Its finite-dimensional analytic local group action has an analytic inverse-function slice near this nonempty source. Only the local identity component neighborhood is claimed; no global orbit uniqueness, boundary identification, quantum measure or comparison with old linear coordinates is inferred.',
        'full1208_linear_response_congruence_or_quantum_measure_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_stabilizer_phase_reduction.json').write_text(json.dumps(record, separators=(',', ':'))+'\n')
    print('PASS independent original stabilizer symplectic reduction', record['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
