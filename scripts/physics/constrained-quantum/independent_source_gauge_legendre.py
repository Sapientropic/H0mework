#!/usr/bin/env python3
"""Original gauge audit using antisymmetric4x4 forms and raw matrix brackets.

The candidate is not imported. Its exterior-square polynomial is compared
with the original four-index metric contraction, while all live Euler jets
are rebuilt by differentiating the original conjugated4x4 Hodge action.
"""
from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path
import re
import sys
import time

import sympy as s

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(BASE))
import exact_readout as source

ROOT_ID = 'positiveSmoothUnifiedSource; repaired Dirac-dual; SpinPair.actual; visit10/tick16/materialEntry -> tick17 unchanged'
PAIRS = [(0, 1), (0, 2), (0, 3), (2, 3), (3, 1), (1, 2)]
ETA = s.diag(-1, 1, 1, 1)
SIGMA = s.Rational(1, 2)
W = s.zeros(6)
for _i in range(3):
    W[_i, _i+3] = W[_i+3, _i] = 1


def clean(A): return s.SparseMatrix(A).applyfunc(s.expand)
def equal(A, B): assert not clean(A-B).todok()
def zero(x): assert s.expand(x) == 0
def read(path): return json.loads(path.read_bytes())
def dot(A, B): return sum(x*y for x, y in zip(A, B))


def decode(record, symbols=None):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(v, locals=symbols or {})
        for i, j, v in record['entries']})


def encode(A):
    return {'shape': list(A.shape), 'entries': [[i, j, str(v)] for (i, j), v in sorted(clean(A).todok().items())]}


def bindings(record):
    count = 0
    for key in ('input_sha256', 'source_sha256'):
        for name, value in record.get(key, {}).items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == value, name
            count += 1
    return count


def form(values):
    A = s.zeros(4)
    for (i, j), value in zip(PAIRS, values):
        A[i, j], A[j, i] = value, -value
    return A


def components(A): return s.Matrix([A[i, j] for i, j in PAIRS])


def fixed_star(A):
    v = components(A)
    return form([*v[3:], *[-z for z in v[:3]]])


def hodge(e):
    inverse = e.inv()
    return clean(s.Matrix.hstack(*(components(inverse*fixed_star(e*form(s.eye(6)[:, j])*e.T)*inverse.T)
        for j in range(6))))


def hodge_field_jet(e, de, F, dF):
    inverse = e.inv()
    inverse_dot = -inverse*de*inverse
    output, derivative = [], []
    for a in range(F.cols):
        external, external_dot = form(F[:, a]), form(dF[:, a])
        internal = e*external*e.T
        internal_dot = de*external*e.T+e*external_dot*e.T+e*external*de.T
        dual = fixed_star(internal)
        output.append(components(inverse*dual*inverse.T))
        derivative.append(components(inverse_dot*dual*inverse.T+
            inverse*fixed_star(internal_dot)*inverse.T+inverse*dual*inverse_dot.T))
    return clean(s.Matrix.hstack(*output)), clean(s.Matrix.hstack(*derivative))


def matrix_coordinates(M):
    # Native basis read directly from entries, independently of any Gram inverse.
    result = []
    for block in ((0, 1, 2), (3, 4)):
        for i, j in itertools.combinations(block, 2):
            result.extend([s.re(M[i, j]), s.im(M[i, j])])
        result.extend(s.im(M[i, i]) for i in block[:-1])
    result.append(s.im(M[5, 5]))
    return s.Matrix(result)


def exterior(T, degree):
    words = list(itertools.combinations(range(7), degree))
    masks = [sum(1 << i for i in word) for word in words]
    positions = {mask: j for j, mask in enumerate(masks)}
    out = s.MutableSparseMatrix.zeros(len(words), len(words))
    for column, mask in enumerate(masks):
        for (a, b), coefficient in s.SparseMatrix(T).todok().items():
            if not mask & (1 << b): continue
            remaining = mask ^ (1 << b)
            if remaining & (1 << a): continue
            sign = (-1)**((mask & ((1 << b)-1)).bit_count()+(remaining & ((1 << a)-1)).bit_count())
            out[positions[remaining | (1 << a)], column] += sign*coefficient
    return s.SparseMatrix(out)


def realify(T):
    return clean(T.applyfunc(s.re).row_join(-T.applyfunc(s.im)).col_join(
        T.applyfunc(s.im).row_join(T.applyfunc(s.re))))


def read_gamma():
    text = (ROOT/'Lean/SaturationMonoid/PhysicsCore/DiracCliffordRepresentation.lean').read_text()
    result = []
    for name in ('Zero', 'One', 'Two', 'Three'):
        body = re.search(r'def diracGamma'+name+r'\s*:.*?:=\s*!!\[(.*?)\]', text, re.S).group(1)
        rows = []
        for row in body.split(';'):
            values = [entry.strip().replace('Complex.I', 'I') for entry in row.split(',')]
            assert all(re.fullmatch(r'[0-9I+*/()\s-]+', value) for value in values)
            rows.append([s.sympify(value, locals={'I': s.I}) for value in values])
        result.append(s.Matrix(rows))
    return result


def main():
    began = time.monotonic()
    candidate_path = HERE/'source_gauge_legendre.json'
    claim = read(candidate_path)
    assert claim['root'] == ROOT_ID
    count = bindings(claim)
    _, vacuum, degrees, hashes = source.parse_source(ROOT)
    assert hashes == claim['source_sha256']
    raw = source.generators([(0, 1, 2), (3, 4)])
    T = [s.Matrix(M)*(s.I if imaginary else 1) for _, imaginary, M in raw]
    G = s.Matrix(12, 12, lambda a, b: s.re(-s.trace(T[a][:3, :3]*T[b][:3, :3])-
        s.trace(T[a][3:5, 3:5]*T[b][3:5, 3:5])-T[a][5, 5]*T[b][5, 5]))
    equal(G, decode(claim['native_Lie_algebra']['native_Lie_Gram']))
    assert G.det() == 1536 and G[11, 11] == 1 and -s.trace(T[11]*T[11]) == 2
    constants = {}
    for a, b in itertools.product(range(12), repeat=2):
        bracket = T[a]*T[b]-T[b]*T[a]
        coordinates = matrix_coordinates(bracket)
        equal(sum((value*matrix for value, matrix in zip(coordinates, T)), s.zeros(7)), bracket)
        for c, value in enumerate(coordinates):
            if value: constants[a, b, c] = value
    assert [[a, b, c, str(v)] for (a, b, c), v in sorted(constants.items())] == claim['native_Lie_algebra']['all_original_brackets']
    ad = [s.Matrix(12, 12, lambda c, b: constants.get((a, b, c), 0)) for a in range(12)]
    for a, b in itertools.product(range(12), repeat=2):
        equal(ad[a]*ad[b]-ad[b]*ad[a], sum((constants.get((a, b, c), 0)*ad[c] for c in range(12)), s.zeros(12)))
    for matrix in ad: equal(matrix.T*G+G*matrix, s.zeros(12))

    def bracket(A, B):
        return matrix_coordinates(sum((a*t for a, t in zip(A, T)), s.zeros(7))*
            sum((b*t for b, t in zip(B, T)), s.zeros(7))-
            sum((b*t for b, t in zip(B, T)), s.zeros(7))*sum((a*t for a, t in zip(A, T)), s.zeros(7)))

    e = s.Matrix(4, 4, s.symbols('e0:16', real=True))
    det = s.expand(e.det())
    g = e.T*ETA*e
    # Four-index contraction, not the candidate's exterior-square Gram product.
    numerator = s.Matrix(6, 6, lambda I, J: -(g[PAIRS[I][0], PAIRS[J][0]]*g[PAIRS[I][1], PAIRS[J][1]]-
        g[PAIRS[I][0], PAIRS[J][1]]*g[PAIRS[I][1], PAIRS[J][0]])/SIGMA)
    numerator = clean(numerator)
    equal(numerator, decode(claim['source_geometry']['kinetic_kernel_numerator'], {str(x): x for x in e}))
    star_numerator = -SIGMA*W*numerator
    for j in range(6):
        equal(e*form(star_numerator[:, j])*e.T, det*fixed_star(e*form(s.eye(6)[:, j])*e.T))
    equal(star_numerator*star_numerator, -det**2*s.eye(6))
    print('PASS generic16 original4x4 Hodge identity and all144 raw matrix brackets with native Gram', flush=True)

    frames = claim['original_auxiliary_and_Legendre']['exact_frames']
    frame_data = []
    WG = s.kronecker_product(W, G)
    for saved in frames:
        e = decode(saved['coframe']); star = hodge(e); Q = clean(-W*star/SIGMA)
        equal(Q, Q.T); equal(star*star, -s.eye(6))
        for name, block in [('electric', Q[:3, :3]), ('mixed', Q[:3, 3:]), ('magnetic', Q[3:, 3:])]:
            equal(block, decode(saved[name]))
        g = e.T*ETA*e
        zero(Q[:3, :3].det()-g[0, 0]**2/(SIGMA**3*e.det()))
        Bmap = s.kronecker_product(-star/SIGMA, s.eye(12))
        WstarG = s.kronecker_product(W*star, G)
        equal(WG-SIGMA*WstarG*Bmap, s.zeros(72))
        equal(Bmap.T*WG+WG*Bmap-SIGMA*Bmap.T*WstarG*Bmap, s.kronecker_product(Q, G))
        frame_data.append((e, Q))
    assert frames[0]['electric_rank'] == frames[1]['electric_rank'] == frames[3]['electric_rank'] == 3
    equal(frame_data[1][1], -frame_data[0][1])
    assert s.sympify(frames[3]['g_inverse00']) == 0 and frames[4]['electric_rank'] == 1

    A = s.Matrix(4, 12, lambda i, j: s.Rational((i*11+j*3)%13-6, 17))
    dA = s.Matrix(4, 48, lambda i, j: s.Rational((i*7+j*2)%11-5, 19))
    ddA = [s.Matrix(4, 48, lambda i, j: s.Rational(((mu+i)*5+j)%7-3, 23)) for mu in range(4)]
    de = s.Matrix(4, 16, lambda i, j: s.Rational((i*3+j)%9-4, 29))

    def curvature(connection, derivative):
        return clean(s.Matrix.vstack(*(derivative[mu, 12*nu:12*(nu+1)]-
            derivative[nu, 12*mu:12*(mu+1)]+bracket(connection[mu, :], connection[nu, :]).T for mu, nu in PAIRS)))

    velocity = s.Matrix(3, 12, s.symbols('v0:36', real=True))
    velocities = dA.copy(); velocities[0, 12:] = velocity.reshape(1, 36)
    Fv = curvature(A, velocities)
    vel0 = dict.fromkeys(velocity, 0)
    for e, Q in (frame_data[0], frame_data[1], frame_data[2], frame_data[3], frame_data[4]):
        density = dot(Fv, Q*Fv*G)/2
        pi = s.Matrix([s.diff(density, value) for value in velocity])
        Hessian = s.kronecker_product(Q[:3, :3], G)
        equal(pi.jacobian(list(velocity)), Hessian)
        load = pi.xreplace(vel0)
        if Q[:3, :3].det() != 0:
            recovered = Hessian.inv()*(pi-load)
            equal(recovered, velocity.reshape(36, 1))
            electric_inverse = Q[:3, :3].inv()
        else:
            null = s.Matrix.hstack(*Hessian.nullspace())
            assert null.cols == 24 and Hessian.rank() == 12
            equal(null.T*(pi-load), s.zeros(24, 1))
            K = Q[:3, :3]
            pinv = K/s.trace(K)**2
            equal(K*pinv*K, K)
            recovered = s.kronecker_product(pinv, G.inv())*(pi-load)
            equal(Hessian*(recovered-velocity.reshape(36, 1)), s.zeros(36, 1))
            electric_inverse = pinv
        H = dot(pi, recovered)-density.xreplace(dict(zip(velocity, recovered)))
        zero(H-dot(pi, velocity)+density)
        Pi = pi.reshape(3, 12)
        magnetic = Fv[3:, :]
        DA0 = -Fv[:3, :].xreplace(vel0)
        shifted = Pi*G.inv()-Q[:3, 3:]*magnetic
        displayed_H = (dot(shifted, electric_inverse*shifted*G)/2-
            dot(magnetic, Q[3:, 3:]*magnetic*G)/2+dot(Pi, DA0))
        zero(displayed_H-dot(pi, velocity)+density)
    print('PASS complete72 BF coefficient elimination and full36 Legendre on both orientations, shifted and characteristic slices', flush=True)

    def ordered(values, mu, nu):
        if mu == nu: return s.zeros(12, 1)
        if (mu, nu) in PAIRS: return values[PAIRS.index((mu, nu)), :].T
        return -values[PAIRS.index((nu, mu)), :].T

    def euler(e, de, connection, derivative, second):
        F = curvature(connection, derivative)
        P = clean(-W*hodge(e)*F*G/SIGMA)
        dP = []
        for mu in range(4):
            dF = s.Matrix.vstack(*(second[mu][rho, 12*nu:12*(nu+1)]-
                second[mu][nu, 12*rho:12*(rho+1)]+
                bracket(derivative[mu, 12*rho:12*(rho+1)], connection[nu, :]).T+
                bracket(connection[rho, :], derivative[mu, 12*nu:12*(nu+1)]).T for rho, nu in PAIRS))
            _, star_dot = hodge_field_jet(e, de[mu, :].reshape(4, 4), F, dF)
            dP.append(clean(-W*star_dot*G/SIGMA))
        EL = s.zeros(4, 12)
        for nu in range(4):
            for mu in range(4):
                EL[nu, :] -= ordered(dP[mu], mu, nu).T
                sourceP = ordered(P, mu, nu)
                for (b, a, c), value in constants.items():
                    EL[nu, a] += connection[mu, b]*value*sourceP[c]
        return F, P, dP, clean(EL)

    active_path = BASE/'active-gauge/receipt.json'; active = read(active_path)
    occupied_path = BASE/'occupied-response/receipt.json'; occupied = read(occupied_path)
    vertices_path = BASE/'matter-vertices/receipt.json'; vertices = read(vertices_path)
    count += sum(bindings(value) for value in (active, occupied, vertices))
    background = active['actual_background']
    e0 = s.Matrix(background['coframe']).applyfunc(s.sympify)
    A0 = s.Matrix(background['gauge_connection']).applyfunc(s.sympify)
    psi = decode(occupied['occupied_frame'])*s.Matrix(background['primal_H']).applyfunc(s.sympify)
    chi = s.sympify(background['dual_multiple'])*psi.T
    rho63 = [clean(s.diag(*(exterior(matrix, degree) for degree in degrees))) for matrix in T]
    rho70 = [realify(exterior(matrix, 4)) for matrix in T]
    gamma = read_gamma()
    primitive = {(row['group'], tuple(row['coordinate'])): decode(row['operator']) for row in vertices['primitive_vertices']}

    def matter(e, verify=False):
        left = [s.Abs(e.det())*sum((e.inv()[mu, a]*s.I*gamma[a] for a in range(4)), s.zeros(4)) for mu in range(4)]
        current = s.zeros(4, 12)
        for mu, a in itertools.product(range(4), range(12)):
            V = s.kronecker_product(left[mu], rho63[a])
            if verify: equal(V, primitive['gauge_A', (mu, a)])
            current[mu, a] = s.re((chi*V*psi)[0]).expand()
        return clean(current)

    def scalar(e, phi, dphi, connection):
        h = s.Abs(e.det())*(e.T*ETA*e).inv()
        cov = [dphi[mu]+sum((connection[mu, a]*rho70[a]*phi for a in range(12)), s.zeros(70, 1)) for mu in range(4)]
        return clean(s.Matrix(4, 12, lambda mu, a: sum(h[mu, nu]*dot(cov[nu], rho70[a]*phi) for nu in range(4))))

    scalar0 = s.Matrix([vacuum.get(word, 0) for word in itertools.combinations(range(7), 4)]+[0]*35)
    jS0 = scalar(e0, scalar0, [s.zeros(70, 1)]*4, A0)
    jM0 = matter(e0, verify=True)
    F0, P0, dP0, EL0 = euler(e0, s.zeros(4, 16), A0, s.zeros(4, 48), [s.zeros(4, 48)]*4)
    saved = claim['original_Euler_currents_Gauss_boundary']
    equal(jS0, decode(saved['actual_source_scalar_current']))
    equal(jM0, decode(saved['actual_source_matter_current']))
    equal(F0, decode(saved['actual_source_curvature']))
    equal(-hodge(e0)*F0/SIGMA, decode(saved['actual_source_auxiliary']))
    equal(EL0+jS0+jM0, s.zeros(4, 12))
    live_e = frame_data[2][0]
    phi = s.Matrix([s.Rational(i+1, 71) for i in range(70)])
    dphi = [s.Matrix([s.Rational((i+1)*(mu+1), 73) for i in range(70)]) for mu in range(4)]
    F, P, dP, EL = euler(live_e, de, A, dA, ddA)
    total = clean(EL+scalar(live_e, phi, dphi, A)+matter(live_e))
    equal(total, decode(saved['full_test_Euler']))
    equal(total[0, :].T, decode(saved['full_test_Gauss']))
    equal(P[:3, :]*A[0, :].T, decode(saved['test_boundary_flux']))
    _, _, _, wrong = euler(live_e, s.zeros(4, 16), A, dA, ddA)
    assert clean(wrong-EL).todok()

    # All independent connection and first-jet variations, without an
    # adjoint-coordinate formula imported from the candidate.
    delta = s.Matrix(4, 12, s.symbols('delta0:48', real=True))
    ddelta = s.Matrix(4, 48, s.symbols('ddelta0:192', real=True))
    variation = s.Matrix.vstack(*(ddelta[mu, 12*nu:12*(nu+1)]-
        ddelta[nu, 12*mu:12*(mu+1)]+bracket(delta[mu, :], A[nu, :]).T+
        bracket(A[mu, :], delta[nu, :]).T for mu, nu in PAIRS))
    theta_div = sum(dot(ordered(dP[mu], mu, nu), delta[nu, :])+dot(ordered(P, mu, nu),
        ddelta[mu, 12*nu:12*(nu+1)]) for mu in range(4) for nu in range(4))
    zero(dot(P, variation)-dot(EL, delta)-theta_div)
    temporal_term = sum(dot(P[i, :], dA[i+1, :12]+bracket(A[i+1, :], A[0, :]).T) for i in range(3))
    flux_div = sum(dot(dP[i+1][i, :], A[0, :])+dot(P[i, :], dA[i+1, :12]) for i in range(3))
    zero(temporal_term+dot(A[0, :], EL[0, :])-flux_div)
    print('PASS original source48 Euler, full252 vertices/full70 currents and all48+192 independent Euler/flux variations including live dHodge', flush=True)

    paths = [candidate_path, HERE/'source_gauge_legendre.py', Path(__file__), BASE/'exact_readout.py',
        active_path, occupied_path, vertices_path]
    paths += [ROOT/'Lean/SaturationMonoid/PhysicsCore'/name for name in [
        'DiracCliffordRepresentation.lean', 'RawLorentzianMetricHodgeRecovery.lean',
        'StageNineTopologicalFourFormPairing.lean', 'ProofFreeRicherAnholonomicSource.lean']]
    result = {'verdict': 'CERTIFIED_ORIGINAL_NATIVE12_GAUGE_BF_LEGENDRE_EULER_AND_GAUSS',
        'root': ROOT_ID, 'source_sha256': hashes,
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'candidate_imported': False, 'source_binding_checks': count,
        'independent_algorithm': '4x4 antisymmetric-form conjugation and its exact directional derivative; four-index metric contraction; raw matrix-entry bracket extraction; occupation-bit exterior representations; full36 velocity Hessian inversion with independent null Moore inverse; raw240-component connection variation and boundary divergence',
        'generic16_literal_Hodge_and_72_BF_coefficients': True,
        'native_Lie_Gram_determinant': 1536, 'original_bracket_nonzero_coefficients': len(constants),
        'original_matrix_commutators_and_Jacobi_maps': 144,
        'native_hypercharge_Gram': 1, 'mother_trace_negative_control': 2,
        'full_velocity_count': 36, 'nonnull_or_characteristic_coframes_checked': len(frames),
        'null_electric_rank': 1, 'null36_velocity_Hessian_rank': 12, 'null_additional_constraints': 24,
        'null_domain': 'Hamiltonian equality holds on the24 primary constraints; public numerical formulas outside that surface are not a solved Legendre inverse',
        'orientation': 'negative determinant reverses the original gauge quadratic density; abs(det e) is retained separately in the scalar and Dirac currents',
        'distinct_characteristic_controls': 'g^00=0 can retain invertible gauge electric block; g00=0 has gauge rank1 while the scalar time map can remain invertible',
        'source_background_all48_Euler_zero': True,
        'original_full252_vertices_rebuilt': 48, 'full70_scalar_current_rebuilt': True,
        'nonconstant_coframe_connection_first_and_second_jets_match': True,
        'dropping_coframe_derivative_changes_Euler_negative_control': True,
        'independent_variation_coordinates': {'connection': 48, 'first_jet': 192},
        'boundary_identity': 'sum Pi_i.D_i A0 = -A0.fieldGauss + sum partial_i(Pi_i.A0); the boundary divergence is retained',
        'original_full_connection_Euler': '-sum_mu(partial_mu P^{mu,nu}-ad(A_mu)^T P^{mu,nu})+j_scalar+j_matter',
        'first_class_constraint_propagation_or_complete_four_block_spectrum_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_gauge_legendre.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent original gauge Legendre audit', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
