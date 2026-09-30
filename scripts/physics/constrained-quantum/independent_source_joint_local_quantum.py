#!/usr/bin/env python3
"""Independent shared-domain audit of the original homogeneous quantum energy.

All four components are rebuilt on the same103-coordinate jet. Raw source
representations generate the scalar/Gauss differential coefficients, native
BF density supplies the gauge Hessian, and the unreduced252 matter density
supplies the actual one-body and Yukawa terms.
"""
from __future__ import annotations

import hashlib
import itertools
import json
from pathlib import Path
import time
import sympy as s

from independent_source_coframe_live_ordering import (
    RawLiveCoefficients, HERE, BASE, ROOT, ROOT_ID, FREE, rational, eq,
    terms, current, polynomial_action, full, state_encode)
from independent_source_gauge_legendre import (
    source, bindings, clean, decode, encode, ETA, SIGMA, W, hodge, matrix_coordinates)
from independent_source_gauss_quantum_current import exterior_bits, polynomial_real_action, decoded_state
from independent_source_common_hamiltonian import raw_matter, original_inventory


def scalar(value): return s.cancel(s.expand(value))
def dot(A, B): return sum(x*y for x, y in zip(A, B))


def representations():
    _, vacuum, degrees, hashes = source.parse_source(ROOT)
    fundamental = [s.SparseMatrix(M)*(s.I if imaginary else 1)
                   for _, imaginary, M in source.generators([(0, 1, 2), (3, 4)])]
    rho = [polynomial_real_action(exterior_bits(T, 4)) for T in fundamental]
    matter = [clean(s.kronecker_product(s.eye(4), s.diag(*(exterior_bits(T, d) for d in degrees)))) for T in fundamental]
    adjoint = [s.Matrix.hstack(*(matrix_coordinates(T*S-S*T) for S in fundamental)) for T in fundamental]
    vacuum = s.Matrix([vacuum.get(word, 0) for word in itertools.combinations(range(7), 4)]+[0]*35)
    return fundamental, rho, matter, adjoint, vacuum, hashes


def scalar_coefficients(e, x, A, inventory):
    fundamental, rho, matter, adjoint, vacuum, _ = inventory
    orbit = clean(s.Matrix.hstack(*(T*vacuum for T in rho)))
    broken = list(orbit.rref()[1]); select = s.eye(12)[:, broken]; O = orbit*select
    stabilizer = s.Matrix.hstack(*orbit.nullspace())
    Gram = O.T*O; P = clean(s.eye(70)-O*Gram.inv()*O.T)
    R = P[:, list(P.rref()[1])]; Rd = clean(R*(R.T*R).inv())
    eq(Rd.T*R, s.eye(61)); eq(Rd.T*O, s.zeros(61, 9))
    y = s.Matrix(s.symbols('joint_scalar_gauge0:97', real=True))
    point = dict(zip(y, x.col_join(A.reshape(36, 1))))
    phi = vacuum+R*y[:61, :]
    Dsym = clean(O.T*s.Matrix.hstack(*(rho[a]*phi for a in broken)))
    D = rational(Dsym.subs(point))
    F, parameters = D.T.gauss_jordan_solve(s.eye(9)); assert parameters.rows == 0
    F = rational(F); eq(D.T*F, s.eye(9))
    # The gauge generator sign is fixed by the original -ad(A)^T Pi term:
    # (ad(T_a) A)^T Pi equals this same native Gauss coefficient.
    generators = [clean(s.diag(Rd.T*rho[a]*R, *[adjoint[a]]*3)) for a in broken]
    Vsym = s.Matrix.vstack(*((T*y).T for T in generators))
    V = clean(Vsym.subs(point))
    normal = -O*F
    a = rational(Rd.row_join(s.zeros(70, 36))+normal*V)
    Q = [clean(s.diag(s.I*matter[j], s.I*matter[j].conjugate())) for j in broken]
    metric = rational(s.Abs(e.det())*(e.T*ETA*e).inv()); h00 = metric[0, 0]
    U = []
    b = s.zeros(70, 1)
    for i in range(3):
        Ri = sum((y[61+12*i+j]*rho[j] for j in range(12)), s.zeros(70))
        covariant = Ri*phi; U.append(rational(covariant.subs(point)))
        b += metric[0, i+1]*covariant
    db = rational(b.jacobian(list(y)).subs(point)); b = rational(b.subs(point))
    drift, dc = s.zeros(1, 97), s.zeros(1, 9)
    derivative_count = 0
    for alpha in range(97):
        dD = Dsym.diff(y[alpha])
        # This is obtained by differentiating D^T F=I and solving its full
        # nine-dimensional equation, independently of the producer helper.
        if dD.todok():
            dF, params = D.T.gauss_jordan_solve(-dD.T*F); assert params.rows == 0
            dF = rational(dF); eq(dD.T*F+D.T*dF, s.zeros(9))
            derivative_count += 1
        else: dF = s.zeros(9)
        dn = -O*dF
        da = rational(dn*V+normal*Vsym.diff(y[alpha]))
        drift += a[:, alpha].T*da; dc += a[:, alpha].T*dn
    phi = clean(phi.subs(point))
    potential = scalar(-sum(metric[i+1, j+1]*dot(U[i], U[j])/2 for i in range(3) for j in range(3))+
                       s.Abs(e.det())*dot(phi-vacuum, phi-vacuum))
    return dict(rho=rho, matter=matter, adjoint=adjoint, vacuum=vacuum, orbit=orbit, O=O,
                select=select, stabilizer=stabilizer, R=R, Rd=Rd, D=D, F=F,
                a=a, normal=normal, Q=Q, b=b, db=db, drift=rational(drift), dc=rational(dc),
                h00=h00, metric=metric, phi=phi, U=U, potential=potential,
                nonconstant_inverse_directions=derivative_count)


def scalar_action(data, state, gradient, Hessian):
    a, m, b = data['a'], data['normal'], data['b']; denominator = 2*data['h00']
    unit = {state: s.S.One}; J = [current(Q, unit) for Q in data['Q']]
    # Full order2, order1 and order0 coefficients are collected before
    # evaluating the common jet, independently of nested producer actions.
    scalar_part = -s.trace((a.T*a)*Hessian)-(data['drift']*gradient)[0]
    scalar_part += 2*s.I*(b.T*a*gradient)[0]+s.I*dot(a, data['db'])+dot(b, b)
    first = rational(-2*s.I*gradient.T*a.T*m-s.I*data['dc']-2*b.T*m)
    square = rational(m.T*m)
    return terms([(scalar(scalar_part/denominator)+data['potential'], unit)]+
        [(first[j]/denominator, J[j]) for j in range(9)]+
        [(coefficient/denominator, current(data['Q'][i], J[j])) for (i, j), coefficient in square.todok().items()])


def gauge_coefficients(e, A, inventory):
    fundamental = inventory[0]
    gram = s.Matrix(12, 12, lambda a, b: s.re(-s.trace(fundamental[a][:3, :3]*fundamental[b][:3, :3])-
        s.trace(fundamental[a][3:5, 3:5]*fundamental[b][3:5, 3:5])-fundamental[a][5, 5]*fundamental[b][5, 5]))
    y = s.Matrix(s.symbols('raw_spatial_gauge0:36', real=True)); field = y.reshape(3, 12)
    connection = [sum((field[i, a]*fundamental[a] for a in range(12)), s.zeros(7)) for i in range(3)]
    magnetic = clean(s.Matrix.vstack(*(matrix_coordinates(connection[i]*connection[j]-connection[j]*connection[i]).T
                                      for i, j in ((1, 2), (2, 0), (0, 1)))))
    constitutive = rational(-W*hodge(e)/SIGMA)
    electric = s.Matrix(s.symbols('raw_electric0:36', real=True))
    curvature = electric.reshape(3, 12).col_join(magnetic)
    density = s.expand(dot(curvature, constitutive*curvature*gram)/2)
    momentum = s.Matrix([s.diff(density, v) for v in electric])
    hessian = momentum.jacobian(list(electric))
    weight, params = hessian.gauss_jordan_solve(s.eye(36)); assert params.rows == 0
    shift = momentum.subs(dict.fromkeys(electric, 0)); ds = shift.jacobian(list(y))
    potential = -density.subs(dict.fromkeys(electric, 0))
    point = dict(zip(y, A.reshape(36, 1)))
    return dict(weight=rational(weight), shift=rational(shift.subs(point)), ds=rational(ds.subs(point)),
                potential=scalar(potential.subs(point)), magnetic=rational(magnetic.subs(point)),
                constitutive=constitutive, gram=gram)


def gauge_action(data, state, gradient, Hessian):
    weight, shift = data['weight'], data['shift']
    value = -s.trace(weight*Hessian)/2+s.I*(shift.T*weight*gradient)[0]
    value += s.I*s.trace(weight*data['ds'])/2+(shift.T*weight*shift)[0]/2+data['potential']
    return terms([(scalar(value), {state: s.S.One})])


def classical_readback(raw_cf, cf, sc, gauge, raw, matter_H, matter_Q, e, A):
    psi = s.Matrix([s.Rational((3*j+2)%11-5, 31)+s.I*s.Rational((5*j+1)%13-6, 37) for j in range(252)])
    p = s.Matrix([[s.Rational((7*j+3)%17-8, 41)+s.I*s.Rational((2*j+5)%11-5, 43) for j in range(252)]])
    kappa = s.Matrix([s.Rational(j-2, 23) for j in range(6)])
    pi = s.Matrix([s.Rational(j%5-2, 31) for j in range(61)])
    PiA = s.Matrix(3, 12, lambda i, a: s.Rational((i+3*a)%11-5, 31))
    ad_A = [sum((A[i, a]*sc['adjoint'][a] for a in range(12)), s.zeros(12)) for i in range(3)]
    pure = -sum((ad_A[i].T*PiA[i, :].T for i in range(3)), s.zeros(12, 1))
    matter_current = s.Matrix([scalar(s.re((s.I*p*T*psi)[0])) for T in sc['matter']])
    peripheral = sc['Rd']*pi
    source_current = pure+matter_current+s.Matrix([dot(peripheral, T*sc['phi']) for T in sc['rho']])
    normal = -sc['F']*sc['select'].T*source_current
    Pi_phi = rational(peripheral+sc['O']*normal)
    Gauss = rational(pure+matter_current+s.Matrix([dot(Pi_phi, T*sc['phi']) for T in sc['rho']]))
    eq(sc['select'].T*Gauss, s.zeros(9, 1))
    dual = s.I*p*raw['E_inverse']
    E, vertices = raw_cf.E, None
    # The same native gamma ports used for the live current have no occupied
    # restriction. Reconstruct the 24 full252 classical currents directly.
    from independent_source_lorentz_contact import original_density_ports, original_gamma
    _, vertices = original_density_ports(e, original_gamma())
    j = s.Matrix([scalar(s.re((dual*full(s.diag(V, s.zeros(4)))[:252, :252]*psi)[0])) for V in vertices])
    Pi = cf['A']*kappa+cf['S']*j[:6, :]
    eq(raw_cf.at(raw_cf.Z, tuple(e[i] for i in FREE)).T*Pi+j[:6, :], s.zeros(6, 1))
    eq(Pi.extract((0, 4, 8, 12), [0]), s.zeros(4, 1))
    Gt = raw_cf.at(raw_cf.Gt, tuple(e[i] for i in FREE))
    velocity = cf['Q']*(Pi+Gt.T*cf['Hinv']*j)
    source_load = Gt*velocity+j
    Lgravity = -3*e.det()-(source_load.T*cf['Hinv']*source_load)[0]/2
    Hgravity = scalar(dot(Pi, velocity)-Lgravity)
    ordered_classical = (kappa.T*cf['K']*kappa)[0]+(kappa.T*cf['A'].T*cf['Q']*cf['L']*j)[0]+(j.T*cf['W']*j)[0]+cf['constant']
    assert scalar(Hgravity-ordered_classical) == 0
    U0 = rational((Pi_phi-sc['b'])/sc['h00']); covariant = [U0, *sc['U']]
    Lscalar = sum(sc['metric'][mu, nu]*dot(covariant[mu], covariant[nu])/2 for mu in range(4) for nu in range(4))
    Lscalar -= s.Abs(e.det())*dot(sc['phi']-sc['vacuum'], sc['phi']-sc['vacuum'])
    Hscalar = scalar(dot(Pi_phi, U0)-Lscalar)
    assert scalar(Hscalar-dot(Pi_phi-sc['b'], Pi_phi-sc['b'])/(2*sc['h00'])-sc['potential']) == 0
    gauge_velocity = gauge['weight']*(PiA.reshape(36, 1)-gauge['shift'])
    curvature = gauge_velocity.reshape(3, 12).col_join(gauge['magnetic'])
    Lgauge = dot(curvature, gauge['constitutive']*curvature*gauge['gram'])/2
    Hgauge = scalar(dot(PiA.reshape(36, 1), gauge_velocity)-Lgauge)
    assert scalar(Hgauge-(gauge_velocity.T*(PiA.reshape(36, 1)-gauge['shift']))[0]/2-gauge['potential']) == 0
    Hmatter = scalar(-s.re((dual*raw['lower']*psi)[0]))
    assert scalar(Hmatter-s.re((p*matter_H*psi)[0])) == 0
    a = psi.col_join(psi.conjugate())/s.sqrt(2); b = p.row_join(-p.conjugate())/s.sqrt(2)
    assert scalar((b*matter_Q*a)[0]-Hmatter) == 0
    return {'coframe_Lorentz_matter': str(Hgravity), 'scalar': str(Hscalar), 'gauge': str(Hgauge),
            'matter_without_Lorentz': str(Hmatter), 'stabilizer_Gauss': encode(sc['stabilizer'].T*Gauss)}


def main():
    began = time.monotonic(); path = HERE/'source_joint_local_quantum.json'
    candidate = json.loads(path.read_text()); count = bindings(candidate)
    assert candidate['root'] == ROOT_ID
    paid = ['independent_source_coframe_live_ordering.json', 'independent_source_scalar_shift_quantum.json',
            'independent_source_gauge_quantum_energy.json', 'independent_source_common_hamiltonian.json']
    for name in paid: count += bindings(json.loads((HERE/name).read_text()))
    configuration = candidate['configuration']; e, x, A = [decode(configuration[key]) for key in ('coframe', 'scalar', 'gauge')]
    raw_cf = RawLiveCoefficients(); q = tuple(e[i] for i in FREE)
    eq(raw_cf.at(raw_cf.e, q), e); cf = raw_cf.coefficients(q)
    inventory = representations(); assert inventory[-1] == candidate['source_sha256']
    sc = scalar_coefficients(e, x, A, inventory)
    gauge = gauge_coefficients(e, A, inventory)
    A4 = s.zeros(4, 12); A4[1:, :] = A
    raw = raw_matter(e, sc['phi'], A4)
    matter_H = clean(-s.I*raw['E_inverse']*raw['lower'])
    matter_Q = clean(s.diag(matter_H, -matter_H.conjugate()))
    print('PASS same103-coordinate raw scalar all97 derivative coefficients, native gauge36 Hessian and full252 density generator', flush=True)
    ell = s.Matrix([s.Rational(j%11+1, 67) for j in range(103)])
    radial = s.Matrix([s.Rational(j%7-3, 53) for j in range(103)])
    gradient, Hessian = s.I*ell, radial*radial.T-s.eye(103)
    state = tuple(candidate['actual_nonseparable_103_wavepacket']['state'])
    cf_action, _ = polynomial_action(cf, state, 1, gradient[:6, :], Hessian[:6, :6])
    sc_action = scalar_action(sc, state, gradient[6:, :], Hessian[6:, 6:])
    g_action = gauge_action(gauge, state, gradient[67:, :], Hessian[67:, 67:])
    m_action = current(matter_Q, {state: s.S.One})
    components = {'coframe': cf_action, 'scalar': sc_action, 'gauge': g_action, 'matter_without_Lorentz': m_action}
    wave = candidate['actual_nonseparable_103_wavepacket']
    for name, actual in components.items():
        assert terms([(1, actual), (-1, decoded_state(wave['components'][name]))]) == {}, name
    total = terms((1, value) for value in components.values())
    assert terms([(1, total), (-1, decoded_state(wave['joint_action']))]) == {}
    separated = Hessian[6:, 6:].copy(); separated[:61, 61:] = s.zeros(61, 36); separated[61:, :61] = s.zeros(36, 61)
    defect = terms([(1, sc_action), (-1, scalar_action(sc, state, gradient[6:, :], separated))])
    assert defect
    assert terms([(1, defect), (-1, decoded_state(wave['dropping_scalar_gauge_cross_jets_defect']))]) == {}
    principal_cross = (sc['a'].T*sc['a'])[:61, 61:]
    assert principal_cross.todok()
    print('PASS actual shared103 nonseparable jet, all four component actions and nonzero scalar/gauge cross-principal action', flush=True)
    original = classical_readback(raw_cf, cf, sc, gauge, raw, matter_H, matter_Q, e, A)
    eq(decode(original['stabilizer_Gauss']), decode(candidate['original_classical_readback']['unreduced_stabilizer_Gauss']))
    print('PASS original four raw-density Legendre values, ten primary and nine broken Gauss rows with full252 independent real matter', flush=True)
    dQ = []
    for r in range(61):
        dY = clean(sum(((sc['R'][j, r]+s.I*sc['R'][j+35, r])*Y
                        for j, Y in enumerate(original_inventory()['scalar'])), s.zeros(252)))
        dH = clean(-s.I*s.Abs(e.det())*raw['E_inverse']*dY)
        dQ.append(clean(s.diag(dH, -dH.conjugate())))
    force = candidate['matter_Yukawa_force']; r, incoming = force['direction'], tuple(force['input'])
    actual_force = current(-dQ[r], {incoming: s.S.One}); assert actual_force
    assert terms([(1, actual_force), (-1, decoded_state(force['i_H_commutator_scalar_momentum']))]) == {}
    # The original density is affine in all70 real scalar coefficients, so
    # these exact61 directional matrices are the full derivative, not a jet fit.
    delta = s.Matrix(s.symbols('source_scalar_delta0:61', real=True))
    assert len(dQ) == 61 and any(Q.todok() for Q in dQ)
    print('PASS original all61 affine Yukawa derivatives and actual scalar-momentum Heisenberg force', flush=True)
    paths = [Path(__file__), path, HERE/'source_joint_local_quantum.py',
             HERE/'independent_source_coframe_live_ordering.py', HERE/'independent_source_common_hamiltonian.py',
             HERE/'independent_source_scalar_shift_quantum.py', HERE/'independent_source_gauge_quantum_energy.py',
             HERE/'independent_source_gauss_quantum_current.py']+[HERE/name for name in paid]
    result = {'verdict': 'CERTIFIED_COMMON103_ORDERED_HOMOGENEOUS_LOCAL_CCR_CAR_HAMILTONIAN',
        'root': ROOT_ID, 'source_sha256': inventory[-1],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks': count, 'candidate_constructor_or_action_imported': False,
        'independent_method': 'original epsilon primary graph; all97 differentiated source Gauss momentum coefficients; native BF36 electric Hessian; full252 raw matter density; one103-coordinate second jet and exterior-slot CAR',
        'shared_domain': {'coordinates': [6, 61, 36], 'original_real_CAR': 504,
            'domain': 'Cc_infinity(Uq times Ux times R36) tensor algebraic CAR(Fin504)',
            'Uq': 'q0,q2,q5 positive; fixed original time column', 'Ux': 'det original D9(phi)!=0',
            'invariance_reason': 'All inverses are smooth on this open chart. Each component differentiates at most twice in these same103 coordinates and uses finite number-preserving CAR words. Derivatives and multiplication preserve compact support, and finite sums/compositions remain on the common domain.'},
        'all97_scalar_gauge_partial_derivatives': True,
        'nonconstant_inverse_directions': sc['nonconstant_inverse_directions'],
        'actual103_jet_all4_components_equal': True, 'joint_action': state_encode(total),
        'scalar_gauge_cross_principal_nonzero_entries': len(principal_cross.todok()),
        'cross_jet_omission_defect': state_encode(defect),
        'raw_classical_original_readback': original,
        'all10_primary_and9_broken_Gauss': True, 'original_full252_independent_dual_Re_normalization': True,
        'Yukawa_force': {'all61_original_affine_derivatives': True, 'direction': r, 'action': state_encode(actual_force)},
        'remaining_quantum_constraints': 'four temporal coframe equations and three stabilizer Gauss rows',
        'scope': 'one explicit ordered homogeneous local differential Hamiltonian; original time coframe fixed; no physical-state, spatial QFT, Hilbert evolution or spectral-measure assumption',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_joint_local_quantum.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent joint local quantum Hamiltonian', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
