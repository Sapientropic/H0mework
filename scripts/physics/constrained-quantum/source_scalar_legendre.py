#!/usr/bin/env python3
"""Full70 scalar Legendre transform of the original live-coframe density.

All source gauge ports and scalar coordinates are retained. The chart-zero
frame is the original identity theorem; no change of moving field variables
or extra field normalization is made. This is local Hamiltonian data, not a
replacement of the constrained gravity/gauge Hamiltonian.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import sys
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, SourceExchange
from full_matter_ports import clean, equal, encode
from scalar_canonical_phase import ScalarCanonicalPhase, K

sys.path.insert(0, str(BASE))
import exact_readout as source


def dot(u, v):
    return (u.T*v)[0]


def realify(matrix):
    a, b = matrix.applyfunc(s.re), matrix.applyfunc(s.im)
    return clean(a.row_join(-b).col_join(b.row_join(a)))


class SourceScalarLegendre:
    def __init__(self):
        self.exchange = SourceExchange()
        _, vacuum, _, self.source_hashes = source.parse_source(ROOT)
        words = list(itertools.combinations(range(7), 4))
        self.vacuum = s.Matrix([vacuum.get(word, 0) for word in words] + [0]*35)
        self.rho = [realify(s.SparseMatrix(source.exterior_action(matrix, 4))*(s.I if imaginary else 1))
                    for _, imaginary, matrix in source.generators([(0, 1, 2), (3, 4)])]
        assert len(self.rho) == 12
        for R in self.rho:
            equal(R.T, -R)

    @staticmethod
    def metric_density(coframe):
        determinant = s.factor(coframe.det())
        assert determinant != 0
        inverse = coframe.inv()
        return clean(s.Abs(determinant)*inverse*s.diag(-1, 1, 1, 1)*inverse.T), s.Abs(determinant)

    def covariant(self, phi, spatial_derivatives, connection):
        matrices = [clean(sum((connection[mu, a]*self.rho[a] for a in range(12)), s.zeros(70)))
                    for mu in range(4)]
        return matrices[0]*phi, [spatial_derivatives[i]+matrices[i+1]*phi for i in range(3)]

    def momentum(self, coframe, phi, velocity, spatial_derivatives, connection):
        h, _ = self.metric_density(coframe)
        temporal, w = self.covariant(phi, spatial_derivatives, connection)
        return clean(h[0, 0]*(velocity+temporal)+sum((h[0, i+1]*w[i] for i in range(3)), s.zeros(70, 1)))

    def hamiltonian(self, coframe, phi, momentum, spatial_derivatives, connection):
        h, volume = self.metric_density(coframe)
        assert h[0, 0] != 0, 'the chosen scalar time direction must be noncharacteristic'
        temporal, w = self.covariant(phi, spatial_derivatives, connection)
        b = sum((h[0, i+1]*w[i] for i in range(3)), s.zeros(70, 1))
        return (dot(momentum-b, momentum-b)/(2*h[0, 0])-dot(momentum, temporal)
                -sum(h[i+1, j+1]*dot(w[i], w[j])/2 for i in range(3) for j in range(3))
                +volume*dot(phi-self.vacuum, phi-self.vacuum))


def scalar_component_identity():
    # Each of the70 original real coordinates has this exact kinetic identity.
    independent = s.symbols('h00 h01 h02 h03 h11 h12 h13 h22 h23 h33', real=True)
    h = s.zeros(4)
    positions = [(i, j) for i in range(4) for j in range(i, 4)]
    for value, (i, j) in zip(independent, positions):
        h[i, j] = h[j, i] = value
    p, v, a, volume, potential = s.symbols('pi velocity A0phi volume potential', real=True)
    w = s.Matrix(s.symbols('D1phi D2phi D3phi', real=True))
    u = s.Matrix([v+a, *w])
    L = dot(u, h*u)/2-volume*potential
    momentum = s.diff(L, v)
    b = sum(h[0, i+1]*w[i] for i in range(3))
    assert s.expand(momentum-h[0, 0]*(v+a)-b) == 0
    solved_v = (p-b)/h[0, 0]-a
    H = ((p-b)**2/(2*h[0, 0])-p*a
         -dot(w, h[1:, 1:]*w)/2+volume*potential)
    assert s.cancel((p*v-L).subs(v, solved_v)-H) == 0
    assert s.cancel(s.diff(H, p)-solved_v) == 0
    assert s.cancel(momentum.subs(v, solved_v)-p) == 0
    # Fixed canonical momentum is essential: these are the coframe stress
    # chain-rule identities, valid for every densitized inverse metric.
    for parameter in [*independent, volume, a, *w]:
        assert s.cancel(s.diff(H, parameter)+s.diff(L, parameter).subs(v, solved_v)) == 0
    return {'density': str(L), 'momentum': str(momentum), 'velocity': str(solved_v),
            'Hamiltonian': str(H), 'fixed_momentum_metric_and_connection_variations_checked': 15}


def main():
    started = time.monotonic()
    native = SourceScalarLegendre()
    generic = scalar_component_identity()
    phase = ScalarCanonicalPhase()
    e0 = s.Matrix(native.exchange.active['actual_background']['coframe']).applyfunc(s.sympify)
    A0 = s.Matrix(native.exchange.active['actual_background']['gauge_connection']).applyfunc(s.sympify)
    h0, volume0 = native.metric_density(e0)
    N = native.exchange.N
    equal(h0, s.diag(-1/N, N, N, N))
    assert volume0 == N
    connection = [clean(sum((A0[mu, a]*native.rho[a] for a in range(12)), s.zeros(70))) for mu in range(4)]
    equal(connection[0], s.zeros(70))
    D = [s.I*K[i]*s.eye(70)+connection[i+1] for i in range(3)]
    # The transpose below includes spatial integration by parts. At k=0 it
    # is still the original full gauge connection, not a free scalar probe.
    stiffness = clean(N*(2*s.eye(70)+sum((M*M for M in D), s.zeros(70))))
    equal(stiffness, -N*phase.L)
    hessian = s.diag(stiffness, -N*s.eye(70))
    equal(phase.T.T*hessian*phase.T, phase.canonical_hessian)
    print('PASS full70 live scalar Legendre identity, all metric/connection derivatives and original122 background', flush=True)

    # Full variable fields test every source gauge-time port; no scalar61
    # projection or selected scalar direction enters this comparison.
    phi = s.Matrix(s.symbols('phi0:70', real=True))
    pi = s.Matrix(s.symbols('pi0:70', real=True))
    gauss = [-dot(pi, R*phi) for R in native.rho]
    velocities = []
    for a, R in enumerate(native.rho):
        force = s.Matrix([s.diff(gauss[a], value) for value in phi])
        equal(-force, -R*pi)
        velocities.append(s.Matrix([s.diff(gauss[a], value) for value in pi]))
        equal(velocities[-1], -R*phi)
    # Two opposite orientations and a genuine shift coframe retain |det e|.
    frames = [s.Matrix([[2, 1, 0, 0], [0, 2, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]]),
              s.Matrix([[-2, 1, 0, 0], [0, 2, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]])]
    frame_reports = []
    for frame in frames:
        h, volume = native.metric_density(frame)
        assert h[0, 0] < 0 and any(h[0, i] != 0 for i in range(1, 4))
        equal(frame*s.Matrix(h/volume)*frame.T, s.diag(-1, 1, 1, 1))
        frame_reports.append({'coframe': encode(frame), 'determinant': str(frame.det()),
                              'volume': str(volume), 'metric_density': encode(h)})
    # Exercise the public full70 functions with every scalar coordinate and
    # all48 gauge connection components present, after the generic proof.
    test_phi = s.Matrix([s.Rational(i+1, 71) for i in range(70)])
    test_dphi = [s.Matrix([s.Rational((i+1)*(j+1), 73) for i in range(70)]) for j in range(3)]
    test_A = s.Matrix(4, 12, s.symbols('connection0:48', real=True))
    velocity = s.Matrix(s.symbols('velocity0:70', real=True))
    h, volume = native.metric_density(frames[0])
    temporal, w = native.covariant(test_phi, test_dphi, test_A)
    actual_pi = native.momentum(frames[0], test_phi, velocity, test_dphi, test_A)
    actual_H = native.hamiltonian(frames[0], test_phi, pi, test_dphi, test_A)
    b = sum((h[0, i+1]*w[i] for i in range(3)), s.zeros(70, 1))
    v = (pi-b)/h[0, 0]-temporal
    equal(s.Matrix([s.diff(actual_H, x) for x in pi]), v)
    equal(actual_pi.subs(dict(zip(velocity, v)), simultaneous=True), pi)
    for a, R in enumerate(native.rho):
        assert s.expand(s.diff(actual_H, test_A[0, a])+dot(pi, R*test_phi)) == 0
    null_frame = s.Matrix([[1, 1, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
    assert native.metric_density(null_frame)[0][0, 0] == 0
    assert native.momentum(null_frame, test_phi, velocity, test_dphi, A0).shape == (70, 1)
    try:
        native.hamiltonian(null_frame, test_phi, pi, test_dphi, A0)
    except AssertionError as error:
        assert 'noncharacteristic' in str(error)
    else:
        raise AssertionError('a null temporal scalar Legendre inverse was accepted')
    print('PASS all12 original scalar Gauss ports, full70 coordinates and both coframe orientations', flush=True)

    core = ROOT/'Lean/SaturationMonoid/PhysicsCore'
    lean_sources = ['StageNineGlobalIntegratedAction.lean', 'StageNineDynamicBreakingVacuum.lean',
                    'StageNineScalarMomentumCoframeReadout.lean', 'StageNineDiracDualFormNativeMotherAction.lean',
                    'StageNineP286GaugeConnectionVariationDensity.lean', 'LowEnergy/FullQuantum/Source.lean']
    bindings = [BASE/'exact_readout.py'] + [core/name for name in lean_sources] + [HERE/name for name in
        ['source_scalar_legendre.py', 'dynamic.py', 'full_matter_ports.py', 'scalar_canonical_phase.py', 'scalar_canonical_phase.json',
         'independent_scalar_canonical_phase.json', 'real_scalar_car_source.json']]
    result = {'root': ROOT_ID, 'source_sha256': native.exchange.vertices['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in bindings},
        'scope': 'ORIGINAL_FULL70_SCALAR_LIVE_COFRAME_LEGENDRE_AND_CANONICAL_GAUGE_STRESS_PORTS',
        'chart': 'original chart0, where scalarFrameRelativeCoordinates_zeroChart is the identity',
        'scalar_dimension': 70, 'density_volume': 'abs(det e)',
        'source_potential': '||phi-sourceGeneratedVacuumCoordinates||^2; its full70 Hessian is2I',
        'canonical_scalar_pairing': 'the real and imaginary parts of the original complex35 exterior coordinates, with no extra normalization',
        'generic_scalar_component': generic,
        'full_field_formula': 'b=sum_i h0i Di phi; Pi=h00(dot(phi)+A0 phi)+b; H=(Pi-b)^T(Pi-b)/(2h00)-Pi^T A0 phi-sum_ij hij(Di phi)^T(Dj phi)/2+abs(det e)V',
        'noncharacteristic_domain': 'det e!=0 and h00!=0; a null temporal direction is not inverted',
        'Hamilton_velocity': 'dot(phi)=(Pi-b)/h00-A0 phi',
        'scalar_Gauss_ports': {'count': 12, 'formula': 'dH/dA0^a=-Pi^T rho_a phi',
                               'generator_variation': 'delta phi=-rho_a phi; delta Pi=-rho_a Pi'},
        'spatial_current_and_coframe_identity': 'at fixed Pi, dH/dparameter=-dL/dparameter evaluated at the source Legendre velocity, for every independent h entry, volume, A0phi and spatial covariant derivative',
        'source_rho70': [encode(R) for R in native.rho], 'source_vacuum70': encode(native.vacuum),
        'actual_background': {'coframe': encode(e0), 'lapse': str(N), 'Pi_rule': '-dot(phi)/N',
                              'full140_Hessian': encode(hessian), 'original122_projected_Hessian_identity': True},
        'orientation_and_shift_consumers': frame_reports,
        'public_full70_and48_connection_components_consumed': True,
        'null_temporal_raw_momentum_retained_but_inverse_rejected': True,
        'matter_source_consumer': 'the same scalar coordinates enter the original full252 H_matter(C,p,k); Re(p_CAR H_matter psi) supplies the independent-dual force, with original two real-action branches',
        'normalization_or_source_occurrence_changed': False,
        'complete_gravity_gauge_constraint_Hamiltonian_claimed': False,
        'full_four_block_spectrum_or_lifetime_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_scalar_legendre.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS original live full70 scalar Hamiltonian', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
