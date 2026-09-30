#!/usr/bin/env python3
"""Source scalar61 canonical phase, Peierls response and genuine CAR coupling.

The phase space is the complete range of P61 on fields and momenta.  Its
canonical form and current signs come from the original scalar and Dirac-dual
densities.  No positive Hilbert adjoint or extra Yukawa term is introduced.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, SourceExchange, decode
from spectral_splice import clean, equal, encode

K = s.symbols('k1:4', real=True)
LAMBDA = s.Symbol('lambda')


class ScalarCanonicalPhase:
    """The original physical-clock generator, in ambient and canonical coordinates."""
    def __init__(self):
        self.source = SourceExchange()
        self.scalar = json.loads((BASE/'scalar-exchange/receipt.json').read_text())
        self.ports = json.loads((HERE/'full-matter-ports.json').read_text())
        self.N = self.source.N
        self.P = decode(self.scalar['peripheral_projector'])
        self.Jactive = decode(self.scalar['full_scalar_source_split_active_map']).T
        assert self.ports['root'] == ROOT_ID and self.ports['source_sha256'] == self.source.vertices['source_sha256']
        assert s.sympify(self.scalar['source_lapse']) == self.N
        u, *r = s.symbols('u r1 r2 r3')
        substitution = dict(zip([u, *r], [LAMBDA/(self.N*s.sqrt(2)), *[s.I*k/s.sqrt(2) for k in K]]))
        normalized = decode(self.scalar['normalized_full_scalar_operator'])
        self.operator = clean(self.N*normalized.subs(substitution))
        self.L = clean(self.operator.subs(LAMBDA, 0)/self.N)
        equal(self.operator, LAMBDA**2*s.eye(70)/self.N+self.N*self.L)
        self.green_numerator = clean(decode(self.scalar['peripheral_scalar_green_numerator']).subs(substitution))
        self.green_denominator = s.expand(s.sympify(self.scalar['peripheral_scalar_green_denominator']).subs(substitution))
        self.phase_projector = s.diag(self.P, self.P)
        z = s.zeros(70)
        self.J = s.SparseMatrix.vstack(s.SparseMatrix.hstack(z, self.P), s.SparseMatrix.hstack(-self.P, z))
        self.A = s.SparseMatrix.vstack(s.SparseMatrix.hstack(z, -self.N*self.P),
                                      s.SparseMatrix.hstack(clean(self.N*self.L*self.P), z))
        self.B = s.SparseMatrix.vstack(s.zeros(70), -self.P)
        self.O = s.SparseMatrix.hstack(self.P, s.zeros(70))
        self.hessian = clean(-self.N*s.diag(self.L*self.P, self.P))

        # A source projector supplies the coordinates.  The momentum uses
        # its dual basis, so the resulting 122-dimensional bracket is exactly
        # canonical even though these original columns are not orthonormal.
        self.pivots = list(self.P.rref()[1])
        self.R = self.P[:, self.pivots]
        gram = clean(self.R.T*self.R)
        inverse_gram = clean(gram.inv(method='DM'))
        self.T = clean(s.diag(self.R, self.R*inverse_gram))
        self.S = clean(s.diag(inverse_gram*self.R.T, self.R.T))
        self.Jcanonical = s.SparseMatrix.vstack(s.SparseMatrix.hstack(s.zeros(61), s.eye(61)),
                                               s.SparseMatrix.hstack(-s.eye(61), s.zeros(61)))
        self.canonical_A = clean(self.S*self.A*self.T)
        self.canonical_B = clean(self.S*self.B)
        self.canonical_O = clean(self.O*self.T)
        self.canonical_hessian = clean(self.T.T*self.hessian*self.T)
        self.E = decode(self.ports['density_temporal_principal'])
        self.Einverse = decode(self.ports['density_temporal_inverse'])
        self.V = [decode(row['operator']) for row in self.source.vertices['primitive_vertices'] if row['group'] == 'scalar']
        self.W = [clean(-s.I*self.Einverse*V) for V in self.V]
        self.projected_V = [clean(sum((self.R[a, j]*self.V[a] for a in range(70) if self.R[a, j]),
                                     s.zeros(252))) for j in range(61)]
        self.projected_W = [clean(sum((self.R[a, j]*self.W[a] for a in range(70) if self.R[a, j]),
                                     s.zeros(252))) for j in range(61)]

    def generator(self, momentum):
        """Canonical122 original time generator at the physical spatial momentum."""
        assert len(momentum) == 3
        return clean(self.canonical_A.subs(dict(zip(K, momentum))))

    def peierls_jet(self, order, momentum=K):
        """The exact ordinary t=0 derivative of the full70 commutator kernel."""
        assert isinstance(order, int) and order >= 0
        return clean(self.canonical_O*self.generator(momentum)**order*
                     self.Jcanonical*self.canonical_O.T)


def main():
    started = time.monotonic()
    phase = ScalarCanonicalPhase()
    source, N, P, L = phase.source, phase.N, phase.P, phase.L
    minus_k = dict(zip(K, [-k for k in K]))
    for name, digest in source.vertices['source_sha256'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    equal(P*P, P); equal(P.T, P)
    equal(P*L, L*P)
    equal(L.subs(minus_k, simultaneous=True).T, L)
    equal(phase.Jactive.T*P, s.zeros(9, 70))
    assert P.rank() == len(phase.pivots) == 61
    equal(phase.phase_projector*phase.phase_projector, phase.phase_projector)
    equal(phase.J*phase.J, -phase.phase_projector)
    equal(phase.A*phase.phase_projector, phase.A)
    equal(phase.phase_projector*phase.A, phase.A)
    equal(phase.A*phase.J+phase.J*phase.A.subs(minus_k, simultaneous=True).T, s.zeros(140))
    equal(phase.J*phase.hessian, phase.A)
    equal(phase.hessian.subs(minus_k, simultaneous=True).T, phase.hessian)
    equal(phase.S*phase.T, s.eye(122))
    equal(phase.T*phase.S, phase.phase_projector)
    equal(phase.T*phase.Jcanonical*phase.T.T, phase.J)
    equal(phase.S*phase.J*phase.S.T, phase.Jcanonical)
    equal(phase.T*phase.canonical_A, phase.A*phase.T)
    equal(phase.T*phase.canonical_B, phase.B)
    equal(phase.Jcanonical*phase.canonical_hessian, phase.canonical_A)
    equal(phase.canonical_A*phase.Jcanonical+
          phase.Jcanonical*phase.canonical_A.subs(minus_k, simultaneous=True).T, s.zeros(122))
    print('PASS all-momentum complete122 canonical scalar phase, Hamiltonian Hessian and CCR-preserving flow', flush=True)

    # Recover the momentum from the original actual coframe, rather than
    # assigning a sign to a desired Green function after the fact.
    coframe = s.Matrix(source.active['actual_background']['coframe']).applyfunc(s.sympify)
    metric = clean(coframe.T*s.diag(-1, 1, 1, 1)*coframe)
    volume = s.expand(coframe.det())
    temporal_density = s.expand(volume*metric.inv()[0, 0])
    assert volume == N and s.expand(temporal_density+1/N) == 0
    assert all(value == '0' for value in source.active['actual_background']['gauge_connection'][0])
    # This is the Legendre identity on the actual projected phase space:
    # Pi=-dot(phi)/N; L=-dot(phi)^2/(2N)+N*phi(-k)^T L(k)phi(k)/2.
    velocity_to_momentum = clean(temporal_density*P)
    momentum_to_velocity = clean(-N*P)
    equal(velocity_to_momentum*momentum_to_velocity, P)
    equal(momentum_to_velocity*velocity_to_momentum, P)
    equal(phase.A[:70, 70:], momentum_to_velocity)
    equal(phase.A[70:, :70], N*L*P)

    num, den = phase.green_numerator, phase.green_denominator
    equal(P*num, num); equal(num*P, num)
    equal(phase.operator*num, den*P)
    equal(num*phase.operator, den*P)
    lifted_numerator = s.SparseMatrix.vstack(num, clean(-LAMBDA*num/N))
    equal((LAMBDA*s.eye(140)-phase.A)*lifted_numerator, den*phase.B)
    equal(phase.O*lifted_numerator, num)
    equal(phase.phase_projector*lifted_numerator, lifted_numerator)
    canonical_lifted = clean(phase.S*lifted_numerator)
    equal((LAMBDA*s.eye(122)-phase.canonical_A)*canonical_lifted, den*phase.canonical_B)
    equal(phase.canonical_O*canonical_lifted, num)
    equal(phase.J*phase.O.T, phase.B)
    equal(phase.Jcanonical*phase.canonical_O.T, phase.canonical_B)
    equal(phase.O*phase.B, s.zeros(70))
    equal(phase.O*phase.A*phase.B, N*P)
    equal(phase.O*phase.A**2+N**2*L*phase.O, s.zeros(70, 140))
    jets = [phase.peierls_jet(n) for n in range(4)]
    equal(jets[0], s.zeros(70)); equal(jets[1], N*P)
    equal(jets[2], s.zeros(70)); equal(jets[3], -N**3*L*P)
    # Therefore H_scalar(D)(theta(t)*Delta(t))=P*delta(t): the initial
    # velocity generates precisely one source delta and no delta prime.
    equal(jets[0]/N, s.zeros(70)); equal(jets[1]/N, P)
    print('PASS original full scalar61 Green by cleared resolvent identity, exact Peierls kernel and retarded delta source', flush=True)

    raw_ports = [row for row in phase.ports['primitive_ports'] if row['group'] == 'scalar']
    assert len(raw_ports) == len(phase.V) == 70
    for V, W, row in zip(phase.V, phase.W, raw_ports):
        equal(W, decode(row['Hamiltonian_coefficients']['constant']))
        assert all(not decode(row['Hamiltonian_coefficients'][str(k)]).todok() for k in K)
        equal(phase.E*(-s.I*W)+V, s.zeros(252))
        # p_CAR=-i chi E gives rho_complex=p_CAR W psi=-chi V psi.
        # The original real scalar variation consumes Re(rho_complex).
        equal(-s.I*phase.E*W, -V)
    for V, W in zip(phase.projected_V, phase.projected_W):
        equal(phase.E*(-s.I*W)+V, s.zeros(252))
        assert W.todok()
    equal(phase.canonical_B, s.SparseMatrix.vstack(s.zeros(61, 70), -phase.R.T))
    equal(phase.canonical_A[:61, 61:]*phase.canonical_B[61:, :], N*phase.S[:61, :70]*P)
    # The complete projected current yields the same source sign as -G*j.
    equal(phase.O*phase.A*phase.B, N*P)
    wrong_source_sign = clean(-phase.O*phase.A*phase.B-N*P)
    assert wrong_source_sign.todok()
    print('PASS all70 original CAR Yukawa ports, all61 nonzero canonical couplings, original current and scalar-source signs', flush=True)

    paths = [BASE/'scalar-exchange/receipt.json', BASE/'matter-vertices/receipt.json',
             BASE/'active-gauge/receipt.json', HERE/'full-matter-ports.json',
             HERE/'independent_full_matter_ports.json',
             ROOT/'Lean/SaturationMonoid/PhysicsCore/StageNineGlobalIntegratedAction.lean',
             BASE/'active-gauge/compute.py', BASE/'scalar-exchange/compute.py']
    output = {'root': ROOT_ID, 'source_sha256': source.vertices['source_sha256'],
        'scope': 'SOURCE_SCALAR61_CANONICAL_CCR_PHASE_PEIERLS_AND_ORIGINAL_FULL252_CAR_COUPLING',
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'physical_momentum_variables': list(map(str, K)), 'physical_laplace_variable': str(LAMBDA),
        'source_lapse': str(N), 'fixed_actual_coframe': encode(coframe),
        'original_temporal_kinetic_coefficient': str(temporal_density),
        'scalar_momentum_rule': 'Pi=-dot(phi)/N on image(P61)',
        'scalar_L': encode(L), 'scalar_Hessian_operator': encode(phase.operator),
        'projector61': encode(P), 'phase_projector122_in_ambient140': encode(phase.phase_projector),
        'phase_dimension': 122, 'ambient_dimension': 140,
        'phase_generator': encode(phase.A), 'phase_Poisson_matrix': encode(phase.J),
        'phase_Hamiltonian_hessian': encode(phase.hessian),
        'source_injection': encode(phase.B), 'field_output': encode(phase.O),
        'canonical_coordinate_pivots': phase.pivots, 'scalar_coordinate_embedding': encode(phase.R),
        'canonical_phase_embedding': encode(phase.T), 'canonical_phase_retraction': encode(phase.S),
        'canonical_Poisson_matrix': encode(phase.Jcanonical),
        'canonical_generator': encode(phase.canonical_A),
        'canonical_Hamiltonian_hessian': encode(phase.canonical_hessian),
        'canonical_source_injection': encode(phase.canonical_B),
        'canonical_field_output': encode(phase.canonical_O),
        'all_momentum_CCR_preservation_identity': 'A(k)J+J A(-k)^T=0',
        'original_Green_numerator': encode(num), 'original_Green_denominator': str(den),
        'phase_resolvent_numerator': encode(lifted_numerator),
        'cleared_resolvent_identity': '(lambda I-A)*X=den*B; O*X=original_Green_numerator',
        'Peierls_kernel': 'Delta(t,k)=O exp(t A(k)) J O^T=O exp(t A(k)) B',
        'Peierls_initial_jets': [encode(value) for value in jets],
        'Peierls_reciprocity': 'Delta(t,k)=-Delta(-t,-k)^T, from exact canonical-flow identity',
        'retarded_kernel': 'Gret(t,k)=theta(t) Delta(t,k); Hscalar(Dt,k) Gret=P61 delta(t)',
        'CCR': '[phi_A(k),Pi_B(kprime)]=i P61_AB delta(k+kprime); [phi,phi]=[Pi,Pi]=0',
        'canonical_CCR': '[q_a(k),p_b(kprime)]=i delta_ab delta(k+kprime)',
        'free_scalar_Hamiltonian': '-N/2 integral[Pi(-k)^T Pi(k)+phi(-k)^T L(k) phi(k)]',
        'CAR_current': 'rho_complex,A=p_CAR W_A psi=-chi V_A psi; rho_real,A=Re(rho_complex,A)=-j_action,real,A; p_CAR and psi are independent canonical variables',
        'interaction_Hamiltonian': 'H_int,classical=sum_A phi_A Re(p_CAR W_A psi)=sum_a q_a Re(p_CAR Wcanonical_a psi)',
        'scalar_Hamilton_equations': 'dot(phi)=-N Pi; dot(Pi)=N L phi-P61 rho_real; Hscalar phi=P61 rho_real',
        'matter_Hamilton_equations': 'dot(psi)=-i(H0+sum_A phi_A W_A)psi; dot(p_CAR)=+i p_CAR(H0+sum_A phi_A W_A), with reversed spatial Fourier labels',
        'original_action_identity': 'Re[chi*(E dot(psi)+K psi+sum_A phi_A V_A psi)]=Re[i p_CAR dot(psi)-p_CAR(H0+sum_A phi_A W_A)psi]',
        'projected_CAR_couplings': [{'coordinate': a, 'density_vertex': encode(V), 'canonical_matter_vertex': encode(W)}
                                   for a, (V, W) in enumerate(zip(phase.projected_V, phase.projected_W))],
        'all70_original_ports_and61_canonical_couplings_checked': True,
        'source_sign_negative_control_nonzero_entries': len(wrong_source_sign.todok()),
        'phase_API': 'ScalarCanonicalPhase().generator(k); .peierls_jet(n,k); .projected_W are original61 full252 CAR bilinear coefficients',
        'quantum_consumer': 'the real canonical matter action supplies the CCR/CAR interaction readout; its realification and complex-branch normalization are consumed explicitly downstream',
        'no_positive_Hilbert_adjoint_or_extra_conjugate_term_added': True,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'scalar_canonical_phase.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS source scalar61 canonical phase and full252 CAR coupling', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
