#!/usr/bin/env python3
"""A real Hamiltonian for one conjugate scalar Fourier pair and its CAR current.

The nonzero pair is one source occurrence represented by real cosine/sine
coordinates.  The zero mode uses the original122 phase directly.  Matter
momenta remain unrestricted and scalar insertions retain their actual shifts;
there is no finite momentum lattice or aliasing prescription.
"""
from __future__ import annotations

import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID, decode
from spectral_splice import clean, equal, encode
from scalar_canonical_phase import ScalarCanonicalPhase, K, LAMBDA

THETA, ETA = s.symbols('theta eta', real=True)
LAPLACE_REAL = s.Symbol('source_laplace_real', real=True)


def real_parts(value):
    # Laplace transforms are analytic in lambda.  Extract real position-space
    # coefficients using a real indeterminate, then restore the formal lambda;
    # this does not impose a real-frequency restriction on the identity.
    temporary = value.subs(LAMBDA, LAPLACE_REAL)
    real = clean(temporary.applyfunc(s.re).subs(LAPLACE_REAL, LAMBDA))
    imag = clean(temporary.applyfunc(s.im).subs(LAPLACE_REAL, LAMBDA))
    equal(value, real+s.I*imag)
    return real, imag


def realify(value):
    real, imag = real_parts(value)
    return clean(s.SparseMatrix.vstack(s.SparseMatrix.hstack(real, -imag),
                                      s.SparseMatrix.hstack(imag, real)))


class ScalarJointHamiltonian:
    def __init__(self):
        self.source = ScalarCanonicalPhase()
        source = self.source
        self.R = source.R
        self.D = clean(source.T[70:, 61:])
        # (qR,pR,qI,pI) -> (qR,qI,pR,pI), the ordering used by the Lean port.
        order = list(range(61))+list(range(122,183))+list(range(61,122))+list(range(183,244))
        self.permutation = s.SparseMatrix(244, 244, {(row, column): 1 for row, column in enumerate(order)})
        self.J = s.SparseMatrix.vstack(s.SparseMatrix.hstack(s.zeros(122), s.eye(122)),
                                      s.SparseMatrix.hstack(-s.eye(122), s.zeros(122)))
        self.hessian = clean(self.permutation*realify(source.canonical_hessian)*self.permutation.T)
        self.A = clean(self.permutation*realify(source.canonical_A)*self.permutation.T)
        self.Rpair = s.diag(self.R, self.R)
        self.Dpair = s.diag(self.D, self.D)
        self.Ppair = s.diag(source.P, source.P)
        self.B = s.SparseMatrix.vstack(s.zeros(122, 140), -self.Rpair.T)
        self.Ophi = s.SparseMatrix.hstack(self.Rpair, s.zeros(140, 122))
        self.Omomentum = s.SparseMatrix.hstack(s.zeros(140, 122), self.Dpair)
        self.Lpair = realify(source.L)
        self.pair_reflection = s.diag(s.eye(61), -s.eye(61), s.eye(61), -s.eye(61))

    def local_frames(self, angle):
        """Original70 field/momentum of this one pair at theta=k dot x."""
        return [clean(s.sqrt(2)*s.SparseMatrix.hstack(s.cos(angle)*frame, -s.sin(angle)*frame))
                for frame in [self.R, self.D]]

    def phase_at(self, momentum):
        """A concrete source mode: zero is122, every nonzero conjugate pair244."""
        assert len(momentum) == 3
        values = [s.simplify(value) for value in momentum]
        assert all(not value.free_symbols and value.is_real for value in values)
        substitution = dict(zip(K, values))
        if all(value == 0 for value in values):
            return {'kind': 'real_zero_mode', 'canonical_position_dimension': 61, 'phase_dimension': 122,
                'hessian': clean(self.source.canonical_hessian.subs(substitution)),
                'generator': clean(self.source.canonical_A.subs(substitution)),
                'field_frame': self.R, 'momentum_frame': self.D}
        # The pair key has its first nonzero component positive.  Reversing
        # it changes only the sine coordinates, not the physical carrier.
        first = next(value for value in values if value != 0)
        assert first.is_positive or first.is_negative
        orientation = 1 if first.is_positive else -1
        representative = [orientation*value for value in values]
        return {'kind': 'one_nonzero_conjugate_pair', 'canonical_position_dimension': 122,
                'phase_dimension': 244, 'representative': representative,
                'requested_orientation': orientation,
                'hessian': clean(self.hessian.subs(substitution)),
                'generator': clean(self.A.subs(substitution)),
                'field_frame': self.Rpair, 'momentum_frame': self.Dpair}


def main():
    started = time.monotonic()
    joint = ScalarJointHamiltonian()
    source = joint.source
    N, P, R, D = source.N, source.P, joint.R, joint.D
    phase_path = HERE/'scalar_canonical_phase.json'
    real_path = HERE/'real_scalar_car_source.json'
    phase_record = json.loads(phase_path.read_text())
    real_record = json.loads(real_path.read_text())
    for record in [phase_record, real_record]:
        assert record['root'] == ROOT_ID and record['source_sha256'] == source.source.vertices['source_sha256']
        for name, expected in record['input_sha256'].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == expected, name
    minus = dict(zip(K, [-value for value in K]))
    h = source.canonical_hessian
    equal(h.subs(minus, simultaneous=True).T, h)
    equal(h.subs(minus, simultaneous=True), h.conjugate())
    equal(h.H, h)
    equal(joint.permutation*joint.permutation.T, s.eye(244))
    equal(joint.J, joint.permutation*s.diag(source.Jcanonical, source.Jcanonical)*joint.permutation.T)
    equal(joint.hessian, joint.hessian.T)
    equal(joint.hessian.applyfunc(s.im), s.zeros(244))
    equal(joint.A.applyfunc(s.im), s.zeros(244))
    equal(joint.J*joint.hessian, joint.A)
    equal(joint.A*joint.J+joint.J*joint.A.T, s.zeros(244))
    equal(joint.hessian.subs(minus, simultaneous=True), joint.pair_reflection*joint.hessian*joint.pair_reflection)
    equal(joint.A.subs(minus, simultaneous=True), joint.pair_reflection*joint.A*joint.pair_reflection)
    equal(joint.pair_reflection*joint.J*joint.pair_reflection, joint.J)

    # x_plus=(xR+i*xI)/sqrt2.  The quadratic energy of {k,-k}
    # therefore has precisely the Hessian above, without a second copy of
    # the same physical pair or an unpaired nonsymmetric Fourier Hessian.
    branch = clean(s.SparseMatrix.vstack(s.SparseMatrix.hstack(s.eye(122), s.I*s.eye(122)),
                                        s.SparseMatrix.hstack(s.eye(122), -s.I*s.eye(122)))/s.sqrt(2))
    equal(branch*realify(h)*branch.H, s.diag(h, h.conjugate()))
    plus_read = clean(s.SparseMatrix.hstack(s.eye(122), s.I*s.eye(122))*joint.permutation.T/s.sqrt(2))
    minus_read = plus_read.conjugate()
    equal(plus_read*joint.A, source.canonical_A*plus_read)
    equal(minus_read*joint.A, source.canonical_A.subs(minus, simultaneous=True)*minus_read)
    energy_pair = clean(minus_read.T*h*plus_read+plus_read.T*h.subs(minus, simultaneous=True)*minus_read)
    equal(energy_pair, joint.hessian)
    print('PASS true real symmetric244 Hamiltonian Hessian for one conjugate pair, exact normalization and q/p canonical ordering', flush=True)

    equal(R*D.T, P); equal(D*R.T, P)
    equal(joint.Rpair*joint.Dpair.T, joint.Ppair)
    equal(joint.Ophi*joint.J*joint.Omomentum.T, joint.Ppair)
    equal(joint.Ophi*joint.J*joint.Ophi.T, s.zeros(140))
    equal(joint.Omomentum*joint.J*joint.Omomentum.T, s.zeros(140))
    equal(joint.Ophi*joint.A, -N*joint.Omomentum)
    equal(joint.Omomentum*joint.A, N*joint.Lpair*joint.Ophi)
    equal(joint.Omomentum*joint.B, -joint.Ppair)
    equal(joint.Ophi*joint.J*joint.Ophi.T, s.zeros(140))
    equal(joint.J*joint.Ophi.T, joint.B)
    equal(joint.Ophi*joint.A*joint.B, N*joint.Ppair)
    equal(joint.B, joint.permutation*s.diag(source.canonical_B, source.canonical_B))
    equal(joint.Ophi, s.diag(source.canonical_O, source.canonical_O)*joint.permutation.T)
    numerator, denominator = source.green_numerator, source.green_denominator
    lifted = clean(source.S*s.SparseMatrix.vstack(numerator, -LAMBDA*numerator/N))
    pair_lifted = clean(joint.permutation*realify(lifted))
    pair_numerator = realify(numerator)
    _, denominator_imag = real_parts(s.Matrix([[denominator]]))
    equal(denominator_imag, s.zeros(1))
    equal((LAMBDA*s.eye(244)-joint.A)*pair_lifted, denominator*joint.B)
    equal(joint.Ophi*pair_lifted, pair_numerator)
    equal((LAMBDA**2*s.eye(140)/N+N*joint.Lpair)*pair_numerator, denominator*joint.Ppair)
    equal(joint.Ophi*joint.A**2+N**2*joint.Lpair*joint.Ophi, s.zeros(140, 244))
    print('PASS original140 real-pair field/momentum, projected CCR, full70-per-branch Green and exact source sign', flush=True)

    Rs, Ds = joint.local_frames(THETA)
    Rt, Dt = joint.local_frames(ETA)
    local_pairing = clean((Rs*Dt.T).applyfunc(s.trigsimp))
    equal(local_pairing, 2*s.cos(THETA-ETA)*P)
    local_B = s.SparseMatrix.vstack(s.zeros(122, 70), -Rs.T)
    equal(joint.J*s.SparseMatrix.vstack(Rs.T, s.zeros(122, 70)), local_B)
    # Keep the actual scalar Fourier transfer on unrestricted matter k.
    # Each canonical position has two opposite Fourier coefficients; their
    # real-space sum is the exact cosine/sine coefficient of the same field.
    fourier_positive = clean(s.SparseMatrix.hstack(R, s.I*R)/s.sqrt(2))
    fourier_negative = fourier_positive.conjugate()
    equal(fourier_positive*s.exp(s.I*THETA)+fourier_negative*s.exp(-s.I*THETA),
          (Rs.rewrite(s.exp) if hasattr(Rs, 'rewrite') else Rs).applyfunc(lambda value: value.rewrite(s.exp)))
    U = decode(real_record['complex_branch_unitary'])
    E = source.E
    current_rows = []
    for j, (V, W, saved) in enumerate(zip(source.projected_V, source.projected_W,
                                         real_record['all61_canonical_sources'])):
        M = decode(saved['real_current_matrix'])
        equal(M, realify(clean(-s.I*W)))
        equal(s.I*M, decode(saved['formal_unit_CAR_matrix']))
        equal(U*(s.I*M)*U.H, s.diag(W, -W.conjugate()))
        equal(E*(-s.I*W)+V, s.zeros(252))
        for sector, positive, negative in [('cosine', 1/s.sqrt(2), 1/s.sqrt(2)),
                                             ('sine', s.I/s.sqrt(2), -s.I/s.sqrt(2))]:
            value = s.sqrt(2)*s.cos(THETA) if sector == 'cosine' else -s.sqrt(2)*s.sin(THETA)
            assert s.expand(positive*s.exp(s.I*THETA)+negative*s.exp(-s.I*THETA)-value.rewrite(s.exp)) == 0
            equal(E*(-s.I*positive*W)+positive*V, s.zeros(252))
            equal(E*(-s.I*negative*W)+negative*V, s.zeros(252))
            equal(U*(s.I*positive*M)*U.H, s.diag(positive*W, -positive*W.conjugate()))
        current_rows.append({'canonical_scalar_coordinate': j,
            'original_full252_vertex': encode(W),
            'real504_current_matrix': encode(M),
            'cosine_positive_transfer_weight': 'sqrt(2)/2', 'cosine_negative_transfer_weight': 'sqrt(2)/2',
            'sine_positive_transfer_weight': 'sqrt(2)*I/2', 'sine_negative_transfer_weight': '-sqrt(2)*I/2',
            'real_density_pairing_preserved': True})
    incoming = s.Matrix(s.symbols('matter_k1:4', real=True))
    position = s.Matrix(s.symbols('x1:4', real=True))
    shift_rows = []
    for sign in [-1, 1]:
        transfer = sign*s.Matrix(K)
        outgoing = incoming+transfer
        assert s.expand((transfer+incoming-outgoing).dot(position)) == 0
        shift_rows.append({'scalar_transfer': [str(value) for value in transfer],
            'incoming_matter_momentum': list(map(str, incoming)), 'outgoing_matter_momentum': list(map(str, outgoing)),
            'Hamiltonian_pairing_phase': 'exp(i transfer*x)*exp(-i outgoing*x)*exp(i incoming*x)=1',
            'primal_equation': 'in -> in+transfer by -i*phi_transfer*W',
            'independent_dual_equation': 'out -> out-transfer by +i*p_out*phi_transfer*W',
            'same_current_derivative': 'rho(-transfer)=integral p(k+transfer)*W*psi(k) dk, with Re taken in the original real action'})
    print('PASS all61 original real CAR currents with actual +/- scalar transfer, independent dual and no finite momentum alias', flush=True)

    zero = joint.phase_at([0, 0, 0])
    assert zero['phase_dimension'] == 122 and zero['canonical_position_dimension'] == 61
    equal(zero['hessian'].T, zero['hessian'])
    equal(zero['generator'], source.Jcanonical*zero['hessian'])
    equal(zero['field_frame']*zero['momentum_frame'].T, P)
    dynamic_path = HERE/'dynamic.json'
    dynamic = json.loads(dynamic_path.read_text())
    sample = next(row for row in dynamic['samples'] if row['name'] == 'energy_transfer')
    actual_momentum = clean(decode(sample['transfer'])[1:, 0]/s.I)
    actual = joint.phase_at(actual_momentum)
    opposite = joint.phase_at(-actual_momentum)
    assert actual['phase_dimension'] == opposite['phase_dimension'] == 244
    assert actual['representative'] == opposite['representative']
    equal(opposite['hessian'], joint.pair_reflection*actual['hessian']*joint.pair_reflection)
    equal(opposite['generator'], joint.pair_reflection*actual['generator']*joint.pair_reflection)
    print('PASS actual source Fourier pair has one244 carrier; original real zero mode has122 with no duplication', flush=True)

    paths = [phase_path, real_path, HERE/'scalar_canonical_phase.py', HERE/'real_scalar_car_source.py',
             HERE/'independent_scalar_canonical_phase.json', HERE/'independent_real_scalar_car_source.json',
             BASE/'scalar-exchange/receipt.json', BASE/'matter-vertices/receipt.json', dynamic_path]
    output = {'root': ROOT_ID, 'source_sha256': source.source.vertices['source_sha256'],
        'scope': 'SOURCE_REAL_SCALAR_CONJUGATE_FOURIER_PAIR_HAMILTONIAN_AND_ORIGINAL_CAR_CONVOLUTION',
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'physical_momentum_variables': list(map(str, K)),
        'pair_coordinate_order': ['q_real61', 'q_imaginary61', 'momentum_real61', 'momentum_imaginary61'],
        'pair_coordinate_normalization': 'x_plus=(x_real+i*x_imaginary)/sqrt2; x_minus=conjugate(x_plus)',
        'pair_canonical_position_dimension': 122, 'pair_phase_dimension': 244,
        'zero_canonical_position_dimension': 61, 'zero_phase_dimension': 122,
        'pair_reordering': encode(joint.permutation), 'pair_reflection': encode(joint.pair_reflection),
        'real_symmetric_Hessian': encode(joint.hessian), 'canonical_J': encode(joint.J),
        'real_phase_generator': encode(joint.A), 'Hamiltonian_matrix_identity': 'J*real_symmetric_Hessian=real_phase_generator',
        'pair_Hamiltonian': 'H_b=1/2 state_real^T K_pair state_real equals the original quadratic energy of the single set {k,-k}',
        'scalar_R': encode(R), 'scalar_D': encode(D), 'pair_R': encode(joint.Rpair), 'pair_D': encode(joint.Dpair),
        'pair_projector': encode(joint.Ppair), 'pair_phi_output': encode(joint.Ophi),
        'pair_Pi_output': encode(joint.Omomentum), 'pair_source_injection': encode(joint.B),
        'R_D_pairing': 'R D^T=P61; Rpair Dpair^T=diag(P61,P61)',
        'local70_field_frame': encode(Rs), 'local70_momentum_frame': encode(Ds),
        'local70_source_injection': encode(local_B),
        'local_pair_CCR_kernel': 'Rspace(theta) Dspace(eta)^T=2*cos(theta-eta)*P61; one pair is not a spatial delta function',
        'positive_transfer_field_frame': encode(fourier_positive), 'negative_transfer_field_frame': encode(fourier_negative),
        'original_pair_Green_numerator': encode(pair_numerator), 'original_pair_Green_denominator': str(denominator),
        'phase_resolvent_numerator': encode(pair_lifted),
        'Green_identity': '(lambda I-Apair)*Xpair=den*Bpair; Ophi*Xpair=realified original scalar61 Green numerator',
        'source_equations': 'dot(phi_pair)=-N Pi_pair; dot(Pi_pair)=N Lpair phi_pair-Ppair rho_real,pair',
        'joint_local_Hamiltonian': 'H_b+integral[P_matter^T A_free(d/dx) q_matter + sum_a q_scalar,a P_matter^T M_a(x) q_matter] dx',
        'joint_variations': 'the same H gives scalar current -Rspace^T rho_real and matter drift sum_a q_scalar,a M_a(x), with independent real dual -transpose; M is original realify(-i W)',
        'quantum_formal_matter_ports': 'i*M_a(x) in the existing formal unit-CAR readout; the two complex branches and their 1/sqrt2 normalization are retained',
        'source_current_reparameterization': 'rho_real,pair=(sqrt2 Re(rho(k)),sqrt2 Im(rho(k))); H_int_pair=phi_real^T rho_real+phi_imaginary^T rho_imaginary',
        'original61_current_ports': current_rows, 'untruncated_momentum_shifts': shift_rows,
        'no_finite_momentum_alias_or_periodization': True,
        'zero_mode': {'phase_dimension': 122, 'canonical_position_dimension': 61,
            'Hessian': encode(zero['hessian']), 'generator': encode(zero['generator']),
            'R': encode(R), 'D': encode(D), 'normalization': 'original real zero mode; no sqrt2 Fourier-pair factor'},
        'actual_source_pair': {'momentum': encode(actual_momentum),
            'canonical_unordered_pair_representative': list(map(str, actual['representative'])),
            'same_representative_for_opposite_momentum': True,
            'phase_dimension': 244, 'Hessian': encode(actual['hessian']), 'generator': encode(actual['generator'])},
        'Lean_consumer': 'sigma=Fin122 for one nonzero pair, or Fin61 for zero; K is the displayed real symmetric q/p Hessian, R/D are the corresponding displayed source frames',
        'new_physical_modes_claimed': False,
        'scope_boundary': 'same fixed-coframe scalar61 sector and original full matter coupling; not a replacement for the other three interacting source blocks',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'scalar_joint_hamiltonian.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS actual real scalar-pair joint Hamiltonian and original matter convolution', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
