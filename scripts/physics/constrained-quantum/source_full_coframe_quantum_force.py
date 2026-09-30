#!/usr/bin/env python3
"""All16 original coframe forces at fixed ambient canonical momenta.

Every coefficient is differentiated before applying either primary section.
The exact quantum Lorentz identity retains the orbital momentum terms and
both CAR degrees. The existing current pairing transports an actual source
input122 germ; this does not relabel raw horizontal forces as current forces.
"""
from __future__ import annotations
from collections import defaultdict
from functools import cached_property
import copy
import hashlib
import json
import time
import sympy as s
from dynamic import HERE, ROOT, ROOT_ID
from source_lorentz_quantum_section import SourceLorentzQuantumSection, TIME
from source_quantum_stabilizer import SourceQuantumStabilizer
from source_coframe_live_ordering import full
from source_lorentz_contact import clean, equal, encode
from source_coframe_legendre import rational
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_joint_ccr_car_ports import simplified, same
from source_joint_current_hilbert_section import SourceJointCurrentHilbertSection
from source_joint_form_hamiltonian import read_bound
from source_quantum_temporal_symbol import N
from scalar_dyson_peierls import annihilate_basis, create_basis


def spin_normal_tensor(tensor, values):
    """Full8 tensor I63 CAR, with both occupied labels kept independently."""
    result = defaultdict(lambda: s.S.Zero)
    for word, amplitude in values.items():
        for j in word:
            after_j, sign_j = annihilate_basis(j, word)
            for ell in after_j:
                after_l, sign_l = annihilate_basis(ell, after_j)
                for k in range(8):
                    after_k, sign_k = create_basis(63*k+ell % 63, after_l)
                    if not sign_k: continue
                    for i in range(8):
                        c = tensor[8*i+j//63, 8*k+ell//63]
                        if not c: continue
                        after_i, sign_i = create_basis(63*i+j % 63, after_k)
                        if sign_i:
                            result[after_i] += amplitude*c*sign_j*sign_l*sign_k*sign_i
    return simplified(result)


class SourceFullCoframeQuantumForce:
    def __init__(self):
        self.spin = SourceLorentzQuantumSection()
        self.native = SourceQuantumStabilizer()
        self.joint = self.native.joint
        active = self.joint.common.scalar.exchange.active['actual_background']
        self.A = s.Matrix(active['gauge_connection']).applyfunc(s.sympify)
        self.phi = self.native.c.vacuum
        for i in range(1, 4):
            equal(sum((self.A[i, a]*self.joint.common.scalar.rho[a]*self.phi
                for a in range(12)), s.zeros(70, 1)), s.zeros(70, 1))
        self.base = self.coefficients(self.spin.e)

    def coefficients(self, e):
        """Original four energies in full122 differential normal form."""
        cf = copy.copy(self.spin); cf.e = e; cf._ambient_coefficients()
        one = cf.D+sum((v*cf.J[a]*cf.J[b] for (a, b), v in cf.W.todok().items()), s.zeros(8))
        J = s.Matrix.hstack(*(M.reshape(64, 1) for M in cf.J))
        tensor = rational(J*cf.W*J.T)
        gauge = self.joint.gauge.coefficients(e)
        at = dict(zip(self.joint.gauge.coordinates, self.A[1:, :].reshape(36, 1)))
        gauge = {k: rational(v.subs(at)) if isinstance(v, s.MatrixBase)
            else s.cancel(v.subs(at)) for k, v in gauge.items()}
        h, _ = self.joint.common.scalar.metric_density(e)
        matter = self.joint.common.matter_data(e, self.phi, self.A)
        H = clean(-s.I*matter['inverse_E']*matter['lower_without_Lorentz'])
        W, C = gauge['weight'], gauge['momentum_shift']
        return {'Q': cf.Q, 'T': cf.T, 'one': rational(one), 'tensor': tensor,
            'matter': clean(s.diag(H, -H.conjugate())),
            'scalar_principal': s.cancel(-1/(2*h[0, 0])),
            'gauge_principal': rational(-W/2), 'gauge_first': rational(s.I*W*C),
            'identity': s.cancel(3*e.det()+(C.T*W*C)[0]/2+
                gauge['derivative_ordering_constant']+gauge['magnetic_potential'])}

    @cached_property
    def derivatives(self):
        result = []
        for i in range(16):
            var = s.Dummy('original_e_'+str(i), positive=True) if i in (0, 5, 10, 15) else s.Dummy('original_e_'+str(i), real=True)
            e = self.spin.e.copy(); e[i] = var
            def differentiate(v):
                if isinstance(v, list): return [differentiate(x) for x in v]
                if isinstance(v, s.MatrixBase): return rational(v.diff(var).subs(var, self.spin.e[i]))
                return s.cancel(s.diff(v, var).subs(var, self.spin.e[i]))
            result.append({k: differentiate(v) for k, v in self.coefficients(e).items()})
        return result

    def apply(self, axis, jet122):
        """-partial_e H with the full canonical Pi and all122 input jets fixed."""
        d = self.derivatives[axis]
        values = {w: row['value'] for w, row in jet122.items() if row['value']}
        scalar = {}
        for w, row in jet122.items():
            g, H = row['gradient'], row['Hessian']
            scalar[w] = sum(v*H[i, j] for (i, j), v in d['Q'].todok().items())/2
            scalar[w] -= d['scalar_principal']*sum(H[16+i, 16+i] for i in range(70))
            scalar[w] -= sum(v*H[86+i, 86+j] for (i, j), v in d['gauge_principal'].todok().items())
            scalar[w] -= (d['gauge_first'].T*g[86:, :])[0]+d['identity']*row['value']
        terms = [(1, scalar), (-1, apply_superposition(full(d['one'])+d['matter'], values)),
            (-1, spin_normal_tensor(d['tensor'], values))]
        for j, matrix in enumerate(d['T']):
            if not matrix.todok(): continue
            gradient = {w: row['gradient'][j] for w, row in jet122.items() if row['gradient'][j]}
            terms.append((s.I, apply_superposition(full(matrix), gradient)))
        return simplified(weighted_sum(terms))

    def verify_noether(self):
        """Full differential-operator identity before a primary is imposed."""
        reports = []
        b = self.base
        for h, (T, R8) in enumerate(zip(self.spin.native.lorentz.basis, self.spin.R8)):
            Z = (T*self.spin.e).reshape(16, 1)
            D = s.kronecker_product(T, s.eye(4)); R = full(R8)
            def along(key):
                v = b[key]
                if isinstance(v, list):
                    return [sum((Z[i]*self.derivatives[i][key][j] for i in range(16)), s.zeros(8)) for j in range(16)]
                if isinstance(v, s.MatrixBase):
                    return sum((Z[i]*self.derivatives[i][key] for i in range(16)), s.zeros(*v.shape))
                return sum(Z[i]*self.derivatives[i][key] for i in range(16))
            orbital = D*b['Q']+b['Q']*D.T
            equal(rational(along('Q')-orbital), s.zeros(16))
            assert orbital.todok()
            derivative = along('T')
            for j in range(16):
                expected = sum((D[j, k]*b['T'][k] for k in range(16)), s.zeros(8))
                equal(rational(derivative[j]-expected-R8*b['T'][j]+b['T'][j]*R8), s.zeros(8))
            equal(rational(along('one')-R8*b['one']+b['one']*R8), s.zeros(8))
            L = s.kronecker_product(R8, s.eye(8))-s.kronecker_product(s.eye(8), R8.T)
            equal(rational(along('tensor')-L*b['tensor']-b['tensor']*L.T), s.zeros(64))
            matter_spin = R*b['matter']-b['matter']*R
            equal(clean(along('matter')-matter_spin), s.zeros(504))
            equal(rational(along('gauge_principal')), s.zeros(36))
            equal(rational(along('gauge_first')), s.zeros(36, 1))
            assert s.cancel(along('scalar_principal')) == 0 and s.cancel(along('identity')) == 0
            reports.append({'generator': h, 'all_four_energy_operator_coefficients_zero': True,
                'omitting_orbital_Pi_term_defect_entries': len(orbital.todok()),
                'omitting_matter_Spin_term_defect_entries': len(matter_spin.todok())})
        return reports


def main():
    began = time.monotonic()
    bound = read_bound('source_joint_current_hilbert_section')
    temporal = read_bound('source_temporal_lorentz_balance')
    model = SourceFullCoframeQuantumForce()
    noether = model.verify_noether()
    print('PASS all16 fixed-Pi derivatives and six full four-energy quantum Noether coefficient identities', flush=True)
    source = SourceJointCurrentHilbertSection()
    word = (5, 144, 396); value = {word: s.S.One}
    gradient = {word: s.Matrix([s.I*s.Rational(j % 7-3, 31) for j in range(100)])}
    u = s.Matrix([s.Rational(j % 5-2, 37) for j in range(100)])
    Hessian = {word: u*u.T-s.eye(100)}
    generated = source.action(value, gradient, Hessian)
    jet = generated['generated122_jet']
    forces = [model.apply(i, jet) for i in range(16)]
    current = [{tuple(w): s.sympify(c) for w, c in row} for row in temporal['forces_minus_time_derivative']]
    correction = generated['source_ordering_correction']
    same(forces[0], simplified(weighted_sum(((1, current[0]), (-1/N, correction)))))
    for mu, axis in enumerate(TIME[1:], 1): same(forces[axis], current[mu])
    print('PASS source122 full16 raw force action and all4 current temporal-ordering return', flush=True)
    counts = []
    for i, d in enumerate(model.derivatives):
        counts.append({'axis': i, 'nonzero_coefficients': {k: sum(len(M.todok()) for M in v) if isinstance(v, list)
            else len(v.todok()) if isinstance(v, s.MatrixBase) else int(v != 0) for k, v in d.items()}})
    paths = ('source_full_coframe_quantum_force.py', 'source_lorentz_quantum_section.py',
        'source_coframe_legendre.py', 'source_coframe_live_ordering.py', 'source_joint_current_hilbert_section.py',
        'source_joint_current_hilbert_section.json', 'source_temporal_lorentz_balance.py',
        'source_temporal_lorentz_balance.json', 'source_gauge_quantum_energy.py', 'source_common_hamiltonian.py')
    out = {'root': ROOT_ID, 'scope': 'ORIGINAL_FULL122_H_FIXED_AMBIENT_PI_ALL16_COFORCES_AND_QUANTUM_NOETHER',
        'source_sha256': bound['source_sha256'],
        'input_sha256': {str((HERE/p).relative_to(ROOT)): hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in paths},
        'force_mouth': 'SourceFullCoframeQuantumForce().apply(axis, jet122) differentiates every original four-energy coefficient at fixed full canonical Pi before applying the input germ. The actual consumer obtains jet122 from the existing source100 inverse-half-density and primary/Gauss producer.',
        'source_point': encode(model.spin.e), 'coefficient_counts': counts, 'all_six_original_Noether': noether,
        'normal_carrier': 'Full spin8 tensor I63, exact onebody504 matter, and independent occupied labels in the normal quartic. No occupied12 or matter48 projection.',
        'original_scalar_shift_fact': 'All three rho(A_i) phi_source vanish by direct source evaluation; the scalar shift and spatial potential therefore vanish for every varied coframe. The original scalar principal remains and is differentiated.',
        'actual_consumer': {'word': list(word), 'generated122_words': len(jet),
            'all16_raw_forces_in_source_pairing': [encode_state(F) for F in forces],
            'existing_source_ordering_correction': encode_state(correction),
            'all_four_temporal_returns_checked': True,
            'temporal_identity': 'Fraw_0 = Fcurrent_0 - (ambient_H-current_H)/N; Fraw_i = Fcurrent_i for the three original shift axes at the actual source.'},
        'derivative_carrier': 'The ambient Pi is fixed. DQ+QD^T and D.T_current are retained in the six Lorentz identities. The raw horizontal forces have not been identified with the reduced100 current forces; their momentum and half-density chain terms must be consumed during that transport.',
        'secondary_equations_solved_or_physical_Ward9_claimed': False,
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_full_coframe_quantum_force.json').write_text(json.dumps(out, indent=2)+'\n')
    print('PASS complete source coframe quantum force', out['seconds'], 'seconds', flush=True)

if __name__ == '__main__': main()
