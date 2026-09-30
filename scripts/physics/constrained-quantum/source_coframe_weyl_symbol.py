#!/usr/bin/env python3
"""Exact canonical Weyl symbol of the original half-density coframe action.

The symbol is obtained from the existing differential operator, including its
live derivatives and normal CAR products. No quantization order is replaced.
Its star commutator retains the coframe derivatives of the actual Gauss G(q).
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_joint_form_hamiltonian import SourceJointFormHamiltonian, read_bound
from source_quantum_ordered_temporal import SourceTemporalQuantumFamily
from source_temporal_coframe_pairing import generic_pairing
from source_coframe_live_ordering import full, verify_jet_action
from source_coframe_legendre import rational
from source_lorentz_contact import equal, encode
from source_gauss_quantum_current import weighted_sum, apply_superposition, encode_state


def zero(value):
    assert s.cancel(s.expand(value)) == 0


def left_to_weyl(polynomial, q, p):
    """exp(i partial_q.partial_p/2), exact for canonical momentum degree <=2."""
    assert s.Poly(polynomial, *p).total_degree() <= 2
    contraction = lambda f: sum(s.diff(f, x, k) for x, k in zip(q, p))
    return s.cancel(polynomial+s.I*contraction(polynomial)/2-contraction(contraction(polynomial))/8)


class SourceCoframeWeylSymbol:
    def __init__(self):
        self.model = SourceJointFormHamiltonian()
        self.family = SourceTemporalQuantumFamily(self.model.native)
        self.d = generic_pairing(self.model, self.family)
        self.q = self.model.coframe.q
        self.p = s.Matrix(s.symbols('canonical_kappa0:6', real=True))
        d, q, p = self.d, self.q, self.p
        self.divdiv = s.cancel(sum(s.diff(d['K'][i, j], q[i], q[j])
                                   for i in range(6) for j in range(6)))
        zero(self.divdiv+self.family.y[0]/d['volume'])
        self.scalar_correction = s.cancel(d['potential']+self.divdiv/4)
        zero(self.scalar_correction-self.family.y[0]*(3*d['m']**2+18*d['m']+20)/(16*d['volume']))
        self.quadratic = s.cancel((p.T*d['K']*p)[0])
        scalar_left = self.quadratic-s.I*(d['divergence'].T*p)[0]+d['potential']
        self.scalar_symbol = left_to_weyl(scalar_left, q, p)
        zero(self.scalar_symbol-self.quadratic-self.scalar_correction)
        self.current_symbol = rational(sum((M*p[j] for j, M in enumerate(d['Mh'])), s.zeros(8)))
        converted = self.current_symbol.applyfunc(lambda f: left_to_weyl(f, q, p))
        equal(rational(converted-self.current_symbol), s.zeros(8))
        equal(self.current_symbol.H, self.current_symbol)
        # The complete two-current tensor and one-body terms are the original
        # multiplication coefficients. They undergo no momentum conversion.
        self.onebody = rational(self.family.cf['one_body']+self.family.cf['correction'])
        equal(self.onebody.H, self.onebody)

    def at(self, value, substitutions):
        if isinstance(value, list): return [self.at(v, substitutions) for v in value]
        if isinstance(value, s.MatrixBase): return rational(value.subs(substitutions))
        return s.cancel(value.subs(substitutions))

    def jet_consumer(self, qpoint, timepoint, word):
        d = self.d
        sub = {**dict(zip(self.q, qpoint)), **dict(zip(self.family.y, timepoint))}
        cf = {key: self.at(value, sub) for key, value in self.family.cf.items()}
        g = s.Matrix([s.Rational(j-2, 19)+s.I*s.Rational(j+1, 17) for j in range(6)])
        u = s.Matrix([s.Rational(j % 3-1, 23) for j in range(6)])
        H = u*u.T-s.eye(6)
        alpha = s.Rational(len(word)+2, 2)
        ell = alpha*self.at(self.model.metric['g'], sub)
        hell = alpha*self.at(self.model.metric['Hessian'], sub)
        ug = g-ell
        uH = H-ell*g.T-g*ell.T+ell*ell.T-hell
        raw = verify_jet_action(cf, word, 1, ug, uH)
        original = {tuple(w): s.sympify(v) for w, v in raw['raw_nested_square']}
        constant = verify_jet_action(cf, word, 1, s.zeros(6, 1), s.zeros(6))
        C = {tuple(w): s.sympify(v) for w, v in constant['raw_nested_square']}
        correction = self.at(self.scalar_correction.subs(d['m'], len(word)), sub)
        # Weyl(Kpp) differentiates K once and twice. These terms remain even
        # at the source value of q; evaluating q does not freeze derivatives.
        quadratic = -sum(v*H[i, j] for (i, j), v in cf['K'].todok().items())
        quadratic -= (self.at(d['divergence'], sub).T*g)[0]+self.at(self.divdiv, sub)/4
        image = [(1, C), (quadratic+correction, {word: 1})]
        for j, Mh in enumerate(d['Mh']):
            image.append((-s.I*g[j], apply_superposition(full(self.at(Mh, sub)), {word: 1})))
        weyl = weighted_sum(image)
        assert weighted_sum([(1, original), (-1, weyl)]) == {}
        omitted = weighted_sum([(1, weyl), (-self.at(self.divdiv, sub)/4, {word: 1})])
        defect = weighted_sum([(1, omitted), (-1, original)])
        assert defect
        return {'q': list(map(str, qpoint)), 'time': list(map(str, timepoint)), 'input_CAR': list(word),
            'gradient6': encode(g), 'Hessian6': encode(H),
            'inverse_half_density_gradient6': encode(ug), 'inverse_half_density_Hessian6': encode(uH),
            'original_U_H_U_inverse': encode_state(original), 'canonical_Weyl_readback': encode_state(weyl),
            'symbol_scalar_correction': str(correction), 'omitted_divdiv_symbol_defect': encode_state(defect)}

    def gauss_matrix_commutator(self):
        """The exact Weyl commutator with G22, at all q and all momenta."""
        q, p, K = self.q, self.p, self.d['K']
        G22 = 1/q[5]**2
        grad = s.Matrix([s.diff(G22, x) for x in q])
        # Since G22 has momentum degree0 and the coframe degree is2, all odd
        # Moyal terms beyond first order vanish, with no semiclassical limit.
        scalar_symbol = s.cancel(-s.I*sum(s.diff(self.scalar_symbol, p[j])*grad[j] for j in range(6)))
        current_symbol = rational(-s.I*sum((self.d['Mh'][j]*grad[j] for j in range(6)), s.zeros(8)))
        scalar_left = s.cancel(scalar_symbol-s.I*sum(s.diff(scalar_symbol, q[j], p[j]) for j in range(6))/2)
        expected_left = s.cancel(-2*s.I*(grad.T*K*p)[0]-sum(
            s.diff(K[i, j]*grad[j], q[i]) for i in range(6) for j in range(6)))
        zero(scalar_left-expected_left)
        assert scalar_symbol != 0
        equal(current_symbol.H, -current_symbol)
        q0 = (1, 0, 1, 0, 0, 1)
        values = self.at(-2*K*grad, {**dict(zip(q, q0)), self.family.y[0]: self.model.coframe.N})
        assert values[0] == self.model.coframe.N
        return {'G22': str(G22), 'exact_star_scalar_commutator': str(scalar_symbol),
            'exact_star_current_spin8_commutator': encode(current_symbol),
            'exact_left_symbol_after_inverse_Weyl': str(scalar_left),
            'source_linear_germ_direction': 0, 'source_linear_germ_value': str(values[0]),
            'higher_Moyal_terms_vanish_by_actual_momentum_degree': True}


def main():
    started = time.monotonic()
    names = ('source_temporal_coframe_pairing', 'independent_source_temporal_coframe_pairing',
             'source_temporal_gauss_relations', 'independent_source_temporal_gauss_relations')
    for name in names: read_bound(name)
    model = SourceCoframeWeylSymbol(); d = model.d
    for b in model.family.y[1:]: zero(s.diff(model.scalar_symbol, b))
    print('PASS exact all6q/all4time canonical Weyl conversion with full Fock number and live coefficients', flush=True)
    q = (s.Rational(7, 6), s.Rational(1, 11), s.Rational(9, 8),
         s.Rational(-1, 13), s.Rational(1, 17), s.Rational(11, 10))
    times = (7*model.model.coframe.N/6, s.Rational(1, 13), -s.Rational(1, 17), s.Rational(1, 19))
    assert times[0]**2 > sum(b*b for b in times[1:])
    consumers = [model.jet_consumer(q, times, word) for word in ((), (144,), (144, 396), (0, 63, 315))]
    commutator = model.gauss_matrix_commutator()
    print('PASS four actual CAR sectors, literal nested-square readback and exact live-G Moyal commutator', flush=True)
    files = [HERE/(name+'.json') for name in names]+[HERE/name for name in (
        'source_coframe_weyl_symbol.py', 'source_coframe_live_ordering.py', 'source_coframe_legendre.py',
        'source_quantum_ordered_temporal.py', 'source_reducing_coframe_metric.py',
        'source_temporal_coframe_pairing.py', 'source_joint_form_hamiltonian.py')]
    result = {'root': ROOT_ID, 'scope': 'EXACT_SOURCE_COFRAME_CANONICAL_WEYL_SYMBOL_AND_LIVE_G_COMPOSITION',
        'source_sha256': model.model.native.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'canonical_coordinates': list(map(str, model.q)), 'canonical_momenta': list(map(str, model.p)),
        'time_parameters': list(map(str, model.family.y)),
        'symbol': {'scalar_momentum_part': str(model.scalar_symbol),
            'mixed_current_spin8': encode(model.current_symbol),
            'complete_normal_current_tensor': encode(d['tensor']), 'onebody_with_live_correction': encode(model.onebody),
            'original_source_potential': str(model.family.cf['constant']),
            'Fock_interpretation': 'The mixed and onebody spin8 matrices act by dGamma(M tensor I63); the normal tensor uses the original two ordered CAR current slots on the whole504-mode carrier.',
            'divdivK_over4': str(model.divdiv/4), 'half_density_potential': str(d['potential']),
            'combined_scalar_correction': str(model.scalar_correction)},
        'symbol_equation': 'OpW(sigma_coframe)=U Hcoframe(n,b) U^-1, U=v^(1+Number/2); the source residual3 density is q-independent. No operator or ordering is replaced.',
        'Gauss_G_composition': commutator, 'actual_consumers': consumers,
        'all_original_scalar_gauge_matter_and_time_constraint_components_assembled': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_coframe_weyl_symbol.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source coframe canonical Weyl symbol', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
