#!/usr/bin/env python3
"""Scalar Weyl symbol on the original residual3 canonical coordinate chart.

The original 70 momentum graph is pulled through the actual group section
before its source half-density is applied. All symbol derivatives are with
respect to the 94 scalar/gauge canonical slice coordinates, not the thirteen
time-reduction readouts. The six coframe coordinates remain parameters of this
component because the original scalar momenta have no coframe derivatives.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_scalar_temporal_form import SourceScalarTemporalForm
from source_scalar_form_hamiltonian import relocate_section
from source_coframe_legendre import rational
from source_lorentz_contact import clean, equal, encode
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_quantum_temporal_symbol import N


def zero(x): assert s.cancel(s.expand(x)) == 0
def state_equal(a, b): assert weighted_sum([(1, a), (-1, b)]) == {}


def binding(name):
    data = json.loads((HERE/(name+'.json')).read_text())
    assert data['root'] == ROOT_ID
    for group in ('source_sha256', 'input_sha256'):
        for path, digest in data[group].items():
            assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path


def quadratic_weyl_action(d, values, gradients, Hessians, current_word, current_action, omit_weyl_correction=False):
    """Exact Weyl quantization of the degree-two canonical momentum symbol."""
    result = []
    central = d['classical_zero']+d['half_density_potential']
    if not omit_weyl_correction: central += d['weyl_correction']
    for w in set(values)|set(gradients)|set(Hessians):
        v = values.get(w, 0); g = gradients.get(w, s.zeros(100, 1))[6:, :]
        h = Hessians.get(w, s.zeros(100))[6:, 6:]
        scalar = -sum(c*h[i, j] for (i, j), c in d['principal'].todok().items())
        scalar -= (d['div_principal'].T*g)[0]+d['divdiv_principal']*v/4
        scalar -= s.I*((d['momentum_identity'].T*g)[0]+d['div_momentum_identity']*v/2)
        scalar += central*v
        result.append((scalar, {w: 1}))
        for a in range(d['momentum_current'].cols):
            coefficient = -s.I*(d['momentum_current'][:, a].T*g)[0]
            coefficient += v*(d['linear_current'][a]-s.I*d['div_momentum_current'][a]/2)
            if coefficient: result.append((coefficient, current_word(a, w)))
        for (a, b), coefficient in d['square_current'].todok().items():
            if v: result.append((v*coefficient, current_action(a, current_word(b, w))))
    return weighted_sum(result)


class SourceScalarWeylSymbol:
    def __init__(self):
        self.temporal = SourceScalarTemporalForm()
        self.native = self.temporal.native
        self.section = self.temporal.section
        self.graph = self.native.graph
        self.free = tuple(i-6 for i in self.section.free if i >= 6)
        self.pivots = tuple(i-6 for i in self.section.pivots)
        assert len(self.free) == 94 and all(i >= 61 for i in self.pivots)
        self.charges = self.native.Q_b+self.native.Q_s
        for Q in self.charges: equal(Q.H, Q)

    @lru_cache(None)
    def current_word(self, a, word):
        return apply_superposition(self.charges[a], {word: 1})

    def current(self, a, state):
        return weighted_sum((v, self.current_word(a, w)) for w, v in state.items())

    def coefficients(self, time_column, q, x, A):
        data = self.temporal.coefficients(time_column, q, x, A)
        point = s.Matrix(q).col_join(x).col_join(A.reshape(36, 1))
        relocate_section(self.section, point)
        y = point[6:, :]; O = self.graph.O; F = data['F']; G = clean(O.T*O)
        B = data['vectors']; S = clean(s.Matrix.hstack(*(T*y for T in self.native.T_s)))
        free, piv = self.free, self.pivots
        M = S[list(piv), :]; U = rational(M.inv()); T = rational(S[list(free), :]*U)
        W = rational(B[:, list(free)]-B[:, list(piv)]*T.T)
        H = rational(F*W)
        E = self.graph.dual_R.row_join(s.zeros(70, 33))
        ahat = rational(E-O*H)
        equal(ahat, rational(data['momentum_vectors']*self.section.z[6:, 6:].T))
        charge_reader = s.eye(9).row_join(rational(-B[:, list(piv)]*U.T))
        chat = rational(-O*F*charge_reader)
        equal(chat[:, :9], -data['normal_embedding'])
        equal(chat[:, 9:], rational(-data['momentum_vectors']*self.section.alpha[:, 6:].T))
        dD, dB, dM, dS = [], [], [], []
        for u in free:
            dD.append(clean(O.T*s.Matrix.hstack(*(R*self.graph.R[:, u] for R in self.native.rho_b)))
                      if u < 61 else s.zeros(9))
            dB.append(clean(s.Matrix.vstack(*(R[:, u].T for R in self.native.T_b))))
            d = clean(s.Matrix.hstack(*(R[:, u] for R in self.native.T_s)))
            dM.append(d[list(piv), :]); dS.append(d[list(free), :])
        dF = [rational(-F*d.T*F) for d in dD]
        dT = [rational((ds-T*dm)*U) for ds, dm in zip(dS, dM)]
        dW = [rational(db[:, list(free)]-db[:, list(piv)]*T.T-B[:, list(piv)]*dt.T)
              for db, dt in zip(dB, dT)]
        dH = [rational(df*W+F*dw) for df, dw in zip(dF, dW)]
        dchat = []
        for df, db, dm in zip(dF, dB, dM):
            du = rational(-U*dm*U)
            dr = s.zeros(9).row_join(rational(-db[:, list(piv)]*U.T-B[:, list(piv)]*du.T))
            dchat.append(rational(-O*(df*charge_reader+F*dr)))
        trH = rational(sum((dH[k][:, k] for k in range(94)), s.zeros(9, 1)))
        div_a = rational(-O*trH)
        first = rational((H.T*G*trH+sum((dh.T*G*H[:, k] for k, dh in enumerate(dH)), s.zeros(94, 1)))/(2*data['h00']))
        principal = rational((E.T*E+H.T*G*H)/(2*data['h00']))
        equal(principal, rational(ahat.T*ahat/(2*data['h00'])))
        equal(first, rational((ahat.T*div_a+sum(((-O*dh).T*ahat[:, k] for k, dh in enumerate(dH)), s.zeros(94, 1)))/(2*data['h00'])))
        # Contract second differentiated inverse identities directly. Only
        # nine normal rows occur, while every 94x94 derivative pair is kept.
        dtrace = s.zeros(9, 94)
        for i in range(94):
            col = s.zeros(9, 1)
            for k in range(94):
                fik = rational(-dF[i]*dD[k].T*F-F*dD[k].T*dF[i])
                tik_row = rational(-dT[i][k, :]*dM[k]*U-dT[k][k, :]*dM[i]*U)
                wik_col = rational(-dB[i][:, list(piv)]*dT[k][k, :].T
                    -dB[k][:, list(piv)]*dT[i][k, :].T-B[:, list(piv)]*tik_row.T)
                col += fik*W[:, k]+dF[i]*dW[k][:, k]+dF[k]*dW[i][:, k]+F*wik_col
            dtrace[:, i] = rational(col)
            if i in (30, 60, 93): print('PASS original inverse/section second-derivative trace', i+1, '/94', flush=True)
        crossed = s.S.Zero
        for i in range(94):
            for k in range(94):
                crossed += (dH[i][:, k].T*G*dH[k][:, i])[0]
        second = s.cancel(((trH.T*G*trH)[0]+crossed+
            2*sum((H[:, i].T*G*dtrace[:, i])[0] for i in range(94)))/(2*data['h00']))
        ell = s.zeros(94, 1); log_H = s.zeros(94)
        for ambient, power in ((62, s.S.One), (73, s.Rational(1, 2))):
            j = free.index(ambient); ell[j] = power/y[ambient]; log_H[j, j] = -power/y[ambient]**2
        shift = data['shift']; dshift = data['shift_derivative'][:, list(free)]
        currents = rational(ahat.T*chat/data['h00'])
        identity_first = rational(-ahat.T*shift/data['h00'])
        div_current = rational((chat.T*div_a+sum((dc.T*ahat[:, i] for i, dc in enumerate(dchat)), s.zeros(12, 1)))/data['h00'])
        div_identity = s.cancel(-(div_a.T*shift)[0]/data['h00']-
            sum((ahat[:, i].T*dshift[:, i])[0] for i in range(94))/data['h00'])
        square = rational(chat.T*chat/(2*data['h00']))
        linear = rational(-chat.T*shift/data['h00'])
        density_potential = s.cancel((ell.T*principal*ell)[0]+(first.T*ell)[0]+
            sum(v*log_H[i, j] for (i, j), v in principal.todok().items()))
        classical_zero = s.cancel((shift.T*shift)[0]/(2*data['h00'])+data['spatial_potential'])
        e = self.temporal.e.subs({**dict(zip(self.temporal.y, time_column)), **dict(zip(self.temporal.q, q))})
        return {'raw': data, 'e': e, 'point103': point, 'a': ahat, 'current': chat,
            'section_primitives': {'free': free, 'pivots': piv, 'U': U, 'T': T,
                'dM': dM, 'dT': dT, 'S': S, 'point97': y, 'Z': self.section.z[6:, 6:]},
            'principal': principal, 'div_principal': first, 'divdiv_principal': second,
            'momentum_current': currents, 'momentum_identity': identity_first,
            'div_momentum_current': div_current, 'div_momentum_identity': div_identity,
            'square_current': square, 'linear_current': linear, 'classical_zero': classical_zero,
            'half_density_potential': density_potential, 'weyl_correction': s.cancel(second/4),
            'ell': ell, 'log_Hessian': log_H, 'inverse_trace_gradient': dtrace,
            'd_a': [rational(-O*dh) for dh in dH], 'd_current': dchat,
            'div_a': div_a, 'shift': shift, 'd_shift': dshift}

    def weyl_action(self, d, values, gradients, Hessians, omit_weyl_correction=False):
        return quadratic_weyl_action(d, values, gradients, Hessians,
            self.current_word, self.current, omit_weyl_correction)

    def half_density_jet(self, d, values, gradients, Hessians):
        ell = s.zeros(100, 1); ell[6:, :] = d['ell']
        log_H = s.zeros(100); log_H[6:, 6:] = d['log_Hessian']
        gs, hs = {}, {}
        for w in set(values)|set(gradients)|set(Hessians):
            v = values.get(w, 0); g = gradients.get(w, s.zeros(100, 1)); H = Hessians.get(w, s.zeros(100))
            gs[w] = rational(g-ell*v)
            hs[w] = rational(H-ell*g.T-g*ell.T+(ell*ell.T-log_H)*v)
        return self.section.extend_jet(values, gs, hs)


def main():
    started = time.monotonic()
    for name in ('source_scalar_temporal_form', 'source_gauss_section_measure',
                 'source_joint_form_hamiltonian', 'independent_source_scalar_form_hamiltonian'):
        binding(name)
    m = SourceScalarWeylSymbol()
    q = (s.Rational(7, 6), s.Rational(1, 11), s.Rational(9, 8),
         s.Rational(-1, 13), s.Rational(1, 17), s.Rational(11, 10))
    x = s.zeros(61, 1); x[19] = s.Rational(1, 100)
    A = m.section.A0.copy(); A[0, 2] += s.Rational(1, 31); A[1, 7] += s.Rational(1, 19)
    time_column = (7*N/6, s.Rational(1, 13), -s.Rational(1, 17), s.Rational(1, 19))
    d = m.coefficients(time_column, q, x, A)
    assert d['weyl_correction'] and d['half_density_potential']
    print('PASS actual canonical slice Weyl correction and nonzero source half-density potential', flush=True)
    word = (7, 71); values = {word: s.S.One}
    gradient = s.Matrix([s.I*s.Rational(i % 5-2, 47) for i in range(100)])
    u = s.Matrix([s.Rational(i % 3-1, 43) for i in range(100)])
    Hessian = u*u.T-s.eye(100)
    gradients, Hessians = {word: gradient}, {word: Hessian}
    jet = m.half_density_jet(d, values, gradients, Hessians)
    gauss = m.section.verify_Gauss_jet(jet)
    # Rebuild the original ambient97 form independently, before descent.
    from independent_source_scalar_form_hamiltonian import RawGaussSection, raw_coefficients, form_action
    raw = RawGaussSection()
    rd = raw_coefficients(raw.native, d['e'], x, A)
    equal(rd['a'], d['raw']['momentum_vectors'])
    original = weighted_sum((1, form_action(rd, w, item['value'], item['gradient'][6:, :], item['Hessian'][6:, 6:]))
                            for w, item in jet.items())
    generated = m.weyl_action(d, values, gradients, Hessians)
    state_equal(original, generated)
    wrong = m.weyl_action(d, values, gradients, Hessians, omit_weyl_correction=True)
    state_equal(weighted_sum([(1, generated), (-1, wrong)]), {word: d['weyl_correction']})
    hidden = {w for w, j in jet.items() if j['value'] == 0 and (j['gradient'].todok() or j['Hessian'].todok())}
    assert hidden and generated
    print('PASS complete original97 form through actual Gauss two-jet equals canonical Weyl action', flush=True)
    names = ('source_scalar_weyl_symbol.py', 'source_scalar_temporal_form.py', 'source_scalar_temporal_form.json',
        'source_scalar_form_hamiltonian.py', 'source_quantum_gauss_section.py', 'source_quantum_stabilizer.py',
        'source_gauss_section_measure.py', 'source_gauss_section_measure.json',
        'source_joint_form_hamiltonian.py', 'source_joint_form_hamiltonian.json',
        'independent_source_scalar_form_hamiltonian.py', 'independent_source_scalar_form_hamiltonian.json')
    result = {'root': ROOT_ID, 'source_sha256': m.graph.common.source_hashes,
        'input_sha256': {str((HERE/name).relative_to(ROOT)): hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in names},
        'scope': 'ORIGINAL_SCALAR_FORM_WEYL_SYMBOL_ON_ACTUAL_RESIDUAL3_CANONICAL_SLICE_HALF_DENSITY',
        'canonical_variables': 'Original100 slice coordinates z=(q6,x61,Afree33), with conjugate momenta; no compressed temporal invariant is treated as a canonical coordinate.',
        'momentum_descent': 'Ahat=a Z^T; Chat=c-i a alpha^T R-b, using the original equivariant section and all12 native CAR currents. The normal graph is unchanged.',
        'weyl_symbol': 'P_ij p_i p_j+M_i p_i+sum(Chat_j^2)/(2h00)+V+ell^T P ell+div(P).ell+P:Hess(log sqrt(rho3))+divdiv(P)/4, P=Ahat^T Ahat/(2h00), M=Ahat^T Chat/h00.',
        'normalization': 'rho3=8*A1^2*A12; ell=grad log sqrt(rho3). The v^(1+Number/2) part commutes with the complete scalar component and changes no scalar symbol coefficient.',
        'differentiated_original_inverses': 'D^T F=1 and M3 U=1; all94 first and all94x94 second derivatives of the actual inverse graph are contracted, with all section-connection coefficients retained.',
        'public_API': 'SourceScalarWeylSymbol.coefficients(time_column,q,x61,A36) returns the complete symbol coefficients and original section_primitives (free,pivots,U,T,dM,dT,S,point97,Z). quadratic_weyl_action consumes these coefficients, arbitrary CAR-valued100-coordinate two-jets and the original current actions.',
        'actual_consumer': {'q': list(map(str, q)), 'time_column': list(map(str, time_column)),
            'x61': encode(x), 'A36': encode(A), 'base103': encode(d['point103']), 'input_CAR': list(word),
            'gradient100': encode(gradient), 'Hessian100': encode(Hessian), 'Gauss': gauss,
            'hidden_zero_value_jet_word_count': len(hidden), 'principal94': encode(d['principal']),
            'div_principal94': encode(d['div_principal']), 'divdiv_principal': str(d['divdiv_principal']),
            'Weyl_correction': str(d['weyl_correction']), 'half_density_potential': str(d['half_density_potential']),
            'momentum_current94x12': encode(d['momentum_current']), 'current_square12': encode(d['square_current']),
            'original_form_image': encode_state(original), 'Weyl_quantized_image': encode_state(generated),
            'omitted_Weyl_correction_defect': encode_state(weighted_sum([(1, generated), (-1, wrong)]))},
        'quantum_ordering_changed': False, 'compressed_invariant_Moyal_bracket_assumed': False,
        'spectrum_Gamma_tau_generated': False, 'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_scalar_weyl_symbol.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source scalar canonical Weyl symbol', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
