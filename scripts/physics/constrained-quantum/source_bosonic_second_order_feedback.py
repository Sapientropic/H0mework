#!/usr/bin/env python3
"""Complete bosonic scalar acceleration and its original reference-kernel source.

For the source Weyl symbol B=pi^T K pi+ell.pi+V_B and v=d_pi B,
i[OpW(B),OpW(v_j)] has symbol
  v_k d_k v_j - 2 K_jk d_k B + (d_a K_bc)(d_bc K_ja)/2.
The last term is the complete third Moyal order. All higher orders vanish by
momentum degree. The source's fixed time column makes ell identically zero.

The exact nonlinear remainder is R_B=A_B-A_reference*x, on the same Gauss
chart. R_B and the already generated fermion S enter R*(R_B+S)/N. This uses
the classical scalar reference kernel, without identifying it with full H_B.
"""
from collections import defaultdict
from concurrent.futures import ProcessPoolExecutor
from functools import lru_cache
import hashlib
import itertools
import json
import math
import multiprocessing as mp
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_joint_current_heisenberg import patch_symbolic_equal
from source_joint_ccr_car_ports import NormalSymbol
from source_joint_form_hamiltonian import read_bound
from source_quantum_temporal_symbol import N
from source_second_order_scalar_retarded import SourceSecondOrderScalarRetarded
from source_lorentz_contact import encode


def clean(value):
    return s.SparseMatrix(value).applyfunc(s.cancel)


def zero(value):
    residual = clean(value)
    assert not residual.todok(), list(residual.todok().items())[:3]


class SourcePrincipalJet:
    """Differentiate the original normal9/orbit3 affine equations, not a fit."""
    def __init__(self, model, data):
        scalar = data['scalar']
        weyl = model.leaf.weyl
        native, graph = weyl.native, weyl.graph
        free = scalar['section_primitives']['free']
        pivots = scalar['section_primitives']['pivots']
        raw = scalar['raw']
        B, S, D = raw['vectors'], scalar['section_primitives']['S'], raw['D']
        M = S[list(pivots), :]
        self.L = clean(D.T.row_join(B[:, list(pivots)]).col_join(
            s.zeros(3, 9).row_join(M.T)))
        right = B[:, list(free)].col_join(S[list(free), :].T)
        self.inverse = clean(self.L.inv())
        self.X = clean(self.inverse*right)
        zero(self.L*self.X-right)
        Es = graph.dual_R.row_join(s.zeros(70, 33))
        Eg = s.eye(97)[61:, list(free)]
        Bp = s.eye(97)[61:, list(pivots)]
        W = model.at_time(data['gauge']['original']['weight'])
        h = model.at_time(raw['h00'])
        self.C = s.diag(graph.O.T*graph.O/h, Bp.T*W*Bp)
        self.B = (Es.T*graph.O/h).row_join(Eg.T*W*Bp)
        self.H = clean(self.X.T*self.C-self.B)
        self.K = clean((Es.T*Es/h+Eg.T*W*Eg-self.B*self.X-
            self.X.T*self.B.T+self.X.T*self.C*self.X)/2)
        zero(self.K-data['principal'][6:, 6:])
        self.L1, self.X1, self.K1 = [], [], []
        for u in free:
            dD = clean(graph.O.T*s.Matrix.hstack(
                *(rho*graph.R[:, u] for rho in native.rho_b))) if u < 61 else s.zeros(9)
            dB = s.Matrix.vstack(*(T[:, u].T for T in native.T_b))
            dS = s.Matrix.hstack(*(T[:, u] for T in native.T_s))
            dL = dD.T.row_join(dB[:, list(pivots)]).col_join(
                s.zeros(3, 9).row_join(dS[list(pivots), :].T))
            dright = dB[:, list(free)].col_join(dS[list(free), :].T)
            dX = clean(self.inverse*(dright-dL*self.X))
            zero(self.L*dX+dL*self.X-dright)
            self.L1.append(clean(dL)); self.X1.append(dX)
            self.K1.append(clean((self.H*dX+dX.T*self.H.T)/2))

    @lru_cache(None)
    def second(self, b, c):
        xb, xc = self.X1[b], self.X1[c]
        xbc = clean(-self.inverse*(self.L1[b]*xc+self.L1[c]*xb))
        return clean((self.H*xbc+xbc.T*self.H.T+
            xb.T*self.C*xc+xc.T*self.C*xb)/2)

    @lru_cache(None)
    def moyal_third(self):
        """Full94 contraction; scalar entries are selected only after summation."""
        weights = defaultdict(dict)
        for a, derivative in enumerate(self.K1):
            for (b, c), value in derivative.todok().items():
                if b <= c:
                    weights[b, c][a] = value*(1 if b == c else 2)
        result = s.zeros(94, 1)
        scalar_nonzero_pairs = 0
        for (b, c), row in weights.items():
            xb, xc = self.X1[b], self.X1[c]
            xbc = clean(-self.inverse*(self.L1[b]*xc+self.L1[c]*xb))
            vector = s.SparseMatrix(94, 1, {(a, 0): v for a, v in row.items()})
            contribution = clean((self.H*xbc*vector+xbc.T*(self.H.T*vector)+
                xb.T*(self.C*(xc*vector))+xc.T*(self.C*(xb*vector)))/4)
            result += contribution
            scalar_nonzero_pairs += bool(contribution[:61, :].todok())
        return clean(result), {'symmetric_derivative_pairs': len(weights),
            'nonzero_scalar_pair_contributions': scalar_nonzero_pairs,
            'first_metric_jet_entries': sum(len(v.todok()) for v in self.K1)}


class SourceBosonicSecondOrderFeedback:
    def __init__(self):
        self.reference = SourceSecondOrderScalarRetarded()
        self.model = self.reference.force.model
        self.background = self.reference.z
        self._central_gradients = {}
        weyl = self.model.leaf.weyl
        q = weyl.native.joint.coframe.q
        self.q = q
        e = weyl.temporal.e.subs(dict(zip(weyl.temporal.y, self.model.time_point)))
        self.metric = clean(weyl.temporal.metric.subs(
            dict(zip(weyl.temporal.y, self.model.time_point))))
        self.gauge_family = weyl.native.joint.gauge.coefficients(e)
        # The original fixed lapse/zero-shift column proves ell=0 throughout
        # this chart. Moving configurations are retained in K and V_B.
        zero(self.metric[0, 1:])
        zero(self.gauge_family['momentum_shift'])

    @lru_cache(None)
    def geometry(self, configuration):
        data = self.model.coefficients(configuration)
        zero(data['linear_identity'])
        jet = SourcePrincipalJet(self.model, data)
        derivatives = []
        scalar_a = self.model.at_time(data['scalar']['a'])
        gauge_a = self.model.at_time(data['gauge']['a'])
        sub = dict(zip(self.q, configuration[:6]))
        coframe = self.model.leaf.weyl.native.joint.coframe
        for variable in self.q:
            derivative = s.zeros(100)
            derivative[:6, :6] = clean(coframe.K.diff(variable).subs(sub))
            inverse_h_derivative = s.diff(1/self.metric[0, 0], variable).subs(sub)
            weight_derivative = self.gauge_family['weight'].diff(variable).subs(sub)
            derivative[6:, 6:] = clean((inverse_h_derivative*scalar_a.T*scalar_a+
                gauge_a.T*weight_derivative*gauge_a)/2)
            derivatives.append(clean(derivative))
        for derivative in jet.K1:
            complete = s.zeros(100)
            complete[6:, 6:] = derivative
            derivatives.append(s.SparseMatrix(complete))
        assert len(derivatives) == 100
        return data, jet, tuple(derivatives)

    def central_derivative(self, k, configuration):
        key = (k, configuration)
        if key in self._central_gradients:
            return self._central_gradients[key]
        variable = s.Dummy('bosonic_coordinate', positive=True) if k in (0, 2, 5) else s.Dummy('bosonic_coordinate', real=True)
        argument = list(configuration); argument[k] = variable
        potential = self.model.coefficients(tuple(argument))['zero'].scalar
        value = s.factor(potential.diff(variable).subs(variable, configuration[k]))
        self._central_gradients[key] = value
        return value

    def acceleration(self, phase):
        """Complete scalar61 Weyl symbol, at any regular original chart point."""
        phase = tuple(phase)
        assert len(phase) == 200
        configuration, p = phase[:100], s.Matrix(phase[100:])
        data, jet, derivatives = self.geometry(configuration)
        K = data['principal']; velocity = 2*K*p
        needed = {k for j, k in K[6:67, :].todok()}
        gradient = {k: s.factor((p.T*derivatives[k]*p)[0]+
            self.central_derivative(k, configuration)) for k in needed}
        moving = sum((velocity[k]*2*derivatives[k][6:67, :]*p
            for k in range(100) if velocity[k]), s.zeros(61, 1))
        force = -2*sum((K[6:67, k]*value for k, value in gradient.items()), s.zeros(61, 1))
        third, _ = jet.moyal_third()
        return clean(moving+force+third[:61, :])

    def remainder(self, phase):
        phase = tuple(phase)
        return clean(self.acceleration(phase)-self.reference.acceleration*s.Matrix(phase[6:67]))

    def source70(self, phase):
        return clean(self.reference.source_map*self.remainder(phase))

    def full_source_symbols(self, phase):
        """Same source S plus R_B; no supplied state or acceleration coefficient."""
        bosonic = self.source70(phase)
        fermionic = self.reference.source_symbols(phase)
        return tuple(NormalSymbol(term.scalar+bosonic[i], term.one_body, term.pairs)
            for i, term in enumerate(fermionic))

    def response_jet(self, order, phase):
        return clean(self.reference.response_jet(order)*self.remainder(phase))


def verify_moyal_formula():
    """Direct finite Weyl convolution fixes the sign and factor independently."""
    z = s.symbols('z0:2', real=True); p = s.symbols('p0:2', real=True)
    K = s.Matrix([[1+z[0]**2+z[0]*z[1], z[0]+z[1]**2],
                  [z[0]+z[1]**2, 2+z[0]**2*z[1]]])
    ell = s.Matrix([z[0]**2-z[1], z[0]*z[1]])
    B = (s.Matrix(p).T*K*s.Matrix(p))[0]+(ell.T*s.Matrix(p))[0]+z[0]**3*z[1]
    velocities = s.Matrix([s.diff(B, v) for v in p])
    def differentiate(value, a, b):
        for variable, order in zip((*z, *p), (*a, *b)):
            if order: value = s.diff(value, variable, order)
        return value
    def star_order(left, right, order):
        value = 0
        for powers in itertools.product(range(order+1), repeat=4):
            if sum(powers) != order: continue
            a, b = powers[:2], powers[2:]
            factor = (s.I/2)**order*(-1)**sum(b)/s.prod(math.factorial(v) for v in powers)
            value += factor*differentiate(left, a, b)*differentiate(right, b, a)
        return s.expand(value)
    thirds = []
    for j in range(2):
        pieces = [s.expand(s.I*(star_order(B, velocities[j], order)-
            star_order(velocities[j], B, order))) for order in range(6)]
        poisson = sum(velocities[k]*s.diff(velocities[j], z[k])-
            2*K[j, k]*s.diff(B, z[k]) for k in range(2))
        third = sum(s.diff(K[b, c], z[a])*s.diff(K[j, a], z[b], z[c])/2
            for a, b, c in itertools.product(range(2), repeat=3))
        assert s.expand(pieces[1]-poisson) == 0
        assert s.expand(pieces[3]-third) == 0 and third != 0
        assert all(pieces[k] == 0 for k in (0, 2, 4, 5))
        thirds.append(str(s.expand(third)))
    return {'nonzero_generic_third_order': thirds, 'orders_checked': 6,
        'sign_and_coefficient': '+1/2 sum_abc (partial_a K_bc)(partial_bc K_ja)',
        'termination': 'Each higher contraction requires more than2+1 total momentum derivatives.'}


_SOURCE = None


def scalar_gradient(k):
    return k, _SOURCE.central_derivative(k, _SOURCE.background)


def main():
    started = time.monotonic()
    patch_symbolic_equal()
    formula = verify_moyal_formula()
    print('PASS direct Weyl convolution, positive half coefficient and nonzero third order', flush=True)
    global _SOURCE
    source = _SOURCE = SourceBosonicSecondOrderFeedback()
    data, jet, derivatives = source.geometry(source.background)
    third, report = jet.moyal_third()
    zero(third[:61, :]); assert third[61:, :].todok()
    assert report['nonzero_scalar_pair_contributions'] == 0
    print('PASS actual affine12 metric jets and all scalar61 Moyal contractions;', report, flush=True)
    gradients = {}
    with ProcessPoolExecutor(max_workers=8, mp_context=mp.get_context('fork')) as pool:
        for k, value in pool.map(scalar_gradient, range(6, 67)):
            gradients[k] = value
            # Populate the source-owned evaluator cache in the parent process.
            source._central_gradients[k, source.background] = value
            print('PASS fresh original V_B derivative', k, flush=True)
    bound = read_bound('source_local_scalar_retarded_identification')
    for k, value in gradients.items():
        assert s.cancel(value+s.sympify(bound['scalar_forces']['scalar_part'][str(k-6)])) == 0
    K = data['principal']
    zero(K[6:67, :6]); zero(K[6:67, 67:])
    central = clean(-2*K[6:67, 6:67]*s.Matrix([gradients[k] for k in range(6, 67)]))
    assert len(central.todok()) == 4
    phase0 = source.background+tuple(s.zeros(100, 1))
    zero(source.remainder(phase0)-central)
    momentum = s.Matrix([s.Rational((j % 5)-2, 97) for j in range(100)])
    velocity = 2*K*momentum
    moving = sum((2*velocity[k]*derivatives[k][6:67, :]*momentum
        for k in range(100) if velocity[k]), s.zeros(61, 1))
    momentum_force = -2*sum((K[6:67, k]*(momentum.T*derivatives[k]*momentum)[0]
        for k in range(100) if K[6:67, k].todok()), s.zeros(61, 1))
    nonlinear = clean(moving+momentum_force)
    assert nonlinear.todok()
    phase = source.background+tuple(momentum)
    zero(source.acceleration(phase)-central-nonlinear)
    lifted = source.source70(phase0)
    assert lifted.todok()
    responses = []
    for order in range(8):
        value = source.response_jet(order, phase0)
        expected = s.zeros(70, 1) if order % 2 == 0 else source.reference.R*source.reference.acceleration**((order-1)//2)*central
        zero(value-expected)
        responses.append({'kernel_jet_order': order, 'value': encode(value)})
    wrong_normalization = clean(N*lifted-lifted)
    assert wrong_normalization.todok()
    paths = ['source_bosonic_second_order_feedback.py', 'source_second_order_scalar_retarded.py',
        'source_joint_ccr_car_ports.py', 'source_scalar_weyl_symbol.py', 'source_common_weyl_symbol.py',
        'source_clock_symbol_recursion.py', 'source_local_scalar_retarded_identification.json',
        'source_second_order_scalar_retarded.json']
    out = {'root': ROOT_ID, 'scope': 'SOURCE_BOSONIC_SCALAR61_ACCELERATION_AND_REFERENCE_RETARDED_FEEDBACK',
        'source_sha256': bound['source_sha256'],
        'input_sha256': {str((HERE/p).relative_to(ROOT)): hashlib.sha256((HERE/p).read_bytes()).hexdigest() for p in paths},
        'exact_moyal_formula': formula,
        'source_metric': {'full94_principal_entries': len(jet.K.todok()), **report,
            'actual_scalar61_third_order': encode(third[:61, :]),
            'actual_gauge_third_order_countercontrol': encode(third[61:, :]),
            'all100_first_metric_columns': len(derivatives)},
        'central_gradient_all61': {str(k-6): str(v) for k, v in gradients.items()},
        'actual_scalar_bosonic_acceleration': encode(central),
        'actual_scalar_reference_remainder': encode(central),
        'fresh_nonzero_canonical_momenta100': list(map(str, momentum)),
        'full_quadratic_momentum_feedback': encode(nonlinear),
        'same_source70_forcing': encode(lifted), 'reference_kernel_consumers': responses,
        'public_mouth': 'SourceBosonicSecondOrderFeedback.{acceleration,remainder,source70,full_source_symbols,response_jet}; coefficients and gradients are generated internally from the original source.',
        'reference_equation': 'd2_t x-A_reference*x=R_B(z,pi)+S; source70=R*(R_B+S)/N. A_reference is the original classical scalar linearization; R_B retains the complete bosonic ordering, nonlinear and Moyal terms.',
        'consumer_scope': 'Zero physical spatial momentum, unchanged source time column; the eight kernel jets act on the actual nonzero background remainder. A time-dependent nonlinear history uses these same source evaluators in the retarded equation, not a constant-force replacement for the full H flow.',
        'proton_lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_bosonic_second_order_feedback.json').write_text(json.dumps(out, indent=2)+'\n')
    print('PASS full bosonic scalar feedback and same original retarded consumer', out['seconds'], flush=True)


if __name__ == '__main__':
    main()
