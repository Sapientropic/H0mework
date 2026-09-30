#!/usr/bin/env python3
"""Live original four-energy differential coefficients and genuine output jets.

The native Weyl div-div correction cancels when returning to coefficient-left
order. Only the original12 orbit inverse and its first jet are needed to
generate H itself; further coefficient derivatives come from that live family.
"""
from collections import Counter
from dataclasses import dataclass
from functools import lru_cache
from itertools import product
import math
import hashlib
import json
import time
import sympy as s

from source_full_gauss_section import SourceFullGaussSection
from source_quantum_ordered_temporal import SourceTemporalQuantumFamily
from source_joint_ccr_car_ports import NormalSymbol
from source_gauss_quantum_current import apply_superposition, weighted_sum, normal_pair
from source_lorentz_contact import equal, ETA, GAMMA
from source_quantum_temporal_symbol import N
from dynamic import HERE, ROOT, ROOT_ID, decode
from source_joint_form_hamiltonian import read_bound
from source_gauss_quantum_current import encode_state
from source_lorentz_contact import encode


def clean(A): return s.SparseMatrix(A).applyfunc(lambda x: s.cancel(s.expand(x)))
def total(terms): return weighted_sum(terms)
def full(A): return s.SparseMatrix(504, 504, {(63*i+k, 63*j+k): v for (i, j), v in A.todok().items() for k in range(63)})


@dataclass
class DifferentialCAR:
    principal: s.MatrixBase
    first: s.MatrixBase
    current: tuple
    zero: NormalSymbol

    def apply(self, value, gradient, Hessian):
        scalar = {}
        for word in set(value)|set(gradient)|set(Hessian):
            g, h = gradient.get(word, s.zeros(100, 1)), Hessian.get(word, s.zeros(100))
            scalar[word] = -sum(v*h[i, j] for (i, j), v in self.principal.todok().items())+(self.first.T*g)[0]
        terms = [(1, scalar), (self.zero.scalar, value), (1, apply_superposition(self.zero.one_body, value))]
        # Exact CAR reduction already expands the algebraic coefficients.
        # Factoring those numbers can invoke an unrelated minimal-polynomial search.
        for c, A, B in self.zero.pairs:
            terms += [(c*v, normal_pair(A, B, w)) for w, v in value.items()]
        for j, M in enumerate(self.current):
            g = {w: v[j] for w, v in gradient.items() if v[j]}
            if g: terms.append((-s.I, apply_superposition(M, g)))
        return total(terms)


class QuadraticInput:
    """The actual local polynomial f(h)=f0+g.h+h.H.h/2, not missing jets."""
    def __init__(self, value, gradient, Hessian):
        self.value, self.gradient, self.Hessian = value, gradient, Hessian

    def partial(self, indices):
        if any(j >= 100 for j in indices): return {}
        if not indices: return self.value
        if len(indices) == 1: return {w: g[indices[0]] for w, g in self.gradient.items() if g[indices[0]]}
        if len(indices) == 2: return {w: h[indices[0], indices[1]] for w, h in self.Hessian.items() if h[indices[0], indices[1]]}
        return {}


def derivative_splits(indices):
    counts = Counter(indices); axes = sorted(counts)
    for degrees in product(*(range(counts[j]+1) for j in axes)):
        left = tuple(j for j, n in zip(axes, degrees) for _ in range(n))
        right = tuple(j for j, n in zip(axes, degrees) for _ in range(counts[j]-n))
        yield math.prod(math.comb(counts[j], n) for j, n in zip(axes, degrees)), left, right


class SourceLiveDifferentialHamiltonian:
    def __init__(self): self._initialize(SourceFullGaussSection())

    @classmethod
    def from_generated_full(cls, full_source):
        value = cls.__new__(cls); value._initialize(full_source); return value

    def _initialize(self, full_source):
        self.full = full_source
        self.family = SourceTemporalQuantumFamily(full_source.native)
        self.q = full_source.native.joint.coframe.q
        self.source_configuration = tuple(full_source.z0)
        self.source_time = (N, s.S.Zero, s.S.Zero, s.S.Zero)
        self.E, self.R, self.C = full_source.embedding[6:, 6:], full_source.retraction[6:, 6:], full_source.constraint[:, 6:]
        self.L = [A[6:, 6:] for A in full_source.L]
        self.V1 = [clean(s.Matrix.hstack(*(L*self.E[:, k] for L in self.L))) for k in range(94)]
        self.M1 = [clean(self.C*V) for V in self.V1]
        self.charges = tuple(clean(s.I*R) for R in full_source.R)
        self.identity = s.SparseMatrix(s.eye(504))
        self.cf_div = clean(s.Matrix([sum(self.family.cf['K'][i, j].diff(self.q[i]) for i in range(6)) for j in range(6)]))
        self.cf_current = [clean((M+M.H)/2) for M in self.family.cf['M']]
        equal(clean(sum((M.diff(self.q[j]) for j, M in enumerate(self.cf_current)), s.zeros(8))), s.zeros(8))
        self.density_axes = {67+full_source.gauge_free.index(1): s.S.One,
                             67+full_source.gauge_free.index(12): s.Rational(1, 2)}

    def _four_energies(self, base, q, A, time_column):
        """Contract original source tensors after cancelling their small inverses.

        The BF numerator is the original X^T eta X numerator, not an
        inverse-metric Maxwell replacement. The full12 inverse below already
        supplies the momentum graph, so its separate9 inverse is not rebuilt.
        """
        at = dict(zip(self.q, q))|dict(zip(self.family.y, time_column))
        def ev(value):
            if isinstance(value, list): return [ev(v) for v in value]
            if isinstance(value, s.MatrixBase): return clean(value.subs(at))
            return s.cancel(value.subs(at))
        e = ev(self.family.e); volume = s.cancel(e.det()); inverse = clean(e.inv(method='DM'))
        metric = clean(volume*inverse*ETA*inverse.T)
        common = self.full.native.joint.common; phi = base[6:76, :]
        RA = [clean(sum((A[i, a]*common.scalar.rho[a] for a in range(12)), s.zeros(70))) for i in range(3)]
        U = [R*phi for R in RA]
        shift = clean(sum((metric[0, i+1]*U[i] for i in range(3)), s.zeros(70, 1)))
        ds = s.zeros(70, 94)
        for i in range(3):
            ds += metric[0, i+1]*RA[i]*self.E[:70, :]
            for a in range(12): ds += metric[0, i+1]*(common.scalar.rho[a]*phi)*self.E[70+12*i+a, :]
        scalar_potential = s.cancel(volume*((phi-common.scalar.vacuum).T*(phi-common.scalar.vacuum))[0]-
            sum(metric[i+1, j+1]*(U[i].T*U[j])[0] for i in range(3) for j in range(3))/2)
        gauge = self.full.native.joint.gauge; source = gauge.source
        kernel = clean(source.at(source.kernel_numerator, e)/volume)
        G = clean(s.kronecker_product(clean(kernel[:3, :3].inv(method='DM')), source.gram_inverse))
        field_at = dict(zip(gauge.coordinates, A))
        magnetic = clean(gauge.magnetic.subs(field_at)); dm = clean(gauge.magnetic_derivative.subs(field_at))
        gs = clean(kernel[:3, 3:]*magnetic*source.gram).reshape(36, 1)
        dgs = clean(s.kronecker_product(kernel[:3, 3:], source.gram)*dm*self.E[70:, :])
        gauge_potential = s.cancel(-sum(a*b for a, b in zip(magnetic, kernel[3:, 3:]*magnetic*source.gram))/2)
        D = [clean(s.I*volume*sum((inverse[mu, a]*GAMMA[a] for a in range(4)), s.zeros(4))) for mu in range(4)]
        Ei = clean(D[0].inv(method='DM')); matter = s.SparseMatrix.zeros(252)
        for i in range(3):
            rho = clean(sum((A[i, a]*common.rho[a][:63, :63] for a in range(12)), s.zeros(63)))
            matter += s.kronecker_product(clean(-s.I*Ei*D[i+1]), rho)
        Y = clean(sum(((phi[a]+s.I*phi[35+a])*common.yukawa_basis[a] for a in range(35)), s.zeros(252)))
        matter = clean(matter+s.kronecker_product(clean(-s.I*volume*Ei), s.SparseMatrix.eye(63))*Y)
        return {'coframe': {key: ev(self.family.cf[key]) for key in ('K', 'one_body', 'correction', 'J', 'W')},
            'weight': s.SparseMatrix.diag(s.eye(70)/metric[0, 0], G),
            'shift': shift.col_join(gs), 'shift_derivative': clean(ds.col_join(dgs)),
            'potential': scalar_potential+gauge_potential,
            'matter_CAR': s.SparseMatrix.diag(matter, -matter.conjugate())}

    @lru_cache(maxsize=32)
    def coefficients(self, configuration, time_column=None):
        configuration = tuple(map(s.sympify, configuration))
        time_column = self.source_time if time_column is None else tuple(map(s.sympify, time_column))
        assert len(configuration) == 100 and len(time_column) == 4
        base = clean(self.full.offset+self.full.embedding*s.Matrix(configuration))
        q = tuple(base[:6, :]); A = base[76:, :].reshape(3, 12)
        V = clean(s.Matrix.hstack(*(L*base[6:, :] for L in self.L)))
        inverse = clean((self.C*V).inv(method='DM')); alpha = clean(inverse*self.C)
        a = clean((self.R*(s.eye(106)-V*alpha)).T); b = clean(-alpha.T)
        equal(clean(self.E.T*a), s.eye(94)); equal(clean(self.E.T*b), s.zeros(94, 12))
        data = self._four_energies(base, q, A, time_column)
        cf, G, shift, dshift = data['coframe'], data['weight'], data['shift'], data['shift_derivative']
        K, C, P = clean(a.T*G*a/2), clean(a.T*G*b), clean(b.T*G*b/2)
        div_a, divK, divC = s.zeros(106, 1), s.zeros(94, 1), s.zeros(12, 1)
        for k, (V1, M1) in enumerate(zip(self.V1, self.M1)):
            dalpha = clean(-inverse*M1*alpha)
            da = clean(-(self.R*(V1*alpha+V*dalpha)).T); db = clean(-dalpha.T)
            div_a += da[:, k]
            divK += da.T*G*a[:, k]/2
            divC += db.T*G*a[:, k]
        divK = clean(divK+a.T*G*div_a/2); divC = clean(divC+b.T*G*div_a)
        momentum_identity = clean(-a.T*G*shift)
        div_identity = s.cancel(-(div_a.T*G*shift)[0]-sum((a[:, k].T*G*dshift[:, k])[0] for k in range(94)))
        ell, logH = s.zeros(94, 1), s.zeros(94)
        for j, power in self.density_axes.items():
            ell[j-6] = power/configuration[j]; logH[j-6, j-6] = -power/configuration[j]**2
        density = s.cancel((ell.T*K*ell)[0]+(divK.T*ell)[0]+sum(v*logH[i, j] for (i, j), v in K.todok().items()))
        linear_current = clean(-b.T*G*shift-s.I*divC/2)
        v = q[0]*q[2]*q[5]; n = time_column[0]
        constant = s.cancel(data['potential']+
            (shift.T*G*shift)[0]/2+density-s.I*div_identity/2+n*(s.Rational(3, 2)/v+3*v))
        one_body = clean(data['matter_CAR']+full(cf['one_body']+cf['correction'])+n*s.Rational(21, 16)/v*self.identity)
        one_body += sum((weight*self.charges[h] for h, weight in enumerate(linear_current) if weight), s.SparseMatrix.zeros(504))
        pairs = [(n*s.Rational(3, 16)/v, self.identity, self.identity)]
        for (h, k), weight in P.todok().items():
            one_body += weight*self.charges[h]*self.charges[k]
            pairs.append((weight, self.charges[h], self.charges[k]))
        currents = [full(Q) for Q in cf['J']]
        pairs += [(weight, currents[h], currents[k]) for (h, k), weight in cf['W'].todok().items()]
        at = dict(zip(self.q, q))|dict(zip(self.family.y, time_column))
        current = [full(clean(M.subs(at))) for M in self.cf_current]
        current += [clean(sum((weight*self.charges[h] for h, weight in enumerate(C[j, :]) if weight), s.SparseMatrix.zeros(504))) for j in range(94)]
        principal = s.diag(cf['K'], K)
        first = -clean(self.cf_div.subs(at)).col_join(divK+s.I*momentum_identity)
        return DifferentialCAR(clean(principal), clean(first), tuple(current), NormalSymbol(constant, clean(one_body), tuple(pairs)))

    @lru_cache(maxsize=128)
    def coefficient_derivative(self, configuration, indices, time_column=None):
        """Ports0..99 are configuration;100..103 are the original time column."""
        indices = tuple(sorted(indices))
        if not indices: return self.coefficients(configuration, time_column)
        assert all(0 <= j < 104 for j in indices)
        point = tuple(configuration)+(self.source_time if time_column is None else tuple(time_column))
        variables = {j: s.Dummy('live_port_'+str(j), positive=True) if j in (0, 2, 5, 100) or j in self.density_axes
                     else s.Dummy('live_port_'+str(j), real=True) for j in set(indices)}
        argument = tuple(variables.get(j, v) for j, v in enumerate(point))
        data = self.coefficients(argument[:100], argument[100:]); at = {variable: point[j] for j, variable in variables.items()}
        def differentiate(A):
            for j in indices: A = A.diff(variables[j])
            return clean(A.subs(at))
        zero = data.zero
        for j in indices: zero = zero.derivative(variables[j])
        zero = NormalSymbol(s.cancel(zero.scalar.subs(at)), clean(zero.one_body.subs(at)),
            tuple((s.cancel(c.subs(at)), clean(A.subs(at)), clean(B.subs(at))) for c, A, B in zero.pairs))
        return DifferentialCAR(differentiate(data.principal), differentiate(data.first),
                               tuple(differentiate(M) for M in data.current), zero)

    def action_jet(self, configuration, input_jet, indices=(), time_column=None):
        """Leibniz generates output derivatives from genuine input derivatives."""
        result = []
        for weight, coefficient_indices, input_indices in derivative_splits(indices):
            data = self.coefficient_derivative(tuple(configuration), coefficient_indices, time_column)
            f = input_jet.partial(input_indices)
            g, H = {}, {}
            for j in range(100):
                for w, v in input_jet.partial(input_indices+(j,)).items():
                    g.setdefault(w, s.zeros(100, 1)); g[w][j] = v
            # Only the generated principal support enters this contraction.
            for (j, k), c in data.principal.todok().items():
                if not c: continue
                for w, v in input_jet.partial(input_indices+(j, k)).items():
                    H.setdefault(w, s.zeros(100)); H[w][j, k] = v
            result.append((weight, data.apply(f, g, H)))
        return total(result)


def main(hamiltonian=None):
    began = time.monotonic()
    from source_native_chi_euler_forcing import joint_source_germ
    native = read_bound('source_current_native_force_transport')
    coframe = read_bound('source_current_coframe_force_transport')
    temporal = read_bound('source_temporal_lorentz_balance')
    for name in ('source_current_native_force_transport', 'source_current_coframe_force_transport',
                 'source_temporal_lorentz_balance', 'source_common_weyl_symbol'):
        read_bound('independent_'+name) if (HERE/('independent_'+name+'.json')).exists() else None
    state = lambda rows: {tuple(w): s.sympify(c) for w, c in rows}
    m = SourceLiveDifferentialHamiltonian() if hamiltonian is None else hamiltonian
    z = m.source_configuration
    source = joint_source_germ(); f = QuadraticInput(source.value, source.gradient, source.Hessian)
    Hf = m.action_jet(z, f)
    assert total([(1, Hf), (-1, state(temporal['current_H']))]) == {}
    old = [state(row['current_q_force']) for row in coframe['actual_consumer']['all6_current_force_returns']]
    old += [state(row['current_native_force']) for row in native['actual_source_consumer']['all94_force_returns']]
    force, output = [], []
    for j in range(104):
        d = m.coefficient_derivative(z, (j,), None)
        value = total([(-1, d.apply(f.value, f.gradient, f.Hessian))]); force.append(value)
        if j < 100: assert total([(1, value), (-1, old[j])]) == {}
        else: assert total([(1, value), (-1, state(temporal['forces_minus_time_derivative'][j-100]))]) == {}
        output.append(m.action_jet(z, f, (j,)))
        if j in (5, 36, 66, 99, 103): print('PASS live original coefficient and output jets', j+1, '/104', flush=True)
    row = read_bound('source_common_weyl_symbol')['actual_consumer']
    q, A = tuple(map(s.sympify, row['q'])), decode(row['A36']).reshape(36, 1)
    off = tuple(s.Matrix(q).col_join(decode(row['x61'])).col_join(A[m.full.gauge_free, :]))
    timepoint = tuple(map(s.sympify, row['time'])); word = tuple(row['input_CAR'])
    test = QuadraticInput({word: s.S.One}, {word: decode(row['gradient100'])}, {word: decode(row['Hessian100'])})
    image = m.action_jet(off, test, time_column=timepoint)
    assert total([(1, image), (-1, state(row['original_H']))]) == {}
    # This is an actual off-source polynomial input, with all its derivatives.
    mixed = {}
    for indices in ((0,), (68,), (101,), (0, 68), (68, 68), (0, 101)):
        mixed[','.join(map(str, indices))] = encode_state(m.action_jet(off, test, indices, timepoint))
        print('PASS off-source genuine output jet', indices, flush=True)
    names = ('source_live_differential_hamiltonian.py', 'source_full_gauss_section.py',
        'source_quantum_ordered_temporal.py', 'source_joint_ccr_car_ports.py',
        'source_gauge_legendre.py', 'source_gauge_quantum_energy.py',
        'source_common_hamiltonian.py', 'source_scalar_legendre.py',
        'source_current_native_force_transport.json', 'independent_source_current_native_force_transport.json',
        'source_current_coframe_force_transport.json', 'independent_source_current_coframe_force_transport.json',
        'source_temporal_lorentz_balance.json', 'independent_source_temporal_lorentz_balance.json',
        'source_common_weyl_symbol.json', 'source_joint_current_hilbert_section.json')
    out = {'root': ROOT_ID, 'scope': 'LIVE_ORIGINAL_FOUR_ENERGY_DIFFERENTIAL_OPERATOR_AND_GENUINE_OUTPUT_JETS',
        'source_sha256': m.full.native.graph.common.source_hashes,
        'input_sha256': {str((HERE/n).relative_to(ROOT)): hashlib.sha256((HERE/n).read_bytes()).hexdigest() for n in names},
        'coefficient_mouth': 'Original12 CV inverse and its first derivative generate the same coefficient-left H at every regular admitted z100 and original time column. The native divdivK/4 Weyl correction cancels in differential order.',
        'jet_mouth': 'Differentiate the generated coefficient family; complete multi-index Leibniz consumes input derivatives through order |alpha|+2. No output jet is supplied.',
        'source': {'configuration100': list(map(str, z)), 'H': encode_state(Hf),
            'negative_coefficient_derivative104': [encode_state(v) for v in force],
            'output_first_jet104': [encode_state(v) for v in output],
            'all100_signed_current_forces_and_four_time_forces_recovered': True},
        'off_source': {'configuration100': list(map(str, off)), 'time4': list(map(str, timepoint)),
            'values': encode_state(test.value), 'gradient100': [[list(w), encode(g)] for w, g in test.gradient.items()],
            'Hessian100': [[list(w), encode(h)] for w, h in test.Hessian.items()],
            'H': encode_state(image), 'output_jets': mixed},
        'input_scope': 'Displayed consumers are genuine local quadratic polynomials. The operator and derivative generator accept arbitrary finite CAR input derivative providers.',
        'source_occurrence_order_pairing_clock_unchanged': True,
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'source_live_differential_hamiltonian.json').write_text(json.dumps(out, separators=(',', ':'))+'\n')
    print('PASS live original differential Hamiltonian', out['seconds'], flush=True)


if __name__ == '__main__': main()
