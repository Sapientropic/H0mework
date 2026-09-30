#!/usr/bin/env python3
"""Audit native force transport by implicit source equations and two inverses.

The inverse third contraction comes from C exp(-alpha.L)b, independently of
the forward inverse-curvature construction. Current coefficients are rebuilt
from separate original normal9 and residual3 momentum equations. Occupation
bits then consume a fresh mixed germ and the unchanged original raw forces.
"""
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_current_native_force_transport import SourceCurrentNativeForceTransport
from independent_source_full_gauss_section import RawFullSection
from independent_source_joint_form_hamiltonian import raw_gauge_coefficients
from independent_source_lorentz_quantum_section import BitAction, total, equal
from independent_source_gauge_legendre import ETA


def clean(A):
    return s.SparseMatrix(A).applyfunc(s.cancel)


def same(left, right):
    assert not total((1, left), (-1, right))


def trace(A, B):
    return sum(v*B[i, j] for (i, j), v in A.todok().items())


def source_inverse_contract(model, raw, G):
    """Differentiate the original implicit slice equation before contraction."""
    V = clean(s.Matrix.hstack(*(L*raw.b0 for L in raw.L)))
    M = clean(raw.C*V)
    alpha, free = M.gauss_jordan_solve(raw.C)
    assert free.rows == 0
    alpha = clean(alpha)
    equal(alpha, model.chart.alpha)
    z = clean(raw.read*(s.eye(112)-V*alpha))
    equal(z, model.chart.z)
    pairs = {(a, b): clean((raw.L[a]*raw.L[b]+raw.L[b]*raw.L[a])/2)
             for a in range(12) for b in range(a, 12)}
    AG = clean(alpha*G)
    weights = clean(AG*alpha.T)
    group = sum((w*(1 if a == b else 2)*pairs[a, b]
        for (a, b), w in weights.todok().items() if a <= b), s.zeros(112))
    residual = -2*sum((L*G*alpha[a, :].T for a, L in enumerate(raw.L)), s.zeros(112, 1))
    residual += group*raw.b0
    Ha, free = M.gauss_jordan_solve(raw.C*residual)
    assert free.rows == 0
    Ha = clean(Ha)
    Hz = clean(raw.read*(residual-V*Ha))
    equal(Ha.col_join(Hz), model.u)
    third = []
    for k in range(94):
        direction = raw.E[:, 6+k]
        dV = clean(s.Matrix.hstack(*(L*direction for L in raw.L)))
        dM = raw.C*dV
        da, free = M.gauss_jordan_solve(-dM*alpha)
        assert free.rows == 0
        da = clean(da)
        dw = clean(da*G*alpha.T+AG*da.T)
        dres = -2*sum((L*G*da[a, :].T for a, L in enumerate(raw.L)), s.zeros(112, 1))
        dres += group*direction
        dres += sum((w*(1 if a == b else 2)*pairs[a, b]*raw.b0
            for (a, b), w in dw.todok().items() if a <= b), s.zeros(112, 1))
        dHa, free = M.gauss_jordan_solve(raw.C*dres-dM*Ha)
        assert free.rows == 0
        dHa = clean(dHa)
        dHz = clean(raw.read*(dres-dV*Ha-V*dHa))
        row = dHa.col_join(dHz)
        equal(row, model.third[k]); third.append(row)
    return {'all94_original_implicit_inverse_third_contractions': True,
            'nonzero_contracted_entries': sum(len(M.todok()) for M in third)}


class SeparatedMomentumJets:
    """Solve normal9, then residual3; no affine12 inverse is used here."""
    def __init__(self, raw, h00, weight):
        n, old = raw.native, raw.old
        self.free = [j-6 for j in old.free if j >= 6]
        self.piv = [j-6 for j in old.fixed]
        y = old.source[6:, :]
        self.O = n.O
        self.D = clean(n.O.T*s.Matrix.hstack(*(R*n.v for R in n.rhob)))
        self.F = clean(self.D.T.inv())
        self.B = clean(s.Matrix.vstack(*((T*y).T for T in n.Tb)))
        S = clean(s.Matrix.hstack(*(T*y for T in n.Ts)))
        self.U = clean(S[self.piv, :].inv())
        self.T = clean(S[self.free, :]*self.U)
        self.W = clean(self.B[:, self.free]-self.B[:, self.piv]*self.T.T)
        self.reader = s.eye(9).row_join(clean(-self.B[:, self.piv]*self.U.T))
        self.Bg = s.eye(97)[61:, self.piv]
        a = clean(n.Rd.row_join(s.zeros(70, 33))-n.O*self.F*self.W)
        c = clean(-n.O*self.F*self.reader)
        g = clean(s.eye(97)[61:, self.free]-self.Bg*self.T.T)
        d = s.zeros(36, 9).row_join(clean(-self.Bg*self.U.T))
        self.a, self.c = a.col_join(g), c.col_join(d)
        self.weight = s.diag(s.eye(70)/h00, weight)
        self.K = clean(self.a.T*self.weight*self.a/2)
        self.C = clean(self.a.T*self.weight*self.c)
        self.P = clean(self.c.T*self.weight*self.c/2)
        self.jets = []
        self.da, self.dc, self.dK, self.dC, self.dP = [], [], [], [], []
        for u in self.free:
            Dk = clean(n.O.T*s.Matrix.hstack(*(R*n.R[:, u] for R in n.rhob))) if u < 61 else s.zeros(9)
            Bk = clean(s.Matrix.vstack(*(T[:, u].T for T in n.Tb)))
            Sk = clean(s.Matrix.hstack(*(T[:, u] for T in n.Ts)))
            Mk = Sk[self.piv, :]
            Fk = clean(-self.F*Dk.T*self.F)
            Uk = clean(-self.U*Mk*self.U)
            Tk = clean((Sk[self.free, :]-self.T*Mk)*self.U)
            Wk = clean(Bk[:, self.free]-Bk[:, self.piv]*self.T.T-self.B[:, self.piv]*Tk.T)
            rk = s.zeros(9).row_join(clean(-Bk[:, self.piv]*self.U.T-self.B[:, self.piv]*Uk.T))
            ak = clean(-n.O*(Fk*self.W+self.F*Wk)).col_join(clean(-self.Bg*Tk.T))
            ck = clean(-n.O*(Fk*self.reader+self.F*rk)).col_join(
                s.zeros(36, 9).row_join(clean(-self.Bg*Uk.T)))
            self.jets.append((Dk, Bk, Mk, Fk, Uk, Tk, Wk, rk))
            self.da.append(ak); self.dc.append(ck)
            self.dK.append(clean((ak.T*self.weight*self.a+self.a.T*self.weight*ak)/2))
            self.dC.append(clean(ak.T*self.weight*self.c+self.a.T*self.weight*ck))
            self.dP.append(clean((ck.T*self.weight*self.c+self.c.T*self.weight*ck)/2))
        self.divK = clean(sum((K[:, j] for j, K in enumerate(self.dK)), s.zeros(94, 1)))
        self.divC = clean(sum((C[j, :].T for j, C in enumerate(self.dC)), s.zeros(12, 1)))

    def second(self, i, j):
        Di, Bi, Mi, Fi, Ui, Ti, Wi, ri = self.jets[i]
        Dj, Bj, Mj, Fj, Uj, Tj, Wj, rj = self.jets[j]
        Fij = clean(-Fi*Dj.T*self.F-self.F*Dj.T*Fi)
        Uij = clean(-Ui*Mj*self.U-self.U*Mj*Ui)
        Tij = clean(-(Ti*Mj+Tj*Mi)*self.U)
        Wij = clean(-Bi[:, self.piv]*Tj.T-Bj[:, self.piv]*Ti.T-self.B[:, self.piv]*Tij.T)
        rij = s.zeros(9).row_join(clean(-Bi[:, self.piv]*Uj.T-Bj[:, self.piv]*Ui.T-self.B[:, self.piv]*Uij.T))
        aij = clean(-self.O*(Fij*self.W+Fi*Wj+Fj*Wi+self.F*Wij)).col_join(clean(-self.Bg*Tij.T))
        cij = clean(-self.O*(Fij*self.reader+Fi*rj+Fj*ri+self.F*rij)).col_join(
            s.zeros(36, 9).row_join(clean(-self.Bg*Uij.T)))
        return aij, cij

    def second_divergences(self):
        ddivK, ddivC = s.zeros(94), s.zeros(94, 12)
        Wa, Wc = self.weight*self.a, self.weight*self.c
        Wda, Wdc = [self.weight*a for a in self.da], [self.weight*c for c in self.dc]
        for k in range(94):
            for j in range(k, 94):
                a2, c2 = self.second(k, j)
                for axis, col in ([(k, j)] if k == j else [(k, j), (j, k)]):
                    v = (a2.T*Wa[:, col]+self.a.T*self.weight*a2[:, col]+
                        self.da[k].T*Wda[j][:, col]+self.da[j].T*Wda[k][:, col])/2
                    ddivK[axis, :] += v.T
                    ddivC[axis, :] += a2[:, col].T*Wc+self.da[k][:, col].T*Wdc[j]+\
                        self.da[j][:, col].T*Wdc[k]+Wa[:, col].T*c2
            if k in (30, 60, 93): print('PASS separated original inverse second contraction', k+1, '/94', flush=True)
        return clean(ddivK), clean(ddivC)


def literal_density(raw):
    z = s.Matrix(s.symbols('audit_native_z0:100', real=True))
    base = raw.offset+raw.E*z
    orbit = s.Matrix.hstack(*(L*base for L in raw.L))
    M = raw.C*orbit
    rho = -s.factor(M[9:, 9:].det())
    point = dict(zip(z, raw.z0)); rho0 = rho.subs(point)
    assert rho0 > 0
    variables = list(z[6:, :]); log_density = s.log(rho)/2
    ell = s.Matrix([s.diff(log_density, x).subs(point) for x in variables])
    H = s.Matrix(94, 94, lambda i, j: s.diff(log_density, variables[i], variables[j]).subs(point))
    third = [s.zeros(94) for _ in variables]
    support = [i for i, x in enumerate(variables) if x in rho.free_symbols]
    for k in support:
        for i in support:
            for j in support:
                third[k][i, j] = s.diff(log_density, variables[k], variables[i], variables[j]).subs(point)
    return clean(ell), clean(H), third, str(rho)


def independent_apply(fields, charges, bits, values, gradients, Hessians):
    second, first, identity, cross, zero, pair = fields
    output = []
    for word in set(values)|set(gradients)|set(Hessians):
        f = values.get(word, 0); g = gradients.get(word, s.zeros(100, 1))[6:, :]
        h = Hessians.get(word, s.zeros(100))[6:, 6:]
        output.append((trace(second, h)+(first.T*g)[0]+identity*f, {word: 1}))
        coefficients = cross.T*g+zero*f
        for a, c in enumerate(coefficients):
            if c: output.append((c, bits.Q(charges[a], {word: 1})))
        if f:
            for (a, b), c in pair.todok().items():
                output.append((f*c, bits.Q(charges[a], bits.Q(charges[b], {word: 1}))))
    return total(*output)


def main():
    began = time.monotonic()
    path = HERE/'source_current_native_force_transport.json'
    receipt = json.loads(path.read_text()); count = 0
    for key in ('source_sha256', 'input_sha256'):
        for name, digest in receipt[key].items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
            count += 1
    model = SourceCurrentNativeForceTransport()
    raw = RawFullSection()
    equal(raw.z0, model.current.point)
    for R, Q in zip(raw.R, model.model.leaf.charges): equal(s.I*R, Q)
    bg = json.loads((HERE.parent/'active-gauge/receipt.json').read_text())['actual_background']
    e = s.Matrix(bg['coframe']).applyfunc(s.sympify)
    A = s.Matrix(bg['gauge_connection']).applyfunc(s.sympify)[1:, :]
    metric = clean(s.Abs(e.det())*e.inv()*ETA*e.inv().T)
    gauge = raw_gauge_coefficients(e, A, raw.native)
    G = s.diag(s.zeros(6), s.eye(70)/metric[0, 0], gauge['weight'])
    inverse = source_inverse_contract(model, raw, G)
    print('PASS independent implicit inverse3 full94', flush=True)
    jets = SeparatedMomentumJets(raw, metric[0, 0], gauge['weight'])
    equal(jets.K, model.K); equal(jets.C, model.C); equal(jets.P, model.P)
    equal(jets.divK, model.Kdiv); equal(jets.divC, model.Cdiv)
    for k in range(94):
        equal(jets.dK[k], model.principal.K1[k]); equal(jets.dC[k], model.C1[k]); equal(jets.dP[k], model.P1[k])
    ddivK, ddivC = jets.second_divergences()
    equal(ddivK, model.ddivK); equal(ddivC, model.ddivC)
    ell, logH, logH1, rho = literal_density(raw)
    equal(ell, model.ell); equal(logH, model.logH)
    fields = []
    for k in range(94):
        dk, dc, dp, ek = jets.dK[k], jets.dC[k], jets.dP[k], logH[:, k]
        identity = s.cancel(2*(ek.T*jets.K*ell)[0]+(ell.T*dk*ell)[0]+\
            (ddivK[k, :]*ell)[0]+(jets.divK.T*ek)[0]+trace(dk, logH)+trace(jets.K, logH1[k]))
        row = (-dk, -ddivK[k, :].T, identity, -s.I*dc, -s.I*ddivC[k, :].T/2, dp)
        for actual, expected in zip(row, model.current_derivative[k].fields()):
            if isinstance(actual, s.MatrixBase): equal(actual, expected)
            else: assert s.cancel(actual-expected) == 0
        fields.append(row)
    print('PASS all94 independent differential-current force coefficients and original rho3 third jet', flush=True)
    values = {(): s.Rational(3, 17), (23, 308): s.Rational(5, 19), (91,): s.S.Zero}
    gradients, Hessians = {}, {}
    for a, word in enumerate(values):
        gradients[word] = s.Matrix([s.Rational((j+2*a) % 7-3, 73)+s.I*s.Rational((2*j+a) % 5-2, 79) for j in range(100)])
        v = s.Matrix([s.Rational((j+a) % 5-2, 83) for j in range(100)])
        Hessians[word] = v*v.T-s.eye(100)/89
    generated = model.generate(values, gradients, Hessians)
    bits = BitAction(); charges = [s.I*R for R in raw.R]
    raw_jet = generated['source122_jet']; data = model.raw_data
    raw_values = {w: r['value'] for w, r in raw_jet.items() if r['value']}
    raw106 = []
    for k in range(106):
        boson = {w: data['identity_force'][k]*r['value']+(data['first_force'][k, :]*r['gradient'][16:, :])[0]
                 for w, r in raw_jet.items()}
        force = total((1, boson), (1, bits.Q(data['onebody_force'][k], raw_values)))
        same(force, generated['raw106_forces'][k]); raw106.append(force)
    counts, defects = [], []
    embedding = raw.E[6:, 6:]
    for k, row in enumerate(generated['native_forces']):
        original = total(*((c, raw106[j]) for j, c in enumerate(embedding[:, k]) if c))
        derivative = independent_apply(fields[k], charges, bits, values, gradients, Hessians)
        force = total((1, original), (-1, derivative))
        same(force, row['current_native_force']); same(force, row['transported_current_native_force'])
        counts.append(len(force))
        defects.append(len(total((1, original), (1, row['source_ordering_gap_derivative']), (-1, force))))
    assert any(defects) and {len(w) for r in generated['native_forces'] for w in r['current_native_force']} == {0, 1, 2}
    empty = model.generate({}, {}, {})
    assert not empty['source122_jet'] and not any(empty['raw106_forces'])
    assert all(not row[key] for row in empty['native_forces'] for key in row if key != 'current_axis')
    paths = [Path(__file__), path, HERE/'source_current_native_force_transport.py',
        HERE/'independent_source_full_gauss_section.py', HERE/'independent_source_quantum_gauss_section.py',
        HERE/'independent_source_joint_form_hamiltonian.py', HERE/'independent_source_lorentz_quantum_section.py',
        HERE/'source_full_native_quantum_force.json', HERE/'independent_source_full_native_quantum_force.json']
    result = {'root': ROOT_ID, 'verdict': 'CERTIFIED_SOURCE_CURRENT_ALL94_NATIVE_FORCE_TRANSPORT',
        'source_sha256': receipt['source_sha256'], 'candidate_binding_checks': count,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'implicit_inverse3': inverse,
        'separated_original_normal9_and_residual3_jets': {'all94_K_C_P_first_derivatives': True,
            'all94_divK_divC_derivatives': True, 'rho3_literal_determinant': rho,
            'density_third_jet_generated': True, 'all94_full_operator_coefficient_matches': True},
        'independent_bit_CAR_fresh_germ': {'particle_numbers': [0, 1, 2],
            'raw106_matches': True, 'current94_output_words': counts, 'drop_chain_defect_words': defects},
        'empty_germ_zero': True, 'caller_supplied_force_or_third_input_jet': False,
        'scope': 'Actual source point, K=0, original100 raw two-jet to current94 native forces and fixed fullPi106; inverse3 is source-generated.',
        'seconds': round(time.monotonic()-began, 3)}
    Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS independent all94 native force transport', result['seconds'], flush=True)


if __name__ == '__main__':
    main()
