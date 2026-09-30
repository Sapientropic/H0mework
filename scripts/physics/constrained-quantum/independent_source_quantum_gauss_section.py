#!/usr/bin/env python3
"""Independent implicit-slice and CAR-jet audit of a local Gauss section.

The section producer is not imported. Its field group action is regenerated
from native representations, the gauge parameters are obtained by implicit
differentiation, and exterior-slot CAR pays the two-jet representation action.
"""
from __future__ import annotations

from collections import defaultdict
import itertools
import hashlib
import json
import time

import sympy as s

from independent_source_quantum_stabilizer import (
    OriginalStabilizer, RawLiveCoefficients, HERE, ROOT, ROOT_ID,
    bindings, clean, rational, eq, decode, encode, terms, current,
    polynomial_action, gauge_coefficients, raw_matter, state_encode)
from independent_source_gauss_quantum_current import decoded_state


def dot(a, b): return sum(x*y for x, y in zip(a, b))
def zero(x): assert s.cancel(x) == 0


def normalize_state(values):
    return {word: s.cancel(value) for word, value in values.items() if s.cancel(value) != 0}


class RawGaussSection:
    def __init__(self):
        self.native = OriginalStabilizer()
        self.T = [s.diag(s.zeros(6), T) for T in self.native.Ts]
        self.r = [clean(-s.I*Q) for Q in self.native.Qs]
        active = json.loads((HERE.parent/'active-gauge/receipt.json').read_text())
        background = active['actual_background']
        e0 = s.Matrix(background['coframe']).applyfunc(s.sympify)
        A0 = s.Matrix(background['gauge_connection']).applyfunc(s.sympify)
        self.source = s.Matrix.vstack(s.Matrix([e0[j] for j in (5, 9, 10, 13, 14, 15)]),
                                     s.zeros(61, 1), A0[1:, :].reshape(36, 1))
        source_orbit = clean(s.Matrix.hstack(*(T*self.source for T in self.T)))
        self.fixed = [67+j for j in source_orbit[67:, :].T.rref()[1]]
        assert len(self.fixed) == 3
        self.free = [j for j in range(103) if j not in self.fixed]
        self.reader = s.eye(103)[self.fixed, :]
        self.free_reader = s.eye(103)[self.free, :]
        self.source_minor = source_orbit[self.fixed, :]
        assert self.source_minor.det() != 0
        self.native.x_symbols = s.Matrix(s.symbols('raw_x0:61', real=True))
        phi = self.native.v+self.native.R*self.native.x_symbols
        self.native.Dsymbol = clean(self.native.O.T*s.Matrix.hstack(*(T*phi for T in self.native.rhob)))

    def implicit_jets(self, y):
        """Solve derivatives of E exp(-alpha.T)y = source fixed positions."""
        eq(self.reader*(y-self.source), s.zeros(3, 1))
        V = clean(s.Matrix.hstack(*(T*y for T in self.T)))
        M = V[self.fixed, :]
        a, parameters = M.gauss_jordan_solve(self.reader)
        assert parameters.rows == 0; a = rational(a)
        tangent = clean(s.eye(103)-V*a)
        eq(self.reader*tangent, s.zeros(3, 103))
        Halpha = [s.zeros(103) for _ in range(3)]
        # Each of the three original slice equations is a polynomial in the
        # 2-jet, and the same nonzero source minor solves every RHS.
        forcing = []
        for k in range(3):
            form = s.zeros(103)
            for h, T in enumerate(self.T):
                row = self.reader[k, :]*T
                form -= row.T*a[h, :]+a[h, :].T*row
            for h, T in enumerate(self.T):
                for ell, U in enumerate(self.T):
                    coefficient = (self.reader[k, :]*(T*U+U*T)*y)[0]/2
                    form += coefficient*a[h, :].T*a[ell, :]
            forcing.append(clean(form))
        for i in range(103):
            for j in range(i, 103):
                rhs = s.Matrix([F[i, j] for F in forcing])
                if not rhs.todok(): continue
                result, params = M.gauss_jordan_solve(rhs); assert params.rows == 0
                for h, value in enumerate(result): Halpha[h][i, j] = Halpha[h][j, i] = s.cancel(value)
        for k in range(3):
            eq(sum((M[k, h]*Halpha[h] for h in range(3)), s.zeros(103)), forcing[k])
        return dict(V=V, M=M, a=a, Halpha=Halpha, tangent=tangent)

    def extension_jet(self, y, value, gradient, Hessian):
        """Arbitrary CAR-valued slice two-jet -> original103 two-jet."""
        geo = self.implicit_jets(y)
        V, a, Ha, tangent = [geo[k] for k in ('V', 'a', 'Halpha', 'tangent')]
        words = set(value)|set(gradient)|set(Hessian)
        output = {}
        def add(word, f=0, g=None, h=None):
            if word not in output: output[word] = [s.S.Zero, s.zeros(103, 1), s.zeros(103)]
            output[word][0] += f
            if g is not None: output[word][1] += g
            if h is not None: output[word][2] += h
        for word in words:
            f0 = value.get(word, s.S.Zero)
            df = self.free_reader.T*gradient.get(word, s.zeros(100, 1))
            ddf = self.free_reader.T*Hessian.get(word, s.zeros(100))*self.free_reader
            scalar_g = clean(tangent.T*df)
            scalar_h = tangent.T*ddf*tangent
            for h, T in enumerate(self.T):
                scalar_h -= (df.T*T*y)[0]*Ha[h]
                row = df.T*T
                scalar_h -= row.T*a[h, :]+a[h, :].T*row
            for h, T in enumerate(self.T):
                for k, U in enumerate(self.T):
                    scalar_h += (df.T*(T*U+U*T)*y)[0]*a[h, :].T*a[k, :]/2
            add(word, f0, scalar_g, clean(scalar_h))
            first = [current(R, {word: 1}) for R in self.r]
            for h in range(3):
                for final, coefficient in first[h].items():
                    add(final, g=f0*coefficient*a[h, :].T,
                        h=coefficient*(f0*Ha[h]+a[h, :].T*scalar_g.T+scalar_g*a[h, :]))
                for k in range(3):
                    sym = terms([(s.Rational(1, 2), current(self.r[h], first[k])),
                                 (s.Rational(1, 2), current(self.r[k], first[h]))])
                    for final, coefficient in sym.items():
                        add(final, h=f0*coefficient*a[h, :].T*a[k, :])
        result = {w: [s.cancel(f), rational(g), rational(h)] for w, (f, g, h) in output.items()
                  if f != 0 or g.todok() or h.todok()}
        # The slice restriction really returns every input coefficient.
        for word, (f, g, h) in result.items():
            zero(f-value.get(word, 0))
            eq(self.free_reader*g, gradient.get(word, s.zeros(100, 1)))
            eq(self.free_reader*h*self.free_reader.T, Hessian.get(word, s.zeros(100)))
        return geo, result

    def Gauss_checks(self, y, jets):
        f0 = normalize_state({w: f for w, (f, _, _) in jets.items()})
        gradients = [{w: g[j] for w, (_, g, _) in jets.items() if g[j] != 0} for j in range(103)]
        V = [T*y for T in self.T]
        for k in range(3):
            directional = normalize_state({w: dot(g, V[k]) for w, (_, g, _) in jets.items()})
            assert terms([(1, directional), (-1, current(self.r[k], f0))]) == {}
            for j in range(103):
                derivative = normalize_state({w: dot(self.T[k][:, j], g)+dot(V[k], h[:, j])
                                               for w, (_, g, h) in jets.items()})
                assert terms([(1, derivative), (-1, current(self.r[k], gradients[j]))]) == {}
            # A direct two-jet readout on an actual one-generator orbit.
            twice = normalize_state({w: (V[k].T*h*V[k])[0]+dot(g, self.T[k]*V[k])
                                     for w, (_, g, h) in jets.items()})
            assert terms([(1, twice), (-1, current(self.r[k], current(self.r[k], f0)))]) == {}
        return {'all3_original_Gauss_values_zero': True, 'all309_first_derivatives_of_Gauss_zero': True,
                'all3_actual_group_orbit_second_derivatives': True}


def general_scalar_action(data, word, f0, gradient, Hessian):
    a, normal, shift = data['a'], data['normal'], data['b']
    denominator = 2*data['h00']; unit = {word: 1}
    charges = [current(Q, unit) for Q in data['Q']]
    scalar = -s.trace((a.T*a)*Hessian)-(data['drift']*gradient)[0]
    scalar += 2*s.I*(shift.T*a*gradient)[0]+f0*(s.I*dot(a, data['db'])+dot(shift, shift))
    first = rational(-2*s.I*gradient.T*a.T*normal-f0*(s.I*data['dc']+2*shift.T*normal))
    square = rational(normal.T*normal)
    return terms([(s.cancel(scalar/denominator+f0*data['potential']), unit)]+
                 [(first[j]/denominator, charges[j]) for j in range(9)]+
                 [(f0*c/denominator, current(data['Q'][i], charges[j])) for (i, j), c in square.todok().items()])


def raw_whole_action(model, y, jets):
    cache_key = tuple(y)
    if not hasattr(model, '_energy_cache'): model._energy_cache = {}
    if cache_key not in model._energy_cache:
        raw_cf = RawLiveCoefficients(); q = tuple(y[:6, 0])
        cf = raw_cf.coefficients(q); e = raw_cf.at(raw_cf.e, q)
        x, A = y[6:67, :], y[67:, :].reshape(3, 12)
        sc = model.native.scalar_data(e, x, A)
        gauge = gauge_coefficients(e, A, model.native.inventory)
        A4 = s.zeros(4, 12); A4[1:, :] = A
        original = raw_matter(e, sc['phi'], A4)
        H = clean(-s.I*original['E_inverse']*original['lower'])
        Q = clean(s.diag(H, -H.conjugate()))
        model._energy_cache[cache_key] = cf, sc, gauge, Q
    cf, sc, gauge, Q = model._energy_cache[cache_key]
    output = dict(coframe=[], scalar=[], gauge=[], matter_without_Lorentz=[])
    for word, (f0, g, h) in jets.items():
        coframe, _ = polynomial_action(cf, word, f0, g[:6, :], h[:6, :6])
        scalar = general_scalar_action(sc, word, f0, g[6:, :], h[6:, 6:])
        weight, shift = gauge['weight'], gauge['shift']
        gv = -s.trace(weight*h[67:, 67:])/2+s.I*(shift.T*weight*g[67:, :])[0]
        gv += f0*(s.I*s.trace(weight*gauge['ds'])/2+(shift.T*weight*shift)[0]/2+gauge['potential'])
        values = (coframe, scalar, {word: s.cancel(gv)}, current(Q, {word: f0}))
        for key, value in zip(output, values): output[key].append((1, value))
    return {key: terms(values) for key, values in output.items()}


def finite_wedge(matrix, word):
    result = {0: s.S.One}
    for j in word:
        next_result = defaultdict(lambda: s.S.Zero)
        for mask, coefficient in result.items():
            for (i, _), value in matrix[:, j].todok().items():
                if mask & (1 << i): continue
                sign = -1 if (mask >> (i+1)).bit_count() % 2 else 1
                next_result[mask | (1 << i)] += sign*coefficient*value
        result = {mask: s.expand(value) for mask, value in next_result.items() if s.expand(value) != 0}
    return {tuple(j for j in range(matrix.rows) if mask & (1 << j)): value for mask, value in result.items()}


def compound(matrix, degree):
    words = list(itertools.combinations(range(matrix.rows), degree))
    index = {word: j for j, word in enumerate(words)}
    entries = {}
    for j, word in enumerate(words):
        for final, value in finite_wedge(matrix, word).items(): entries[index[final], j] = value
    return s.SparseMatrix(len(words), len(words), entries)


def group_checks(model, candidate):
    from independent_source_gauge_legendre import source
    _, _, degrees, _ = source.parse_source(ROOT)
    fund = model.native.fund
    K = [clean(sum((model.native.S[j, h]*fund[j] for j in range(12)), s.zeros(7))) for h in range(3)]
    P = clean(-K[0]*K[0]); eq(P*P, P); assert P.rank() == 2
    for k, encoded in zip(K, candidate['group']['original_fundamental_generators']): eq(k, decode(encoded))
    eq(P, decode(candidate['group']['active_projector']))
    group = lambda u: clean(s.eye(7)-P+u[0]*P+sum((u[h+1]*K[h] for h in range(3)), s.zeros(7)))
    u, v = s.symbols('u0:4', real=True), s.symbols('v0:4', real=True)
    w = [u[0]*v[0]-sum(u[j]*v[j] for j in range(1, 4))]
    for h in range(3):
        w.append(u[0]*v[h+1]+v[0]*u[h+1]+sum(model.native.structure[a][h, b]*u[a+1]*v[b+1]/2
                                            for a in range(3) for b in range(3)))
    eq(group(u)*group(v), group(w))
    norm = sum(j*j for j in u)
    eq(group(u).H*group(u)-s.eye(7), (norm-1)*P)
    zero(group(u).det()-norm)
    zero(s.expand(sum(j*j for j in w)-norm*sum(j*j for j in v)))
    compounds = {d: compound(group(u), d) for d in set(degrees)|{4}}
    internal = s.diag(*(compounds[d] for d in degrees))
    matter = s.diag(*([internal]*4)); CAR = s.diag(matter, matter.conjugate())
    at_identity = dict(zip(u, (1, 0, 0, 0)))
    for h in range(3):
        eq(CAR.diff(u[h+1]).subs(at_identity), model.r[h])
        scalar_derivative = compounds[4].diff(u[h+1]).subs(at_identity)
        from independent_source_gauge_legendre import realify
        eq(realify(scalar_derivative), model.native.rhos[h])
    small = list(map(s.sympify, candidate['actual_finite_group_consumer']['unit_quaternion']))
    zero(sum(x*x for x in small)-1)
    substitution = dict(zip(u, small))
    full = clean(CAR.subs(substitution))
    word = tuple(candidate['actual_input']['CAR'])
    moved = finite_wedge(full, word)
    assert terms([(1, moved), (-1, decoded_state(candidate['actual_finite_group_consumer']['CAR_image']))]) == {}
    g = group(small)
    scalar = model.native.Rd.T*realify(compounds[4].subs(substitution))*model.native.R
    Gram = model.native.Gram
    def native_pair(A, B):
        return s.expand(s.re(-s.trace(A[:3, :3]*B[:3, :3])-s.trace(A[3:5, 3:5]*B[3:5, 3:5])-A[5, 5]*B[5, 5]))
    adjoint = clean(Gram.inv()*s.Matrix(12, 12, lambda i, j: native_pair(fund[i], g*fund[j]*g.H)))
    boson = s.diag(s.eye(6), scalar, adjoint, adjoint, adjoint)
    eq(boson*model.source, decode(candidate['actual_finite_group_consumer']['moved_source_configuration']))
    center = {u[0]: -1, u[1]: 0, u[2]: 0, u[3]: 0}
    odd_word = tuple(candidate['center']['original_CAR_odd_word'])
    odd = finite_wedge(clean(CAR.subs(center)), odd_word)
    assert odd == {odd_word: -1}
    assert terms([(1, odd), (-1, decoded_state(candidate['center']['odd_word_image']))]) == {}
    center_scalar = clean(model.native.Rd.T*realify(compounds[4].subs(center))*model.native.R)
    gc = group((-1, 0, 0, 0))
    center_adjoint = clean(Gram.inv()*s.Matrix(12, 12, lambda i, j: native_pair(fund[i], gc*fund[j]*gc.H)))
    center_boson = s.diag(s.eye(6), center_scalar, center_adjoint, center_adjoint, center_adjoint)
    eq(center_boson*model.source, model.source); assert center_boson != s.eye(103)
    return {'original_quaternion_product_unitarity_determinant': True,
            'compound_matrices_regenerated_by_integer_bit_wedges': True,
            'all_original_scalar70_and_matter504_group_derivatives': True,
            'actual_nontrivial_group_field_and_CAR_actions': True,
            'source_fixed_center_and_original_odd_CAR_sign_retained': True}


def sliced_second_derivative(model, y, geo, index):
    a, Ha = geo['a'], geo['Halpha']
    H = s.zeros(103)
    for h, T in enumerate(model.T):
        H -= (T*y)[index]*Ha[h]
        row = T[index, :]
        H -= row.T*a[h, :]+a[h, :].T*row
    for h, T in enumerate(model.T):
        for k, U in enumerate(model.T):
            H += ((T*U+U*T)*y)[index]*a[h, :].T*a[k, :]/2
    return rational(H)


def main():
    began = time.monotonic()
    path = HERE/'source_quantum_gauss_section.json'; candidate = json.loads(path.read_text())
    count = bindings(candidate); assert candidate['root'] == ROOT_ID
    paid = ['independent_source_quantum_stabilizer.json', 'independent_source_stabilizer_phase_reduction.json']
    for name in paid: count += bindings(json.loads((HERE/name).read_text()))
    model = RawGaussSection(); assert model.native.hashes == candidate['source_sha256']
    eq(model.source, decode(candidate['source_boson_configuration']))
    assert model.fixed == candidate['slice']['coordinate_pivots']
    assert model.free == candidate['slice']['remaining_coordinates']
    eq(model.source_minor, decode(candidate['slice']['source_orbit_minor']))
    zero(model.source_minor.det()-s.sympify(candidate['slice']['source_minor_determinant']))
    group = group_checks(model, candidate)
    print('PASS independent source quaternion/exterior/CAR group and actual central action', flush=True)
    incoming = candidate['actual_input']; word = tuple(incoming['CAR'])
    values = {word: s.S.One}; gradient = {word: decode(incoming['gradient'])}; Hessian = {word: decode(incoming['Hessian'])}
    geo, jets = model.extension_jet(model.source, values, gradient, Hessian)
    eq(geo['a'], decode(candidate['inverse_first_derivatives']['alpha']))
    eq(model.free_reader*geo['tangent'], decode(candidate['inverse_first_derivatives']['slice']))
    for actual, encoded in zip(geo['Halpha'], candidate['inverse_second_derivatives']['alpha']): eq(actual, decode(encoded))
    for index, encoded in zip(model.free, candidate['inverse_second_derivatives']['slice']):
        eq(sliced_second_derivative(model, model.source, geo, index), decode(encoded))
    expected_jets = {tuple(item['CAR']): item for item in candidate['actual_extended_jet']}
    assert set(jets) == set(expected_jets)
    for w, (f, g, h) in jets.items():
        expected = expected_jets[w]
        zero(f-s.sympify(expected['value'])); eq(g, decode(expected['gradient'])); eq(h, decode(expected['Hessian']))
    gauss = model.Gauss_checks(model.source, jets)
    assert any(f == 0 and (g.todok() or h.todok()) for f, g, h in jets.values())
    assert all(current(R, values) for R in model.r)
    print('PASS independently solved implicit gauge inverse, arbitrary slice chain rule and complete charged103 two-jet', flush=True)
    components = raw_whole_action(model, model.source, jets)
    assert all(components.values())
    Hrecord = candidate['Hamiltonian']
    for key, component in components.items():
        assert terms([(1, component), (-1, decoded_state(Hrecord['actual_four_components'][key]))]) == {}, key
    image = terms((1, value) for value in components.values())
    assert terms([(1, image), (-1, decoded_state(Hrecord['actual_complete_image']))]) == {}
    naive = {word: [1, model.free_reader.T*gradient[word], model.free_reader.T*Hessian[word]*model.free_reader]}
    naive_components = raw_whole_action(model, model.source, naive)
    naive_image = terms((1, value) for value in naive_components.values())
    defect = terms([(1, image), (-1, naive_image)]); assert defect
    assert terms([(1, defect), (-1, decoded_state(Hrecord['omit_orbit_derivatives_defect']))]) == {}
    _, constant_extension = model.extension_jet(model.source, values, {}, {})
    ext_components = raw_whole_action(model, model.source, constant_extension)
    trivial_components = raw_whole_action(model, model.source, {word: [1, s.zeros(103, 1), s.zeros(103)]})
    spin = terms([(1, terms((1, v) for v in ext_components.values())),
                  (-1, terms((1, v) for v in trivial_components.values()))]); assert spin
    assert terms([(1, spin), (-1, decoded_state(Hrecord['constant_slice_section_spin_connection_correction']))]) == {}
    print('PASS raw coframe/scalar/gauge/full252 Hamiltonian on true finite-CAR jets and both nonzero orbit corrections', flush=True)
    assert candidate['center']['arbitrary_local_sections_declared_global_physical_states'] is False
    assert candidate['second_class_temporal_branch_or_full_Hilbert_evolution_spectrum_generated'] is False
    paths = [HERE/name for name in ('independent_source_quantum_gauss_section.py', 'source_quantum_gauss_section.py',
        'source_quantum_gauss_section.json', 'independent_source_quantum_stabilizer.py',
        'independent_source_joint_local_quantum.py', 'independent_source_coframe_live_ordering.py',
        'independent_source_gauss_quantum_current.py', 'independent_source_gauge_legendre.py')]+[HERE/name for name in paid]
    result = {'root': ROOT_ID, 'source_sha256': model.native.hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'verdict': 'CERTIFIED_LOCAL_SOURCE_EQUIVARIANT_SECTION_AND_COMPLETE_HAMILTONIAN_TWO_JET',
        'scope': candidate['scope'], 'checked_input_bindings': count, 'candidate_constructor_imported': False,
        'source_group': group, 'Gauss_output': gauss,
        'implicit_slice_inverse': 'All103 first and all103x103 second derivatives are independently solved from E exp(-alpha.L)y=c, and compared with the producer forward-map inverse. The source minor is nonzero; the local analytic inverse map exists before any section or Gauss condition is supplied.',
        'local_section_review': 'The original finite exterior representation satisfies the same local group product. Therefore F(g.z)=Gamma(g)f(z) is equivariant and gives Gauss zero for arbitrary slice germs. Restriction recovers f, and local orbit-ODE uniqueness gives the converse. The signed full Hamiltonian commutator preserves this equivariance and yields Extension Restriction H Extension=H Extension.',
        'actual_zero_value_nonzero_derivative_CAR_words_consumed': True,
        'actual_all4_Hamiltonian_components': {k: state_encode(v) for k, v in components.items()},
        'actual_joint_image': state_encode(image), 'both_omitted_orbit_and_constant_slice_spin_defects_nonzero': True,
        'global_atlas_center_compatibility_Hilbert_measure_or_time_reduced_quantization_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_quantum_gauss_section.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent local quantum Gauss section', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
