#!/usr/bin/env python3
"""Independent primitive, nested-CAR and mixed-curve temporal Lorentz audit."""
from __future__ import annotations

from collections import defaultdict
import copy
import hashlib
import itertools
import json
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_lorentz_contact import ETA, GAMMA, PAIRS, encode
from source_lorentz_temporal_ordering import SourceLorentzTemporalOrdering
from independent_source_lorentz_quantum_section import (
    BitAction, equal, total, clean, lift_matrix, make_extension,
    original_coefficients, make_hamiltonians,
)
from independent_source_joint_form_hamiltonian import (
    RawGaussSection, RawLiveCoefficients, raw_gauge_coefficients, whole_action,
    raw_coefficients, raw_matter, state_encode,
)
from independent_source_quantum_ordered_temporal import raw_coframe_family
from independent_source_scalar_temporal_form import at, reclock_scalar


def bound(name):
    result = json.loads((HERE / (name + '.json')).read_text())
    assert result['root'] == ROOT_ID
    count = 0
    for key in ('source_sha256', 'input_sha256'):
        for path, digest in result.get(key, {}).items():
            assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, path
            count += 1
    compile((HERE / (name + '.py')).read_text(), name, 'exec')
    return result, count


def same(first, second):
    difference = total((1, first), (-1, second))
    assert not difference, list(difference.items())[:3]


def wedge_polynomial(matrices, states):
    """Exterior-slot multiplication, with literal degree<=2 convolution."""
    columns = {}
    result = [defaultdict(int) for _ in range(3)]
    for degree, state in enumerate(states):
        for word, coefficient in state.items():
            current = {((), degree): coefficient}
            for column in word:
                if column not in columns:
                    columns[column] = [(row, k, value)
                        for k, matrix in enumerate(matrices)
                        for (row, j), value in s.SparseMatrix(matrix[:, column]).todok().items()]
                following = defaultdict(int)
                for (occupied, old_degree), value in current.items():
                    for row, k, entry in columns[column]:
                        if row in occupied or old_degree + k > 2:
                            continue
                        sign = (-1) ** sum(i > row for i in occupied)
                        target = tuple(sorted((*occupied, row)))
                        following[target, old_degree + k] += sign * value * entry
                current = following
            for (word_out, k), value in current.items():
                result[k][word_out] += value
    return [clean(row) for row in result]


def finite_primitive_covariance(model):
    native = model.source.native
    lorentz = native.lorentz
    # Two noncommuting finite transformations, with exact rational entries.
    r = s.Rational(3, 5)
    T, S = lorentz.basis[0], lorentz.spin[0]
    boost = s.eye(4) + 2*r/(1-r*r)*T + 2*r*r/(1-r*r)*T*T
    spin_boost = (s.eye(4) + 2*r*S) / s.sqrt(1-r*r)
    T, S = lorentz.basis[4], lorentz.spin[4]
    rotation = s.eye(4) + s.Rational(24, 25)*T + s.Rational(18, 25)*T*T
    spin_rotation = s.Rational(4, 5)*s.eye(4) + s.Rational(6, 5)*S
    Lambda, spin = boost*rotation, spin_boost*spin_rotation
    equal(Lambda.T*ETA*Lambda, ETA)
    assert Lambda.det() == 1
    e = s.Matrix([[s.Rational(7, 4), s.Rational(1, 9), 0, 0],
                  [s.Rational(1, 11), s.Rational(6, 5), 0, 0],
                  [s.Rational(-1, 13), s.Rational(1, 17), s.Rational(9, 8), 0],
                  [s.Rational(1, 19), 0, s.Rational(1, 23), s.Rational(10, 9)]])
    transformed = Lambda*e
    B16 = s.kronecker_product(Lambda, s.eye(4))
    ad = s.Matrix(6, 6, lambda a, b:
        ETA[PAIRS[a][0], PAIRS[a][0]] *
        (Lambda*lorentz.basis[b]*Lambda.inv())[PAIRS[a][0], PAIRS[a][1]])
    B24 = s.kronecker_product(s.eye(4), ad)
    for a in range(6):
        equal(spin*lorentz.spin[a]*spin.inv(),
              sum((ad[b, a]*lorentz.spin[b] for b in range(6)), s.zeros(4)))
    equal(B24.T*lorentz.hessian(transformed)*B24, lorentz.hessian(e))
    equal(B24.T*lorentz.geometry_maps(transformed)[0]*s.kronecker_product(s.eye(4), B16),
          lorentz.geometry_maps(e)[0])
    old, new = native.geometry(e), native.geometry(transformed)
    equal(new['velocity_inverse'], B16*old['velocity_inverse']*B16.T)
    equal(new['R'], B16*old['R'])
    equal(new['Lorentz_inverse'], B24*old['Lorentz_inverse']*B24.T)
    p, q = lorentz.raw_matter_ports(e), lorentz.raw_matter_ports(transformed)
    for mu in range(4):
        equal(q['oriented_principals'][mu], spin*p['oriented_principals'][mu]*spin.inv())
        for a in range(6):
            original = sum((ad.inv()[b, a]*p['E'].inv()*p['V'][6*mu+b]
                            for b in range(6)), s.zeros(4))
            equal(q['E'].inv()*q['V'][6*mu+a], spin*original*spin.inv())
    equal(model.family.joint.common.gauge.constitutive(transformed)['Hodge'],
          model.family.joint.common.gauge.constitutive(e)['Hodge'])
    equal(e.det()*e.inv()*ETA*e.inv().T,
          transformed.det()*transformed.inv()*ETA*transformed.inv().T)
    equal(spin*s.diag(0, 0, 1, 1), s.diag(0, 0, 1, 1)*spin)
    print('PASS independent finite noncommuting Lorentz primitive covariance', flush=True)
    return {'coframe': encode(e), 'Lambda': encode(Lambda),
            'full_G24_by64_checked': True, 'all24_Dirac_current_slots': True,
            'H_Q_R_Hodge_scalar_metric_and_repaired_chirality': True}


def ordering_audit():
    receipt, count = bound('source_lorentz_temporal_ordering')
    model = SourceLorentzTemporalOrdering()
    model.primitive_covariance()
    covariance = finite_primitive_covariance(model)
    numeric = copy.copy(model.ambient)
    clock = (s.Rational(7, 6), s.Rational(1, 11), -s.Rational(2, 13), s.Rational(3, 17))
    replacement = dict(zip(model.y, clock))
    numeric.e = model.ambient.e.subs(replacement)
    numeric.data = {key: at(value, replacement) for key, value in model.ambient.data.items()}
    C, J, dC = original_coefficients(numeric)
    action = BitAction()
    ambient, reduced = make_hamiltonians(numeric, action, C, J, dC)
    extend = make_extension(model.source, model.source.inverse, model.source.second, action)
    n, *b = clock
    b2 = sum(x*x for x in b)
    drift = s.Matrix([-n/2-b2/(4*n), 0, -b2/(4*n), 0, 0, n/2-b2/(4*n)])
    one = -3*b2/(8*n)
    equal(model.drift.subs(replacement), drift)
    equal(model.one.subs(replacement), one*s.eye(8))
    constant_words = [()] + [(63*a+5,) for a in range(8)]
    constant_words += [tuple(sorted((63*a+5, 63*b+37))) for a in range(8) for b in range(8)]
    constant_words += [(63*a+5, 63*b+5) for a, b in itertools.combinations(range(8), 2)]
    for word in constant_words:
        values = {word: s.S.One}
        first = {word: s.zeros(6, 1)}
        second = {word: s.zeros(6)}
        raw = total((1, ambient(extend(values, first, second))), (-1, reduced(values, first, second)))
        same(raw, {word: len(word)*one})
    consumers = []
    for word in ((18, 289), (72, 181, 446)):
        value = {word: s.Rational(2, 7)}
        g = s.Matrix([s.Rational(2*j-3, 23)+s.I*s.Rational(j % 3-1, 29) for j in range(6)])
        v = s.Matrix([s.Rational(j % 4-1, 31) for j in range(6)])
        H = v*v.T+s.diag(1, -2, 3, -1, 2, -3)/37
        gradients, Hessians = {word: g}, {word: H}
        raw = total((1, ambient(extend(value, gradients, Hessians))),
                    (-1, reduced(value, gradients, Hessians)))
        expected = {word: (drift.T*g)[0]+len(word)*one*value[word]}
        same(raw, expected)
        oracle = model.difference(value, gradients)
        same(raw, {w: coefficient.subs(replacement) for w, coefficient in oracle.items()})
        q = s.symbols('audit_half_q0:6', positive=True)
        Uinv = (q[0]*q[2]*q[5])**(-s.Rational(len(word)+2, 2))
        point = dict(zip(q, model.source.q))
        ell = s.Matrix([s.diff(Uinv, x).subs(point) for x in q])
        d2 = s.Matrix(6, 6, lambda i, j: s.diff(Uinv, q[i], q[j]).subs(point))
        gg = g+value[word]*ell
        HH = H+ell*g.T+g*ell.T+value[word]*d2
        conjugated = total((1, ambient(extend(value, {word: gg}, {word: HH}))),
                          (-1, reduced(value, {word: gg}, {word: HH})))
        same(conjugated, {word: (drift.T*g)[0]+3*b2/(4*n)*value[word]})
        consumers.append({'word': list(word), 'raw_difference': state_encode(raw),
                          'literal_half_density_difference': state_encode(conjugated)})
    print('PASS independent nonzero-three-shift ordering:101 complete CAR coefficient words and fresh jets', flush=True)
    return model, {'candidate_source_binding_checks': count, 'finite_covariance': covariance,
        'independent_time': list(map(str, clock)), 'constant_CAR_coefficient_carrier': len(constant_words),
        'actual_consumers': consumers, 'full504_internal_sectors_retained': True}


def inverse_density(point, free, values, gradients, Hessians):
    active = (0, 2, 5, free.index(68), free.index(79))
    variables = s.symbols('literal_density0:5', positive=True)
    substitution = {x: point[j] for x, j in zip(variables, active)}
    out_g, out_H = {}, {}
    for word in set(values) | set(gradients) | set(Hessians):
        powers = [s.Rational(len(word)+2, 2)]*3+[s.S.One, s.Rational(1, 2)]
        f = s.prod((point[j]/x)**power for j, x, power in zip(active, variables, powers))
        first, second = s.zeros(100, 1), s.zeros(100)
        for i, x in zip(active, variables):
            first[i] = s.diff(f, x).subs(substitution)
            for j, y in zip(active, variables):
                second[i, j] = s.diff(f, x, y).subs(substitution)
        v = values.get(word, 0)
        g = gradients.get(word, s.zeros(100, 1))
        H = Hessians.get(word, s.zeros(100))
        out_g[word] = g+v*first
        out_H[word] = H+first*g.T+g*first.T+v*second
    return values.copy(), out_g, out_H


def balance_audit():
    from source_temporal_lorentz_balance import SourceTemporalLorentzBalance
    receipt, count = bound('source_temporal_lorentz_balance')
    candidate = SourceTemporalLorentzBalance()
    section, raw = RawGaussSection(), RawLiveCoefficients()
    values = {(): s.Rational(2, 7), (11, 288): s.Rational(3, 5)}
    gradients, Hessians = {}, {}
    for k, word in enumerate(values):
        gradients[word] = s.Matrix([s.Rational((j+2*k) % 7-3, 41)+
            s.I*s.Rational((2*j+k) % 5-2, 43) for j in range(100)])
        u = s.Matrix([s.Rational((j+3*k) % 6-2, 47) for j in range(100)])
        Hessians[word] = u*u.T-s.eye(100)/53
    point = section.free_reader*section.source
    equal(point, candidate.current.point)
    native = inverse_density(point, section.free, values, gradients, Hessians)
    _, jets = section.extension_jet(section.source, *native)
    section.Gauss_checks(section.source, jets)
    result = candidate.generate(values, gradients, Hessians)
    for word in set(jets) | set(result.input103):
        row = jets.get(word, [0, s.zeros(103, 1), s.zeros(103)])
        other = result.input103.get(word, {'value': 0, 'gradient': s.zeros(103, 1), 'Hessian': s.zeros(103)})
        assert s.cancel(row[0]-other['value']) == 0
        equal(row[1], other['gradient']); equal(row[2], other['Hessian'])
    e, coframe = raw_coframe_family(raw, candidate.y)
    q = tuple(section.source[:6, :])
    replacement = dict(zip(raw.q, q))
    e = at(e, replacement)
    coframe = {key: at(value, replacement) for key, value in coframe.items()}
    x, A = section.source[6:67, :], section.source[67:, :].reshape(3, 12)
    initial = raw_coefficients(section.native, e.subs(candidate.at_clock), x, A)
    scalar = reclock_scalar(section.native, initial, e, A)
    gauge = raw_gauge_coefficients(e, A, section.native)
    connection = s.zeros(4, 12); connection[1:, :] = A
    matter = raw_matter(e, scalar['phi'], connection)
    Hmatter = -s.I*matter['E_inverse']*matter['lower']
    Hmatter = s.diag(Hmatter, -Hmatter.conjugate())
    _, family = whole_action(dict(coframe=coframe, scalar=scalar, gauge=gauge, matter=Hmatter), jets)
    same(family, result.family)
    value = clean({w: coefficient.subs(candidate.at_clock) for w, coefficient in family.items()})
    force = [clean({w: -s.diff(coefficient, y).subs(candidate.at_clock)
                   for w, coefficient in family.items()}) for y in candidate.y]
    same(value, result.value)
    for left, right in zip(force, result.forces): same(left, right)
    assert all(force)
    print('PASS independent literal U, implicit native jets and complete original four-time H/forces', flush=True)

    directions = [s.eye(13)[:, i] for i in range(13)]
    directions += [s.Matrix([s.Rational((j*3+2) % 7-3, 13) for j in range(13)]),
                   s.Matrix([s.Rational((j*5+1) % 9-4, 17) for j in range(13)])]
    curves = []
    t = s.Symbol('independent_orbit_parameter', real=True)
    spin_R = [lift_matrix(s.diag(S, S.conjugate()))
              for S in candidate.spin.native.lorentz.spin]
    for index, u in enumerate(directions):
        X = sum((u[4+j]*candidate.spin.native.lorentz.basis[j] for j in range(6)), s.zeros(4))
        R = sum((u[4+j]*matrix for j, matrix in enumerate(spin_R+section.r)), s.zeros(504))
        inv = s.eye(4)-t*X+t*t*X*X/2
        body = inv*(candidate.y0+t*u[:4, :])
        substitution = dict(zip(candidate.y, body))
        time_series = []
        for k in range(3):
            time_series.append(clean({w: s.diff(coefficient.subs(substitution), t, k).subs(t, 0)/s.factorial(k)
                                      for w, coefficient in family.items()}))
        finite = wedge_polynomial([s.eye(504), R, R*R/2], time_series)
        oracle = result.orbit_direction_jet(u)
        same(finite[0], oracle['value']); same(finite[1], oracle['first'])
        same(total((2, finite[2])), oracle['second'])
        spatial = candidate.spin.e.copy(); spatial[:, 0] = s.zeros(4, 1)
        curve = (s.eye(4)+t*X+t*t*X*X/2)*spatial
        curve[:, 0] = candidate.y0+t*u[:4, :]
        scalar_R = sum((u[10+j]*section.native.rhos[j] for j in range(3)), s.zeros(70))
        gauge_R = sum((u[10+j]*section.native.ads[j] for j in range(3)), s.zeros(12))
        scalar_curve = (s.eye(70)+t*scalar_R+t*t*scalar_R*scalar_R/2)*section.native.v
        gauge_curve = s.Matrix.vstack(*[((s.eye(12)+t*gauge_R+t*t*gauge_R*gauge_R/2)*A[i, :].T).T
                                        for i in range(3)])
        whole = curve.reshape(16, 1).col_join(scalar_curve).col_join(gauge_curve.reshape(36, 1))
        equal(whole.diff(t).subs(t, 0), oracle['configuration122_first'])
        equal(whole.diff(t, 2).subs(t, 0), oracle['configuration122_second'])
        if index >= 13:
            curves.append({'coefficients13': encode(u), 'first': state_encode(finite[1]),
                           'second': state_encode(total((2, finite[2])))})
    ports = result.noether_ports()
    assert not any(ports['full_Lorentz_primary_on_H'])
    assert not any(ports['residual_su2_primary_on_H'])
    for i, T in enumerate(candidate.T):
        expected = total(*((-c, force[mu]) for mu, c in enumerate(T*candidate.y0) if c))
        same(ports['i_H_spatial_primary'][i], expected)
        assert bool(expected) == (i < 3)
    print('PASS independent exterior-polynomial13 plus new mixed time/Lorentz/native orbit two-jets', flush=True)
    return {'candidate_source_binding_checks': count, 'raw_germ_words': [list(w) for w in values],
        'independent_implicit103_words': len(jets), 'current_H': state_encode(value),
        'forces': list(map(state_encode, force)), 'independent_coordinate_curve_count': len(directions),
        'mixed_curves': curves, 'secondary_forces_nonzero': True,
        'output_scope': 'Only the original13 time4/Lorentz6/residual-su2-3 directions and their source122 curve derivatives. No horizontal100 output jet is inferred.'}


def main():
    started = time.monotonic()
    _, ordering = ordering_audit()
    balance = balance_audit()
    names = ('source_lorentz_temporal_ordering', 'source_temporal_lorentz_balance')
    paths = [HERE / (name + suffix) for name in names for suffix in ('.py', '.json')]
    paths += [HERE / 'independent_source_temporal_lorentz_balance.py',
        HERE / 'independent_source_lorentz_quantum_section.py',
        HERE / 'independent_source_joint_form_hamiltonian.py',
        HERE / 'independent_source_quantum_ordered_temporal.py',
        HERE / 'independent_source_scalar_temporal_form.py']
    result = {'verdict': 'CERTIFIED_SOURCE_FOUR_TIME_ORDERING_AND_LORENTZ_ORBIT_BALANCE',
        'root': ROOT_ID, 'ordering': ordering, 'balance': balance,
        'source_sha256': json.loads((HERE / 'source_lorentz_temporal_ordering.json').read_text())['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'source_scope': 'The original generic16 H/G/Dirac/Hodge covariance and explicit all-time ordering difference are consumed before the current-H orbit image. Primary input constraints do not imply vanishing temporal secondary forces.',
        'seconds': round(time.monotonic()-started, 3)}
    (HERE / 'independent_source_temporal_lorentz_balance.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent temporal Lorentz audit', result['seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
