#!/usr/bin/env python3
"""True joint source jets at zero incoming momentum in actual fixed native frames."""
from itertools import product
import importlib.util
import json
from pathlib import Path
import sys
import time
import sympy as s

_spec = importlib.util.spec_from_file_location('propagation_curvature_source', Path(__file__).with_name('source.py'))
source = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(source)

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE, FQ, BASE = source.HERE, source.FQ, source.BASE
sys.path.insert(0, str(FQ/'packet-gauge-bilocal'))
import hermitian as h
K = h.K
variables = [*source.k, *source.d]
indices = sorted([a for a in product(range(3), repeat=6) if sum(a) <= 2], key=lambda a: (sum(a), a))
zero = (0,)*6


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def empty(n, m): return h.matrix(n, m, [])
def eye(n): return h.matrix(n, n, [(i, i, K.one) for i in range(n)])
def finite(M):
    return h.matrix(M.rows, M.cols, [(i, j, h.scalar(s.expand(v))) for (i, j), v in s.SparseMatrix(M).todok().items()])


def jet(M):
    records = {a: [] for a in indices}
    for (i, j), v in s.SparseMatrix(M).todok().items():
        P = s.Poly(v, *variables)
        for a in indices:
            value = P.coeff_monomial(a)*s.prod(s.factorial(j) for j in a)
            if value: records[a].append((i, j, h.scalar(value)))
    return {a: h.matrix(M.rows, M.cols, records[a]) for a in indices}


def subtract(a, b): return tuple(x-y for x, y in zip(a, b))
def subindices(a): return [b for b in indices if all(x <= y for x, y in zip(b, a))]
def choose(a, b): return K.convert(int(s.prod(s.binomial(x, y) for x, y in zip(a, b))))


def multiply(A, B):
    result = {}
    for a in indices:
        value = empty(A[zero].shape[0], B[zero].shape[1])
        for b in subindices(a):
            value += A[b].matmul(B[subtract(a, b)]).scalarmul(choose(a, b))
        result[a] = value
    return result


def solve(operator, inverse, rhs):
    result = {}
    for a in indices:
        value = rhs[a]
        for b in subindices(a):
            if b != zero:
                value -= operator[b].matmul(result[subtract(a, b)]).scalarmul(choose(a, b))
        result[a] = inverse.matmul(value)
    assert all((v-rhs[a]).is_zero_matrix for a, v in multiply(operator, result).items())
    return result


def global_origin_columns(global_data, frequency):
    module = load('curvature_global_source_jets', FQ/'packet-gauge-global-transfer/jets.py')
    data = module.evaluate_jet(global_data, [0, 0, 0], frequency)
    assert module.FIELD == K
    out = {}
    for label in ['X', 'I']:
        value = data[label]
        denominators = [v.get((0,), K.zero) for v in value['denominators']]
        assert all(denominators)
        result = s.MutableSparseMatrix(289, 1, {})
        for i in range(289):
            result[i, 0] = K.to_sympy(value['value'][i].get((0,), K.zero)/denominators[0])
            for a in range(3):
                result[i, 0] += source.k[a]*K.to_sympy(value['first'][a][i].get((0,), K.zero)/denominators[1])
                for b in range(a, 3):
                    result[i, 0] += source.k[a]*source.k[b]*K.to_sympy(value['second'][a, b][i].get((0,), K.zero)/denominators[2])/(2 if a == b else 1)
        out[label] = source.clean(result)
    return out


def frame(circle_data, y, z):
    t = s.Symbol('t', real=True)
    values = []
    for axis, parameter in [(1, y), (2, z)]:
        entry = circle_data['certificates'][axis]
        denominator = s.Integer(entry['field_constant_denominator'])*(1+parameter**2)**4
        M = s.SparseMatrix(289, 289, {(i, j): sum(a*parameter**n for n, a in enumerate(v))/denominator
                                    for i, j, v in entry['field_numerator']})
        values.append(finite(M))
    return values[1].matmul(values[0])


def main():
    started = time.monotonic()
    src = source.read(HERE/'source.json')
    actual = source.read(BASE/'active-gauge/receipt.json')
    ward = source.read(FQ/'packet-gauge-kernel/ward.json')
    quotient = source.read(BASE/'active-gauge/quotient.json')
    catalog = source.read(BASE/'active-gauge/propagation.json')
    global_data = source.read(FQ/'packet-gauge-global-transfer/source.json')
    circle_data = source.read(BASE/'active-gauge/rotation/finite.json')
    N = s.sympify(actual['source_lapse'])
    frequency = s.sympify(src['physical_frequency'])
    incoming = global_origin_columns(global_data, frequency)
    X, I = jet(incoming['X']), jet(incoming['I'])
    Xout = jet(incoming['X'].subs(dict(zip(source.k, [v-w for v, w in zip(source.k, source.d)])), simultaneous=True))
    polynomial = {name: source.matrix(record) for name, record in src['source_polynomial'].items()}
    V, Q, K1, C1 = [jet(polynomial[name]) for name in ['V', 'Q', 'K1', 'C1']]
    pout = [s.sympify(v, locals=dict(zip(map(str, variables), variables))) for v in src['physical_p_out']]
    pin = [s.sympify(v, locals=dict(zip(map(str, variables), variables))) for v in src['physical_p_in']]
    Hw = jet(source.native.ward.operator(actual['Fourier_Jacobi_entries'], values=pout))
    Hin = jet(source.native.ward.operator(actual['Fourier_Jacobi_entries'], values=pin))
    assert all((value-I[a]).is_zero_matrix for a, value in multiply(Hin, X).items())
    Kminus = jet(source.clean(source.matrix(ward['K0']).subs(dict(zip(source.native.ward.p, [-v for v in pout])))))
    torque = multiply({a: v.transpose() for a, v in K1.items()}, I)
    term = multiply({a: v.transpose() for a, v in C1.items()}, X)
    torque = {a: -value-term[a] for a, value in torque.items()}
    external = multiply(V, X)
    removed = quotient['fixed_section_removed_original_fields']
    keep = [i for i in range(121) if i not in removed]
    scale = dict(zip(quotient['retained_original_fields'], map(s.sympify, catalog['constant_diagonal_field_scaling'])))
    D = s.diag(*[1 if i < 9 else scale[i] for i in keep])
    zero_output = empty(289, 1)
    print('PASS original all28 incoming/source jets and Noether torque before solving fields', flush=True)
    records, reference = [], None
    for name, L in [('native_origin', eye(289)), ('native_two_circle', frame(circle_data, s.Rational(1, 7), s.Rational(2, 9)))]:
        Li = L.inv()
        assert (Li.matmul(L)-eye(289)).is_zero_matrix
        H = {a: L.transpose().matmul(value).matmul(L) for a, value in Hw.items()}
        minor = {a: Li.matmul(value).extract(removed, range(9)).transpose() for a, value in Kminus.items()}
        inverse_minor = minor[zero].inv()
        charge = solve(minor, inverse_minor, torque)
        Iaxis = {a: h.matrix(289, 1, [(removed[i], 0, v) for (i, j), v in value.to_dok().items()]) for a, value in charge.items()}
        Iworld = {a: Li.transpose().matmul(value) for a, value in Iaxis.items()}
        rhs = {a: Iaxis[a]-L.transpose().matmul(external[a]) for a in indices}
        current, fields, steps = H, list(range(289)), []
        for step in actual['algebraic_Schur_steps']:
            eliminated = step['eliminated_fields']
            retained = [i for i in fields if i not in eliminated]
            erows, krows = [[fields.index(i) for i in ids] for ids in [eliminated, retained]]
            inv = h.matrix(len(eliminated), len(eliminated), [(eliminated.index(i), eliminated.index(j), h.number(v))
                           for i, j, v in step['algebraic_block_inverse']])
            assert (current[zero].extract(erows, erows).matmul(inv)-eye(len(eliminated))).is_zero_matrix
            assert (inv.matmul(current[zero].extract(erows, erows))-eye(len(eliminated))).is_zero_matrix
            assert all(current[a].extract(erows, erows).is_zero_matrix for a in indices if a != zero)
            particular = {a: inv.matmul(rhs[a].extract(erows, [0])) for a in indices}
            back = {a: -inv.matmul(current[a].extract(erows, krows)) for a in indices}
            left = {a: current[a].extract(krows, erows) for a in indices}
            update, correction = multiply(left, back), multiply(left, particular)
            rhs = {a: rhs[a].extract(krows, [0])-correction[a] for a in indices}
            current = {a: current[a].extract(krows, krows)+update[a] for a in indices}
            steps.append((eliminated, retained, particular, back))
            fields = retained
        section = {a: v.extract(keep, keep) for a, v in current.items()}
        force = {a: value.extract(keep, [0]) for a, value in rhs.items()}
        normalized = source.clean(D*section[zero].to_Matrix()*D/N)
        inverse, blocks = source.native.rational_inverse(normalized)
        true_inverse = finite(source.clean(D*inverse*D/N))
        assert (section[zero].matmul(true_inverse)-eye(112)).is_zero_matrix
        answer = solve(section, true_inverse, force)
        vectors = {a: h.matrix(289, 1, [(keep[i], 0, v) for (i, j), v in value.to_dok().items()]) for a, value in answer.items()}
        for eliminated, retained, particular, back in reversed(steps):
            added = multiply(back, {a: value.extract(retained, [0]) for a, value in vectors.items()})
            vectors = {a: vectors[a]+h.matrix(289, 1, [(eliminated[i], 0, v) for (i, j), v in
                         (particular[a]+added[a]).to_dok().items()]) for a in indices}
        world = {a: L.matmul(value) for a, value in vectors.items()}
        residual = multiply(Hw, world)
        assert all((residual[a]+external[a]-Iworld[a]).is_zero_matrix for a in indices)
        assert all(value.extract(removed, [0]).is_zero_matrix for value in vectors.values())
        readback = multiply(multiply({a: h.conjugate_matrix(value).transpose() for a, value in Xout.items()}, Q), world)
        scalar = {a: value.to_dok().get((0, 0), K.zero) for a, value in readback.items()}
        different = [] if reference is None else [list(a) for a in indices if scalar[a] != reference[a]]
        entry = {'frame': name, 'all28_full289_original_equations': True,
                 'actual112_inverse_blocks': blocks, 'noether_before_field': True,
                 'fixed_frame_scalar_jet': [[list(a), str(K.to_sympy(value))] for a, value in scalar.items() if value],
                 'different_scalar_jet_from_origin_frame': different}
        if reference is None:
            reference = scalar
            entry['field_jet'] = [[list(a), source.encode(value.to_Matrix())] for a, value in world.items()]
            entry['source_jet'] = [[list(a), source.encode(value.to_Matrix())] for a, value in Iworld.items()]
        records.append(entry)
        print('PASS actual fixed frame', name, '28 field equations, differing scalar jets', different, flush=True)
    report = {'scope': 'ACTUAL_FIXED_SOURCE_FRAMES_JOINT_ORIGIN_JETS_NOT_AN_INCOMING_FRAME_SMOOTHNESS_ASSUMPTION',
              'physical_variables': list(map(str, variables)), 'physical_frequency': str(frequency),
              'scalar_definition': 'F(k-d)^dagger Qeff(k-d) G_d(k-d;k)',
              'true_implicit_source_root_used': True, 'torque_support_by_jet': [[list(a), len(value.to_dok())]
                  for a, value in torque.items() if not value.is_zero_matrix],
              'source_and_frames': records, 'seconds': round(time.monotonic()-started, 3)}
    (HERE/'origin.json').write_text(json.dumps(report, separators=(',', ':'))+'\n')
    print('PASS source propagation origin jet', report['seconds'], flush=True)


if __name__ == '__main__': main()
