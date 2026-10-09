#!/usr/bin/env python3
"""Original nonlinear Bg backwrite in the actual induced gauge current.

The direct reduced Euler current and the original quadratic current plus its
linear second-order auxiliary correction consume the same theta fields.
"""
from fractions import Fraction as F
from functools import lru_cache
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
BASE = FQ.parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(FQ/'packet-gauge-bilocal'))
import hermitian as h
K, POLY, U = h.K, h.POLY, h.U


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def read(path):
    return json.loads(gzip.decompress(path.read_bytes()) if path.suffix == '.gz' else path.read_bytes())


def main():
    started = time.monotonic()
    interval = load(FQ/'packet-gauge-response/response.py', 'reduced_current_intervals')
    paths = [BASE/'active-gauge/receipt.json', FQ/'packet-gauge-causal/transfer.json.gz',
             FQ/'packet-gauge-causal/source.json', FQ/'packet-gauge-bilocal/vertices.json',
             FQ/'packet-gauge-constitutive-vertex/vertices.json', FQ/'packet-gauge-constitutive-reduction/reduction.json',
             FQ/'packet-gauge-kinetic/receipt.json', FQ/'packet-current-hessian/integrals.json']
    original, transfer, causal, vertices, auxiliary_vertices, reduction, kinetic, moments = map(read, paths)
    for path, digest in original['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
    x = s.symbols('x', real=True)
    p = list(s.symbols('p0:4', real=True))
    r = list(s.symbols('r0:4', real=True))
    c = 6*s.sqrt(15)/25
    frequency = 6*c*(1-s.I)
    kin = list(map(s.sympify, causal['physical_momentum']))
    right = [frequency, *[s.I*v for v in kin]]
    left = list(map(s.conjugate, right))
    total = [s.expand(l+v) for l, v in zip(left, right)]
    reader = [-v for v in total]
    assert total == [12*c, 0, 0, 0]

    @lru_cache(None)
    def at_frequency(value):
        return h.scalar(s.sympify(value, locals={'x': x}).subs(x, 6*(1-s.I)))

    X = h.matrix(289, 6, [(i, j, at_frequency(value)) for i, j, value in transfer['X0']['entries']])
    Xbar = h.conjugate_matrix(X)
    factor_expr = s.Poly(s.sympify(transfer['Fhat'], locals={'U': U}), U, domain=s.QQ)
    factor = h.polynomial(factor_expr.as_expr())
    fields = original['fields']
    gauge = [i for i, f in enumerate(fields) if f['group'] == 'gauge_A']
    bg = [i for i, f in enumerate(fields) if f['group'] == 'gauge_B']
    reduced_fields = reduction['retained_original_fields']
    H = h.operator(original['Fourier_Jacobi_entries'], right)
    Hsum = h.operator(original['Fourier_Jacobi_entries'], total)
    assert H.extract(bg, range(289)).matmul(X).is_zero_matrix
    Hbb = H.extract(bg, bg)
    Hbb_inverse = Hbb.inv()
    assert (Hbb.matmul(Hbb_inverse)-h.matrix(72, 72, [(i, i, K.one) for i in range(72)])).is_zero_matrix
    assert (Hbb_inverse.matmul(Hbb)-h.matrix(72, 72, [(i, i, K.one) for i in range(72)])).is_zero_matrix

    def quadratic(Q, half=False):
        table = Xbar.transpose().matmul(Q).matmul(X).to_dok()
        poly = POLY.zero
        for (i, j), value in table.items():
            poly += POLY.ground_new(value/K.convert(2 if half else 1))*h.u**(i+j)
        return poly.rem(factor)

    QB = [h.stored_matrix(row['Q']) for row in auxiliary_vertices['original_unit_auxiliary_readers']]
    second_euler = [quadratic(Q) for Q in QB]

    def poly_column(polynomials):
        return h.matrix(len(polynomials), 6, [(i, power[0], value) for i, poly in enumerate(polynomials)
                                              for power, value in poly.items()])

    QBcolumn = poly_column(second_euler)
    Bsecond = Hbb_inverse.matmul(QBcolumn).scalarmul(-K.one)
    assert (Hbb.matmul(Bsecond)+QBcolumn).is_zero_matrix
    correction = Hsum.extract(gauge, bg).matmul(Bsecond).scalarmul(K.one/K.convert(2))
    print('PASS actual theta homogeneous Bg equations and native nonlinear second auxiliary backwrite', flush=True)

    # Both curvature legs and every coframe leg vanish initially. The actual
    # first curvature transfer is strictly proper, so polarizing B'' creates
    # no omitted lower time boundary in either Laplace variable.
    symbols = {str(v): v for v in p}
    derivative = s.SparseMatrix(*kinetic['curvature_derivative']['shape'],
        {(i, j): s.sympify(v, locals=symbols) for i, j, v in kinetic['curvature_derivative']['entries']})
    variable_point = [c*x, *[s.I*v for v in kin]]
    Acoeff = s.SparseMatrix(48, 6, {(gauge.index(i), j): s.sympify(v, locals={'x': x})
                                   for i, j, v in transfer['X0']['entries'] if i in gauge})
    Fcoeff = derivative.subs(dict(zip(p, variable_point)))*Acoeff
    assert all(s.degree(s.expand(v), x) <= 1 for v in Fcoeff.todok().values())
    spatial_A = set(gauge[12:])
    assert all(s.degree(s.sympify(v, locals={'x': x}), x) <= 0
               for i, j, v in transfer['X0']['entries'] if i in spatial_A)
    print('PASS original spatial-A initial kernel zero and proper first curvature; both auxiliary time boundaries zero', flush=True)

    rho = s.Rational(causal['rho'])
    lo, hi = 3*rho*rho/4, 4*rho*rho/5
    assert factor_expr.count_roots(lo, hi) == 1
    sign = s.sign(factor_expr.eval(lo))
    assert sign*factor_expr.eval(hi) < 0
    for _ in range(220):
        mid = (lo+hi)/2
        value = sign*factor_expr.eval(mid)
        assert value
        if value > 0:
            lo = mid
        else:
            hi = mid
    root_box = tuple(F(int(v.p), int(v.q)) for v in [lo, hi])
    denominator = h.polynomial(s.sympify(transfer['theta_denominator'], locals={'x': x, 'U': U}).subs(x, 6*(1-s.I)))
    conjugate_den = POLY.from_dict({power: h.conjugate(v) for power, v in denominator.items()})
    modulus = (denominator*conjugate_den).rem(factor)
    denominator_box = interval.evaluate_interval(modulus, root_box)
    assert denominator_box[0] > 0

    # Actual diagonal two-Laplace Gram. Use the source moment bound before P,
    # so the same comparison pays raw, centered and mean decompositions.
    variance = tuple(map(F, moments['noise_zero']['rational']))
    mean = tuple(map(F, moments['mean_zero']['rational']))
    mean_squared = interval.multiply(mean, mean)
    raw0 = interval.add(variance, mean_squared)
    assert variance[1] < 49 and raw0[1] < 49
    absz2 = F(7776, 125)
    assert s.expand(frequency*s.conjugate(frequency)) == s.Rational(absz2.numerator, absz2.denominator)
    assert 2*rho*rho < s.Rational(1, 90000)**2 and absz2 > 49
    shift_error = F(8, 90000)
    gram_error = 2*shift_error+shift_error**2
    noise_connected = (variance[0]/absz2-gram_error, variance[1]/absz2+gram_error)
    noise_raw = (raw0[0]/absz2-gram_error, raw0[1]/absz2+gram_error)
    assert noise_connected[0] > 0 and noise_raw[0] > 0

    curvature_matrix = h.matrix(72, 48, [(i, j, h.scalar(s.sympify(v, locals=symbols).subs(dict(zip(p, reader)))))
                                         for i, j, v in kinetic['curvature_derivative']['entries']])
    star = h.stored_matrix(kinetic['source_hodge'])
    star72 = h.matrix(72, 72, [(12*i+a, 12*j+a, value)
                              for (i, j), value in star.to_dok().items() for a in range(12)])
    bmap = star72.matmul(curvature_matrix).scalarmul(-K.convert(2))
    correction_from_density = bmap.transpose().matmul(QBcolumn).scalarmul(K.one/K.convert(2))
    assert (correction-correction_from_density).is_zero_matrix
    reduced_tables = {tuple(row['reader']): row['reduced_external_vertex'] for row in reduction['readers']}
    Xr = X.extract(reduced_fields, range(6))
    Xrbar = h.conjugate_matrix(Xr)

    def coefficients_to_poly(table):
        value = POLY.zero
        for (i, j), v in table.to_dok().items():
            value += POLY.ground_new(v/K.convert(2))*h.u**(i+j)
        return value.rem(factor)

    correction_rows = correction.to_dok()
    rows = []
    for index, row in enumerate(vertices['readers']):
        assert row['reader'] == [index//12, index % 12]
        Q = h.bijet(row['Q0_bijet'], list(map(h.scalar, left)), list(map(h.scalar, right)))
        primitive = quadratic(Q, half=True)
        addition = POLY.from_dict({(j,): correction_rows[index, j] for j in range(6) if (index, j) in correction_rows})
        native = (primitive+addition).rem(factor)
        bgset = set(bg)
        Qbf = h.matrix(289, 289, [(i, j, v) for (i, j), v in Q.to_dok().items() if i in bgset or j in bgset])
        table = reduced_tables[tuple(row['reader'])]
        substitution = dict(zip(p, right)) | dict(zip(r, reader))
        Qred = h.matrix(64, 64, [(i, j, h.scalar(s.sympify(v, locals=symbols | {str(t): t for t in r}).subs(substitution)))
                                for i, j, v in table['entries']])
        reduced_gauge = coefficients_to_poly(Xrbar.transpose().matmul(Qred).matmul(Xr))
        assert reduced_gauge == (quadratic(Qbf, half=True)+addition).rem(factor)
        boxes = []
        for value in [primitive, addition, native]:
            assert all(h.conjugate(v) == v for v in value.values())
            if value:
                assert value.gcd(factor).degree() == 0
                box = interval.multiply(interval.evaluate_interval(value, root_box), interval.inverse(denominator_box))
                assert box[0] > 0 or box[1] < 0
            else:
                box = (F(0), F(0))
            boxes.append(box)
        rows.append({'reader': row['reader'], 'primitive_numerator': h.encode_poly(primitive),
                     'second_auxiliary_correction_numerator': h.encode_poly(addition),
                     'reduced_current_numerator': h.encode_poly(native),
                     'nonzero_auxiliary_correction': bool(addition), 'nonzero_reduced_current': bool(native),
                     'primitive_interval': interval.interval_record(boxes[0]),
                     'auxiliary_correction_interval': interval.interval_record(boxes[1]),
                     'reduced_coefficient_interval': interval.interval_record(boxes[2]),
                     'connected_native_current_interval': interval.interval_record(interval.multiply(boxes[2], noise_connected)),
                     'raw_native_current_interval': interval.interval_record(interval.multiply(boxes[2], noise_raw)),
                     'original_nonlinear_auxiliary_equation_paid': True,
                     'direct_reduced_density_readback': True})
    selected = next(row for row in rows if row['reader'] == [1, 1])
    result = {'scope': 'STRIKE_ACTUAL_THETA_SECOND_AUXILIARY_BACKWRITE_AND_NATIVE_REDUCED_GAUGE_CURRENT',
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_sha256': original['source_sha256'], 'physical_lambda': str(frequency),
        'physical_momentum': list(map(str, kin)), 'left_field_derivative': list(map(str, left)),
        'right_field_derivative': list(map(str, right)), 'weak_reader_derivative': list(map(str, reader)),
        'reader_derivative_identity': 'r=-left-right gives the local Euler current; after the true two-time Laplace transform r0=-conj(lambda)-lambda',
        'second_auxiliary_backwrite_numerator': {'shape': list(Bsecond.shape), 'entries':
            [[i, j, str(K.to_sympy(v))] for (i, j), v in sorted(Bsecond.to_dok().items())]},
        'source_Bg_linear_equations_zero': True, 'spatial_A_initial_kernel_zero': True,
        'first_curvature_strictly_proper': True, 'both_polarized_auxiliary_initial_boundaries_zero': True,
        'all48_two_independent_reduced_current_readbacks': True,
        'root_interval': list(map(str, root_box)), 'positive_denominator_interval': interval.interval_record(denominator_box),
        'connected_noise_interval': interval.interval_record(noise_connected), 'raw_noise_interval': interval.interval_record(noise_raw),
        'noise_bound_source': 'original pre-projection full-time B_k comparison <=8|k| for eta>=5; |Bhat_0 psi|<1; both original Gram legs retained',
        'readers': rows, 'selected_reader': selected,
        'nonzero_auxiliary_correction_count': sum(row['nonzero_auxiliary_correction'] for row in rows),
        'nonzero_native_current_count': sum(row['nonzero_reduced_current'] for row in rows),
        'time_scope': 'same actual zero-past theta field, two-time polarization of the local Euler current, actual common Laplace domain',
        'amplitude_scope': 'second fluctuation amplitude on the true nonlinear Bg constitutive graph; other nonlinear fields are not supplied by this algebraic writeback',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'current.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS all48 true nonlinear auxiliary corrections and direct reduced Euler current', result['elapsed_seconds'], flush=True)
    print('selected native coefficient', selected['reduced_coefficient_interval']['decimal_outward'], flush=True)


if __name__ == '__main__':
    main()
