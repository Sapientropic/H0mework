#!/usr/bin/env python3
"""Combine the native reader, constitutive field variation and actual source."""
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
    began = time.monotonic()
    box = load(FQ/'packet-gauge-response/response.py', 'native_response_boxes')
    paths = [FQ/'packet-gauge-joint-momentum-jet/jets.json.gz', FQ/'packet-gauge-joint-momentum-jet/source.json',
             BASE/'active-gauge/receipt.json', FQ/'packet-gauge-reduced-current/current.json',
             FQ/'packet-gauge-reduced-contact/contact.json', FQ/'packet-gauge-bilocal/vertices.json',
             FQ/'packet-gauge-constitutive-vertex/vertices.json', FQ/'packet-gauge-kinetic/receipt.json',
             FQ/'packet-current-hessian/integrals.json', FQ/'packet-gauge-noise/intervals.json',
             FQ/'packet-gauge-cosine-curvature/probe-bounds.json']
    jets, source, original, baseline, contacts, vertices, bv, kinetic, moments, variation, probe = map(read, paths)
    assert jets['derivatives'][0]['physical_s_derivative_order'] == 0
    X, I0 = [h.stored_matrix(jets[key]) for key in ['X0_numerator_coefficients', 'I0_numerator_coefficients']]
    X1, I1 = [h.stored_matrix(jets['derivatives'][0][key])
              for key in ['X1_numerator_coefficients', 'I1_numerator_coefficients']]
    frequency = s.sympify(jets['physical_lambda'])
    kin = list(map(s.sympify, jets['physical_k_in']))
    point = [frequency, *[s.I*k for k in kin]]
    left = list(map(s.conjugate, point))
    reader = [-s.expand(a+b) for a, b in zip(left, point)]
    assert [str(v) for v in reader] == baseline['weak_reader_derivative']
    ray = s.symbols('s', real=True)
    V = h.matrix(289, 289, [(i, j, h.scalar(s.sympify(v, locals={'s': ray}).subs(ray, 0)))
                           for i, j, v in source['source_polynomial']['V']['entries']])
    H = h.operator(original['Fourier_Jacobi_entries'], point)
    assert (H.matmul(X)-I0).is_zero_matrix
    assert (H.matmul(X1)+V.matmul(X)-I1).is_zero_matrix
    Xbar, X1bar = h.conjugate_matrix(X), h.conjugate_matrix(X1)
    Hbar, Vbar = h.conjugate_matrix(H), h.conjugate_matrix(V)
    assert (Hbar.matmul(X1bar)+Vbar.matmul(Xbar)-h.conjugate_matrix(I1)).is_zero_matrix
    print('PASS actual constitutive epsilon field variation on both original289 legs', flush=True)

    factor = h.polynomial(s.sympify(jets['incoming_complete_Fhat'], locals={'U': U}))
    root_box = tuple(map(F, baseline['root_interval']))
    denominator_box = tuple(map(F, baseline['positive_denominator_interval']['rational']))
    assert denominator_box[0] > 0
    p = list(s.symbols('p0:4', real=True))
    q = list(s.symbols('q0:4', real=True))
    r = list(s.symbols('r0:4', real=True))
    substitutions = dict.fromkeys(q, 0) | dict(zip(r, reader))
    names = {str(v): v for v in [*p, *q, *r]}
    derivative = h.matrix(72, 48, [(i, j, h.scalar(s.sympify(v, locals=names).subs(dict(zip(p, reader)))))
                                   for i, j, v in kinetic['curvature_derivative']['entries']])
    star = h.stored_matrix(kinetic['source_hodge'])
    star72 = h.matrix(72, 72, [(12*i+a, 12*j+a, v)
                              for (i, j), v in star.to_dok().items() for a in range(12)])
    bmap = star72.matmul(derivative).scalarmul(-K.convert(2)).to_dok()
    QB = [h.stored_matrix(row['Q']) for row in bv['original_unit_auxiliary_readers']]
    Qcontact = {tuple(row['reader']): row['native_contact_complete'] for row in contacts['readers']}
    old = {tuple(row['reader']): row for row in baseline['readers']}

    @lru_cache(None)
    def coefficient(v):
        return h.scalar(s.sympify(v, locals=names).subs(substitutions))

    def pair(a, Q, b):
        out = POLY.zero
        for (i, j), value in a.transpose().matmul(Q).matmul(b).to_dok().items():
            out += POLY.ground_new(value/K.convert(2))*h.u**(i+j)
        return out.rem(factor)

    def interval(poly):
        if not poly:
            return (F(0), F(0))
        assert all(h.conjugate(v) == v for v in poly.values())
        assert poly.gcd(factor).degree() == 0
        return box.multiply(box.evaluate_interval(poly, root_box), box.inverse(denominator_box))

    def data_interval(record):
        return tuple(map(F, record['rational']))

    variance = data_interval(moments['noise_zero'])
    mean0 = data_interval(moments['mean_zero'])
    mean1 = data_interval(variation['generated_intervals']['mean'])
    connected1 = data_interval(variation['generated_intervals']['noise_derivative'])
    raw0 = box.add(variance, box.multiply(mean0, mean0))
    raw1 = box.add(connected1, tuple(2*v for v in box.multiply(mean0, mean1)))
    variation_norm = data_interval(variation['generated_intervals']['variation_vector_norm_squared'])
    assert variance[1] < 49 and raw0[1] < 49 and variation_norm[1] < 16
    assert box.add(variation_norm, box.multiply(mean1, mean1))[1] < 25
    absz2 = F(7776, 125)
    assert s.expand(frequency*s.conjugate(frequency)) == s.Rational(absz2.numerator, absz2.denominator)
    assert absz2 > 49 and s.expand(sum(v*v for v in kin)) < s.Rational(1, 90000)**2
    Jlip = F(probe['eta_ge5_constants']['J_probe_Lipschitz'])
    eta = s.symbols('eta', positive=True)
    Clip = F(str(s.sympify(probe['weighted_probe_difference']['0']['probe_Lipschitz_Laplace_bound'],
                           locals={'eta': eta}).subs(eta, 5)))
    dJ, dC = Jlip/F(90000), Clip/F(90000)
    error0 = 2*dJ+dJ*dJ
    error1c = 2*(dC+F(4, 7)*dJ+dC*dJ)
    error1r = 2*(dC+F(5, 7)*dJ+dC*dJ)

    def transport(value, error):
        return value[0]/absz2-error, value[1]/absz2+error

    Nc0, Nr0 = transport(variance, error0), transport(raw0, error0)
    Nc1, Nr1 = transport(connected1, error1c), transport(raw1, error1r)
    assert Nc0[0] > 0 and Nr0[0] > 0 and Nc1[0] > 0 and Nr1[0] > 0
    rows = []
    for index, row in enumerate(vertices['readers']):
        Q = h.bijet(row['Q0_bijet'], list(map(h.scalar, left)), list(map(h.scalar, point)))
        for i in range(72):
            if (i, index) in bmap:
                Q += QB[i].scalarmul(bmap[i, index])
        assert (Q-h.conjugate_matrix(Q).transpose()).is_zero_matrix
        current = pair(Xbar, Q, X)
        assert current == h.polynomial(s.sympify(old[tuple(row['reader'])]['reduced_current_numerator'], locals={'U': U}))
        Qp = h.matrix(289, 289, [(i, j, coefficient(v)) for i, j, v in Qcontact[tuple(row['reader'])]['entries']])
        direct = pair(Xbar, Qp, X)
        field = (pair(X1bar, Q, X)+pair(Xbar, Q, X1)).rem(factor)
        native_prime = (field+direct).rem(factor)
        C0, Cf, Cq, C1 = map(interval, [current, field, direct, native_prime])
        connected = box.add(box.multiply(C1, Nc0), box.multiply(C0, Nc1))
        raw = box.add(box.multiply(C1, Nr0), box.multiply(C0, Nr1))
        rows.append({'reader': row['reader'], 'unvaried_current_numerator': h.encode_poly(current),
                     'native_field_variation_numerator': h.encode_poly(field),
                     'native_reader_contact_numerator': h.encode_poly(direct),
                     'native_coefficient_variation_numerator': h.encode_poly(native_prime),
                     'native_field_variation_interval': box.interval_record(Cf),
                     'native_reader_contact_interval': box.interval_record(Cq),
                     'native_coefficient_variation_interval': box.interval_record(C1),
                     'connected_total_response_interval': box.interval_record(connected),
                     'raw_total_response_interval': box.interval_record(raw),
                     'connected_strict_sign': 1 if connected[0] > 0 else -1 if connected[1] < 0 else 0,
                     'raw_strict_sign': 1 if raw[0] > 0 else -1 if raw[1] < 0 else 0})
    selected = next(row for row in rows if row['reader'] == [1, 1])
    result = {'scope': 'STRIKE_NATIVE_CURRENT_FREQUENCY_RESPONSE_WITH_CONSTITUTIVE_FIELD_CONTACT_AND_ACTUAL_SOURCE',
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'physical_lambda': str(frequency), 'physical_k': list(map(str, kin)),
        'root_interval': list(map(str, root_box)),
        'all289_constitutive_variation_readback': True,
        'constant_input_q': True, 'weak_Euler_reader_derivative': list(map(str, reader)),
        'field_scope': 'X1 is the background-epsilon field derivative at external momentum s=0; not its external-momentum derivative',
        'native_variation': 'C1=1/2[X1bar Qeff X0+X0bar Qeff X1+X0bar Qeffprime X0]; response=C1 N0+C0 N1',
        'source_intervals': {k: box.interval_record(v) for k, v in [('connected0', Nc0), ('connected1', Nc1), ('raw0', Nr0), ('raw1', Nr1)]},
        'source_probe_bounds': {'Jlip': str(Jlip), 'Clip': str(Clip), 'dJ': str(dJ), 'dC': str(dC),
                                'both_complex_legs_kept': True, 'fixed_preparation_and_P': True},
        'readers': rows, 'selected_reader': selected,
        'strict_connected_response_count': sum(row['connected_strict_sign'] != 0 for row in rows),
        'strict_raw_response_count': sum(row['raw_strict_sign'] != 0 for row in rows),
        'time_consumer': 'JointCausal and JointFamily identify these actual frequency derivatives with the same retarded finite-family current; this capsule retains the explicit frequency algebra until those consumer receipts are attached.',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'response.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS all48 native field/contact/source responses', result['strict_raw_response_count'], result['elapsed_seconds'], flush=True)
    print('native S01 raw interval', selected['raw_total_response_interval']['decimal_outward'], flush=True)


if __name__ == '__main__':
    main()
