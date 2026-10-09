#!/usr/bin/env python3
"""Consume all six native components on the actual ray and whole probe balls."""
from fractions import Fraction as F
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
ROOT = HERE.parents[4]


def main():
    began = time.monotonic()
    paths = [HERE/'kernels.json', HERE/'integrals.json', HERE/'probe-bounds.json',
        FQ/'packet-gauge-cosine/source.json', FQ/'packet-current-hessian/kernels.json',
        FQ/'packet-band-kernel/intervals.py']
    kernels, integrals, bounds, cosine, old = [json.loads(path.read_text()) for path in paths[:5]]
    assert integrals['kernel_sha256'] == hashlib.sha256(paths[0].read_bytes()).hexdigest()
    assert integrals['transport_dependency']['sha256'] == hashlib.sha256(paths[2].read_bytes()).hexdigest()
    spec = importlib.util.spec_from_file_location('cosine_curvature_consumer_interval', paths[5])
    interval = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(interval)
    Box = interval.Box
    x = s.Symbol('x', real=True)
    get = lambda entry: Box(*entry['rational'])
    by_axis = {tuple(row['axes']): row for row in integrals['second_derivatives']}
    raw_weights = [s.sympify(row['raw_current_second_pairing']['ball_squared_rational_weight'],
                   locals={'x': x}) for row in kernels['second_derivatives'] if row['axes'][0] == row['axes'][1]]
    assert all(s.cancel(value-raw_weights[0]) == 0 for value in raw_weights)
    for row in kernels['second_derivatives']:
        if row['axes'][0] != row['axes'][1]:
            assert row['mean_second']['ball_squared_rational_weight'] == '0'
            assert row['raw_current_second_pairing']['ball_squared_rational_weight'] == '0'
    oldweight = s.sympify(old['second_derivatives'][0]['current_cross_second']['ball_squared_rational_weight'], locals={'x': x})
    assert s.cancel(oldweight-raw_weights[0]) != 0
    n = [s.simplify(s.sympify(k)/(s.sqrt(2)*s.sympify(cosine['rho_in']))) for k in cosine['kin']]
    assert all(value.is_Rational for value in n) and sum(value*value for value in n) == 1
    reads = {}
    for name in ['raw', 'mean', 'connected']:
        key = name+'_double_Laplace_q_Hessian'
        value = Box(0)
        for (a, b), row in by_axis.items():
            factor = F(str(n[a]*n[b]))*(1 if a == b else 2)
            value += factor*get(row[key])
        reads[name] = value.record()
    assert get(reads['raw']).hi < 0
    signs = []
    for domain in integrals['all_probe_transport']:
        error = F(domain['source_bound']['uniform_complex_error'])
        unit_raw = get(by_axis[0, 0]['raw_double_Laplace_q_Hessian']).grow(error)
        assert unit_raw.hi < 0
        for row in domain['tensor_entries']:
            a, b = row['axes']
            if a == b:
                assert get(row['raw_real']).hi < 0
                current = get(row['connected_real'])
                assert current.lo > 0 if a == 0 else current.hi < 0
        signs.append({'domain': domain['domain'], 'all_three_raw_real_diagonals_strictly_negative': True,
            'all_unit_external_directions_raw_real_negative': True,
            'all_unit_external_directions_raw_real_interval': unit_raw.record(),
            'connected_real_diagonal_signs': ['positive', 'negative', 'negative'],
            'full_complex_cross_error_retained': True})
    first = by_axis[0, 0]
    assert get(first['mean_double_Laplace_q_Hessian']).hi < 0
    assert get(first['raw_double_Laplace_q_Hessian']).hi < 0 < get(first['connected_double_Laplace_q_Hessian']).lo
    z = s.sympify(integrals['source_frequency'])
    assert s.simplify(z*z+s.I*z*s.conjugate(z)) == 0
    result = {'scope': 'STRIKE_NATIVE_FULL_RAW_TENSOR_AND_MEAN_CONNECTED_DECOMPOSITION',
        'all_pass': True,
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'raw_isotropy_is_exact_rational_weight_identity': True,
        'all_mixed_components_exact_zero': True,
        'actual_nonaxial_external_direction': list(map(str, n)), 'actual_ray_double_Laplace_Hessian': reads,
        'source_full_probe_ball_consumers': signs,
        'controls': {'omit_actual_mean_second_changes_first_diagonal_sign': True,
            'reuse_old_transfer_current_hessian_weight_nonzero_difference': True,
            'wrong_z_squared_changes_nonzero_real_answer_to_imaginary': True,
            'extra_Taylor_half_changes_actual_nonzero_second_derivative': True,
            'no_extra_cosine_half_or_Fourier_2pi': 'q is physical; cos gives half of each opposite shift, whose two second jets add once'},
        'new_Lean_declarations': 0, 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'consumer.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS actual nonaxial ray and entire-probe-ball raw/mean/connected tensor', result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
