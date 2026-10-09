#!/usr/bin/env python3
"""The actual A1(S01) insertion changes the fixed packet's current noise."""
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
x = s.symbols('x', real=True)
p = s.symbols('p1:4', real=True)


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    started = time.monotonic()
    source = load(FQ/'packet-noise/source_kernel.py', 'gauge_noise_original_packet')
    record, data = source.exact_source()
    N, omega, H0, Hj, Cinv, K, w = data
    occupied = json.loads((BASE/'occupied-response/receipt.json').read_text())
    vertices = json.loads((BASE/'matter-vertices/receipt.json').read_text())
    full = json.loads((FQ/'receipt.json').read_text())
    assert occupied['source_sha256'] == vertices['source_sha256'] == full['source_sha256'] == record['source_sha256']
    frame = source.decode(occupied['occupied_frame'])
    Cfull = source.decode(full['time_principal_inverse'])
    density = source.decode(next(row['operator'] for row in vertices['primitive_vertices']
        if row['group'] == 'gauge_A' and row['coordinate'] == [1, 1]))
    raw = density/N  # The original coframe volume is N and stays fixed.
    Vfull = source.clean(-s.I*Cfull*raw)
    V = source.clean(frame.H*Vfull*frame)
    expected = source.decode(occupied['gauge_Hamiltonian_forces'][occupied['gauge_coordinates'].index([1, 1])])
    source.zero(V-expected)
    source.zero(Vfull*frame-frame*V)
    source.zero(frame.H*Vfull-V*frame.H)
    source.zero(V.H-V)
    source.zero(V*K-K*V)
    variation = source.clean((K*V+V.H*K)/N**2)
    source.zero(variation-2*K*V/N**2)
    assert variation.todok()
    H = source.clean(H0+sum((p[a]*Hj[a] for a in range(3)), s.zeros(12)))
    A0 = source.clean(2*K*H/N**2)
    Q, G0 = K/s.sqrt(2), Cinv/(s.I*N)
    source.zero(variation*Q-Q*variation)
    source.zero(A0*Q-Q*A0)
    numerator = {'mean': 0, 'left_cross': 0, 'right_cross': 0, 'variation_second': 0}
    for sign in [-1, 1]:
        seed = source.clean((s.eye(12)+sign*Q)*G0*w/2)
        partner = source.clean((sign*H-omega*s.eye(12))*seed/N)
        vector = source.clean((s.I-3*sign*omega)*seed+sign*N*partner)
        numerator['mean'] += (vector.H*variation*vector)[0]
        numerator['left_cross'] += (vector.H*variation.H*A0*vector)[0]
        numerator['right_cross'] += (vector.H*A0.H*variation*vector)[0]
        numerator['variation_second'] += (vector.H*variation.H*variation*vector)[0]
    def angular(expression):
        result = 0
        for powers, coefficient in s.Poly(s.expand(expression), *p).terms():
            if any(power % 2 for power in powers):
                continue
            total = sum(powers)
            result += coefficient*x**(total//2)*s.prod(s.factorial2(power-1) for power in powers)/s.factorial2(total+1)
        return s.factor(result)
    denominator = (1-3*omega**2+N**2*x)**2+16*omega**2
    weights = {key: s.factor(N**2*angular(value)/denominator) for key, value in numerator.items()}
    radius = s.symbols('r', nonnegative=True)
    norm = s.sympify(record['zero_transfer_raw_norm_integrand'], locals={'r': radius}).subs(radius**2, x)
    mean = s.sympify(record['zero_transfer_raw_mean_integrand'], locals={'r': radius}).subs(radius**2, x)
    first, second = s.symbols('first second')
    expressions = {}
    for name, weight in weights.items():
        equations = s.Poly(s.together(weight-first*norm-second*mean).as_numer_denom()[0], x).all_coeffs()
        solutions = s.solve(equations, [first, second], dict=True)
        assert len(solutions) == 1
        coefficients = solutions[0]
        assert s.cancel(weight-coefficients[first]*norm-coefficients[second]*mean) == 0
        expressions[name] = [s.simplify(coefficients[first]), s.simplify(coefficients[second])]
    mu = s.symbols('mu', real=True)
    normalized = {name: a+b*mu for name, (a, b) in expressions.items()}
    noise_derivative = s.factor(normalized['left_cross']+normalized['right_cross']-2*mu*normalized['mean'])
    centered_second = s.factor(normalized['variation_second']-normalized['mean']**2)
    assert s.simplify(normalized['left_cross']-s.conjugate(normalized['right_cross'])) == 0
    result = {'scope': 'STRIKE_ACTUAL_SELECTED_PRIMITIVE_GAUGE_FIXED_PREPARATION_NOISE_RESPONSE',
        'source_sha256': record['source_sha256'],
        'source_inputs_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [BASE/'matter-vertices/receipt.json', BASE/'occupied-response/receipt.json', FQ/'receipt.json']},
        'gauge': {'spatial_component': 1, 'generator': 'S01', 'primitive_coordinate': [1, 1]},
        'density_to_H': 'rawDiracVertex=densityVertex/N; V=-i*C0_inverse*rawDiracVertex',
        'full252_both_sides_to_same12': True,
        'actual_V_Hermitian_and_commutes_K_on_selected12': True,
        'C_selected': source.encode(variation),
        'radial_weights': {name: str(value) for name, value in weights.items()},
        'normalized_reads_in_original_mu0': {name: str(s.factor(value)) for name, value in normalized.items()},
        'same_transfer_noise_derivative': str(noise_derivative),
        'centered_variation_norm_squared': str(centered_second),
        'fixed_state': 'psi=original E0 eta1 normalized Dirac-filtered unit-ball packet; P and n are independent of epsilon',
        'mu_variable': 'The already source-generated original mean mu0; not a new state or supplied variance.',
        'no_new_halfline_integral': True, 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'selected.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS actual selected current derivative', noise_derivative,
        'mu_prime', s.factor(normalized['mean']), 'centered_norm', centered_second, flush=True)


if __name__ == '__main__':
    main()
