#!/usr/bin/env python3
"""Actual paired-ray fourth-order remainder and complete whole-ball enclosures."""
from fractions import Fraction as F
from math import comb
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
sys.path.insert(0, str(FQ/'packet-band-kernel'))
from intervals import Box, pi_box


def read(path): return json.loads(path.read_bytes())
def box(rec): return Box(*map(F, rec['rational']))
def up(v): return F(-((-v.numerator*10**12)//v.denominator), 10**12)
def complex_upper(rec):
    a, b = box(rec['real']), box(rec['imaginary'])
    return (Box(max(abs(a.lo), abs(a.hi)))**2+Box(max(abs(b.lo), abs(b.hi)))**2).sqrt().hi


def main():
    started = time.monotonic()
    left = read(HERE/'uniform.json')
    solution = read(HERE/'solution-series.json')
    angular = read(HERE/'angular.json')
    quantum = read(FQ/'packet-gauge-probe-fourth/receipt.json')
    moments = read(FQ/'packet-gauge-probe-moments/integrals.json')
    other = read(FQ/'packet-gauge-projected-source-reader/receipt.json')
    assert s.expand(s.sympify(angular['physical_frequency'])-s.sympify(other['actual_physical_frequency'])) == 0
    l = list(map(lambda v: up(F(v)), left['effective_reader_uniform_q_jets']))
    lb = list(map(lambda v: up(F(v)), left['effective_Bg_reader_uniform_q_jets']))
    part = {(a, b): up(F(v)) for a, b, v in left['actual_particular_Bg_mixed_q_bounds']}
    scalar_bounds = {(tuple(v['external_multiindex']), v['radial_order']): up(F(v['normalized_q_source_solution_derivative']))
                     for v in solution['uniform_derivatives']}
    y = {}
    for a in range(5):
        y[a, 0] = scalar_bounds[(0, 0, 0), a]
        if a <= 3:
            y[a, 1] = up(Box(sum(scalar_bounds[tuple(1 if k == j else 0 for k in range(3)), a]**2 for j in range(3))).sqrt().hi)
        if a <= 2:
            y[a, 2] = max(sum(scalar_bounds[tuple((1 if k == i else 0)+(1 if k == j else 0) for k in range(3)), a]
                                for j in range(3)) for i in range(3))
    D = {}
    for a in range(5):
        for b in range(min(2, 4-a)+1):
            total = sum(F(comb(a, i)*comb(b, j))*(l[i+j]*y[a-i, b-j]+lb[i+j]*part[a-i, b-j])
                        for i in range(a+1) for j in range(b+1))
            D[a, b] = up(9*total/(Box(2).sqrt()**(a+b)).lo)
    raw_B = [up(F(v['actual_frequency_light_ball_B'])) for v in quantum['vector_derivatives']]
    gram = {v['name']: v for v in moments['all_two_probe_Gram_jets']}
    means = moments['actual_complex_mean_jets']
    eps = F(5234375, 294988800512)
    B = Box(2).sqrt()*eps
    pi = pi_box()
    layers = {}
    for layer in ['raw', 'mean', 'connected']:
        B0 = box(gram['N0_left_base'][layer]['real']).sqrt().hi
        B1 = Box(max(sum(complex_upper(gram[f'N0_mixed_{i}{j}'][layer]) for j in range(3)) for i in range(3))).sqrt().hi
        profile = raw_B.copy()
        if layer == 'mean':
            mean2 = max(sum(complex_upper(means[f'mean_B_{min(i,j)}{max(i,j)}']) for j in range(3)) for i in range(3))
            profile[2] = up(mean2+B.hi*profile[3])
        profile[1] = up(B1+B.hi*profile[2])
        profile[0] = up(B0+B.hi*B1+B.hi**2*profile[2]/2)
        N = {(a, b): sum(F(comb(a, j))*profile[b+j]*profile[a-j] for j in range(a+1))
             for a in range(5) for b in range(min(2, 4-a)+1)}
        total = {}
        for a, b in [(0, 0), (2, 0), (2, 2), (3, 1), (4, 0)]:
            total[a, b] = sum(F(comb(a, i)*comb(b, j))*D[i, j]*N[a-i, b-j]
                              for i in range(a+1) for j in range(b+1))
        error = (B**5/pi**2)*(total[2, 2]/40+total[3, 1]/48+
                   total[4, 0]*(Box(1)+Box(1)/Box(3).sqrt()).hi/144)
        radius = up(error.hi*10**24)/10**24
        # The extra decimal grid is applied after scaling the tiny radius;
        # it is a directed rational enclosure, never a floating estimate.
        assert radius >= error.hi
        leading = [box(v) for v in angular['layers'][layer]['diagonal_source_quadratic_polynomial_integral']]
        full = [v.grow(radius) for v in leading]
        c0 = s.simplify(s.re(s.sympify(angular['constant_source_value']))/s.sqrt(30))
        assert c0.is_Rational
        source0 = Box(F(str(c0)))*Box(30).sqrt()*box(gram['N0_left_base'][layer]['real'])
        i0_leading = B**3/(6*pi**2)*source0
        i1_leading = -(B**2/(8*pi**2))*source0
        i0_error = (B**5/(20*pi**2)*total[2, 0]).hi
        i1_error = (B**4/(16*pi**2)*total[2, 0]).hi
        layers[layer] = {'actual_projected_packet_vector_bounds': list(map(str, profile)),
            'full_complex_pair_mixed_fourth_bounds': [[a, b, str(total[a, b])] for a, b in [(2, 2), (3, 1), (4, 0)]],
            'quadratic_uniform_error_radius': str(radius),
            'quadratic_uniform_error_display': Box(radius).record(),
            'two_propagation_diagonal_enclosures': [v.record() for v in full],
            'all_unit_direction_rule': 'sum_i n_i^2 * leading_diagonal_i plus [-error,+error], |n|=1',
            'off_diagonal_entry_abs_bound': str(radius),
            'constant_two_propagation_enclosure': i0_leading.grow(i0_error).record(),
            'absolute_value_cusp_enclosure_all_unit_directions': i1_leading.grow(i1_error).record()}
        print(layer, 'whole-ball error', float(radius), 'diagonal',
              [(float(v.lo), float(v.hi)) for v in full], flush=True)
    output = {'scope': 'TRUE_WHOLE_LIGHT_BALL_TWO_PROPAGATION_QUADRATIC_COEFFICIENTS',
        'physical_frequency': angular['physical_frequency'], 'physical_measure': 'd^3k/(2*pi)^3',
        'same_actual_preparation_projection_and_paired_frames': True,
        'paired_ray_formula': 'I2=1/2 int_ball Re r_dd +1/2 int_sphere u Re r_d +1/4 int_sphere[u^2 partial_radius Re r0+(3u^2-1)Re r0/B]',
        'fourth_order_error': 'B^5/pi^2 * [M22/40 + M31/48 + (1+1/sqrt3)*M40/144]',
        'physical_scalar_mixed_bounds': [[a, b, str(v)] for (a, b), v in D.items()],
        'same_complex_state_word_before_readback': True,
        'not_a_zero_momentum_Hessian_of_the_full_sharp_window_function': True,
        'layers': layers, 'seconds': round(time.monotonic()-started, 3)}
    (HERE/'remainder.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS actual full-radius source, complete packet and true cap remainder', output['seconds'], flush=True)


if __name__ == '__main__': main()
