#!/usr/bin/env python3
"""Consume all five original spatial summands in their common state sectors."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
sys.path.insert(0, str(FQ/'packet-band-kernel'))
from intervals import Box


def read(path): return json.loads(path.read_bytes())
def box(value): return Box(*map(F, value['rational']))


def main():
    started = time.monotonic()
    propagation = read(HERE/'remainder.json')
    angular = read(HERE/'angular.json')
    other_path = FQ/'packet-gauge-projected-source-reader/receipt.json'
    other = read(other_path)
    off_other = box(other['mixed_entries_source_plus_reader_enclosure'])
    off_abs = max(abs(off_other.lo), abs(off_other.hi))
    sectors = {}
    for layer in ['raw', 'mean', 'connected']:
        G = propagation['layers'][layer]
        diagonal = [box(v) for v in G['two_propagation_diagonal_enclosures']]
        rest = [box(v['source_two_legs_plus_reader_quadratic_coefficient']) for v in other['sectors'][layer]['diagonal']]
        complete = [a+b for a, b in zip(diagonal, rest)]
        mixed = off_abs+F(G['quadratic_uniform_error_radius'])
        central_boxes = [box(v) for v in angular['layers'][layer]['diagonal_source_quadratic_polynomial_integral']]
        centers = [(v.lo+v.hi)/2 for v in central_boxes]
        error = F(G['quadratic_uniform_error_radius'])+max((v.hi-v.lo)/2 for v in central_boxes)
        error += max(max(abs(v.lo), abs(v.hi))+2*off_abs for v in rest)
        if layer in ['raw', 'connected']:
            assert centers[0] < 0 < centers[1] and centers[2] < 0
            assert min(map(abs, centers)) > error
        sectors[layer] = {'complete_five_diagonal_enclosures': [v.record() for v in complete],
            'complete_five_mixed_entry_abs_bound': str(mixed),
            'mixed_convention': 'T_ij in n^T T n; cross monomial is 2*T_ij*n_i*n_j',
            'same_fixed_state_identity': 'raw=mean+connected before interval enclosure',
            'source_diagonal_reference': list(map(str, centers)),
            'whole_matrix_error_about_reference': str(error),
            'two_negative_one_positive_quadratic_inertia_proved': layer in ['raw', 'connected']}
        print(layer, 'all five diagonal', [(float(v.lo), float(v.hi)) for v in complete], flush=True)
    result = {'scope': 'COMPLETE_FIVE_ORIGINAL_SPATIAL_RESPONSE_SUMMANDS_WHOLE_BALL_QUADRATIC_COEFFICIENT',
              'physical_frequency': propagation['physical_frequency'], 'reader': [1, 1],
              'outgoing_physical_momentum': [0, 0, 0], 'source_and_observer_radius': 'sqrt2*5234375/294988800512',
              'physical_measure': 'd^3k/(2*pi)^3', 'all_five_summands_used_once': True,
              'extra_cosine_or_Taylor_half_added': False, 'raw_mean_connected_original_identity': True,
              'input_sha256': {str(p.relative_to(source_root())): hashlib.sha256(p.read_bytes()).hexdigest()
                  for p in [HERE/'remainder.json', HERE/'angular.json', other_path]},
              'sectors': sectors, 'scope_limit': 'Quadratic coefficient after the actual sharp-window absolute-value term; no claim of a Hessian at q=0 or of a beta function.',
              'seconds': round(time.monotonic()-started, 3)}
    (HERE/'complete.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS actual complete five-summand sector consumer', result['seconds'], flush=True)


def source_root(): return HERE.parents[4]


if __name__ == '__main__': main()
