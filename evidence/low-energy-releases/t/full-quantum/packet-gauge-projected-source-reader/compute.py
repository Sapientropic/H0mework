#!/usr/bin/env python3
"""Keep the genuine mean and connected source/contact summands in the ball."""
from fractions import Fraction as F
import hashlib
import importlib.util
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
FQ = HERE.parent
ROOT = HERE.parents[4]
spec = importlib.util.spec_from_file_location('projection_interval_source', FQ/'packet-band-kernel/intervals.py')
intervals = importlib.util.module_from_spec(spec)
spec.loader.exec_module(intervals)
Box = intervals.Box


def box(record):
    return Box(*record['rational'])


def main():
    start = time.monotonic()
    paths = [FQ/'packet-gauge-cosine-curvature/integrals.json',
             FQ/'packet-gauge-cosine-curvature/probe-bounds.json',
             FQ/'packet-gauge-spatial-source-curvature/receipt.json',
             FQ/'packet-gauge-spatial-reader-curvature/shape.json',
             FQ/'packet-gauge-spatial-reader-curvature/bounds.json']
    exact, probes, source, reader, reader_bounds = [json.loads(p.read_bytes()) for p in paths]
    delta = F(probes['whole_original_light_ball']['uniform_complex_error'])
    C = box(source['native_current_coefficient_full_ball'])
    volume = box(source['original_physical_ball_measure'])
    contact = F(reader['all_unit_directions_abs_q_squared_coefficient_upper'])
    assert min(delta, C.lo, volume.lo, contact) > 0
    sectors = {}
    for sector in ['raw', 'mean', 'connected']:
        diagonal = []
        for axis in range(3):
            row = next(v for v in exact['second_derivatives'] if v['axes'] == [axis, axis])
            center = box(row[sector+'_double_Laplace_q_Hessian'])
            hessian = center.grow(delta)
            source_second = volume*C*hessian/2
            total = source_second.grow(contact)
            diagonal.append({'axis': axis, 'zero_probe_source_Hessian': center.record(),
                'whole_light_ball_source_Hessian': hessian.record(),
                'source_two_legs_quadratic_coefficient': source_second.record(45),
                'source_two_legs_plus_reader_quadratic_coefficient': total.record(45)})
        c0, cp = [box(diagonal[i]['zero_probe_source_Hessian']) for i in [0, 1]]
        assert cp.record() == diagonal[2]['zero_probe_source_Hessian']
        source_universal = volume*C*Box(min(c0.lo, cp.lo)-delta, max(c0.hi, cp.hi)+delta)/2
        sectors[sector] = {'diagonal': diagonal,
            'all_unit_directions_zero_probe_form': '(1-n1^2)*perpendicular+n1^2*parallel',
            'parallel': c0.record(), 'perpendicular': cp.record(),
            'all_unit_directions_source_plus_reader_enclosure': source_universal.grow(contact).record(45)}
    for i in range(3):
        assert (box(sectors['raw']['diagonal'][i]['zero_probe_source_Hessian'])
                -box(sectors['mean']['diagonal'][i]['zero_probe_source_Hessian'])
                -box(sectors['connected']['diagonal'][i]['zero_probe_source_Hessian'])).lo <= 0
        assert (box(sectors['raw']['diagonal'][i]['zero_probe_source_Hessian'])
                -box(sectors['mean']['diagonal'][i]['zero_probe_source_Hessian'])
                -box(sectors['connected']['diagonal'][i]['zero_probe_source_Hessian'])).hi >= 0
    for sector in ['raw', 'mean']:
        assert box(sectors[sector]['all_unit_directions_source_plus_reader_enclosure']).hi < 0
    conn = sectors['connected']['diagonal']
    assert box(conn[0]['source_two_legs_plus_reader_quadratic_coefficient']).lo > 0
    assert all(box(conn[i]['source_two_legs_plus_reader_quadratic_coefficient']).hi < 0 for i in [1, 2])
    mixed = (volume*C*Box(-delta, delta)/2).grow(contact)
    result = {'scope': 'ORIGINAL_PROJECTED_TWO_SOURCE_LEGS_AND_READER_WHOLE_BALL_QUADRATIC_TERMS',
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'same_preparation_and_fixed_projection': True,
        'actual_physical_frequency': source['physical_frequency'], 'reader': source['reader'],
        'outgoing_momentum': source['outgoing_momentum'], 'physical_measure': source['original_physical_ball_measure'],
        'projection_error_radius': str(delta), 'reader_abs_quadratic_bound_each_sector': str(contact),
        'sectors': sectors, 'mixed_entries_source_plus_reader_enclosure': mixed.record(45),
        'exact_sector_identity': 'raw=mean+connected before and after every derivative and physical integral',
        'raw_and_mean_all_unit_directions_negative': True,
        'connected_parallel_positive_and_two_coordinate_perpendicular_negative': True,
        'all_unit_direction_bound_rule': 'Multiply the positive C/volume box by ((1-n1^2)*perpendicular+n1^2*parallel)+[-delta,delta], divide by2, then add [-contact,contact].',
        'proof_identity': 'Fixed quantum orthogonal projection acts on the whole F tensor B vector and all its derivatives; source-Hessian transport and reader body/flux norm remainder contract.',
        'remaining_summands': 'The two actual field-propagation terms must still be added in the matching sector.',
        'seconds': round(time.monotonic()-start, 3)}
    (HERE/'receipt.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS actual raw/mean/connected three summands, original measure and Taylor factor, whole-ball bounds', result['seconds'], flush=True)
    for sector, data in sectors.items():
        print(sector, [v['source_two_legs_plus_reader_quadratic_coefficient']['decimal'] for v in data['diagonal']], flush=True)


if __name__ == '__main__':
    main()
