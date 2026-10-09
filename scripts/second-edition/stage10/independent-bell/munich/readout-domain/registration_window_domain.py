"""Raw birth support -> complete flight domains and joint registration faces.

The normalization is the registered D1 reference, Gamma=2*pi*5.75 MHz.
The broad exact 3<pi<4 enclosure suffices for window coverage; no rounded pi
is installed as a physical clock.  These are source-model realizers, not
attestations of the apparatus flight times.
"""
from fractions import Fraction as Q
import json

import atomic_full_forward as full


NS = Q(1, 10**9)
D1_REFERENCE_HZ = Q(5750000)


def _require(condition, reason):
    if not condition:
        raise ValueError(reason)


def covered_flight_domain(birth_support, acceptance_window):
    _require(type(birth_support) is tuple and len(birth_support) == 2 and
             type(acceptance_window) is tuple and len(acceptance_window) == 2,
             'ordered raw birth and acceptance intervals required')
    a, b = map(full.nonnegative, birth_support)
    c, d = map(full.nonnegative, acceptance_window)
    _require(a <= b and c <= d, 'ordered physical time intervals required')
    lower, upper = max(Q(0), c-a), d-b
    return {'status': 'nonempty' if lower < upper else 'empty',
            'flight_seconds': [str(lower), str(upper)],
            'flight_lower_closed': True, 'flight_upper_closed': False,
            'birth_support_seconds': [str(a), str(b)],
            'birth_support_convention': 'closed conservative source enclosure',
            'acceptance_window_seconds': [str(c), str(d)],
            'acceptance_window_convention': 'half-open [start,end)',
            'criterion': 'every source birth plus raw flight lies in the acceptance window'}


def normalized_pulse_domain(raw_segment):
    _require(type(raw_segment) is full.Segment, 'original raw atomic segment required')
    raw = full.Segment.from_record(raw_segment.record())
    _require(all(raw.gammas[key] == 1 for key in full.WIDTHS if key[0] == 'D1'),
             'registered D1-normalized pulse source required')
    unit = (1/(8*D1_REFERENCE_HZ), 1/(6*D1_REFERENCE_HZ))
    birth = (Q(0), raw.duration*unit[1])
    windows = ((3*NS, 243*NS), (3*NS, 163*NS),
               (330*NS, 570*NS), (505*NS, 725*NS))
    return {'schema': 'stage10-source-birth-flight-domain/v1', 'raw_segment': raw.record(),
            'reference_linewidth_Hz': str(D1_REFERENCE_HZ),
            'normalization': 'Gamma_D1 = 2*pi*reference_linewidth; 3 < pi < 4',
            'seconds_per_source_unit_enclosure': list(map(str, unit)),
            'source_birth_support_seconds': list(map(str, birth)),
            'electron_window_starts_are_raw_inverse_choices': True,
            'window_length_source': 'PRL SI I.C: electron 240/160ns, ion 240/220ns',
            'ion_window_end_source': 'PRL SI I.C central ionization+flight endpoints 570/725ns',
            'flight_domains': {key: covered_flight_domain(birth, window)
                               for key, window in zip(('electron_A', 'electron_B', 'ion_A', 'ion_B'), windows)},
            'actual_hardware_uniquely_identified': False, 'actual_flight_parameters_identified': False,
            'controller_advance': False, 'probability_table_or_target_effect_supplied': False}


def registration_face(effective_efficiency):
    eta = full.exact(effective_efficiency)
    _require(0 <= eta <= 1, 'legal raw accepted-fragment efficiency required')
    return {'schema': 'stage10-source-joint-registration-face/v1',
            'registration_order': ['neither', 'electron_only', 'ion_only', 'both'],
            'p00': str(1-eta), 'remaining_simplex_mass': str(eta),
            'constraints': 'p10 >= 0, p01 >= 0, p10+p01 <= eta; p11=eta-p10-p01',
            'raw_joint_registration_is_independent_product': False,
            'constant_both_windows_gate_probability': str(eta),
            'vertices': [[str(1-eta), str(eta), '0', '0'],
                         [str(1-eta), '0', str(eta), '0'],
                         [str(1-eta), '0', '0', str(eta)]],
            'actual_hardware_uniquely_identified': False, 'controller_advance': False}


def registration_point(face, electron_only, ion_only):
    eta, a, b = Q(face['remaining_simplex_mass']), full.nonnegative(electron_only), full.nonnegative(ion_only)
    _require(face == registration_face(eta) and a+b <= eta, 'point outside the source registration face')
    return 1-eta, a, b, eta-a-b


def source_registration_point(face, electron_only, ion_only):
    p00, p10, p01, p11 = registration_point(face, electron_only, ion_only)
    return p00, p01, p10, p11


def paid_joint_domains():
    """Consume the exact already-certified raw model, without new inference."""
    import mode_prefix_intake as paid
    evidence = paid.consume()
    candidate = json.loads(paid.frozen(paid.BASE/'hardware-inverse-first-hi0002.json',
                                      evidence['science_freeze']))
    template = full.Segment.from_record(candidate['raw_template'])
    geometry = normalized_pulse_domain(template)
    runs = []
    for run in candidate['runs']:
        sides = []
        for index, side in enumerate(('alice', 'bob')):
            d, eta = map(Q.from_float, run['raw_parameters'][8+2*index:10+2*index])
            sides.append({'side': side, 'raw_background': str(d),
                          'accepted_efficiency_from_raw_candidate': str(eta),
                          'raw_registration_face': registration_face(eta)})
        runs.append({'run': run['run'], 'sides': sides})
    _require([run['run'] for run in runs] == [run['run'] for run in evidence['runs']],
             'same original source runs required')
    return {'schema': 'stage10-paid-source-registration-window-domains/v1',
            'prior_full_joint_membership': evidence, 'window_geometry': geometry, 'runs': runs,
            'constant_gate_source_reduction_certified': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False,
            'new_confidence_budget_spent': False, 'archive_files_read': 0,
            'new_numerical_solves': 0, 'new_statistical_executions': 0}
