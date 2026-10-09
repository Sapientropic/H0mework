"""Independent rational Mark flow and raw-factor contraction for the full gate."""
from fractions import Fraction as Q
from math import factorial

import atomic_dipole as dipole
import bsm_retry_source as bsm
import fluorescence_channel as channel


def require(value, reason):
    if not value:
        raise ValueError(reason)


def background_masses(law, duration, scale=Q(1), order=32):
    gate = bsm.BSMSource.from_record(law['BG_source']['raw_BSM_gate'])
    rates = [Q(x)*scale for x in law['BG_source']['BG_rates_per_second']]
    total = sum(rates, Q(0)); marks = {bsm.INITIAL}; pending = [bsm.INITIAL]
    while pending:
        mark = pending.pop()
        if mark.receipt is not None:
            continue
        for port in range(4):
            target = gate.target(mark, port)
            if target not in marks:
                marks.add(target); pending.append(target)
    state = {bsm.INITIAL: Q(1)}; coefficient = dict(state)
    for n in range(1, order+1):
        image = {mark: Q(0) for mark in marks}
        for mark, value in coefficient.items():
            if mark.receipt is not None:
                continue
            image[mark] -= total*value
            for port, rate in enumerate(rates): image[gate.target(mark, port)] += rate*value
        coefficient = {mark: value*duration/n for mark, value in image.items() if value}
        for mark, value in coefficient.items(): state[mark] = state.get(mark, Q(0))+value
    # The exact Mark semigroup contracts l1, so the integral Taylor remainder
    # uses ||A||_1<=2 beta without a Hamiltonian or matrix exponential factor.
    error = (2*total*duration)**(order+1)/factorial(order+1)
    masses = [sum((value for mark, value in state.items() if mark.receipt == p), Q(0)) for p in range(4)]
    return masses, error, len(marks)


def _rational(value):
    require(not value.imag and all(root == 1 for root, _ in value.real.terms),
            'the completed scalar must retain its exact rational form')
    return value.real.as_rational()


def _operator(record):
    require(type(record) is list, 'complete original source operator inventory required')
    result = {}
    for row in record:
        require(type(row) is list and len(row) == 3, 'source operator entry required')
        i, j, value = row
        require(type(i) is int and type(j) is int and 0 <= i < 33 and 0 <= j < 33 and (i, j) not in result,
                'duplicate or out-of-range source operator coordinate')
        result[i, j] = channel._complex_record(value)
    return {key: value for key, value in result.items() if value}


def _interval_record(lower, upper, bits=192):
    grid = 1 << bits
    return [str(Q((lower.numerator*grid)//lower.denominator, grid)),
            str(Q(-((-upper.numerator*grid)//upper.denominator), grid))]


def population(raw):
    banks = [{row['factor_id']: channel._read_input(row['complete_retarded_local_endpoint'], 33)
              for row in bank} for bank in raw['checked_local_density_inventories']]
    zero = dipole.ComplexRadical()
    return sum((_rational(banks[0][a].get((dipole.ION, dipole.ION), zero))*
                _rational(banks[1][b].get((dipole.ION, dipole.ION), zero))
                for a, b in raw['source_factor_ids']), Q(0))


def certify(report):
    require(report['schema'] == 'stage10-complete-retarded-receipt-normalizer/rha0028', 'whole gate bound scope changed')
    raw = report['source_record']; law = raw['retarded_detector_law']
    g0, g1 = map(Q, law['gate_seconds']); require(report['receipt_interval_seconds'] == law['gate_seconds'],
        'independent first receipt certification covers the complete original gate')
    projected = report['invariant_empty_face']['four_pattern_poststates']
    require([row['pattern'] for row in projected] == [0, 1, 2, 3] and
        [row['pattern'] for row in report['four_pattern_mass_bounds']] == [0, 1, 2, 3],
        'all four original receipt patterns must be complete and ordered')
    require(report['invariant_empty_face']['source_inlet'] == raw and
        report['invariant_empty_face']['original_empty_time_face']['source_record']['complete_retarded_field_mother'] == law and
        report['complete_source_activity_cap']['source_record']['retarded_source_record'] == law,
        'lower block, complete activity and inlet must belong to the same occurrence')
    legs = law['complete_driven_field_source']['Gaussian_source_legs']; duration = g1-g0
    for leg in legs:
        for name in ('complete_static_H_per_second', 'source_raising_operator_per_second'):
            matrix = _operator(leg[name])
            require(not any((i == dipole.ION) != (j == dipole.ION) for i, j in matrix),
                    'source Hamiltonian does not preserve the empty face')
        for jump in leg['original_physical_natural_jumps']:
            matrix = _operator(jump['normalized_natural_jump_operator'])
            require(not any(i == dipole.ION or j == dipole.ION for i, j in matrix),
                    'a natural source jump radiates from the empty face')
    clock = legs[0]['reference_clock']; require(all(leg['reference_clock'] == clock for leg in legs), 'one source Gamma family required')
    gamma = Q(clock['Gamma_numerical_centre']); lo, hi = map(Q, clock['angular_Gamma_enclosure_per_second'])
    require(0 < lo <= gamma <= hi, 'positive complete Gamma family required')
    low, elow, count = background_masses(law, duration, lo/gamma)
    high, ehigh, _ = background_masses(law, duration, hi/gamma)
    centre = population(raw); error = Q(raw['whole_retarded_gate_input_error'])
    require(Q(report['invariant_empty_face']['empty_source_population_centre']) == centre,
            'empty population differs from the independent raw-factor contraction')
    p_lower, p_upper = max(Q(0), centre-error), max(Q(0), centre+error)
    rows = []
    time_face = report['invariant_empty_face']['original_empty_time_face']
    require([row['pattern'] for row in time_face['four_pattern_poststates']] == [0, 1, 2, 3],
            'all original empty time-face patterns required')
    for p, (a, b, saved, claimed, face) in enumerate(zip(low, high, projected,
            report['four_pattern_mass_bounds'], time_face['four_pattern_poststates'])):
        bg = max(Q(0), a-elow), min(Q(1), b+ehigh)
        interval = bg[0]*p_lower, bg[1]*p_upper
        primary = Q(saved['centre_mass'])-Q(saved['whole_trace_norm_error']), Q(saved['centre_mass'])+Q(saved['whole_trace_norm_error'])
        require(max(interval[0], primary[0]) <= min(interval[1], primary[1]), 'independent BG source mass intervals are disjoint')
        require(claimed['whole_instrument_mass_lower'] == saved['projected_receipt_mass_lower'],
                'whole-gate lower bound does not consume the actual invariant block')
        output = centre*Q(face['centre_mass'])
        payment = error*Q(face['true_empty_effect_upper'])+abs(centre)*Q(face['whole_trace_norm_error'])
        grid = 1 << time_face['scalar_bits']
        outward = Q(-((-payment.numerator*grid)//payment.denominator), grid)
        require(Q(saved['centre_mass']) == output and Q(saved['whole_trace_norm_error']) == outward and
            Q(claimed['whole_instrument_mass_lower']) == max(Q(0), output-payment),
            'whole-gate lower bound or outward price changed')
        require(Q(claimed['whole_instrument_mass_lower']) <= interval[0],
                'whole-gate lower bound exceeds the independent proved subinstrument bound')
        rows.append({'pattern_index': p, 'independent_projected_mass_interval': _interval_record(*interval)})
    source = law['complete_driven_field_source']; pack = source['working_common_optical_source']
    transfer = [[channel._complex_record(z) for z in row] for row in pack['generated_four_by_six_transfer']]
    gram = [[sum((row[i].conjugate()*row[j] for row in transfer), dipole.ComplexRadical())
             for j in range(6)] for i in range(6)]
    require(all(not z for i, row in enumerate(gram) for j, z in enumerate(row) if i != j),
            'this independent activity audit requires the original diagonal transfer Gram')
    kappa = max((_rational(gram[i][i]) for i in range(6)), default=Q(0))
    natural = []
    for leg in legs:
        r = channel._read_input(leg['complete_natural_R_per_second'], 33)
        require(all(i == j for i, j in r), 'original natural source loss is not diagonal')
        require(all(_rational(z) >= 0 for z in r.values()), 'original natural loss is not positive')
        natural.append(max((_rational(z) for z in r.values()), default=Q(0)))
    rate = (kappa*sum(natural, Q(0))+sum(map(Q, law['BG_source']['BG_rates_per_second']), Q(0)))*hi/gamma
    gate = bsm.BSMSource.from_record(law['BG_source']['raw_BSM_gate'])
    require(all(gate.target(bsm.INITIAL, p).receipt is None for p in range(4)), 'one arrival can already trigger a receipt')
    x = rate*duration; require(0 <= x <= 1, 'registered Poisson mean exceeds the independent alternating-series range')
    exponential = sum(((-x)**n/factorial(n) for n in range(33)), Q(0)); tail = x**33/factorial(33)
    cap = min(Q(1), max(Q(0), 1-max(Q(0), exponential-tail)*(1+x)))
    primary_cap = report['complete_source_activity_cap']
    require(Q(primary_cap['source_record']['source_activity']['registered_total_activity_upper_per_second']) == rate and
        Q(primary_cap['whole_first_receipt_input_contraction_upper']) >= cap,
        'independent complete activity or Poisson enclosure changed')
    union_upper = Q(raw['source_positive_mass_upper'])*Q(primary_cap['whole_first_receipt_input_contraction_upper'])
    union_lower = sum((Q(row['whole_instrument_mass_lower']) for row in report['four_pattern_mass_bounds']), Q(0))
    require(report['whole_first_receipt_mass_interval'] == list(map(str, (union_lower, union_upper))) and
        all(Q(row['whole_instrument_mass_upper']) == union_upper for row in report['four_pattern_mass_bounds']),
        'whole receipt interval does not consume the same full activity and positive mass')
    require(report['whole_first_receipt_strictly_positive'] is (union_lower > 0) and
        report['four_pattern_masses_strictly_positive'] is all(Q(row['whole_instrument_mass_lower']) > 0
            for row in report['four_pattern_mass_bounds']), 'whole-gate positivity flags changed')
    require(all(report[name] is False for name in ('other_occupation_blocks_replaced_by_empty_face',
        'complete_gate_state_or_response_difference_computed', 'generation1_asserted',
        'actual_hardware_member_asserted', 'actual_hardware_uniquely_identified', 'controller_advance')),
        'whole-gate mass bounds were promoted to a different source or response claim')
    return {'schema': 'stage10-independent-complete-retarded-normalizer/rha0028',
        'independent_rational_mark_count': count, 'exact_empty_population': str(centre),
        'Gamma_family_monotone_BG_endpoints_checked': True, 'complete_source_activity_rederived': True,
        'four_pattern_mass_bounds': rows, 'whole_first_receipt_mass_interval': report['whole_first_receipt_mass_interval'],
        'complete_gate_state_or_response_difference_computed': False, 'actual_hardware_uniquely_identified': False,
        'controller_advance': False}
