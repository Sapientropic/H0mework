"""The driven atom and every retarded photon share one source occurrence.

Field coordinates use the full symmetric product measure.  The n-photon
amplitude is the sum of the 2**n source-arm assignments divided by sqrt(n!).
Each local word retains all33 matter coordinates and every intervening
drive.  A numerical bank certifies fixed-start propagator families; missing
families are rejected rather than replaced by a vacuum or an inverse.
"""
from fractions import Fraction as Q
from itertools import product
from math import factorial
from pathlib import Path
import hashlib
import json

import gaussian_atomic_pulse_source as gaussian
import retarded_receipt_source as original

field = gaussian.field
atomic, dipole, full, channel = gaussian.atomic, gaussian.dipole, gaussian.full, gaussian.channel
optical, joint, bsm = original.optical, original.joint, original.bsm
SCHEMA = 'stage10-driven-Gaussian-retarded-field-source/v1'
ZERO = dipole.ComplexRadical()
_ISSUED = {}
_GAUSSIAN_CHECK = gaussian._CHECK


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
            (Path(__file__), *(Path(m.__file__) for m in
              (gaussian, field, original, atomic, dipole, full, channel, optical, joint, bsm)))}


def _freeze_report(report):
    trial = report['untrusted_trial']
    prices = report['complete_piece_prices']
    _require(len(trial['pieces']) == len(prices), 'every source curve piece needs its uniform price')
    pieces = []
    for piece, price in zip(trial['pieces'], prices):
        start, stop = map(Q, price['physical_slice_seconds'])
        _require(stop-start == Q(piece['duration_seconds']), 'source piece clocks disagree')
        modes = tuple((tuple(map(Q, mode['lambda_per_second'])), tuple(
            tuple((i, j, a, b) for i, j, a, b in entries) for entries in mode['coefficients']))
            for mode in piece['modes'])
        pieces.append((start, stop, modes, Q(price['uniform_rotating_operator_error_upper'])))
    return (tuple(map(Q, report['source_interval_seconds'])), trial['mode_bits'], tuple(pieces),
            Q(report['Gamma_math_operator_price']))


def _bank_summary(report):
    return {'certificate_sha256': _digest(report),
            'source_interval_seconds': list(report['source_interval_seconds']),
            'piece_count': len(report['complete_piece_prices']),
            'fixed_start_is_I': report['initial_operator'],
            'operator_norm_error_upper': report['operator_norm_error_upper'],
            'curve_price_scope': 'fixed s, all t in each original certified piece; each numeric frame evaluation is paid separately'}


def _eval(raw, family, start, stop, bits):
    (s, t), mode_bits, pieces, gamma_price = family
    _require(s == start and s <= stop <= t, 'a genuine I-at-s source family must cover the requested clock')
    if stop == start:
        return {(i, i): dipole.ComplexRadical(1) for i in range(full.DIMENSION)}, Q(0)
    for a, b, modes, uniform in pieces:
        if a <= stop <= b:
            u = (stop-a)/(b-a)
            centre = {}; scalar_price = Q(0)
            for (lr, li), coefficients in modes:
                polynomial = {}
                for n, entries in enumerate(coefficients):
                    field._scaled_add(polynomial, field._read_entries([list(e) for e in entries], mode_bits), u**n)
                exponent, error = gaussian._exponential(lr*(stop-a), li*(stop-a), bits)
                field._scaled_add(centre, {key: field._product(exponent, z) for key, z in polynomial.items()}, 1)
                scalar_price += error*field._norm(polynomial)
            physical, frame_price = gaussian._restore(raw, centre, start, stop, bits)
            # uniform already contains all previous joins and endpoint prices,
            # but excludes this evaluation and this physical two-endpoint frame.
            return physical, uniform+scalar_price+frame_price+gamma_price
    raise ValueError('the source bank contains no certified propagator piece at this clock')


def _norm(matrix, bits):
    return field._operator_bound(matrix, bits)


def _multiply(left, left_error, right, right_error, bits):
    matrix = dipole.matrix_product(left, right)
    error = left_error*_norm(right, bits)+right_error*_norm(left, bits)+left_error*right_error
    return matrix, error


def _sqrt_interval(value, bits):
    lo, hi = full._sqrt(value.numerator*value.denominator, bits)
    return lo/value.denominator, hi/value.denominator


def _price_record(value, bits):
    return str(field._price_upper(value, bits))


def _price_rule(bits):
    return {'rule': 'ceil nonnegative public error or norm upper on the registered dyadic grid',
            'bits': bits, 'increment_upper_per_ceil': str(Q(1, 1 << bits)),
            'matrix_centre_quantized_here': False}


def _jump(raw, jumps, side, group, mode, bits):
    pack = raw['working_common_optical_source']
    transfer = pack['generated_four_by_six_transfer']
    clock = raw['reference_clock']; gamma = Q(clock['Gamma_numerical_centre'])
    gamma_lo, gamma_hi = map(Q, clock['angular_Gamma_enclosure_per_second'])
    matrix = {}; scalar_error = Q(0); gamma_error = Q(0)
    for jump in jumps:
        if tuple(jump['group']) != group:
            continue
        index = 3*side+dipole.Q_COMPONENTS.index(jump['q'])
        coefficient = channel._complex_record(transfer[mode[1]][index]) if mode[0] == 'port' else \
            dipole.ComplexRadical(int(mode[1] == index))
        if not coefficient:
            continue
        rate = Q(jump['physical_amplitude_squared_per_second'])
        a, b = _sqrt_interval(rate, bits); centre = (a+b)/2
        lower, _ = _sqrt_interval(rate*gamma_lo/gamma, bits)
        _, upper = _sqrt_interval(rate*gamma_hi/gamma, bits)
        numerical = (b-a)/2
        variation = max(abs(a-lower), abs(upper-b))
        operator = gaussian._matrix(jump['normalized_natural_jump_operator'])
        weight = _norm(operator, bits)*original.bsm._entry_norm({(0, 0): coefficient}, bits=bits)
        field._add(matrix, operator, coefficient*centre)
        scalar_error += numerical*weight; gamma_error += variation*weight
    return matrix, scalar_error+gamma_error, {'sqrt_rate_scalar_price': str(scalar_error),
        'sqrt_Gamma_interval_price': str(gamma_error)}


def _word(source, word):
    _require(type(word) is list, 'an arbitrary finite original field-coordinate word is required')
    groups = source._groups
    for entry in word:
        _require(type(entry) is dict and set(entry) == {'group', 'mode', 'arrival_seconds'} and
                 type(entry['group']) is list and tuple(entry['group']) in groups,
                 'original resolved natural radiation group required')
        mode = entry['mode']
        _require(type(mode) is list and len(mode) == 2 and mode[0] in ('port', 'loss') and
                 type(mode[1]) is int and 0 <= mode[1] < (4 if mode[0] == 'port' else 6),
                 'original four-port or six-mode loss coordinate required')
        full.nonnegative(entry['arrival_seconds'])


def _operator_at(source, side, start, stop, bits):
    raw = source._value
    _require(start <= stop <= Q(raw['Gaussian_source_legs'][side]['duration_seconds']),
             'requested source clock is outside the declared certification horizon; no future vacuum is supplied')
    if start == stop:
        return {(i, i): dipole.ComplexRadical(1) for i in range(full.DIMENSION)}, Q(0)
    families = [f for f in source._banks[side] if f[0][0] == start and stop <= f[0][1]]
    _require(families, 'no certified I-at-s source family; an inverse or endpoint substitution is forbidden')
    family = min(families, key=lambda f: f[0][1])
    # The full-family Gamma price is monotone in its terminal time, so it is
    # also a uniform upper bound for every readout in the same fixed-s family.
    return _eval(raw['Gaussian_source_legs'][side], family, start, stop, bits)


def _amplitude(source, word, observation, bits):
    raw = source._value; _word(source, word)
    origins = tuple(map(Q, raw['emission_origins_seconds']))
    _require(observation >= max(origins) and all(observation-origin <= Q(p['duration_seconds'])
                for origin, p in zip(origins, raw['Gaussian_source_legs'])),
             'observation must lie in both certified Gaussian horizons; future field is not a vacuum')
    operator = {}; error = Q(0); count = 0
    for assignment in product((0, 1), repeat=len(word)):
        if any(Q(e['arrival_seconds'])-Q(raw['flight_seconds'][s]) < origins[s] or
               Q(e['arrival_seconds'])-Q(raw['flight_seconds'][s]) > observation or
               (e['mode'][0] == 'loss' and e['mode'][1]//3 != s)
               for e, s in zip(word, assignment)):
            continue
        entries = tuple([e for e, s in zip(word, assignment) if s == side] for side in (0, 1))
        a, ea = DrivenGaussianFieldSource._local_word(source, 0, entries[0], observation, bits)
        b, eb = DrivenGaussianFieldSource._local_word(source, 1, entries[1], observation, bits)
        field._add(operator, original._tensor(a, b))
        error += ea*_norm(b, bits)+eb*_norm(a, bits)+ea*eb; count += 1
    lower, upper = _sqrt_interval(Q(1, factorial(len(word))), bits)
    normalizer = (lower+upper)/2; normalizer_error = (upper-lower)/2
    error = upper*error+normalizer_error*_norm(operator, bits)
    return {key: value*normalizer for key, value in operator.items() if value*normalizer}, error, count


class DrivenGaussianFieldSource:
    def __init__(self, first, second, *, flight_seconds, emission_origins_seconds=None,
                 gate_seconds=None, gate_start_seconds=None, operator_certificates=((), ())):
        _CHECK()
        pulses = (first, second)
        _require(all(type(p) is gaussian.GaussianAtomicPulseSource for p in pulses),
                 'two closed same-parent Gaussian source legs required; G or prepared rho is not input')
        records = tuple(gaussian.GaussianAtomicPulseSource.record(p) for p in pulses)
        _require(tuple(r['side'] for r in records) == (0, 1) and
                 records[0]['reference_local_parent'] == records[1]['reference_local_parent'],
                 'the two driven legs need the same original reference parent and their own sides')
        parent = records[0]['reference_local_parent']; pack = records[0]['working_common_optical_source']
        _require(all(r['working_common_optical_source'] == pack and r['reference_clock'] == parent['reference_clock']
                     and r['working_aperture_source'] == parent['working_aperture_source'] for r in records),
                 'field, Gamma and aperture must retain the same optical lambda')
        flights = tuple(map(full.nonnegative, flight_seconds))
        if emission_origins_seconds is None:
            ready = Q(parent['source_ready_physical_clock_seconds'])
            origins = tuple(ready+sum((Q(p['raw_controls']['duration_seconds']) for p in plan[:-1]), Q(0))
                            for plan in parent['source_generated_local_plans'])
        else:
            origins = tuple(map(full.nonnegative, emission_origins_seconds))
        _require(len(flights) == len(origins) == 2, 'two raw physical flights and source excitation origins required')
        _require(not (gate_seconds is not None and gate_start_seconds is not None), 'one declared fixed gate origin required')
        width = Q(optical.PUBLIC_SOURCE['2016_arrival_gate_seconds'])
        if gate_seconds is None:
            # The controller offset comes from its same-owner gate.  A flight
            # override must not silently move this fixed detector gate.
            common = optical.CommonOpticalReadout.from_record(pack)
            gate, _ = optical.CommonOpticalReadout.bsm_gate(common)
            base_start = max(origins)+gate.gate_start*Q(pack['common_atomic_owner']['atomic_base']['seconds_per_unit'])
            g0 = base_start if gate_start_seconds is None else full.nonnegative(gate_start_seconds)
            gate_seconds = (g0, g0+width)
        gate_seconds = tuple(map(full.nonnegative, gate_seconds))
        _require(len(gate_seconds) == 2 and gate_seconds[1]-gate_seconds[0] == width and
                 gate_seconds[0] >= max(origins), 'one fixed original 120ns gate after both source origins required')
        _require(type(operator_certificates) in (tuple, list) and len(operator_certificates) == 2,
                 'two source-certified fixed-start operator banks required')
        banks = []; summaries = []; witness_json = []
        for side, reports in enumerate(operator_certificates):
            _require(type(reports) in (tuple, list), 'complete Gaussian operator certificates required')
            rows = []; descriptions = []; witnesses = []
            for report in reports:
                gaussian.GaussianAtomicPulseSource.verify_operator(pulses[side], report)
                rows.append(_freeze_report(report)); descriptions.append(_bank_summary(report))
                witnesses.append(channel._canonical(report))
            _require(len({family[0] for family in rows}) == len(rows), 'duplicate source family interval')
            banks.append(tuple(rows)); summaries.append(descriptions); witness_json.append(tuple(witnesses))
        owner = atomic.MunichAtomicProgramme.from_record(parent['working_atomic_owner'])
        legs = tuple(field._source(owner, side) for side in (0, 1))
        transfer = tuple(tuple(channel._complex_record(v) for v in row) for row in pack['generated_four_by_six_transfer'])
        _, _, loss = joint.passive_transfer(transfer)
        self._pulses = pulses; self._banks = tuple(banks); self._witnesses = tuple(witness_json)
        self._groups = frozenset(tuple(j['group']) for leg in legs for j in leg['original_physical_natural_jumps'])
        self._value = {'schema': SCHEMA, 'Gaussian_source_legs': list(records),
            'reference_local_parent': parent, 'working_common_optical_source': pack,
            'working_atomic_owner': parent['working_atomic_owner'], 'working_aperture_source': parent['working_aperture_source'],
            'reference_clock': parent['reference_clock'], 'physical_legs': list(legs),
            'flight_seconds': list(map(str, flights)), 'emission_origins_seconds': list(map(str, origins)),
            'gate_seconds': list(map(str, gate_seconds)), 'operator_certificate_bank': summaries,
            'loss_environment_gram': [[v.serialize() for v in row] for row in loss],
            'field_basis': 'full symmetric product-coordinate Fock measure; no factorial in the trace',
            'n_photon_amplitude_rule': '(sum source-arm assignments of chronological full33 jump words)/sqrt(n!)',
            'same_arm_repeated_emissions_retained': True, 'all_photon_number_and_time_coherences_retained': True,
            'in_flight_and_loss_fields_retained': True, 'Gaussian_horizon_is_hard_field_cutoff': False,
            'operator_bank_scope': 'fixed-start uniform families only; unsupported s or future clocks are rejected',
            'initial_operator_at_each_family_start': 'I; no U(t,0) inverse',
            'source_scope': 'same-reference declared Gaussian raw-drive family with full natural field; numerical fixed-clock field words',
            'actual_2016_pulse_identity_certified': False, 'controller_advance': False, 'source_bindings': _bindings()}
        self._seal = _digest(self._value)
        _ISSUED[id(self)] = (self._seal, self._banks, self._witnesses, self._groups)

    def record(self):
        _CHECK(); field._closed(self)
        issued = _ISSUED.get(id(self))
        _require(type(self) is DrivenGaussianFieldSource and set(vars(self)) ==
                 {'_pulses', '_banks', '_witnesses', '_groups', '_value', '_seal'} and issued is not None and
                 self._seal == issued[0] and self._banks is issued[1] and self._witnesses is issued[2] and self._groups is issued[3] and
                 _digest(self._value) == self._seal and self._value['source_bindings'] == _bindings() and
                 [gaussian.GaussianAtomicPulseSource.record(p) for p in self._pulses] == self._value['Gaussian_source_legs'],
                 'driven source, sealed operator bank, field clocks or source actions changed')
        return _copy(self._value)

    @classmethod
    def from_record(cls, record, *, operator_certificates):
        _require(cls is DrivenGaussianFieldSource and type(record) is dict and record.get('schema') == SCHEMA,
                 'closed driven field record and complete operator witnesses required')
        pulses = tuple(gaussian.GaussianAtomicPulseSource.from_record(raw) for raw in record['Gaussian_source_legs'])
        source = cls(*pulses, flight_seconds=record['flight_seconds'], emission_origins_seconds=record['emission_origins_seconds'],
                     gate_seconds=record['gate_seconds'], operator_certificates=operator_certificates)
        _require(DrivenGaussianFieldSource.record(source) == record, 'driven field source or operator witnesses changed')
        return source

    def operator_witnesses(self):
        DrivenGaussianFieldSource.record(self)
        return tuple(tuple(json.loads(text) for text in side) for side in self._witnesses)

    def operator(self, side, start, stop, *, bits=160):
        DrivenGaussianFieldSource.record(self); gaussian._precision(bits)
        _require(type(side) is int and side in (0, 1), 'original source side required')
        s, t = map(full.nonnegative, (start, stop))
        matrix, error = _operator_at(self, side, s, t, bits)
        return {'source_record_digest': self._seal, 'side': side, 'source_interval_seconds': list(map(str, (s, t))),
            'full33_operator': channel._input_record(matrix), 'operator_norm_error_upper': _price_record(error, bits),
            'uniform_fixed_start_price_consumed': True, 'new_physical_frame_evaluation_paid': True,
            'outward_price_rounding': _price_rule(bits), 'scalar_bits': bits}

    def source_jump(self, side, group, mode, *, bits=160):
        raw = DrivenGaussianFieldSource.record(self); gaussian._precision(bits)
        _require(type(side) is int and side in (0, 1), 'original source side required')
        _word(self, [{'group': list(group), 'mode': list(mode), 'arrival_seconds': '0'}])
        matrix, error, prices = _jump(raw, raw['physical_legs'][side]['original_physical_natural_jumps'],
                                     side, tuple(group), tuple(mode), bits)
        return {'source_record_digest': self._seal, 'side': side, 'radiation_group': list(group), 'mode': list(mode),
            'full33_jump_operator': channel._input_record(matrix), 'operator_norm_error_upper': _price_record(error, bits),
            **prices, 'outward_price_rounding': _price_rule(bits), 'scalar_bits': bits}

    def _local_word(self, side, entries, observation, bits):
        raw = self._value; origin = Q(raw['emission_origins_seconds'][side]); flight = Q(raw['flight_seconds'][side])
        elapsed = observation-origin
        ordered = sorted(((Q(e['arrival_seconds'])-flight-origin, e) for e in entries), key=lambda x: x[0])
        if any(t < 0 or t > elapsed for t, _ in ordered):
            return {}, Q(0)
        matrix = {(i, i): dipole.ComplexRadical(1) for i in range(full.DIMENSION)}; error = Q(0); previous = Q(0)
        for t, entry in ordered:
            j, je, _ = _jump(raw, raw['physical_legs'][side]['original_physical_natural_jumps'],
                            side, tuple(entry['group']), tuple(entry['mode']), bits)
            if not j and not je:
                return {}, Q(0)
            u, ue = _operator_at(self, side, previous, t, bits)
            matrix, error = _multiply(u, ue, matrix, error, bits)
            matrix, error = _multiply(j, je, matrix, error, bits); previous = t
        u, ue = _operator_at(self, side, previous, elapsed, bits)
        return _multiply(u, ue, matrix, error, bits)

    def field_amplitude(self, word, observation, *, bits=160):
        raw = DrivenGaussianFieldSource.record(self); gaussian._precision(bits)
        time = full.nonnegative(observation); operator, error, count = _amplitude(self, word, time, bits)
        return {'schema': SCHEMA+'/field-amplitude', 'source_record': raw,
            'physical_observation_seconds': str(time), 'photon_word': _copy(word),
            'full_pair_operator': channel._input_record(operator), 'operator_error_upper': _price_record(error, bits),
            'source_arm_assignment_count': count, 'symmetric_full_product_sector': len(word),
            'wavefunction_factor_squared': str(Q(1, factorial(len(word)))),
            'same_arm_repeated_emissions_retained': True, 'future_arrivals_not_discarded': True,
            'outward_price_rounding': _price_rule(bits), 'scalar_bits': bits}

    def field_density_column(self, row, column, bra_word, ket_word, observation, *, bits=160):
        _require(type(row) is int and type(column) is int and 0 <= row < joint.DIMENSION and 0 <= column < joint.DIMENSION,
                 'original full33 pair matrix-unit column required')
        raw = DrivenGaussianFieldSource.record(self); gaussian._precision(bits); time = full.nonnegative(observation)
        a, ea, _ = _amplitude(self, bra_word, time, bits); b, eb, _ = _amplitude(self, ket_word, time, bits)
        matrix = dipole.matrix_product(dipole.matrix_product(a, {(row, column): dipole.ComplexRadical(1)}), dipole.matrix_adjoint(b))
        # E_ij selects two columns.  The certified operator error bounds each
        # column; the other vector's norm is its actual complete column norm.
        # This preserves every output coordinate without paying unrelated inputs.
        norm_a = _norm({key: value for key, value in a.items() if key[1] == row}, bits)
        norm_b = _norm({key: value for key, value in b.items() if key[1] == column}, bits)
        error = ea*norm_b+eb*norm_a+ea*eb
        return {'schema': SCHEMA+'/matter-field-column', 'source_record': raw, 'matrix_unit': [row, column],
            'physical_observation_seconds': str(observation), 'bra_photon_word': _copy(bra_word), 'ket_photon_word': _copy(ket_word),
            'complete_matter_field_kernel': channel._input_record(matrix), 'trace_norm_kernel_error': _price_record(error, bits),
            'full_output_column_norms_upper': [_price_record(n, bits) for n in (norm_a, norm_b)],
            'off_diagonal_photon_time_and_number_retained': True,
            'outward_price_rounding': _price_rule(bits), 'scalar_bits': bits}

    def field_trace_metric(self, bra_word, ket_word):
        raw = DrivenGaussianFieldSource.record(self); _word(self, bra_word); _word(self, ket_word)
        if len(bra_word) != len(ket_word):
            return ZERO
        value = dipole.ComplexRadical(1)
        loss = tuple(tuple(channel._complex_record(v) for v in row) for row in raw['loss_environment_gram'])
        for a, b in zip(bra_word, ket_word):
            if a['group'] != b['group'] or Q(a['arrival_seconds']) != Q(b['arrival_seconds']) or a['mode'][0] != b['mode'][0]:
                return ZERO
            p, q = a['mode'][1], b['mode'][1]
            value *= dipole.ComplexRadical(int(p == q)) if a['mode'][0] == 'port' else loss[q][p]
        return value

    def tail_certificate(self, observation, maximum_photon_number, *, bits=160):
        raw = DrivenGaussianFieldSource.record(self); gaussian._precision(bits)
        time = full.nonnegative(observation); n = maximum_photon_number
        _require(type(n) is int and n >= 0 and time >= max(map(Q, raw['emission_origins_seconds'])),
                 'reached source clock and finite photon-number cutoff required')
        gamma = Q(raw['reference_clock']['Gamma_numerical_centre']); hi = Q(raw['reference_clock']['angular_Gamma_enclosure_per_second'][1])
        rates = []; hazard = Q(0)
        for side, leg in enumerate(raw['physical_legs']):
            r = gaussian._matrix(leg['full_R_per_second'])
            rate = max((value.real.as_rational() for (i, j), value in r.items() if i == j), default=Q(0))*max(1, hi/gamma)
            rates.append(rate); hazard += rate*(time-Q(raw['emission_origins_seconds'][side]))
        # A factorial-moment bound on the Poisson-dominated count tail avoids
        # subtracting a rounded near-one CDF.  It applies to every number sector.
        k = n+1
        if hazard == 0:
            epsilon = Q(0)
        elif hazard >= k:
            epsilon = Q(1)
        else:
            epsilon = min(Q(1), hazard**k/factorial(k))
        _, coherence = _sqrt_interval(epsilon, bits)
        return {'schema': SCHEMA+'/source-number-tail', 'source_record_digest': self._seal,
            'physical_observation_seconds': str(time), 'maximum_photon_number': n,
            'natural_intensity_upper_per_second': list(map(str, rates)), 'integrated_intensity_upper': str(hazard),
            'omitted_event_mass_per_positive_input_mass_upper': str(epsilon),
            'full_field_trace_norm_price_per_input_trace_norm_upper': str(2*coherence),
            'bound_rule': 'source factorial-moment bound min(1,Lambda_integral**(N+1)/(N+1)!) on the Poisson-dominated count tail',
            'includes_loss_and_in_flight_photons': True, 'number_coherence_priced_separately_from_event_mass': True,
            'old_input_error_repeated_in_tail': False, 'scalar_bits': bits}


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None)), repr(getattr(value, '__defaults__', None)), repr(getattr(value, '__kwdefaults__', None))


def _signature():
    functions = (_require, _copy, _digest, _bindings, _freeze_report, _bank_summary, _eval, _norm, _multiply,
        _sqrt_interval, _price_record, _price_rule, _jump, _word, _operator_at, _amplitude, _function, _signature, _check,
        gaussian.GaussianAtomicPulseSource.record, gaussian.GaussianAtomicPulseSource.from_record,
        gaussian.GaussianAtomicPulseSource.verify_operator, gaussian.GaussianAtomicPulseSource.Gamma_math_price,
        gaussian._restore, gaussian._exponential, gaussian._matrix, gaussian._precision,
        field._source, field._closed, field._read_entries, field._scaled_add, field._product, field._norm,
        field._operator_bound, field._add, field._price_upper, full._sqrt, full.nonnegative,
        optical.CommonOpticalReadout.record, optical.CommonOpticalReadout.from_record, optical.CommonOpticalReadout.bsm_gate,
        atomic.MunichAtomicProgramme.from_record, joint.passive_transfer, original._tensor, original._matrix,
        dipole.matrix_product, dipole.matrix_adjoint, channel._input_record, channel._complex_record, bsm._entry_norm)
    methods = tuple(_function(v) for v in vars(DrivenGaussianFieldSource).values() if callable(v) or isinstance(v, classmethod))
    return tuple(map(_function, functions)), methods, tuple(dipole.STATES), tuple(dipole.Q_COMPONENTS), \
        channel._canonical(optical.PUBLIC_SOURCE), SCHEMA, full.DIMENSION, joint.DIMENSION


def _check():
    if _check is not _CHECK or _check.__code__ is not _CHECK_CODE or _signature is not _SIGNATURE or _signature() != _EXPECTED:
        raise ValueError('driven Gaussian field source execution closure changed')
    if gaussian._CHECK is not _GAUSSIAN_CHECK:
        raise ValueError('Gaussian operator source checker changed')
    _GAUSSIAN_CHECK()


_SIGNATURE = _signature
_CHECK, _CHECK_CODE = _check, _check.__code__
_EXPECTED = _signature()
