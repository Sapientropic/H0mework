"""The original registered-jump source bounds its first-receipt instrument.

For each resolved environment, T* T <= kappa I bounds its complete detected
jump effect by kappa times the original natural loss.  The bound is uniform
in the drive and in the number of same-arm photons.  The original mark graph
then supplies the number of arrivals still required for a first receipt.

The resulting effect bound contracts a Hermitian input error for the whole
receipt-time/state direct sum.  It does not contract the pending complement,
a point time-density kernel, or an already normalized conditional state.
"""
from collections import deque
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import hashlib
import json

import retarded_gaussian_bsm_source as law
import aperture_collection_domain as aperture

field, full, dipole, channel, joint, bsm = (law.field, law.full, law.dipole,
                                           law.channel, law.joint, law.bsm)
SCHEMA = 'stage10-source-retarded-first-receipt-activity-envelope/v1'
_ISSUED = {}
_LAW_CHECK, _APERTURE_CHECK = law._CHECK, aperture._CHECK


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
                (law, aperture, law.driven, law.gaussian, law.original, law.optical,
                 dipole, full, channel, joint, bsm)))}


def _norm_upper(matrix, bits):
    centre, error = full._midpoint_matrix(matrix, bits)
    return full._norm(centre)+full._operator_bound(error)


def _law_record(source):
    raw = law.RetardedGaussianBSMSource.record(source)
    _require(source._groups == law._closed_groups(raw['complete_driven_field_source']),
             'executed natural jump groups differ from their original source')
    return raw


def _source_loss(leg, expected):
    matrix = {}
    for jump in leg['original_physical_natural_jumps']:
        operator = law.gaussian._matrix(jump['normalized_natural_jump_operator'])
        rate = full.nonnegative(jump['physical_amplitude_squared_per_second'])
        field._add(matrix, dipole.matrix_product(dipole.matrix_adjoint(operator), operator), rate)
    _require(matrix == law.gaussian._matrix(expected) and
             matrix == dipole.matrix_adjoint(matrix) and
             all(i == j and not z.imag and z.real.as_rational() >= 0 for (i, j), z in matrix.items()),
             'all original natural jumps must reconstruct the full positive33 loss operator')
    _require(all(not matrix.get((i, i), dipole.ComplexRadical()) for i, s in enumerate(dipole.STATES)
                 if s.family in ('ground', 'ion')),
             'original natural loss must keep ground and ion source coordinates')
    return matrix


def _facts(raw, bits):
    source = raw['complete_driven_field_source']
    pack = source['working_common_optical_source']
    transfer = tuple(tuple(channel._complex_record(z) for z in row)
                     for row in pack['generated_four_by_six_transfer'])
    _, gram, _ = joint.passive_transfer(transfer)
    gram_matrix = {(i, j): z for i, row in enumerate(gram) for j, z in enumerate(row) if z}
    transfer_upper = min(Q(1), _norm_upper(gram_matrix, bits))
    objective = aperture.ApertureCollectionDomain.from_record(source['working_aperture_source'])
    cone = aperture.ApertureCollectionDomain.record(objective)
    _require(cone['common_optical_source'] == pack and
             cone['full_detected_transfer_gram'] == law.optical._matrix(gram),
             'the objective domain must constrain this same complete optical transfer')
    cone_upper = Q(0)
    for side in cone['cone_eigenvalues']:
        for value in side:
            centre, rounding = full.radical_midpoint(dipole.Radical({int(k): Q(v) for k, v in value.items()}), bits)
            cone_upper = max(cone_upper, centre+rounding)
    kappa = min(transfer_upper, cone_upper, Q(1))
    clock = source['reference_clock']
    gamma = full.exact(clock['Gamma_numerical_centre'])
    gamma_lo, gamma_hi = map(full.exact, clock['angular_Gamma_enclosure_per_second'])
    _require(0 < gamma_lo <= gamma <= gamma_hi,
             'the same source needs its complete positive reference Gamma family')
    scale = gamma_hi/gamma
    losses = []; rates = []
    for leg, pulse in zip(source['physical_legs'], source['Gaussian_source_legs']):
        loss = _source_loss(leg, pulse['complete_natural_R_per_second'])
        upper = _norm_upper(loss, bits)*scale
        losses.append(channel._input_record(loss)); rates.append(upper)
    bg = raw['BG_source']
    unit = Q(bg['seconds_per_source_unit'])
    _require(unit*gamma == 1 and bg['common_optical_source'] == pack and
             bg['raw_rates_per_source_unit'] == pack['background_rates'],
             'Gamma clock and all four background primitives must belong to the same source')
    backgrounds = tuple(full.nonnegative(v)*scale for v in bg['BG_rates_per_second'])
    _require(tuple(Q(v)/unit for v in pack['background_rates']) == tuple(map(Q, bg['BG_rates_per_second'])),
             'each background rate must be converted from its original unit once')
    signal = kappa*sum(rates, Q(0)); noise = sum(backgrounds, Q(0))
    return {'full_detected_transfer_gram': law.optical._matrix(gram),
        'full_transfer_operator_norm_square_upper': str(transfer_upper),
        'source_objective_operator_norm_square_upper': str(min(Q(1), cone_upper)),
        'registered_optical_operator_norm_square_upper': str(kappa),
        'source_objective_domain_sha256': _digest(cone),
        'complete_original_natural_loss_operators_per_second': losses,
        'Gamma_family_rate_scale_upper': str(scale),
        'complete_Gamma_family_natural_loss_operator_norms_per_second': list(map(str, rates)),
        'four_source_BG_rate_upper_per_second': list(map(str, backgrounds)),
        'registered_signal_activity_upper_per_second': str(signal),
        'registered_BG_activity_upper_per_second': str(noise),
        'registered_total_activity_upper_per_second': str(signal+noise),
        'source_operator_law': 'sum_g D_g*D_g <= kappa*(R_A tensor I + I tensor R_B); original four BG effects add beta_total I',
        'drive_independent': True, 'same_arm_repeated_arrivals_retained': True,
        'one_photon_per_arm_assumed': False, 'BG_arrivals_discarded': False}


def _minimum_arrivals(source, mark):
    _require(type(mark) is bsm.Mark and mark.receipt is None,
             'an original pending Mark is required; an existing receipt is not a future first receipt')
    queue = deque([(mark, ())]); seen = {mark}
    while queue:
        current, path = queue.popleft()
        for port in range(4):
            target = bsm.BSMSource.target(source._gate, current, port)
            following = path+(port,)
            if target.receipt is not None:
                return len(following), following
            if target not in seen:
                seen.add(target); queue.append((target, following))
    raise ValueError('the original mark graph has no supported future receipt')


def _poisson_cap(mean, count, bits):
    outward_mean = field._price_upper(mean, bits)
    moment = min(Q(1), outward_mean**count/factorial(count))
    exponential, error = law.original.scalar._exp_negative(outward_mean, bits)
    survival = sum((outward_mean**j/factorial(j) for j in range(count)), Q(0))
    poisson = min(Q(1), max(Q(0), 1-max(Q(0), exponential-error)*survival))
    upper = min(Q(1), field._price_upper(min(moment, poisson), bits))
    return upper, {'outward_activity_mean_upper': str(outward_mean),
        'activity_mean_rounding_increment_upper': str(Q(1, 1 << bits)),
        'factorial_moment_tail_upper': str(field._price_upper(moment, bits)),
        'Poisson_tail_upper': str(field._price_upper(poisson, bits)),
        'Poisson_exponential_scalar_error': str(field._price_upper(error, bits))}


class RetardedReceiptActivityEnvelope:
    def __init__(self, source, *, bits=160):
        _CHECK(); field._closed(source); law.gaussian._precision(bits)
        _require(type(source) is law.RetardedGaussianBSMSource,
                 'closed RetardedGaussianBSMSource required; a rate, effect or target table is not input')
        raw = _law_record(source)
        self._source = source
        self._value = {'schema': SCHEMA, 'retarded_source_record': raw,
            'fixed_gate_seconds': raw['gate_seconds'], 'source_activity': _facts(raw, bits),
            'instrument_scope': 'whole original first-receipt time/state direct sum in its fixed detector gate',
            'input_scope': 'original retarded quantum coimage and its pending Mark; independent vacuum baths and fixed flight',
            'point_density_contraction_claimed': False,
            'pending_complement_contraction_claimed': False,
            'actual_hardware_uniquely_identified': False,
            'scalar_bits': bits, 'source_bindings': _bindings(), 'controller_advance': False}
        self._seal = _digest(self._value)
        _ISSUED[id(self)] = self._seal, source

    def record(self):
        _CHECK(); field._closed(self)
        issued = _ISSUED.get(id(self))
        _require(type(self) is RetardedReceiptActivityEnvelope and set(vars(self)) == {'_source', '_value', '_seal'} and
                 issued is not None and self._seal == issued[0] and self._source is issued[1] and
                 _digest(self._value) == self._seal and self._value['source_bindings'] == _bindings() and
                 _law_record(self._source) == self._value['retarded_source_record'],
                 'original activity source, Gamma, optics, Mark law or fixed gate changed')
        return _copy(self._value)

    def first_receipt_cap(self, *, start_marks=(bsm.INITIAL,), input_time=None, interval=None):
        raw = RetardedReceiptActivityEnvelope.record(self); bits = raw['scalar_bits']
        g0, g1 = map(Q, raw['fixed_gate_seconds'])
        start = g0 if input_time is None else full.nonnegative(input_time)
        lower, upper = (start, g1) if interval is None else tuple(map(full.nonnegative, interval))
        _require(g0 <= start <= lower <= upper <= g1,
                 'input and restriction clocks must stay in this same fixed gate')
        _require(type(start_marks) in (list, tuple) and start_marks and all(type(mark) is bsm.Mark for mark in start_marks) and
                 len(set(start_marks)) == len(start_marks),
                 'the complete pending Mark inventory must be nonempty and unique')
        rate = Q(raw['source_activity']['registered_total_activity_upper_per_second'])
        mean = rate*(upper-start)
        rows = []; whole = Q(0)
        for mark in start_marks:
            count, path = _minimum_arrivals(self._source, mark)
            cap, arithmetic = _poisson_cap(mean, count, bits)
            if lower == upper:
                cap = Q(0)
            whole = max(whole, cap)
            rows.append({'original_mark_counts': list(mark.counts), 'original_mark_receipt': mark.receipt,
                'minimum_future_registered_arrivals': count, 'shortest_original_port_path': list(path),
                'first_receipt_instrument_input_contraction_upper': str(cap), 'tail_arithmetic': arithmetic})
        return {'schema': SCHEMA+'/first-receipt-cap', 'source_record': raw,
            'input_detector_clock_seconds': str(start), 'receipt_time_restriction_seconds': list(map(str, (lower, upper))),
            'restriction_semantics': '(lower,upper]; first arrivals before lower remain in the original Mark history',
            'activity_horizon_seconds': str(upper-start), 'source_Poisson_mean_upper': str(mean),
            'pending_mark_bounds': rows, 'whole_first_receipt_input_contraction_upper': str(whole),
            'whole_pending_plus_receipt_input_contraction_upper': '1',
            'source_effect_law': '0 <= receipt_effect <= cap I; Hermitian direct-sum trace norm contracts by cap',
            'all_four_patterns_and_their_poststates_retained': True,
            'coherent_same_arm_and_BG_histories_retained': True,
            'source_bindings': _bindings(), 'controller_advance': False}

    def input_error_payment(self, upstream_error, *, start_marks=(bsm.INITIAL,), input_time=None, interval=None):
        error = full.nonnegative(upstream_error)
        cap = RetardedReceiptActivityEnvelope.first_receipt_cap(self, start_marks=start_marks,
                                                               input_time=input_time, interval=interval)
        coefficient = Q(cap['whole_first_receipt_input_contraction_upper'])
        price = coefficient*error
        return {'schema': SCHEMA+'/input-error-payment', 'source_generated_instrument_cap': cap,
            'whole_upstream_trace_norm_error': str(error),
            'first_receipt_input_error_payment': str(price),
            'whole_upstream_error_consumed_once': True,
            'mark_components_received_duplicate_upstream_error': False,
            'point_density_or_normalized_posterior_price_claimed': False,
            'new_generator_or_quadrature_errors_included': False,
            'source_bindings': _bindings(), 'controller_advance': False}

    def verify_payment(self, report):
        _require(type(report) is dict and report.get('schema') == SCHEMA+'/input-error-payment',
                 'the source-generated first-receipt payment is required')
        cap = report['source_generated_instrument_cap']
        marks = tuple(bsm.Mark(tuple(row['original_mark_counts']), row['original_mark_receipt'])
                      for row in cap['pending_mark_bounds'])
        expected = RetardedReceiptActivityEnvelope.input_error_payment(self, report['whole_upstream_trace_norm_error'],
            start_marks=marks, input_time=cap['input_detector_clock_seconds'], interval=cap['receipt_time_restriction_seconds'])
        _require(expected == report, 'original activity rate, Mark requirement or inherited payment changed')
        return True

    @classmethod
    def from_record(cls, record, *, operator_certificates=((), ())):
        _CHECK()
        _require(cls is RetardedReceiptActivityEnvelope and type(record) is dict and record.get('schema') == SCHEMA,
                 'closed source-generated activity envelope record required')
        raw = record['retarded_source_record']
        source = law.driven.DrivenGaussianFieldSource.from_record(raw['complete_driven_field_source'],
                                                                 operator_certificates=operator_certificates)
        parent = law.RetardedGaussianBSMSource(source)
        _require(_law_record(parent) == raw, 'original retarded source changed')
        result = cls(parent, bits=record['scalar_bits'])
        _require(RetardedReceiptActivityEnvelope.record(result) == record, 'original envelope changed')
        return result


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None)), repr(getattr(value, '__defaults__', None)), repr(getattr(value, '__kwdefaults__', None))


def _signature():
    functions = (_require, _copy, _digest, _bindings, _norm_upper, _law_record, _source_loss, _facts, _minimum_arrivals,
        _poisson_cap, _function, _signature, _check,
        law.RetardedGaussianBSMSource.record, law.RetardedGaussianBSMSource.__init__, law._closed_groups,
        law.driven.DrivenGaussianFieldSource.record, law.driven.DrivenGaussianFieldSource.from_record,
        bsm.BSMSource.target, bsm.Mark.__init__, bsm.Mark.__post_init__,
        joint.passive_transfer, dipole.matrix_product, dipole.matrix_adjoint,
        full._midpoint_matrix, full._norm, full._operator_bound, full.radical_midpoint,
        full.nonnegative, full.exact, channel._complex_record, channel._input_record,
        channel._canonical, law.gaussian._matrix, law.gaussian._precision,
        law.optical._matrix, aperture.ApertureCollectionDomain.from_record,
        aperture.ApertureCollectionDomain.record, law.original.scalar._exp_negative,
        field._price_upper, field._closed, field._add)
    methods = tuple(_function(v) for v in vars(RetardedReceiptActivityEnvelope).values() if callable(v) or isinstance(v, classmethod))
    return tuple(map(_function, functions)), methods, tuple(bsm.PATTERNS), tuple(dipole.STATES), SCHEMA


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
             law._CHECK is _LAW_CHECK and aperture._CHECK is _APERTURE_CHECK,
             'source activity envelope execution closure changed')
    _LAW_CHECK(); _APERTURE_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
