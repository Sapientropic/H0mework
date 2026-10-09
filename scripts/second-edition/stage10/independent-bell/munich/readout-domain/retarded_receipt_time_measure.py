"""Time-tagged receipt measures from a checked complete stopped trajectory.

The ideal candidate measure is the physical derivative of its absorbed
coimage, including signed atoms at numerical joins.  Its total-variation
enclosure uses the full pending/absorbed source defect, rather than a CDF
supremum.  Scalar reading and integration prices are paid separately.
"""
from fractions import Fraction as Q
from math import comb
from pathlib import Path
import hashlib

import retarded_receipt_trajectory_certificate as continuous
import retarded_component_integer_action as integer
import retarded_integer_residual_certificate as common_integer
import retarded_frequency_clustered_certificate as frequency_clustered
import retarded_residual_cell_certificate as residual_cells
import retarded_gaussian_tail_certificate as gaussian_tail
import retarded_gaussian_tail_duhamel_certificate as gaussian_tail_duhamel
import retarded_gaussian_tail_duhamel_cell_certificate as gaussian_tail_duhamel_cells
import source_mode_time_measure as moments
import radical_time_accumulator as accumulator

field, gaussian, full, dipole, channel, joint, bsm = (continuous.field, continuous.gaussian,
    continuous.full, continuous.dipole, continuous.channel, continuous.joint, continuous.bsm)
SCHEMA = 'stage10-source-retarded-time-tagged-receipt-measure/v1'
_CONTINUOUS_CHECK = continuous._CHECK
_INTEGER_CHECK = integer._CHECK
_COMMON_INTEGER_CHECK = common_integer._CHECK
_FREQUENCY_CLUSTERED_CHECK = frequency_clustered._CHECK
_RESIDUAL_CELLS_CHECK = residual_cells._CHECK
_GAUSSIAN_TAIL_CHECK = gaussian_tail._CHECK
_GAUSSIAN_TAIL_DUHAMEL_CHECK = gaussian_tail_duhamel._CHECK
_GAUSSIAN_TAIL_DUHAMEL_CELLS_CHECK = gaussian_tail_duhamel_cells._CHECK
_ISSUED = {}


def _require(value, message):
    if not value:
        raise ValueError(message)


def _bindings(backend):
    modules = (continuous, moments, accumulator)
    if backend in ('integer', 'common_integer', 'frequency_clustered', 'residual_cells', 'gaussian_tail', 'gaussian_tail_duhamel', 'gaussian_tail_duhamel_cells'):
        modules += (integer,)
    if backend in ('common_integer', 'frequency_clustered', 'residual_cells', 'gaussian_tail', 'gaussian_tail_duhamel', 'gaussian_tail_duhamel_cells'):
        modules += (common_integer,)
    if backend in ('frequency_clustered', 'residual_cells', 'gaussian_tail', 'gaussian_tail_duhamel', 'gaussian_tail_duhamel_cells'):
        modules += (frequency_clustered,)
    if backend in ('residual_cells', 'gaussian_tail_duhamel_cells'):
        modules += (residual_cells,)
    if backend in ('gaussian_tail', 'gaussian_tail_duhamel', 'gaussian_tail_duhamel_cells'):
        modules += (gaussian_tail, gaussian_tail.tails)
    if backend in ('gaussian_tail_duhamel', 'gaussian_tail_duhamel_cells'):
        modules += (gaussian_tail_duhamel,)
    if backend == 'gaussian_tail_duhamel_cells':
        modules += (gaussian_tail_duhamel_cells,)
    paths = (Path(__file__), *(Path(m.__file__) for m in modules))
    if backend in ('gaussian_tail', 'gaussian_tail_duhamel', 'gaussian_tail_duhamel_cells'):
        paths += (Path(__file__).with_name('retarded_counterflow_numpy_writer.py'),)
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _verified_curve(certificate, report, requested_backend):
    _require(type(report) is dict, 'named original or integer continuous certificate required')
    schemas = {'original': continuous.SCHEMA + '/checked-curve',
               'integer': integer.SCHEMA + '/checked-complete-curve',
               'common_integer': common_integer.SCHEMA + '/checked-complete-curve',
               'frequency_clustered': frequency_clustered.SCHEMA + '/checked-complete-curve',
               'residual_cells': residual_cells.SCHEMA + '/checked-complete-curve',
               'gaussian_tail': gaussian_tail.SCHEMA + '/checked-complete-curve',
               'gaussian_tail_duhamel': gaussian_tail_duhamel.SCHEMA + '/checked-complete-curve',
               'gaussian_tail_duhamel_cells': gaussian_tail_duhamel_cells.SCHEMA + '/checked-complete-curve'}
    selected = next((name for name, schema in schemas.items() if report.get('schema') == schema), None)
    _require(selected is not None and requested_backend in (None, selected),
             'fixed certificate backend must match its named source schema')
    if selected == 'gaussian_tail_duhamel_cells':
        _GAUSSIAN_TAIL_DUHAMEL_CELLS_CHECK()
        return selected, gaussian_tail_duhamel_cells.verify(certificate, report)
    if selected == 'gaussian_tail_duhamel':
        _GAUSSIAN_TAIL_DUHAMEL_CHECK()
        return selected, gaussian_tail_duhamel.verify(certificate, report)
    if selected == 'residual_cells':
        _RESIDUAL_CELLS_CHECK()
        return selected, residual_cells.verify(certificate, report)
    if selected == 'gaussian_tail':
        _GAUSSIAN_TAIL_CHECK()
        return selected, gaussian_tail.verify(certificate, report)
    if selected == 'frequency_clustered':
        _FREQUENCY_CLUSTERED_CHECK()
        return selected, frequency_clustered.verify(certificate, report)
    if selected == 'common_integer':
        _COMMON_INTEGER_CHECK()
        return selected, common_integer.verify(certificate, report)
    if selected == 'integer':
        _INTEGER_CHECK()
        return selected, integer.verify(certificate, report)
    return selected, continuous.RetardedReceiptTrajectoryCertificate.verify(certificate, report)


def _initial_absorbed_zero(certificate, report):
    trial = report['untrusted_trial']
    _require(trial['pieces'], 'a nonempty source curve is required for a time measure')
    total = {}
    for mode in trial['pieces'][0]['modes']:
        state = continuous._coefficient(mode['coefficients'][0], trial['mode_bits'], certificate._source)
        continuous._add(total, {key: value for key, value in state.items() if key[0].receipt is not None})
    _require(not total, 'the exact sum of all initial absorbed mode coefficients must be zero')


def _compile(certificate, report):
    start, stop = map(Q, report['source_detector_interval_seconds'])
    original = continuous._read_state(report['untrusted_trial']['complete_initial_marked_state'], certificate._source)
    _require(original and all(mark.receipt is None for mark, _, _ in original),
             'the original complete input must be pending at the source cut')
    pieces = []
    for raw in report['untrusted_trial']['pieces']:
        width, groups = continuous._modes(raw, report['untrusted_trial']['mode_bits'], certificate._source)
        frozen = tuple((exponent, tuple((n, tuple(matrix.items())) for n, matrix in sorted(polynomial.items())))
                       for exponent, polynomial in sorted(groups.items()))
        pieces.append((start, width, frozen)); start += width
    _require(start == stop, 'the source curve covers its full declared clock interval')
    return tuple(pieces), tuple(sorted({mark for mark, _, _ in original}, key=continuous.trajectory._key))


def _frame_recipe(source):
    raw = source._value['retarded_source']['complete_driven_field_source']
    births = tuple(Q(a) + Q(b) for a, b in zip(raw['emission_origins_seconds'], raw['flight_seconds']))
    omega = tuple(Q(r['carrier_angular_frequency_per_second']) for r in raw['Gaussian_source_legs'])
    return births, omega


def _frame_word(recipe, time, i, j):
    births, omega = recipe
    local = tuple(max(Q(0), time - birth) for birth in births)
    active = tuple(time >= birth for birth in births)
    rows, columns = divmod(i, full.DIMENSION), divmod(j, full.DIMENSION)
    signs = tuple(int(dipole.STATES[columns[s]].family == 'D2') -
                  int(dipole.STATES[rows[s]].family == 'D2') for s in (0, 1))
    angle = sum((omega[s] * local[s] * signs[s] for s in (0, 1)), Q(0))
    frequency = sum((omega[s] * signs[s] for s in (0, 1) if active[s]), Q(0))
    return angle, frequency


def _add_image(images, word, key, pair):
    image = images.setdefault(word, {})
    continuous._add(image, {key: pair})
    if not image:
        del images[word]


def _physical_density_terms(frame_recipe, piece):
    origin, width, groups = piece
    images = {}
    for (lr, li), polynomial in groups:
        for n, entries in polynomial:
            for (mark, i, j), (a, b) in entries:
                if mark.receipt is None:
                    continue
                angle, frequency = _frame_word(frame_recipe, origin, i, j)
                exponent = lr * width, (li + frequency) * width
                key = mark.receipt * joint.DIMENSION + i, mark.receipt * joint.DIMENSION + j
                # dQ_abs - counter(Q_abs), after the exact physical frame.
                _add_image(images, (exponent, angle, n), key,
                           (width * (lr * a - (li + frequency) * b),
                            width * (lr * b + (li + frequency) * a)))
                if n:
                    _add_image(images, (exponent, angle, n - 1), key, (n * a, n * b))
    return images


def _value(frame_recipe, piece, time, bits):
    origin, width, groups = piece
    u = (time - origin) / width
    images = {}
    for (lr, li), polynomial in groups:
        for n, entries in polynomial:
            for (mark, i, j), pair in entries:
                if mark.receipt is not None:
                    angle, _ = _frame_word(frame_recipe, time, i, j)
                    word = lr * width * u, li * width * u + angle
                    key = mark.receipt * joint.DIMENSION + i, mark.receipt * joint.DIMENSION + j
                    _add_image(images, word, key, (pair[0] * u**n, pair[1] * u**n))
    if not images:
        return {}, Q(0)
    matrices = [continuous._exact(image) for image in images.values()]
    total = accumulator.RadicalMatrixTimeAccumulator(matrices, scalar_bits=bits, norm_bits=bits)
    for k, exponent in enumerate(images):
        centre, error = gaussian._exponential(*exponent, bits)
        total.add_matrix(k, moments.Enclosure(centre, error).rounded(bits))
    return total.result()


def _polynomial_weight(origin, width, start, stop, power):
    span = stop - start
    _require(span > 0, 'positive full source horizon required')
    return [Q(comb(power, k)) * ((origin - start) / span)**(power - k) *
            (width / span)**k for k in range(power + 1)]


def _contains(time, lower, upper, left_closed, right_closed):
    if lower == upper:
        return left_closed and right_closed and time == lower
    return lower < time < upper or time == lower and left_closed or time == upper and right_closed


def _split(matrix):
    patterns = [{}, {}, {}, {}]
    for (i, j), value in matrix.items():
        h, row = divmod(i, joint.DIMENSION); k, column = divmod(j, joint.DIMENSION)
        _require(h == k and 0 <= h < 4, 'complete four-pattern direct sum required')
        field._add(patterns[h], {(row, column): value})
    return patterns


class RetardedReceiptTimeMeasure:
    def __init__(self, certificate, report, *, backend=None):
        _CHECK(); field._closed(certificate)
        _require(type(certificate) is continuous.RetardedReceiptTrajectoryCertificate,
                 'closed original continuous source certificate required')
        source_record = continuous.RetardedReceiptTrajectoryCertificate.record(certificate)
        _initial_absorbed_zero(certificate, report)
        selected_backend, verified = _verified_curve(certificate, report, backend)
        self._certificate, self._report = certificate, continuous._copy(verified)
        self._pieces, marks = _compile(certificate, self._report)
        self._frame = _frame_recipe(certificate._source)
        self._value = {'schema': SCHEMA, 'continuous_certificate_source': source_record,
            'continuous_certificate_backend': selected_backend,
            'continuous_certificate_schema': verified['schema'],
            'checked_curve_digest': continuous._digest(self._report),
            'source_detector_interval_seconds': self._report['source_detector_interval_seconds'],
            'source_issued_input_used': self._report['source_issued_input_used'],
            'candidate_join_atoms_are_signed': True, 'default_Stieltjes_interval': '(lower,upper]',
            'original_finite_rate_source_has_no_fixed_time_atoms': True,
            'all_initial_absorbed_mode_coefficients_sum_exactly_to_zero': True,
            'complete_source_pending_marks': [{'counts': list(m.counts), 'receipt': m.receipt} for m in marks],
            'ideal_candidate_TV_price': self._report['source_rotating_curve_error'],
            'lifted_Gamma_instrument_price_once': self._report['mathematical_Gamma_full_marked_price'],
            'CDF_supremum_used_as_time_TV_price': False,
            'numerical_integration_price_included_in_ideal_TV_price': False,
            'complete_time_field_and_queue_mother_retained': True,
            'complete_curve_witness_required_for_reconstruction': True,
            'actual_hardware_member_asserted': False, 'source_bindings': _bindings(selected_backend), 'controller_advance': False}
        self._seal = continuous._digest(self._value)
        _ISSUED[id(self)] = self._seal, certificate, self._pieces, self._frame

    def record(self):
        _CHECK(); field._closed(self)
        _require(type(self) is RetardedReceiptTimeMeasure and set(vars(self)) ==
            {'_certificate', '_report', '_pieces', '_frame', '_value', '_seal'} and
            _ISSUED.get(id(self)) == (self._seal, self._certificate, self._pieces, self._frame) and
            continuous._digest(self._value) == self._seal and
            continuous._digest(self._report) == self._value['checked_curve_digest'] and
            self._value['source_bindings'] == _bindings(self._value['continuous_certificate_backend']) and
            continuous.RetardedReceiptTrajectoryCertificate.record(self._certificate) ==
                self._value['continuous_certificate_source'], 'original time measure, witness or source changed')
        return continuous._copy(self._value)

    def checked_curve(self):
        RetardedReceiptTimeMeasure.record(self)
        return continuous._copy(self._report)

    @classmethod
    def from_record(cls, record, certificate, report):
        _require(cls is RetardedReceiptTimeMeasure, 'closed named time-measure type required')
        result = cls(certificate, report, backend=record.get('continuous_certificate_backend'))
        _require(RetardedReceiptTimeMeasure.record(result) == record, 'original time measure source record changed')
        return result

    def _tv_price(self, lower, upper):
        report = self._report; start = Q(report['source_detector_interval_seconds'][0])
        if report['source_issued_input_used']:
            envelope = continuous.activity.RetardedReceiptActivityEnvelope(self._certificate._source._law,
                bits=report['coefficient_bits'])
            initial = continuous._read_state(report['untrusted_trial']['complete_initial_marked_state'], self._certificate._source)
            payment = continuous.activity.RetardedReceiptActivityEnvelope.input_error_payment(envelope,
                report['whole_upstream_trace_norm_error_once'], start_marks=tuple({m for m, _, _ in initial}),
                input_time=start, interval=(lower, upper))
            old = Q(payment['first_receipt_input_error_payment'])
        else:
            old = Q(report['whole_upstream_trace_norm_error_once'])
            payment = {'input_effect_contraction_upper': '1', 'first_receipt_input_error_payment': str(old),
                       'generic_error_support_inferred_from_centre_marks': False}
        local = Q(report['source_rotating_curve_error'])
        gamma = Q(report['mathematical_Gamma_full_marked_price'])
        return old + local + gamma, {'whole_upstream_error_payment_once': payment,
            'initial_numeric_full_residual_and_signed_join_price': str(local),
            'lifted_Gamma_pending_and_event_instrument_price_once': str(gamma),
            'all_pattern_time_TV_is_one_direct_sum_bound': True}

    def _integral(self, lower, upper, power, left_closed, right_closed, bits):
        start, stop = map(Q, self._report['source_detector_interval_seconds'])
        images = []; weights = []; atoms = []
        for piece in self._pieces:
            origin, width, _ = piece; a, b = max(lower, origin), min(upper, origin + width)
            if a >= b:
                continue
            polynomial = _polynomial_weight(origin, width, start, stop, power)
            for (exponent, angle, n), image in _physical_density_terms(self._frame, piece).items():
                _require(n + power <= 64, 'registered scalar moment degree required')
                moment = moments.Enclosure((Q(0), Q(0)), Q(0))
                for k, coefficient in enumerate(polynomial):
                    if coefficient:
                        moment = moment.add(moments.exponential_moment(exponent, n + k,
                            (a - origin) / width, (b - origin) / width, bits=bits).scale(coefficient))
                centre, error = gaussian._exponential(0, angle, bits)
                weights.append(moment.multiply(moments.Enclosure(centre, error)).rounded(bits))
                images.append(continuous._exact(image))
        atom_price = Q(0)
        for left, right in zip(self._pieces, self._pieces[1:]):
            time = right[0]
            if not _contains(time, lower, upper, left_closed, right_closed):
                continue
            after, after_error = _value(self._frame, right, time, bits)
            before, before_error = _value(self._frame, left, time, bits)
            atom = dict(after); field._add(atom, before, -1)
            factor = ((time - start) / (stop - start))**power
            atoms.append({'detector_time_seconds': str(time), 'weight': str(factor),
                          'complete_signed_four_pattern_atom': channel._input_record(atom),
                          'fresh_exponential_and_frame_atom_price': str(field._price_upper(after_error + before_error, bits))})
            images.append(atom); weights.append(moments.Enclosure((factor, Q(0)), Q(0)).rounded(bits))
            atom_price += factor * (after_error + before_error)
        if not images:
            return {}, Q(0), atoms
        total = accumulator.RadicalMatrixTimeAccumulator(images, scalar_bits=bits, norm_bits=bits)
        for n, weight in enumerate(weights):
            total.add_matrix(n, weight)
        value, price = total.result()
        return value, price + atom_price, atoms

    def interval(self, lower, upper, *, time_power=0, left_closed=False, right_closed=True, bits=192):
        source = RetardedReceiptTimeMeasure.record(self)
        gaussian._precision(bits); lower, upper = map(full.nonnegative, (lower, upper))
        start, stop = map(Q, self._report['source_detector_interval_seconds'])
        _require(start <= lower <= upper <= stop and type(time_power) is int and 0 <= time_power <= 8 and
                 type(left_closed) is bool and type(right_closed) is bool,
                 'ordered original clock cell and registered bounded time weight required')
        empty = lower == upper and not (left_closed and right_closed)
        value, scalar, atoms = ({}, Q(0), []) if empty else RetardedReceiptTimeMeasure._integral(
            self, lower, upper, time_power, left_closed, right_closed, bits)
        tv, details = (Q(0), {}) if empty else RetardedReceiptTimeMeasure._tv_price(self, lower, upper)
        return {'schema': SCHEMA + '/interval', 'source_record': source,
            'detector_interval_seconds': list(map(str, (lower, upper))),
            'Stieltjes_left_closed': left_closed, 'Stieltjes_right_closed': right_closed,
            'source_bounded_time_weight_power': time_power,
            'source_weight_coordinate': '(detector_time-source_start)/(source_stop-source_start)',
            'four_pattern_poststates': [{'pattern_index': h, 'pattern_name': bsm.PATTERNS[h][0],
                'complete_retarded_poststate': channel._input_record(matrix)} for h, matrix in enumerate(_split(value))],
            'signed_candidate_join_atoms': atoms, 'time_total_variation_error': str(field._price_upper(tv, bits)),
            'fresh_scalar_integration_and_frame_price': str(field._price_upper(scalar, bits)),
            'whole_four_pattern_trace_norm_error': str(field._price_upper(tv + scalar, bits)),
            'TV_price_components': details, 'retarded_coimage_is_actual_detector_time_atom': False,
            'public_error_price_rounding': 'upward to the requested dyadic precision',
            'actual_hardware_member_asserted': False}

    def tagged_carrier_parity_image(self, lower, upper, *, bits=192):
        whole = RetardedReceiptTimeMeasure.interval(self, lower, upper, bits=bits)
        weighted = RetardedReceiptTimeMeasure.interval(self, lower, upper, time_power=1, bits=bits)
        patterns = []
        for first, second in zip(whole['four_pattern_poststates'], weighted['four_pattern_poststates']):
            base, moment = (channel._read_input(row['complete_retarded_poststate'], joint.DIMENSION)
                            for row in (first, second))
            image = dict(base); field._add(image, moment, -1)
            conjugate = {(i, j): value * (-1 if
                (dipole.STATES[i // full.DIMENSION].family == 'D2') !=
                (dipole.STATES[j // full.DIMENSION].family == 'D2') else 1) for (i, j), value in moment.items()}
            field._add(image, conjugate)
            patterns.append({'pattern_index': first['pattern_index'], 'complete_retarded_poststate': channel._input_record(image)})
        numeric = Q(whole['fresh_scalar_integration_and_frame_price']) + 2 * Q(weighted['fresh_scalar_integration_and_frame_price'])
        return {'schema': SCHEMA + '/time-dependent-CPTP-image', 'source_record': whole['source_record'],
            'detector_interval_seconds': whole['detector_interval_seconds'], 'four_pattern_poststates': patterns,
            'source_CPTP_family': '(1-u)Id+u Ad(I-2 P_D2_A), 0<=u<=1',
            'time_total_variation_error_paid_once': whole['time_total_variation_error'],
            'fresh_numeric_integration_price': str(field._price_upper(numeric, bits)),
            'whole_four_pattern_trace_norm_error': str(field._price_upper(Q(whole['time_total_variation_error']) + numeric, bits)),
            'consumer_is_actual_apparatus_operation': False, 'actual_hardware_member_asserted': False}


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None)), repr(getattr(value, '__defaults__', None)), repr(getattr(value, '__kwdefaults__', None))


def _signature():
    helpers = (_require, _bindings, _verified_curve, _initial_absorbed_zero, _compile, _frame_recipe, _frame_word, _add_image,
        _physical_density_terms, _value, _polynomial_weight, _contains, _split, _function, _signature, _check,
        continuous.RetardedReceiptTrajectoryCertificate.record, continuous.RetardedReceiptTrajectoryCertificate.verify,
        integer.verify, integer.certify,
        common_integer.verify, common_integer.certify,
        frequency_clustered.verify, frequency_clustered.certify,
        residual_cells.verify, residual_cells.certify,
        gaussian_tail.verify, gaussian_tail.certify,
        gaussian_tail_duhamel.verify, gaussian_tail_duhamel.certify,
        gaussian_tail_duhamel_cells.verify, gaussian_tail_duhamel_cells.certify,
        continuous._modes, continuous._coefficient, continuous._add, continuous._exact,
        moments.exponential_moment, moments._unit_moment, moments._unit_moment.__wrapped__, moments._exp,
        moments.Enclosure.__post_init__, moments.Enclosure.add, moments.Enclosure.scale,
        moments.Enclosure.multiply, moments.Enclosure.rounded,
        accumulator._require, accumulator.RadicalTimeAccumulator.__init__,
        accumulator.RadicalTimeAccumulator._weight, accumulator.RadicalTimeAccumulator._add_image,
        accumulator.RadicalTimeAccumulator.result, accumulator.RadicalMatrixTimeAccumulator.__init__,
        accumulator.RadicalMatrixTimeAccumulator._image, accumulator.RadicalMatrixTimeAccumulator.add_matrix,
        full._sqrt, gaussian._exponential, field._price_upper, field._add, channel._input_record, channel._read_input)
    methods = tuple(_function(value) for value in vars(RetardedReceiptTimeMeasure).values()
                    if callable(value) or isinstance(value, classmethod))
    return tuple(map(_function, helpers)), methods, SCHEMA, joint.DIMENSION, tuple(dipole.STATES)


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
             continuous._CHECK is _CONTINUOUS_CHECK, 'source time-measure execution changed')
    _CONTINUOUS_CHECK()
    _require(integer._CHECK is _INTEGER_CHECK, 'fixed integer certificate backend changed')
    _require(common_integer._CHECK is _COMMON_INTEGER_CHECK,
             'fixed common-integer certificate backend changed')
    _require(frequency_clustered._CHECK is _FREQUENCY_CLUSTERED_CHECK,
             'fixed frequency-clustered certificate backend changed')
    _require(residual_cells._CHECK is _RESIDUAL_CELLS_CHECK,
             'fixed residual-cell certificate backend changed')
    _require(gaussian_tail._CHECK is _GAUSSIAN_TAIL_CHECK,
             'fixed Gaussian-tail certificate backend changed')
    _require(gaussian_tail_duhamel._CHECK is _GAUSSIAN_TAIL_DUHAMEL_CHECK,
             'fixed whole Gaussian-tail Duhamel certificate backend changed')
    _require(gaussian_tail_duhamel_cells._CHECK is _GAUSSIAN_TAIL_DUHAMEL_CELLS_CHECK,
             'fixed whole-tail residual-cell certificate backend changed')


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
