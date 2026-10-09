"""Full natural recycling during the source Gaussian drive.

Hermitian polynomial witnesses are checked against complete source columns.
The true CPTP flow contracts the integrated defect; the optical carrier is
restored at the actual readout time.  A numerical curve is never a prepared
hardware input.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import gaussian_atomic_pulse_source as gaussian
import fourier_local_phase_source as fourier

dipole, full, field, channel = gaussian.dipole, gaussian.full, gaussian.field, gaussian.channel
SCHEMA = 'stage10-source-Gaussian-complete-local-density/v1'
_ISSUED = {}
_CHECKED = {}
_GAUSSIAN_CHECK = gaussian._CHECK


def _require(value, message):
    if not value:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__), *(Path(m.__file__) for m in (gaussian, fourier, dipole, full, field, channel)))}


def _add(result, matrix, factor=1):
    field._add(result, matrix, factor)


def _parts(raw, bits):
    h = gaussian._matrix(raw['complete_static_H_per_second'])
    r = gaussian._matrix(raw['complete_natural_R_per_second'])
    a = gaussian._matrix(raw['source_raising_operator_per_second'])
    k = gaussian._scale(h, dipole.ComplexRadical(0, -1))
    _add(k, r, Q(-1, 2))
    _add(k, {(i, i): dipole.ComplexRadical(0, Q(raw['carrier_angular_frequency_per_second']))
             for i, s in enumerate(dipole.STATES) if s.family == 'D2'})
    phase, error = gaussian._exponential(Q(0), Q(raw['phase_radians']), bits)
    raising = gaussian._scale(a, dipole.ComplexRadical(*phase))
    v = gaussian._scale(gaussian._sum(raising, dipole.matrix_adjoint(raising)), dipole.ComplexRadical(0, -1))
    jumps = tuple((Q(j['physical_amplitude_squared_per_second']),
                   gaussian._matrix(j['normalized_natural_jump_operator']))
                  for j in raw['original_physical_natural_jumps'])
    _require(not gaussian._sum(k, dipole.matrix_adjoint(k), r) and
             not gaussian._sum(v, dipole.matrix_adjoint(v)), 'the source density generator lost its Hermitian CP law')
    recovered = {}
    for rate, jump in jumps:
        _require(all(dipole.STATES[i].family == 'ground' and dipole.STATES[j].family in ('D1', 'D2')
                     for i, j in jump) and len({dipole.STATES[j].family for _, j in jump}) <= 1,
                 'one source-resolved bath must keep its common frame phase')
        _add(recovered, dipole.matrix_product(dipole.matrix_adjoint(jump), jump), rate)
    _require(recovered == r, 'all source recycling columns must exactly recover natural R')
    return k, v, jumps, 4*error*gaussian._norm(a, bits)


class _Columns:
    def __init__(self, raw, bits):
        self.raw, self.bits = raw, bits
        self.k, self.v, self.jumps, self.phase_error = _parts(raw, bits)
        self.cache = {}

    def column(self, component, key):
        if (component, key) in self.cache:
            return self.cache[component, key]
        matrix = {key: dipole.ComplexRadical(1)}
        k = self.k if component == 'quiet' else self.v
        result = dipole.matrix_product(k, matrix)
        _add(result, dipole.matrix_product(matrix, dipole.matrix_adjoint(k)))
        if component == 'quiet':
            for rate, jump in self.jumps:
                _add(result, dipole.matrix_product(dipole.matrix_product(jump, matrix), dipole.matrix_adjoint(jump)), rate)
        centres, errors = full._midpoint_matrix(result, self.bits)
        centres, rounding = fourier.exact._dyadic_state(centres, self.bits)
        value = centres, sum(errors.values(), Q(0))+rounding
        self.cache[component, key] = value
        return value

    def action(self, component, state):
        result = {}; error = Q(0)
        for key, pair in state.items():
            image, price = self.column(component, key)
            fourier._add_rational(result, image, pair)
            error += (abs(pair[0])+abs(pair[1]))*price
        return result, error


def _initial(matrix, bits):
    matrix = gaussian._matrix(matrix) if type(matrix) is list else channel._read_input(channel._input_record(matrix), full.DIMENSION)
    _require(bsm_hermitian(matrix), 'complete Hermitian local input required; positivity is owned by its source')
    result, errors = full._midpoint_matrix(matrix, bits)
    result, price = fourier.exact._dyadic_state(fourier._hermitian(result), bits)
    return matrix, result, sum(errors.values(), Q(0))+price


def bsm_hermitian(matrix):
    return all(matrix.get((j, i), dipole.ComplexRadical()) == value.conjugate() for (i, j), value in matrix.items())


def _rows(matrix, bits):
    quantum = 1 << bits
    return [[i, j, int(a*quantum), int(b*quantum)] for (i, j), (a, b) in sorted(matrix.items()) if a or b]


def _sum_pairs(matrices):
    result = {}
    for matrix in matrices:
        fourier._add_rational(result, matrix, (Q(1), Q(0)))
    return result


def _frame(raw, matrix, time, bits, inverse=False):
    result = {}; error = Q(0); phases = {}
    omega = Q(raw['carrier_angular_frequency_per_second'])
    for (i,j), value in matrix.items():
        angle = omega*time*((dipole.STATES[j].family == 'D2')-(dipole.STATES[i].family == 'D2'))
        if inverse:
            angle = -angle
        if angle not in phases:
            phases[angle] = gaussian._exponential(Q(0), angle, bits)
        phase, price = phases[angle]
        result[i,j] = field._product(phase, value)
        error += price*(abs(value[0])+abs(value[1]))
    hermitian = fourier._hermitian(result)
    return hermitian, error+fourier._difference(result, hermitian)


def _rotating_initial(raw, initial, start, bits):
    original, pairs, price = _initial(initial, bits)
    pairs, phase = _frame(raw, pairs, start, bits, inverse=True)
    pairs, rounding = fourier.exact._dyadic_state(pairs, bits)
    return original, pairs, price+phase+rounding


def _density_modes(piece, mode_bits):
    _require(type(piece) is dict and set(piece) == {'duration_seconds', 'modes'} and
             type(piece['modes']) is list and piece['modes'], 'complete exponential-polynomial density piece required')
    width = full.exact(piece['duration_seconds'])
    _require(width > 0, 'positive source density interval required')
    groups = {}
    for mode in piece['modes']:
        _require(type(mode) is dict and set(mode) == {'lambda_per_second', 'coefficients'} and
                 type(mode['lambda_per_second']) is list and len(mode['lambda_per_second']) == 2 and
                 type(mode['coefficients']) is list and 1 <= len(mode['coefficients']) <= 65,
                 'complete complex source mode and coefficient inventory required')
        lr, li = map(full.exact, mode['lambda_per_second'])
        _require(lr*width <= Q(1, 2), 'source mode growth must satisfy Re(lambda)*duration <= 1/2')
        for n, rows in enumerate(mode['coefficients']):
            matrix = fourier._coefficient(rows, 1 << mode_bits)
            fourier._add_rational(groups.setdefault((lr, li), {}).setdefault(n, {}), matrix, (Q(1, 2), Q(0)))
            adjoint = {(j, i): (a, -b) for (i, j), (a, b) in matrix.items()}
            fourier._add_rational(groups.setdefault((lr, -li), {}).setdefault(n, {}), adjoint, (Q(1, 2), Q(0)))
    return width, groups


def _piece_modes(columns, raw, piece, current, start, mode_bits, envelope_order):
    width, groups = _density_modes(piece, mode_bits)
    g, tail = gaussian._envelope_polynomial(raw, start, width, envelope_order, columns.bits)
    residual = {}; begin = {}; end = {}
    column_error = drive_tail = endpoint_error = Q(0)
    for exponent, polynomial in groups.items():
        lr, li = exponent
        for n, matrix in polynomial.items():
            fourier._add_rational(residual.setdefault(exponent, {}).setdefault(n, {}), matrix, (width*lr, width*li))
            if n:
                fourier._add_rational(residual.setdefault(exponent, {}).setdefault(n-1, {}), matrix, (Q(n), Q(0)))
            quiet, eq = columns.action('quiet', matrix)
            drive, ev = columns.action('drive', matrix)
            fourier._add_rational(residual.setdefault(exponent, {}).setdefault(n, {}), quiet, (-width, Q(0)))
            for j, coefficient in enumerate(g):
                fourier._add_rational(residual.setdefault(exponent, {}).setdefault(n+j, {}), drive, (-width*coefficient, Q(0)))
            column_error += 2*width*(eq+(sum(map(abs, g), Q(0))+tail)*ev+
                columns.phase_error*fourier._norm(matrix))/Q(n+1)
            drive_tail += 2*width*tail*(fourier._norm(drive)+ev)/Q(n+1)
            if n == 0:
                fourier._add_rational(begin, matrix, (Q(1), Q(0)))
        scalar, price = gaussian._exponential(lr*width, li*width, columns.bits)
        for matrix in polynomial.values():
            fourier._add_rational(end, matrix, scalar)
            endpoint_error += price*fourier._norm(matrix)
    defect = 2*sum((fourier._norm(matrix)/Q(n+1) for polynomial in residual.values()
                   for n, matrix in polynomial.items()), Q(0))
    join = fourier._difference(begin, current)
    projected = fourier._hermitian(end)
    endpoint_error += fourier._difference(end, projected)
    price = join+defect+column_error+drive_tail+endpoint_error
    return width, projected, price, {
        'source_interval_seconds': list(map(str, (start, start+width))),
        'actual_full_column_exponential_polynomial_defect_integral': str(defect),
        'source_Gaussian_tail_price': str(drive_tail),
        'source_column_and_phase_price': str(column_error), 'actual_join_price': str(join),
        'endpoint_exponential_scalar_price': str(endpoint_error),
        'source_exact_exponents_after_merge': len(groups),
        'complete_coordinate_inventory': len(set().union(*(set(m) for p in groups.values() for m in p.values()))),
        'entire_complex_curve_Hermitian_projection': True,
        'Hermitian_CPTP_contraction_used': True, 'Hamiltonian_norm_exponential_used': False}


def _piece(columns, raw, piece, current, start, mode_bits, envelope_order):
    if type(piece) is dict and set(piece) == {'duration_seconds', 'modes'}:
        return _piece_modes(columns, raw, piece, current, start, mode_bits, envelope_order)
    _require(type(piece) is dict and set(piece) == {'duration_seconds', 'coefficients'} and
             type(piece['coefficients']) is list and 1 <= len(piece['coefficients']) <= 65,
             'complete source-density polynomial piece required')
    width = full.exact(piece['duration_seconds'])
    _require(width > 0, 'positive source slice required')
    matrices = [fourier._coefficient(rows, 1 << mode_bits) for rows in piece['coefficients']]
    _require(all(full._hermitian(m) for m in matrices), 'each true defect coefficient must be Hermitian')
    g, tail = gaussian._envelope_polynomial(raw, start, width, envelope_order, columns.bits)
    residual = {}; column_error = Q(0); drive_norm = Q(0)
    for n, matrix in enumerate(matrices):
        if n:
            fourier._add_rational(residual.setdefault(n-1, {}), matrix, (Q(n), Q(0)))
        quiet, eq = columns.action('quiet', matrix)
        drive, ev = columns.action('drive', matrix)
        fourier._add_rational(residual.setdefault(n, {}), quiet, (-width, Q(0)))
        for j, coefficient in enumerate(g):
            fourier._add_rational(residual.setdefault(n+j, {}), drive, (-width*coefficient, Q(0)))
        column_error += width*(eq + (sum(map(abs, g), Q(0))+tail)*ev + columns.phase_error*fourier._norm(matrix))
        drive_norm += fourier._norm(drive)+ev
    defect = sum((fourier._norm(matrix)/Q(n+1) for n, matrix in residual.items()), Q(0))
    join = fourier._difference(matrices[0], current)
    price = join+defect+column_error+width*tail*drive_norm
    return width, _sum_pairs(matrices), price, {
        'source_interval_seconds': list(map(str, (start, start+width))),
        'actual_full_column_polynomial_defect_integral': str(defect),
        'source_Gaussian_tail_price': str(width*tail*drive_norm),
        'source_column_and_phase_price': str(column_error), 'actual_join_price': str(join),
        'complete_coordinate_inventory': len(set().union(*(set(m) for m in matrices))),
        'Hermitian_CPTP_contraction_used': True, 'Hamiltonian_norm_exponential_used': False}


class GaussianLocalDensitySource:
    def __init__(self, pulse):
        _CHECK(); field._closed(pulse)
        _require(type(pulse) is gaussian.GaussianAtomicPulseSource, 'closed same-owner Gaussian pulse required; G is generated')
        raw = gaussian.GaussianAtomicPulseSource.record(pulse)
        self._pulse = pulse
        self._value = {'schema': SCHEMA, 'Gaussian_source': raw, 'source_bindings': _bindings(),
            'all_33_coordinates_and_natural_recycling': True,
            'candidate_or_initial_matrix_is_actual_hardware_input': False,
            'density_rule': 'D(t) rho_rot(t) D(t)*; every resolved natural recycle is frame invariant',
            'old_error_paid_once_by_CPTP_contraction': True, 'controller_advance': False}
        self._seal = _digest(self._value); _ISSUED[id(self)] = self._seal

    def record(self):
        _CHECK(); field._closed(self)
        _require(type(self) is GaussianLocalDensitySource and set(vars(self)) == {'_pulse', '_value', '_seal'} and
                 _ISSUED.get(id(self)) == self._seal and _digest(self._value) == self._seal and
                 self._value['source_bindings'] == _bindings() and
                 gaussian.GaussianAtomicPulseSource.record(self._pulse) == self._value['Gaussian_source'],
                 'complete Gaussian density source or executed columns changed')
        return _copy(self._value)

    def generate_trial(self, initial, stop, *, start=0, slices=64, order=32, mode_bits=160, coefficient_bits=192, envelope_order=10):
        raw = GaussianLocalDensitySource.record(self)['Gaussian_source']
        gaussian._precision(mode_bits); gaussian._precision(coefficient_bits)
        start, stop = map(full.nonnegative, (start, stop))
        _require(start <= stop and type(slices) is int and slices > 0 and type(order) is int and 0 <= order <= 64 and
                 type(envelope_order) is int and 0 <= envelope_order <= 32, 'source interval and finite density proposal budget required')
        original, current, _ = _rotating_initial(raw, initial, start, mode_bits)
        columns = _Columns(raw, coefficient_bits); pieces = []
        width = (stop-start)/slices
        for n in range(slices if start < stop else 0):
            origin = start+n*width
            g, _ = gaussian._envelope_polynomial(raw, origin, width, envelope_order, coefficient_bits)
            matrices = [current]; drives = [columns.action('drive', current)[0]]
            for degree in range(order):
                action = columns.action('quiet', matrices[degree])[0]
                for j in range(min(degree, len(g)-1)+1):
                    fourier._add_rational(action, drives[degree-j], (g[j], Q(0)))
                proposal = {k:(a*width/(degree+1), b*width/(degree+1)) for k,(a,b) in action.items()}
                proposal, _ = fourier.exact._dyadic_state(fourier._hermitian(proposal), mode_bits)
                matrices.append(proposal); drives.append(columns.action('drive', proposal)[0])
            pieces.append({'duration_seconds': str(width), 'coefficients': [_rows(m, mode_bits) for m in matrices]})
            current = _sum_pairs(matrices)
        return {'schema': SCHEMA+'/untrusted-curve', 'source_record': GaussianLocalDensitySource.record(self),
            'complete_initial_matrix': channel._input_record(original), 'start_seconds': str(start), 'stop_seconds': str(stop), 'mode_bits': mode_bits,
            'pieces': pieces, 'writer_correctness_assumed': False}

    def certify(self, trial, *, input_error=0, coefficient_bits=192, envelope_order=10):
        raw = GaussianLocalDensitySource.record(self)
        _require(type(trial) is dict and set(trial) == {'schema','source_record','complete_initial_matrix','start_seconds','stop_seconds',
                'mode_bits','pieces','writer_correctness_assumed'} and trial['schema'] == SCHEMA+'/untrusted-curve' and
                trial['source_record'] == raw and trial['writer_correctness_assumed'] is False,
                 'untrusted density curve must bind the exact original source')
        gaussian._precision(trial['mode_bits']); gaussian._precision(coefficient_bits)
        _require(type(envelope_order) is int and 0 <= envelope_order <= 32 and type(trial['pieces']) is list,
                 'registered Gaussian checking order and complete pieces required')
        source = raw['Gaussian_source']; start, stop = map(full.nonnegative, (trial['start_seconds'], trial['stop_seconds']))
        _require(start <= stop, 'ordered original density source interval required')
        initial, current, error = _rotating_initial(source, trial['complete_initial_matrix'], start, trial['mode_bits'])
        inherited = full.nonnegative(input_error); initial_norm = fourier.bsm._entry_norm(initial, bits=coefficient_bits)
        columns = _Columns(source, coefficient_bits); time = start; records = []
        for piece in trial['pieces']:
            width, current, payment, record = _piece(columns, source, piece, current, time, trial['mode_bits'], envelope_order)
            time += width; error += payment; records.append(record)
        _require(time == stop, 'complete density curve must end at the exact source cut')
        physical, phase_price = _frame(source, current, time, coefficient_bits)
        physical = {key:dipole.ComplexRadical(*value) for key,value in physical.items()}
        gamma = Q(source['reference_clock']['Gamma_numerical_centre'])
        lo, hi = map(Q, source['reference_clock']['angular_Gamma_enclosure_per_second'])
        delta = max(abs(gamma-lo), abs(hi-gamma))
        gamma_price = initial_norm*(2*gaussian.GaussianAtomicPulseSource.Gamma_math_price(self._pulse, start, stop, bits=coefficient_bits)+
            delta/gamma*(stop-start)*gaussian._norm(gaussian._matrix(source['complete_natural_R_per_second']), coefficient_bits))
        total = inherited+error+phase_price+gamma_price
        report = {'schema': SCHEMA+'/checked-curve', 'source_record': raw, 'untrusted_trial': _copy(trial),
            'input_trace_norm_error': str(inherited), 'source_curve_residual_error': str(field._price_upper(error, coefficient_bits)),
            'physical_frame_entry_trace_norm_price': str(field._price_upper(phase_price, coefficient_bits)),
            'mathematical_Gamma_full_density_price': str(field._price_upper(gamma_price, coefficient_bits)),
            'whole_trace_norm_error': str(field._price_upper(total, coefficient_bits)),
            'complete_physical_endpoint': channel._input_record(physical), 'source_cut_seconds': str(stop),
            'source_interval_seconds': list(map(str, (start, stop))),
            'original_operator_certification_horizon_seconds': source['duration_seconds'],
            'density_interval_checked_by_its_own_full_residual': True,
            'piece_records': records, 'coefficient_bits': coefficient_bits, 'envelope_order': envelope_order,
            'Hermitian_CPTP_contraction_used': True, 'full_emission_numbers_resummed': True}
        _CHECKED[_digest(report)] = _copy(report)
        return report

    def verify(self, certificate, *, recheck=False):
        raw = GaussianLocalDensitySource.record(self)
        _require(type(certificate) is dict and certificate.get('source_record') == raw,
                 'checked density curve must belong to the same original source')
        _require(type(recheck) is bool, 'explicit Boolean density recheck override required')
        key = _digest(certificate)
        # The inlet consumes these same certificates immediately after their
        # complete residual check.  Keep that paid result owned and detached.
        if not recheck and key in _CHECKED:
            _require(_CHECKED[key] == certificate, 'cached complete density certificate changed')
            return _copy(_CHECKED[key])
        expected = GaussianLocalDensitySource.certify(self, certificate['untrusted_trial'],
            input_error=certificate['input_trace_norm_error'], coefficient_bits=certificate['coefficient_bits'],
            envelope_order=certificate['envelope_order'])
        _require(expected == certificate, 'actual density residual, endpoint or paid error changed')
        return expected


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    helpers = (_require, _copy, _digest, _bindings, _add, _parts, _initial, bsm_hermitian, _rows, _sum_pairs, _frame, _rotating_initial,
        _density_modes, _piece_modes, _piece,
        _function, _signature, _check, gaussian.GaussianAtomicPulseSource.record, gaussian.GaussianAtomicPulseSource.Gamma_math_price,
        gaussian._envelope_polynomial, gaussian._matrix, gaussian._norm, gaussian._exponential,
        dipole.matrix_product, dipole.matrix_adjoint, full._midpoint_matrix, fourier._add_rational,
        fourier._norm, fourier._difference, fourier._coefficient, fourier._hermitian, fourier.exact._dyadic_state,
        field._closed, field._price_upper, field._product, field._add, channel._read_input, channel._input_record)
    classes = (_Columns, GaussianLocalDensitySource)
    return tuple(map(_function, helpers)), tuple(tuple(_function(v) for v in vars(c).values() if callable(v)) for c in classes), SCHEMA


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
             gaussian._CHECK is _GAUSSIAN_CHECK, 'complete Gaussian density execution changed')
    _GAUSSIAN_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
