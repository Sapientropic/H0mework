"""The original local carrier chart feeds the joint stopped-count action.

Both atoms use one detector-time frame during the gate.  Their unequal
flight phases remain in the drives; the coherent port/loss transfer stays
unchanged.  The existing local density checker supplies the pre-gate flows.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib

import gaussian_local_density_source as density
import retarded_gate_common_phase_source as count

excitation, gaussian = count.excitation, count.excitation.gaussian
dipole, channel, joint, field = count.dipole, count.channel, count.joint, count.field
SCHEMA = 'stage10-same-source-detector-time-rotating-count/v1'
_ISSUED = {}


def bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
            (Path(__file__), Path(__file__).with_name('retarded_count_rotating_independent.py'),
             Path(__file__).with_name('criterion-rha0024.md'), Path(count.__file__), Path(density.__file__))}


def line_projector():
    return excitation.preparation.frame._projector('D2')


def rotating_primitive(pulse, detector_time, flight, phase, *, bits=192):
    """H_rot=H_static-omega P+g(t-flight)(A exp(i(phase+omega flight))+h.c.)."""
    gaussian._precision(bits)
    t, f, angle = map(excitation.full.exact, (detector_time, flight, phase))
    count.require(t >= f >= 0, 'the gate must follow this original retarded activation')
    omega = Q(pulse['carrier_angular_frequency_per_second'])
    local = t-f; fixed = angle+omega*f
    chart_pulse = {**pulse, 'phase_radians': str(fixed)}
    scalar, scalar_error = gaussian._scalar(chart_pulse, local, bits, carrier=False)
    raising = gaussian._matrix(pulse['source_raising_operator_per_second'])
    drive = {key: value*dipole.ComplexRadical(*scalar) for key, value in raising.items()}
    quiet = gaussian._sum(gaussian._matrix(pulse['complete_static_H_per_second']),
                          {key: -omega*value for key, value in line_projector().items()})
    h = gaussian._sum(quiet, drive, dipole.matrix_adjoint(drive))
    loss = gaussian._matrix(pulse['complete_natural_R_per_second'])
    k = gaussian._sum({key: value*dipole.ComplexRadical(0, -1) for key, value in h.items()},
                     {key: -value*Q(1, 2) for key, value in loss.items()})
    count.require(h == dipole.matrix_adjoint(h) and
                  not gaussian._sum(k, dipole.matrix_adjoint(k), loss),
                  'the complete rotating source must retain its exact Hermitian CP identity')
    return {'complete_K_per_second': channel._input_record(k),
        'H_scalar_operator_error_upper_per_second': str(2*scalar_error*gaussian._norm(raising, bits)),
        'original_resolved_natural_jumps': count.copy(pulse['original_physical_natural_jumps']),
        'source_rotating_H_per_second': channel._input_record(h),
        'source_rotating_static_H_per_second': channel._input_record(quiet),
        'source_local_seconds': str(local), 'source_detector_seconds': str(t),
        'source_original_carrier_per_second': str(omega), 'fixed_drive_phase_in_detector_frame': str(fixed),
        'carrier_scalar_exponential_evaluated': False,
        'frame_generator': '-i omega (P_D2_A+P_D2_B)',
        'coherent_port_and_loss_transfer_changed': False}


def gate_primitives(raw, detector_time, relative_phase, *, bits=192):
    pulses = raw['source_generated_zero_line_chart_pulses']
    flights = tuple(map(Q, raw['flight_seconds']))
    omega = tuple(Q(p['carrier_angular_frequency_per_second']) for p in pulses)
    count.require(len(pulses) == len(flights) == 2 and omega[0] == omega[1],
                  'the common detector frame requires both original equal carriers')
    g0, g1 = map(Q, raw['source_gate_offsets_from_pump_end_seconds'])
    t = excitation.full.exact(detector_time)
    count.require(g0 <= t <= g1 and g0 >= max(flights), 'the complete original gate clock is required')
    return [rotating_primitive(p, t, f, phase, bits=bits)
            for p, f, phase in zip(pulses, flights, (Q(0), excitation.full.exact(relative_phase)))]


def inlet_protocol(raw, relative_phase):
    """Reuse local density residuals, then join their frames at the true gate cut."""
    pulses = raw['source_generated_zero_line_chart_pulses']
    flights = tuple(map(Q, raw['flight_seconds'])); g0 = Q(raw['source_gate_offsets_from_pump_end_seconds'][0])
    count.require(len(pulses) == len(flights) == 2 and g0 >= max(flights), 'both causal pre-gate local flows required')
    rows = []
    for side, (pulse, flight, phase) in enumerate(zip(pulses, flights, (Q(0), excitation.full.exact(relative_phase)))):
        rows.append({'side': side, 'local_density_source': {**count.copy(pulse), 'phase_radians': str(phase)},
            'source_local_interval_seconds': ['0', str(g0-flight)],
            'local_to_detector_frame_angle_radians': str(Q(pulse['carrier_angular_frequency_per_second'])*flight)})
    return {'schema': SCHEMA+'/pre-gate-local-density-feed', 'local_source_flows': rows,
        'local_checker': 'gaussian_local_density_source._Columns/_piece; raw input owned by qualified count source',
        'initial_local_frames_are_identity': True,
        'join_at_original_retarded_gate_cut': True, 'signed_tensor_terms_need_not_be_positive': True,
        'source_inlet_error_transported_once': True, 'new_density_residuals_or_join_phase_error_paid': False,
        'quantum_time_queue_product_assumed': False}


def local_pair_frame(angles, matrix, *, bits=192):
    """Join two local rotating endpoints by their actual constant flight phases."""
    gaussian._precision(bits); angles = tuple(map(excitation.full.exact, angles))
    count.require(len(angles) == 2, 'both original local-to-detector frame angles required')
    matrix = joint._matrix(matrix); phases, result, price = {}, {}, Q(0)
    for (row, column), value in matrix.items():
        a, b = divmod(row, excitation.full.DIMENSION); c, d = divmod(column, excitation.full.DIMENSION)
        charge = lambda i: int(dipole.STATES[i].family == 'D2')
        angle = (charge(a)-charge(c))*angles[0]+(charge(b)-charge(d))*angles[1]
        positive = abs(angle)
        if positive not in phases:
            centre, error = gaussian._exponential(0, positive, bits) if positive else ((Q(1), Q(0)), Q(0))
            phases[positive] = dipole.ComplexRadical(*centre), error
        phase, error = phases[positive]
        result[row, column] = value*(phase if angle >= 0 else phase.conjugate())
        price += error*count.gate_input.bsm._entry_norm({(0, 0): value}, bits=bits)
    return result, price


def check_local_inlet_curve(pulse, clock, initial, pieces, stop, *, mode_bits=96,
                            coefficient_bits=192, envelope_order=10):
    """Use the existing complete local residual on a source-issued factor."""
    density._CHECK(); gaussian._precision(mode_bits); gaussian._precision(coefficient_bits)
    stop = excitation.full.nonnegative(stop)
    count.require(type(pieces) is list and type(envelope_order) is int and 0 <= envelope_order <= 32,
                  'complete original local curve and registered Gaussian envelope order required')
    original, current, error = density._initial(initial, mode_bits)
    columns = density._Columns(pulse, coefficient_bits); elapsed = Q(0); payments = []
    for piece in pieces:
        width, current, price, row = density._piece(columns, pulse, piece, current, elapsed, mode_bits, envelope_order)
        elapsed += width; error += price; payments.append(row)
    count.require(elapsed == stop, 'the curve must cover the whole original retarded inlet interval')
    gamma = Q(clock['Gamma_numerical_centre']); lo, hi = map(Q, clock['angular_Gamma_enclosure_per_second'])
    delta = max(abs(gamma-lo), abs(hi-gamma))
    gamma_price = density.fourier.bsm._entry_norm(original, bits=coefficient_bits)*(
        2*excitation._Gamma_chart_price(pulse, clock, Q(0), stop, coefficient_bits)+
        delta/gamma*stop*gaussian._norm(gaussian._matrix(pulse['complete_natural_R_per_second']), coefficient_bits))
    endpoint = {key: dipole.ComplexRadical(*value) for key, value in current.items()}
    return endpoint, error+gamma_price, {'source_local_interval_seconds': ['0', str(stop)],
        'source_complete_local_piece_prices': payments, 'local_numeric_error': str(error),
        'original_physical_Gamma_family_price': str(gamma_price),
        'endpoint_in_local_rotating_frame': channel._input_record(endpoint),
        'complete_CPTP_residual_reused': True, 'curve_endpoint_used_as_source_input': False}


class DetectorTimeRotatingCountSource:
    def __init__(self, source):
        count.require(type(source) is count.CommonPhaseRetardedCountSource,
                      'closed same-occurrence qualified count source required')
        source.verify(); parent = source.record(); raw = source._source.record()
        lo, hi = map(Q, parent['relative_fixed_phase_interval']); centre = (lo+hi)/2
        omega = [Q(p['carrier_angular_frequency_per_second']) for p in raw['source_generated_zero_line_chart_pulses']]
        count.require(len(omega) == 2 and omega[0] == omega[1], 'both original carriers must agree')
        self._source = source
        self._value = {'schema': SCHEMA, 'qualified_source_digest': count.digest(parent),
            'original_excitation_source_digest': raw['source_digest'],
            'original_relative_phase_interval': parent['relative_fixed_phase_interval'],
            'relative_phase_centre': str(centre), 'source_inlet_protocol': inlet_protocol(raw, centre),
            'source_frame': 'D(t)=exp(-i omega t (P_D2_A+P_D2_B))',
            'source_frame_H_shift': '-omega (P_D2_A+P_D2_B)',
            'four_port_transfer_and_Mark_targets_preserved': True,
            'herald_trace_boundary_fixed_by_frame': True,
            'relative_phase_and_flight_phases_retained': True,
            'actual_gate_numerical_certificate': False, 'actual_hardware_uniquely_identified': False,
            'controller_advance': False, 'source_bindings': bindings()}
        self._seal = count.digest(self._value); _ISSUED[id(self)] = source, self._seal

    def record(self):
        count.require(type(self) is DetectorTimeRotatingCountSource and
                      set(vars(self)) == {'_source', '_value', '_seal'} and
                      _ISSUED.get(id(self)) == (self._source, self._seal) and
                      count.digest(self._value) == self._seal and self._value['source_bindings'] == bindings() and
                      count.digest(self._source.record()) == self._value['qualified_source_digest'],
                      'the same count source, frame or fixed coordinates changed')
        return count.copy(self._value)

    def source_herald_observer_seed(self, herald):
        self.record()
        return self._source.source_herald_observer_seed(herald)

    def certify_inlet(self, curves, *, mode_bits=96, coefficient_bits=192, envelope_order=10):
        record = self.record(); original = self._source.source_tensors()
        terms = original['tensor_terms']; rows = record['source_inlet_protocol']['local_source_flows']
        count.require(type(curves) is list and len(curves) == len(terms) and
                      all(type(pair) is list and len(pair) == 2 for pair in curves),
                      'exactly two original local curves per source-issued tensor term required')
        new_error, endpoints, prices = Q(0), [], []
        for factors, proposals in zip(terms, curves):
            pair, errors, local_prices = [], [], []
            for initial, pieces, row in zip(factors, proposals, rows):
                matrix, error, price = check_local_inlet_curve(row['local_density_source'],
                    self._source._source.record()['reference_clock'], initial, pieces,
                    row['source_local_interval_seconds'][1], mode_bits=mode_bits,
                    coefficient_bits=coefficient_bits, envelope_order=envelope_order)
                joined, join_error = excitation._line_frame(Q(row['local_to_detector_frame_angle_radians']), matrix, coefficient_bits)
                pair.append(joined); errors.append(error+join_error)
                local_prices.append({**price, 'local_to_detector_frame_error': str(join_error)})
            payment, _, _ = excitation.preparation.factors._tensor_price(*pair, *errors, coefficient_bits)
            new_error += payment; endpoints.append(tuple(pair)); prices.append(local_prices)
        parent = self._source.record()
        old = Q(parent['whole_preparation_error_once'])+Q(
            parent['source_positive_mother_projection']['joint_mother_projection_trace_norm_upper'])
        return {'schema': SCHEMA+'/complete-retarded-inlet-certificate', 'source_record': record,
            'detector_frame_tensor_terms': endpoints, 'source_local_price_inventory': prices,
            'source_quantum_input_error_once': old, 'new_inlet_numeric_error': new_error,
            'whole_quantum_inlet_trace_norm_error': old+new_error,
            'new_future_old_drive_scalar_instrument_price': Q(
                parent['new_future_old_field_Duhamel_price']['future_instrument_difference_upper']),
            'future_drive_price_used_as_input_quantum_error': False, 'gate_Mark_initialized_after_inlet': True,
            'actual_gate_numerical_certificate': False}

    def generator_images(self, detector_time, matrix, *, bits=192, adjoint=False):
        count.require(type(adjoint) is bool, 'explicit primal/adjoint selection required')
        record = self.record(); raw = self._source._source.record()
        primitives = gate_primitives(raw, detector_time, record['relative_phase_centre'], bits=bits)
        if adjoint:
            pending, ports, complete, scalar = count.adjoint_images(raw, primitives, matrix)
        else:
            pending, ports, complete, _, scalar = excitation._retarded_images(raw, primitives, matrix)
        return {'schema': SCHEMA+'/source-generator-image', 'source_record': record,
            'source_detector_seconds': str(excitation.full.exact(detector_time)), 'adjoint': adjoint,
            'no_arrival_image_per_second': channel._input_record(pending),
            'four_port_images_per_second': [channel._input_record(j) for j in ports],
            'complete_image_per_second': channel._input_record(complete),
            'source_scalar_generator_error_per_second_per_input_norm': str(scalar),
            'relative_phase_box_difference_priced': False, 'reference_Gamma_family_priced': False,
            'continuous_curve_residual_priced': False}
