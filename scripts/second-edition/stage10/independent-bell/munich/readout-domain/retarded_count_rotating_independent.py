"""Independent clock and full-matrix checks for the detector-time chart."""
from fractions import Fraction as Q

import retarded_gate_common_phase_source as original

excitation, gaussian = original.excitation, original.excitation.gaussian
dipole, channel = original.dipole, original.channel


def require(value, reason):
    if not value:
        raise ValueError(reason)


def check_primitive(pulse, detector_time, flight, phase, report, *, bits=192):
    t, f, angle = map(Q, (detector_time, flight, phase))
    require(t >= f >= 0, 'original retarded gate clock')
    omega = Q(pulse['carrier_angular_frequency_per_second']); local = t-f
    h = gaussian._matrix(pulse['complete_static_H_per_second'])
    raising = gaussian._matrix(pulse['source_raising_operator_per_second'])
    scalar, error = gaussian._scalar({**pulse, 'phase_radians': str(angle+omega*f)}, local, bits, carrier=False)
    quiet = dict(h)
    for i, state in enumerate(dipole.STATES):
        if state.family == 'D2':
            original.field._add(quiet, {(i, i): dipole.ComplexRadical(-omega)})
    h = dict(quiet)
    for (i, j), value in raising.items():
        product = value*dipole.ComplexRadical(*scalar)
        original.field._add(h, {(i, j): product})
        original.field._add(h, {(j, i): product.conjugate()})
    loss = gaussian._matrix(pulse['complete_natural_R_per_second'])
    k = {key: -dipole.ComplexRadical(0, 1)*value for key, value in h.items()}
    original.field._add(k, loss, Q(-1, 2))
    require(gaussian._matrix(report['complete_K_per_second']) == k and
            gaussian._matrix(report['source_rotating_H_per_second']) == h and
            gaussian._matrix(report['source_rotating_static_H_per_second']) == quiet,
            'source detector-time frame H/K or sign')
    require(report['source_detector_seconds'] == str(t) and report['source_local_seconds'] == str(local) and
            report['fixed_drive_phase_in_detector_frame'] == str(angle+omega*f) and
            report['source_original_carrier_per_second'] == str(omega), 'source drive and unequal-flight phase')
    require(report['original_resolved_natural_jumps'] == pulse['original_physical_natural_jumps'] and
            Q(report['H_scalar_operator_error_upper_per_second']) == 2*error*gaussian._norm(raising, bits) and
            report['carrier_scalar_exponential_evaluated'] is False and
            report['coherent_port_and_loss_transfer_changed'] is False, 'full bath and source chart error')
    require(not gaussian._sum(k, dipole.matrix_adjoint(k), loss), 'same Hermitian CP identity')
    return True


def check_inlet_protocol(raw, relative_phase, report):
    g0 = Q(raw['source_gate_offsets_from_pump_end_seconds'][0]); flights = list(map(Q, raw['flight_seconds']))
    rows = report['local_source_flows']; pulses = raw['source_generated_zero_line_chart_pulses']
    require(len(rows) == len(flights) == len(pulses) == 2 and min(flights) >= 0 and g0 >= max(flights),
            'complete causal two-arm inlet')
    for side, row in enumerate(rows):
        phase = Q(0) if side == 0 else Q(relative_phase)
        require(row['side'] == side and row['source_local_interval_seconds'] == ['0', str(g0-flights[side])] and
                row['local_density_source'] == {**pulses[side], 'phase_radians': str(phase)} and
                row['local_to_detector_frame_angle_radians'] == str(
                    Q(pulses[side]['carrier_angular_frequency_per_second'])*flights[side]),
                'source pre-gate cut or local-to-detector join')
    require(report['initial_local_frames_are_identity'] is True and report['join_at_original_retarded_gate_cut'] is True and
            report['source_inlet_error_transported_once'] is True and report['quantum_time_queue_product_assumed'] is False,
            'source inlet scope')
    return True
