"""One checked preparation occurrence emits its next driven field carrier.

The numerical zero-phase pulse is a chart.  Its physical input/output line
frames, emission origin, all Ready faces and the old field/queue mother remain
source coordinates.  The clock coordinates stay fixed across this update.
"""
from fractions import Fraction as Q
from pathlib import Path
from itertools import product
from math import factorial
import hashlib
import json

import retarded_native_preparation_source as preparation
import gaussian_atomic_pulse_source as gaussian
import driven_gaussian_field_source as driven
import b_field_photon_source as field
import retarded_gaussian_bsm_source as retarded

atomic, full, dipole, channel, joint, local = preparation.atomic, preparation.full, preparation.dipole, preparation.channel, preparation.joint, preparation.local
SCHEMA = 'stage10-same-preparation-next-excitation-field-carrier/v1'
_PREPARATION_CHECK, _GAUSSIAN_CHECK, _DRIVEN_CHECK, _RETARDED_CHECK = preparation._CHECK, gaussian._CHECK, driven._CHECK, retarded._CHECK
_ISSUED, _MEMBERS = {}, {}


def _require(value, message):
    if not value: raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _freeze_terms(terms):
    return tuple((tuple(sorted(a.items())), tuple(sorted(b.items()))) for a, b in terms)


def _matrices(terms):
    return tuple((dict(a), dict(b)) for a, b in terms)


def _coimage_field_kernel(terms, bra, ket, bra_weight, ket_weight):
    result = {}
    for first_a, first_b in bra:
        for second_a, second_b in ket:
            for a, b in terms:
                left = dipole.matrix_product(dipole.matrix_product(first_a, a), dipole.matrix_adjoint(second_a))
                right = dipole.matrix_product(dipole.matrix_product(first_b, b), dipole.matrix_adjoint(second_b))
                field._add(result, driven.original._tensor(left, right), bra_weight*ket_weight)
    return result


def _kernel_price(old_error, positive_mass, bra, bra_error, ket, ket_error, bits):
    na, nb = driven._norm(bra, bits), driven._norm(ket, bits)
    amplitude_product = (na+bra_error)*(nb+ket_error)
    old = old_error*amplitude_product
    curve = (positive_mass+old_error)*(bra_error*nb+ket_error*na+bra_error*ket_error)
    return old+curve, old, curve, amplitude_product


def _common_line_law(pulses, optics):
    projector = preparation.frame._projector('D2'); groups = {}; counts = []
    for pulse in pulses:
        static = gaussian._matrix(pulse['complete_static_H_per_second']); loss = gaussian._matrix(pulse['complete_natural_R_per_second'])
        raising = gaussian._matrix(pulse['source_raising_operator_per_second']); rebuilt_loss = {}
        _require(not preparation.frame._commutator(projector, static) and not preparation.frame._commutator(projector, loss),
                 'the complete static Zeeman and natural loss must commute with the common D2 chart')
        _require(preparation.frame._commutator(projector, raising) == raising, 'every raw excitation edge must have D2 charge +1')
        for item in pulse['original_physical_natural_jumps']:
            operator = gaussian._matrix(item['normalized_natural_jump_operator']); group = tuple(item['group'])
            charge = -int(group[0] == 'D2')
            _require(preparation.frame._commutator(projector, operator) == {k: charge*v for k, v in operator.items() if charge*v},
                     'every original natural jump must have its full source line charge')
            _require(groups.setdefault(group, charge) == charge, 'each original port bath must preserve one line charge across both arms')
            field._add(rebuilt_loss, dipole.matrix_product(dipole.matrix_adjoint(operator), operator), Q(item['physical_amplitude_squared_per_second']))
        _require(rebuilt_loss == loss, 'all original natural bath jumps must reconstruct the complete R once')
        counts.append(len(pulse['original_physical_natural_jumps']))
    transfer = tuple(tuple(channel._complex_record(v) for v in row) for row in optics['generated_four_by_six_transfer'])
    joint.passive_transfer(transfer)
    frequencies = tuple(Q(p['carrier_angular_frequency_per_second']) for p in pulses)
    return {'schema': SCHEMA+'/source-derived-common-line-law', 'local_line_projector': 'P_D2',
        'complete_static_H_Z_R_and_all_raw_raising_edges_checked': True, 'complete_natural_jump_counts': counts,
        'original_resolved_bath_group_charges': [{'group': list(g), 'charge': q} for g, q in sorted(groups.items())],
        'all_four_port_and_six_loss_coordinates_keep_their_original_bath_charge': True,
        'full_two_leg_common_phase_word_law': 'F(phase+chi)=exp(i*n_D2*chi)*U_pair(chi)*F(phase)*U_pair(chi)^dag',
        'same_word_final_trace_law': 'on P_D2=0 input, trace(F rho F^dag) is independent of the common chi',
        'two_raw_carriers_equal': frequencies[0] == frequencies[1], 'true_two_leg_carrier_difference_per_second': str(frequencies[1]-frequencies[0]),
        'relative_phase_or_ground_Zeeman_beat_removed': False, 'a_common_chart_is_an_actual_clock_restart': False}


def _project_common_line_input(terms, old_error, mass, bits):
    gaussian._precision(bits); old_error, mass = map(full.nonnegative, (old_error, mass))
    moment = dipole.ComplexRadical(); projected = []
    for a, b in terms:
        pa = {k: v for k, v in a.items() if all(dipole.STATES[i].family != 'D2' for i in k)}
        pb = {k: v for k, v in b.items() if all(dipole.STATES[i].family != 'D2' for i in k)}
        tr = lambda matrix: sum((v for (i, j), v in matrix.items() if i == j), dipole.ComplexRadical())
        moment += tr(a)*tr(b)-tr(pa)*tr(pb); projected.append((pa, pb))
    _require(not moment.imag, 'the source coimage projector moment must be real; no centre positivity is assumed')
    centre, rounding = full.radical_midpoint(moment.real, bits)
    eta = min(mass, max(Q(0), centre+rounding+old_error))
    _, upper = driven._sqrt_interval(mass*eta, bits); gentle = min(2*mass, 2*upper)
    return tuple(projected), {'schema': SCHEMA+'/same-positive-mother-common-line-input-projection',
        'source_projector': '(I-P_D2) tensor (I-P_D2) tensor I_field_queue_time',
        'source_centre_projector_complement_moment': moment.serialize(), 'source_centre_moment_scalar_rounding': str(rounding),
        'whole_quantum_coimage_error_used_for_projector_moment': str(old_error), 'same_positive_joint_mother_mass_upper': str(mass),
        'true_joint_mother_projector_complement_mass_upper': str(eta), 'joint_mother_projection_trace_norm_upper': str(field._price_upper(gentle, bits)),
        'price_law': 'eta <= Tr((I-P) rho_coimage)+E; integral norm(mu-P mu P) <= 2*sqrt(M*eta)',
        'positive_source_mother_used': True, 'numeric_coimage_centre_assumed_positive': False,
        'an_arbitrary_quantum_marginal_error_lifted_to_fine_queue_TV': False,
        'ground_ION_and_D1_coordinates_and_true_ground_coherences_retained': True}


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
            (Path(__file__), *(Path(m.__file__) for m in (preparation, gaussian, driven, field, retarded, atomic, full, dipole, channel, joint, local)))}


def _excitation_step_coordinates(values):
    _require(type(values) in (tuple, list) and len(values) == 2, 'two fixed excitation phase-step coordinates required; a future phase table is not input')
    result = []
    for value in values:
        lo, hi = (tuple(map(full.exact, value)) if type(value) in (tuple, list) and len(value) == 2 else
                  (full.exact(value), full.exact(value)))
        _require(lo <= hi, 'ordered exact fixed excitation phase-step interval required')
        result.append({'phase_step_radians': list(map(str, (lo, hi))), 'centre': str((lo+hi)/2), 'radius': str((hi-lo)/2)})
    return result


def _primitive(owner, plan, shape, side, horizon):
    _require(type(owner) is atomic.MunichAtomicProgramme and type(plan) is dict and plan['raw_controls']['kind'] == 'excitation',
             'same-owned raw final excitation role required; H, R and target state are not input')
    phase = atomic._read_phase(plan['source_phase']); source = atomic.AtomicPhase.record(phase); programme = phase.programme()
    _require(source['parent'] == owner.record() and source['side'] == side and len(programme.tones) == 1 and
             programme.tones[0].name == 'excitation' and programme.tones[0].line == 'D2', 'the complete same-owner single D2 excitation tone is required')
    sigma, centre, horizon = full.exact(shape['sigma_squared_seconds']), full.exact(shape['centre_seconds']), full.exact(horizon)
    _require(sigma > 0 and 0 <= centre <= horizon and horizon > 0, 'the original Gaussian shape and positive certification horizon are required')
    quiet = field._source(owner, side); unit = Q(owner.record()['atomic_base']['seconds_per_unit'])
    raising = {k: v*(1/unit) for k, v in programme.excitations[0].items()}
    covariance = preparation._line_covariance(phase)
    return {'schema': SCHEMA+'/zero-common-line-chart', 'side': side, 'original_constant_excitation_controls': _copy(plan),
        'working_atomic_owner': owner.record(), 'sigma_squared_seconds': str(sigma), 'centre_seconds': str(centre),
        'duration_seconds': str(horizon), 'phase_radians': '0', 'zero_is_a_computational_common_line_chart': True,
        'carrier_angular_frequency_per_second': str(programme.tones[0].angular_frequency/unit),
        'source_raising_operator_per_second': channel._input_record(raising),
        'complete_static_H_per_second': quiet['full_H_per_second'], 'complete_natural_R_per_second': quiet['full_R_per_second'],
        'original_physical_natural_jumps': quiet['original_physical_natural_jumps'],
        'common_line_frame_covariance': covariance, 'Gaussian_horizon_is_physical_turnoff': False,
        'source_primitive_complete_H_R_and_jumps_computed': True}


def _source_H(raw, local_seconds, phase_angle, bits):
    pulse = {**raw, 'phase_radians': str(phase_angle)}
    scalar, error = gaussian._scalar(pulse, local_seconds, bits)
    raising = gaussian._matrix(raw['source_raising_operator_per_second'])
    drive = {k: v*dipole.ComplexRadical(*scalar) for k, v in raising.items()}
    h = gaussian._sum(gaussian._matrix(raw['complete_static_H_per_second']), drive, dipole.matrix_adjoint(drive))
    return h, 2*error*gaussian._norm(raising, bits)


def _line_frame(angle, matrix, bits):
    pairs = {}; radical = Q(0)
    for key, value in matrix.items():
        a, ea = full.radical_midpoint(value.real, bits); b, eb = full.radical_midpoint(value.imag, bits)
        pairs[key] = a, b; radical += ea+eb
    result, error = preparation._rotate_template(pairs, angle, bits)
    return {k: dipole.ComplexRadical(*v) for k, v in result.items()}, radical+error


def _pair_line_frame(angle, matrix, bits):
    pairs, error = {}, Q(0)
    for (row, column), value in matrix.items():
        a, ea = full.radical_midpoint(value.real, bits); b, eb = full.radical_midpoint(value.imag, bits)
        charge = (sum(int(dipole.STATES[i].family == 'D2') for i in divmod(row, full.DIMENSION))-
            sum(int(dipole.STATES[i].family == 'D2') for i in divmod(column, full.DIMENSION)))
        phase, scalar = gaussian._exponential(0, charge*angle, bits) if charge*angle else ((Q(1), Q(0)), Q(0))
        pairs[row, column] = field._product((a, b), phase)
        error += (ea+eb)*(abs(phase[0])+abs(phase[1]))+scalar*(abs(a)+abs(b)+ea+eb)
    pairs, rounding = preparation.exact._dyadic_state(pairs, bits)
    return {k: dipole.ComplexRadical(*v) for k, v in pairs.items()}, error+rounding


def _Gamma_chart_price(raw, clock, start, stop, bits):
    gamma = Q(clock['Gamma_numerical_centre']); lo, hi = map(Q, clock['angular_Gamma_enclosure_per_second'])
    delta = max(abs(gamma-lo), abs(hi-gamma)); upper = max(gamma, hi)
    a = gaussian._norm(gaussian._matrix(raw['source_raising_operator_per_second']), bits)/gamma
    fixed = (gaussian._norm(gaussian._matrix(raw['complete_static_H_per_second']), bits)+
             gaussian._norm(gaussian._matrix(raw['complete_natural_R_per_second']), bits)/2)/gamma+2*a
    omega = abs(Q(raw['carrier_angular_frequency_per_second'])/gamma)
    return field._price_upper(delta*((stop-start)*fixed+upper*omega*a*(stop*stop-start*start)), bits)


def _certify_chart(raw, clock, trial, coefficient_bits, phase_bits, envelope_order):
    gaussian._precision(coefficient_bits); gaussian._precision(phase_bits)
    _require(type(trial) is dict and set(trial) == {'source_interval_seconds', 'mode_bits', 'pieces'} and type(trial['pieces']) is list and
             type(envelope_order) is int and 0 <= envelope_order <= 16, 'complete untrusted chart operator interval and Gaussian budget required')
    start, stop = map(full.nonnegative, trial['source_interval_seconds']); gaussian._precision(trial['mode_bits'])
    _require(start <= stop <= Q(raw['duration_seconds']), 'the actual fixed-start operator interval must remain in its certified horizon')
    current = {(i, i): (Q(1), Q(0)) for i in range(full.DIMENSION)}; elapsed = start; error = Q(0); prices = []
    parts = gaussian._parts(raw, coefficient_bits)
    for piece in trial['pieces']:
        width, current, local_price, paid = gaussian._piece_integer(raw, piece, current, elapsed, trial['mode_bits'], phase_bits, envelope_order, parts)
        _require(elapsed+width <= stop, 'chart operator curve cannot cross its actual source interval')
        paid['uniform_rotating_operator_error_upper'] = str(error+Q(paid['uniform_rotating_curve_error_from_piece_input']))
        paid['previous_rotating_endpoint_error'] = str(error)
        error += local_price; elapsed += width; prices.append(paid)
    _require(elapsed == stop, 'the whole genuine I-at-s operator interval must be covered')
    endpoint, frame_price = (gaussian._restore(raw, current, start, stop, phase_bits) if start < stop else
                             ({(i, i): dipole.ComplexRadical(1) for i in range(full.DIMENSION)}, Q(0)))
    gamma_price = _Gamma_chart_price(raw, clock, start, stop, coefficient_bits)
    return {'schema': SCHEMA+'/fixed-start-chart-operator-certificate', 'chart_raw_source': _copy(raw), 'reference_clock': _copy(clock),
        'untrusted_trial': _copy(trial), 'source_interval_seconds': list(map(str, (start, stop))),
        'full33_operator': channel._input_record(endpoint), 'rotating_operator_error': str(error),
        'frame_endpoint_scalar_price': str(frame_price), 'Gamma_math_operator_price': str(gamma_price),
        'operator_norm_error_upper': str(error+frame_price+gamma_price), 'complete_piece_prices': prices,
        'coefficient_bits': coefficient_bits, 'phase_bits': phase_bits, 'envelope_order': envelope_order,
        'initial_operator': 'I at s', 'physical_optical_restart_inferred_from_chart_zero': False,
        'reference_Gamma_math_price_is_hardware_calibration': False}


def _retarded_images(raw, primitives, matrix):
    matrix = joint._matrix(matrix)
    transfer = tuple(tuple(channel._complex_record(v) for v in row) for row in raw['working_common_optical_source']['generated_four_by_six_transfer'])
    _, _, loss_gram = joint.passive_transfer(transfer)
    beta = tuple(Q(rate)/Q(raw['working_atomic_owner']['atomic_base']['seconds_per_unit']) for rate in raw['working_common_optical_source']['background_rates'])
    pending, independent, scalar = {}, {}, Q(0)
    for side, primitive in enumerate(primitives):
        k = gaussian._matrix(primitive['complete_K_per_second'])
        image = gaussian._sum(joint._operator_left(matrix, side, k), joint._operator_right(matrix, side, dipole.matrix_adjoint(k)))
        field._add(pending, image); field._add(independent, image)
        scalar += 2*Q(primitive['H_scalar_operator_error_upper_per_second'])
        for jump in primitive['original_resolved_natural_jumps']:
            operator = gaussian._matrix(jump['normalized_natural_jump_operator'])
            rate = Q(jump['physical_amplitude_squared_per_second'])
            field._add(independent, joint._operator_right(joint._operator_left(matrix, side, operator), side, dipole.matrix_adjoint(operator)), rate)
    groups = retarded._closed_groups({'physical_legs': raw['source_generated_zero_line_chart_pulses']})
    jumps = [{}, {}, {}, {}]
    for _, rate, modes in groups:
        for mu, first in modes:
            for nu, second in modes:
                image = retarded._recycle(matrix, first, second)
                if loss_gram[nu][mu]: field._add(pending, image, rate*loss_gram[nu][mu])
                for port in range(4):
                    coefficient = transfer[port][mu]*transfer[port][nu].conjugate()*rate
                    if coefficient: field._add(jumps[port], image, coefficient)
    for port, rate in enumerate(beta): field._add(jumps[port], matrix, rate)
    field._add(pending, matrix, -sum(beta, Q(0)))
    complete = dict(pending)
    for jump in jumps: field._add(complete, jump)
    _require(complete == independent, 'forgetting all original ports must exactly recover both complete local source generators')
    return pending, jumps, complete, independent, scalar


def _excitation_fibre(raw, point, receipt, face, elapsed, initial):
    parent = raw['preparation_source']; total = sum(map(Q, parent['source_expiry_free_preparation_support']['physical_pump_durations_seconds']), Q(0))
    elapsed = full.nonnegative(elapsed); origin = Q(initial['physical_clock_seconds'])
    expiry = Q(parent['source_expiry_free_preparation_support']['earliest_possible_recent_expiry_seconds'])
    _require(origin+elapsed < expiry, 'the whole next-field source clock must remain before the original recent-count expiry')
    period = Q(parent['source_poll_period_seconds']); rules = {r['name']: r for r in parent['raw_PC_rules']}
    high_start = Q(initial['source_high_poll_seconds']); state, changed = preparation._pc_steps(rules,
        parent['source_expiry_free_preparation_support']['source_all_Ready_face_PC_updates'][face]['original_high_poll_PC_state'], int((total+elapsed)//period))
    PC_origin = Q(initial['phase_started_at_seconds'])
    if changed is not None and parent['original_PC_phase_policy'] == 'restart_on_stage_change': PC_origin = high_start+changed*period
    old = raw['original_prior_driven_field_source']; ages, angles = [], []
    policy = raw['fixed_pump_clock_member']['restart_policy']
    for side in (0, 1):
        old_origin = Q(old['emission_origins_seconds'][side])
        if policy == 'continuous': age_offset = origin-old_origin
        elif policy == 'restart_on_preparation': age_offset = total-preparation._pump_prefix(parent['original_source_local_plans'], side, 2)
        elif policy == 'restart_on_pump': age_offset = Q(0)
        else:
            baseline = old_origin-Q(parent['source_original_Ready_PC_phase_origins_seconds'][face])
            age_offset = origin-PC_origin-baseline
        base_phase = Q(old['Gaussian_source_legs'][side]['phase_radians']); step = Q(point['two_side_fixed_excitation_phase_steps'][side]['centre'])
        omega = Q(raw['source_generated_zero_line_chart_pulses'][side]['carrier_angular_frequency_per_second'])
        ages.append(str(age_offset+elapsed)); angles.append(str(base_phase+step-omega*age_offset))
    return {'schema': SCHEMA+'/same-source-excitation-time-phase-fibre', 'source_receipt_seconds': str(full.exact(receipt)),
        'source_Ready_face_index': face, 'source_excitation_origin_seconds': str(origin), 'physical_atom_seconds': str(origin+elapsed),
        'elapsed_after_excitation_seconds': str(elapsed), 'source_original_PC_state': state, 'phase_started_at_seconds': str(PC_origin),
        'field_started_at_seconds': str(origin), 'two_side_optical_phase_arguments_seconds': ages, 'two_side_common_line_chart_angles': angles,
        'same_history_complete_clock_digest': point['same_history_complete_clock_digest'],
        'field_started_at_proves_optical_restart': False, 'numerical_origin_selected_as_unique_actual_time': False}


def _excitation_clock_cuts(parent, policy, face, start, stop):
    start, stop = map(full.nonnegative, (start, stop)); _require(start <= stop, 'ordered local field interval required')
    cuts = {start, stop}
    if policy == 'source_PC_policy' and parent['original_PC_phase_policy'] == 'restart_on_stage_change':
        total = sum(map(Q, parent['source_expiry_free_preparation_support']['physical_pump_durations_seconds']), Q(0))
        period = Q(parent['source_poll_period_seconds']); rules = {r['name']: r for r in parent['raw_PC_rules']}
        initial = parent['source_expiry_free_preparation_support']['source_all_Ready_face_PC_updates'][face]['original_high_poll_PC_state']
        for k in range(int((total+start)//period)+1, int((total+stop)//period)+1):
            when = k*period-total
            if when < stop and preparation._pc_steps(rules, initial, k)[0]['stage'] != preparation._pc_steps(rules, initial, k-1)[0]['stage']: cuts.add(when)
    return sorted(cuts)


class ExcitationClockMember:
    def __init__(self, *args, **kwargs):
        raise ValueError('an excitation clock member is emitted by the same preparation/clock carrier')

    def record(self):
        _CHECK()
        _require(type(self) is ExcitationClockMember and set(vars(self)) == {'_owner', '_value', '_seal'} and
                 _MEMBERS.get(id(self)) == (self._owner, self._seal) and _digest(self._value) == self._seal and
                 self._value['source_bindings'] == _bindings() and self._owner.record()['source_digest'] == self._value['source_family_digest'],
                 'the fixed same-cohort excitation coordinates changed')
        return _copy(self._value)


class RetardedPreparedExcitationFieldSource:
    def __init__(self, source, two_pump_report, clock_member):
        _CHECK()
        _require(type(source) is preparation.RetardedNativePreparationSource and type(clock_member) is preparation.RawPumpClockMember,
                 'the complete same-occurrence preparation source and its fixed clock member are required; rho is not input')
        inlet = preparation.RetardedNativePreparationSource.source_tensors(source, two_pump_report, clock_member=clock_member)
        raw = source.record(); point = source._clock_member(clock_member)
        _require(all(len(side) == 3 and side[2]['raw_controls']['kind'] == 'excitation' for side in raw['source_generated_local_plans']),
                 'both same-source optional index-two excitation roles must actually exist')
        original = source._native._coimage._source._value['retarded_detector_law']['complete_driven_field_source']
        _require(original['working_atomic_owner'] == raw['working_atomic_owner'] and
                 original['working_common_optical_source'] == raw['working_common_optical_source'], 'the old field and new excitation have the same atomic/optical lambda')
        old_origins = tuple(map(Q, original['emission_origins_seconds'])); gate = tuple(map(Q, original['gate_seconds']))
        _require(old_origins[0] == old_origins[1], 'this same-boundary two-pump carrier preserves the original common activation geometry')
        relative_gate = gate[0]-old_origins[0], gate[1]-old_origins[0]
        _require(relative_gate[1]-relative_gate[0] == Q('3/25000000') and relative_gate[0] >= max(map(Q, original['flight_seconds'])),
                 'the original 120ns gate and pump-photon causal restriction must survive the same source shift')
        owner = atomic.MunichAtomicProgramme.from_record(raw['working_atomic_owner'])
        horizon = max(Q(p['duration_seconds']) for p in original['Gaussian_source_legs'])
        horizon = max(horizon, relative_gate[1])
        primitives = tuple(_primitive(owner, raw['source_generated_local_plans'][side][2], original['Gaussian_source_legs'][side], side, horizon) for side in (0, 1))
        transfer = tuple(tuple(channel._complex_record(v) for v in row) for row in raw['working_common_optical_source']['generated_four_by_six_transfer'])
        _, _, loss = joint.passive_transfer(transfer)
        self._source, self._clock_member = source, clock_member
        self._report_json = channel._canonical(two_pump_report)
        self._terms = _freeze_terms(inlet['tensor_terms']); self._banks = ([], [])
        self._value = {'schema': SCHEMA, 'preparation_source': raw, 'checked_preparation_report_digest': _digest(two_pump_report),
            'fixed_pump_clock_member': point, 'source_preparation_generation': 1,
            'whole_preparation_quantum_error_once': str(inlet['whole_upstream_trace_norm_error']),
            'same_positive_CEM_mother_mass_upper': str(inlet['same_positive_CEM_mass_upper']),
            'whole_original_time_field_queue_mother': inlet['retained_time_state_mother'],
            'pump_end_time_family_seconds': list(map(str, inlet['source_preparation_end_time_family_seconds'])),
            'source_generated_zero_line_chart_pulses': list(primitives), 'reference_clock': raw['reference_clock'],
            'working_atomic_owner': raw['working_atomic_owner'], 'working_common_optical_source': raw['working_common_optical_source'],
            'working_aperture_source': raw['working_aperture_source'], 'original_prior_driven_field_source': original,
            'flight_seconds': original['flight_seconds'], 'source_gate_offsets_from_pump_end_seconds': list(map(str, relative_gate)),
            'loss_environment_gram': [[v.serialize() for v in row] for row in loss],
            'loss_field_trace_rule': 'contract original six input-mode coordinates with their source Gram I-T^dag*T',
            'old_noncompact_Gaussian_drive_retained': True, 'old_field_or_queue_replaced_by_vacuum': False,
            'time_quantum_mother_replaced_by_product': False, 'actual_continuous_Gamma_calibration_domain_generated': False,
            'source_scope': 'generation-one next-field action of the supplied fixed atomic line/physical-clock model and its fixed clock family',
            'actual_hardware_member_asserted': False, 'source_bindings': _bindings()}
        self._seal = _digest(self._value); _ISSUED[id(self)] = source, clock_member, self._seal, self._terms

    def record(self):
        _CHECK()
        _require(type(self) is RetardedPreparedExcitationFieldSource and set(vars(self)) ==
                 {'_source', '_clock_member', '_report_json', '_terms', '_banks', '_value', '_seal'} and
                 _ISSUED.get(id(self)) == (self._source, self._clock_member, self._seal, self._terms) and
                 _digest(self._value) == self._seal and self._value['source_bindings'] == _bindings() and
                 self._source.record() == self._value['preparation_source'] and self._source._clock_member(self._clock_member) == self._value['fixed_pump_clock_member'] and
                 _digest(json.loads(self._report_json)) == self._value['checked_preparation_report_digest'],
                 'the same preparation event, complete mother or physical source changed')
        return {**_copy(self._value), 'source_digest': self._seal}

    def excitation_member(self, two_side_phase_steps):
        raw = self.record(); steps = _excitation_step_coordinates(two_side_phase_steps)
        value = {'schema': SCHEMA+'/fixed-excitation-clock-member', 'source_family_digest': raw['source_digest'],
                 'fixed_pump_clock_member': raw['fixed_pump_clock_member'], 'two_side_fixed_excitation_phase_steps': steps,
                 'same_history_complete_clock_digest': _digest({'fixed_pump_clock_member': raw['fixed_pump_clock_member']['same_history_raw_lambda_clock_digest'], 'excitation_steps': steps}),
                 'source_bindings': _bindings(), 'phase_steps_rechosen_per_record': False}
        result = object.__new__(ExcitationClockMember); result._owner, result._value, result._seal = self, value, _digest(value)
        _MEMBERS[id(result)] = self, result._seal
        return result

    def _member(self, member):
        _require(type(member) is ExcitationClockMember and member._owner is self, 'an explicit fixed member of this same excitation clock family is required')
        return member.record()

    def time_phase_fibre(self, receipt_seconds, Ready_face_index, elapsed_after_excitation, member):
        raw = self.record(); point = self._member(member)
        parent = raw['preparation_source']; total = sum(map(Q, parent['source_expiry_free_preparation_support']['physical_pump_durations_seconds']), Q(0))
        initial = self._source.pc_fibre(receipt_seconds, Ready_face_index, total)
        return _excitation_fibre(raw, point, receipt_seconds, Ready_face_index, elapsed_after_excitation, initial)

    def primitive_fibre(self, side, receipt_seconds, Ready_face_index, elapsed_after_excitation, member, *, bits=192):
        raw = self.record(); point = self._member(member); gaussian._precision(bits)
        _require(type(side) is int and side in (0, 1), 'the original excitation leg is required')
        fibre = self.time_phase_fibre(receipt_seconds, Ready_face_index, elapsed_after_excitation, member)
        elapsed = full.nonnegative(elapsed_after_excitation); pulse = raw['source_generated_zero_line_chart_pulses'][side]
        h, error = _source_H(pulse, elapsed, Q(fibre['two_side_common_line_chart_angles'][side]), bits)
        old = raw['original_prior_driven_field_source']; old_local = Q(fibre['physical_atom_seconds'])-Q(old['emission_origins_seconds'][side])
        old_h, old_error = _source_H(old['Gaussian_source_legs'][side], old_local, Q(old['Gaussian_source_legs'][side]['phase_radians']), bits)
        old_static = gaussian._matrix(old['Gaussian_source_legs'][side]['complete_static_H_per_second'])
        h = gaussian._sum(h, old_h, {k: -v for k, v in old_static.items()}); error += old_error
        loss = gaussian._matrix(pulse['complete_natural_R_per_second'])
        k = gaussian._sum({key: value*dipole.ComplexRadical(0, -1) for key, value in h.items()},
                         {key: -value*Q(1, 2) for key, value in loss.items()})
        _require(not gaussian._sum(k, dipole.matrix_adjoint(k), loss), 'the complete actual source must retain K+Kadj+R=0')
        phase_radius = Q(point['two_side_fixed_excitation_phase_steps'][side]['radius'])
        return {'schema': SCHEMA+'/actual-excitation-primitive-fibre', 'source_carrier_digest': raw['source_digest'],
            'source_time_phase_fibre': fibre, 'source_side': side, 'complete_H_per_second': channel._input_record(h),
            'complete_K_per_second': channel._input_record(k), 'complete_R_per_second': pulse['complete_natural_R_per_second'],
            'original_resolved_natural_jumps': pulse['original_physical_natural_jumps'],
            'H_scalar_operator_error_upper_per_second': str(field._price_upper(error, bits)),
            'fixed_excitation_phase_box_H_difference_upper_per_second': str(2*min(Q(2), phase_radius)*gaussian._norm(gaussian._matrix(pulse['source_raising_operator_per_second']), bits)),
            'prior_noncompact_Gaussian_drive_evaluated_without_turnoff': True, 'complete_K_loss_identity_checked': True,
            'reference_physical_clock_model_used': True, 'actual_continuous_Gamma_calibration_asserted': False}

    def retarded_generator(self, detector_seconds, receipt_seconds, Ready_face_index, member, matrix, *, bits=192):
        raw = self.record(); gaussian._precision(bits); self._member(member); matrix = joint._matrix(matrix)
        origin = Q(self.time_phase_fibre(receipt_seconds, Ready_face_index, 0, member)['source_excitation_origin_seconds'])
        detector = full.nonnegative(detector_seconds); g0, g1 = (origin+Q(t) for t in raw['source_gate_offsets_from_pump_end_seconds'])
        _require(g0 <= detector <= g1, 'the same source-origin restriction of the original full 120ns gate is required')
        primitives = []
        for side in (0, 1):
            local_time = detector-Q(raw['flight_seconds'][side])-origin
            primitives.append(self.primitive_fibre(side, receipt_seconds, Ready_face_index, local_time, member, bits=bits))
        pending, jumps, complete, independent, scalar = _retarded_images(raw, primitives, matrix)
        return {'schema': SCHEMA+'/same-field-retarded-generator-image', 'source_carrier_digest': raw['source_digest'],
            'same_history_complete_clock_digest': self._member(member)['same_history_complete_clock_digest'],
            'physical_detector_seconds': str(detector), 'source_gate_seconds': list(map(str, (g0, g1))),
            'two_retarded_local_seconds': [str(detector-Q(f)-origin) for f in raw['flight_seconds']],
            'no_arrival_generator_image_per_second': channel._input_record(pending),
            'four_physical_port_jump_images_per_second': [channel._input_record(j) for j in jumps],
            'forget_arrival_complete_generator_image_per_second': channel._input_record(complete),
            'independently_computed_two_local_full_generator_image_per_second': channel._input_record(independent),
            'source_scalar_generator_error_per_second_per_input_norm': str(field._price_upper(scalar, bits)),
            'whole_original_mother_retained': raw['whole_original_time_field_queue_mother'],
            'original_background_added_once': True, 'independent_baths_recovered_when_all_ports_are_forgotten': True,
            'physical_atom_at_detector_time_claimed': False}

    def chart_operator_certificate(self, side, trial, *, coefficient_bits=192, phase_bits=192, envelope_order=8):
        raw = self.record(); _require(type(side) is int and side in (0, 1), 'the original source leg is required')
        return {**_certify_chart(raw['source_generated_zero_line_chart_pulses'][side], raw['reference_clock'], trial, coefficient_bits, phase_bits, envelope_order),
                'source_carrier_digest': raw['source_digest'], 'source_side': side, 'source_bindings': _bindings()}

    def verify_chart_operator(self, report):
        raw = self.record(); _require(type(report) is dict and report.get('schema') == SCHEMA+'/fixed-start-chart-operator-certificate' and
            report.get('source_carrier_digest') == raw['source_digest'], 'the same actual-source chart operator certificate is required')
        expected = self.chart_operator_certificate(report['source_side'], report['untrusted_trial'],
            coefficient_bits=report['coefficient_bits'], phase_bits=report['phase_bits'], envelope_order=report['envelope_order'])
        _require(expected == report, 'the chart raw source, full operator or paid price changed')
        return True

    def install_operator_certificate(self, report):
        self.verify_chart_operator(report); side = report['source_side']; interval = tuple(report['source_interval_seconds'])
        _require(all(tuple(r['source_interval_seconds']) != interval for r in self._banks[side]), 'a genuine fixed-start family cannot be replaced or duplicated')
        self._banks[side].append(_copy(report))

    def _chart_operator(self, side, start, stop, bits):
        raw = self.record(); pulse = raw['source_generated_zero_line_chart_pulses'][side]
        if start == stop: return {(i, i): dipole.ComplexRadical(1) for i in range(full.DIMENSION)}, Q(0)
        matches = [r for r in self._banks[side] if Q(r['source_interval_seconds'][0]) == start and stop <= Q(r['source_interval_seconds'][1])]
        _require(matches, 'a verified genuine I-at-s chart family must cover this source interval; no inverse or future vacuum is supplied')
        report = min(matches, key=lambda r: Q(r['source_interval_seconds'][1])-start)
        self.verify_chart_operator(report)
        return driven._eval(pulse, driven._freeze_report(report), start, stop, bits)

    def _operator_fibre(self, side, start, stop, receipt, face, member, bits):
        raw = self.record(); point = self._member(member); pulse = raw['source_generated_zero_line_chart_pulses'][side]
        _require(0 <= start <= stop <= Q(pulse['duration_seconds']), 'an actual local source interval inside its certified horizon is required')
        if start == stop: return {(i, i): dipole.ComplexRadical(1) for i in range(full.DIMENSION)}, Q(0)
        cuts = _excitation_clock_cuts(raw['preparation_source'], raw['fixed_pump_clock_member']['restart_policy'], face, start, stop)
        if len(cuts) > 2:
            current = {(i, i): dipole.ComplexRadical(1) for i in range(full.DIMENSION)}; price = Q(0)
            for left, right in zip(cuts, cuts[1:]):
                step, error = self._operator_fibre(side, left, right, receipt, face, member, bits)
                current, price = driven._multiply(step, error, current, price, bits)
            return current, price
        a = self.time_phase_fibre(receipt, face, start, member)
        interior = self.time_phase_fibre(receipt, face, (start+stop)/2, member)
        angle = Q(interior['two_side_common_line_chart_angles'][side])
        centre, error = self._chart_operator(side, start, stop, bits)
        centre, scalar = _line_frame(angle, centre, bits)
        radius = Q(point['two_side_fixed_excitation_phase_steps'][side]['radius'])
        clock = raw['reference_clock']; gamma = Q(clock['Gamma_numerical_centre'])
        offset = Q(interior['two_side_optical_phase_arguments_seconds'][side])-(start+stop)/2
        radius += abs(Q(pulse['carrier_angular_frequency_per_second'])/gamma)*Q(clock['Gamma_numerical_error'])*abs(offset)
        source_phase = min(Q(2), radius)*2*driven._norm(centre, bits)
        old = raw['original_prior_driven_field_source']; old_pulse = self._source._native._record_source._source._measure._certificate._source._law._field._pulses[side]
        after = Q(a['physical_atom_seconds'])-Q(old['emission_origins_seconds'][side])
        tail = gaussian.GaussianAtomicPulseSource.field_off_tail_price(old_pulse, after, bits=bits)
        ratio = max(gamma, Q(clock['angular_Gamma_enclosure_per_second'][1]))/gamma
        old_field_price = ratio*Q(tail['no_jump_operator_Duhamel_price_upper'])
        return centre, error+scalar+source_phase+old_field_price

    def _word_parts(self, word, observation_after_excitation, receipt_seconds, Ready_face_index, member, bits):
        raw = self.record(); gaussian._precision(bits); self._member(member)
        elapsed = full.nonnegative(observation_after_excitation); fibre = self.time_phase_fibre(receipt_seconds, Ready_face_index, elapsed, member)
        origin = Q(fibre['source_excitation_origin_seconds']); observation = origin+elapsed
        groups = {tuple(j['group']) for pulse in raw['source_generated_zero_line_chart_pulses'] for j in pulse['original_physical_natural_jumps']}
        _require(type(word) is list and all(type(e) is dict and set(e) == {'group', 'mode', 'arrival_seconds'} and
            type(e['group']) is list and tuple(e['group']) in groups and type(e['mode']) is list and len(e['mode']) == 2 and
            e['mode'][0] in ('port', 'loss') and type(e['mode'][1]) is int and e['mode'][1] in range(4 if e['mode'][0] == 'port' else 6)
            for e in word), 'the complete source natural-group/four-port/loss photon word is required')
        for entry in word: full.nonnegative(entry['arrival_seconds'])
        branches, total, price = [], {}, Q(0)
        jump_raw = {'working_common_optical_source': raw['working_common_optical_source'], 'reference_clock': raw['reference_clock']}
        for assignment in product((0, 1), repeat=len(word)):
            if any(full.exact(e['arrival_seconds'])-Q(raw['flight_seconds'][s]) < origin or
                   full.exact(e['arrival_seconds'])-Q(raw['flight_seconds'][s]) > observation or
                   (e['mode'][0] == 'loss' and e['mode'][1]//3 != s) for e, s in zip(word, assignment)): continue
            arms = []
            for side in (0, 1):
                entries = sorted([(full.exact(e['arrival_seconds'])-Q(raw['flight_seconds'][side])-origin, e)
                                  for e, s in zip(word, assignment) if s == side], key=lambda item: item[0])
                matrix = {(i, i): dipole.ComplexRadical(1) for i in range(full.DIMENSION)}; error = Q(0); before = Q(0)
                for time, entry in entries:
                    u, eu = self._operator_fibre(side, before, time, receipt_seconds, Ready_face_index, member, bits)
                    jump, ej, _ = driven._jump(jump_raw, raw['source_generated_zero_line_chart_pulses'][side]['original_physical_natural_jumps'],
                                               side, tuple(entry['group']), tuple(entry['mode']), bits)
                    matrix, error = driven._multiply(u, eu, matrix, error, bits)
                    matrix, error = driven._multiply(jump, ej, matrix, error, bits); before = time
                u, eu = self._operator_fibre(side, before, elapsed, receipt_seconds, Ready_face_index, member, bits)
                arms.append(driven._multiply(u, eu, matrix, error, bits))
            (a, ea), (b, eb) = arms; field._add(total, driven.original._tensor(a, b)); price += ea*driven._norm(b, bits)+eb*driven._norm(a, bits)+ea*eb
            branches.append((a, b))
        low, high = driven._sqrt_interval(Q(1, factorial(len(word))), bits); weight = (low+high)/2
        price = high*price+(high-low)/2*driven._norm(total, bits)
        return raw, fibre, tuple(branches), weight, {k: v*weight for k, v in total.items()}, field._price_upper(price, bits)

    def field_amplitude(self, word, observation_after_excitation, receipt_seconds, Ready_face_index, member, *, bits=192):
        raw, fibre, branches, weight, matrix, price = self._word_parts(word, observation_after_excitation, receipt_seconds, Ready_face_index, member, bits)
        return {'schema': SCHEMA+'/same-time-fibre-field-amplitude', 'source_carrier_digest': raw['source_digest'],
            'source_time_phase_fibre': fibre, 'photon_word': _copy(word), 'full_pair_operator': channel._input_record(matrix),
            'operator_error_upper': str(price), 'source_arm_assignments': len(branches),
            'source_symmetric_product_wavefunction_factor_squared': str(Q(1, factorial(len(word)))),
            'all_matter_coordinates_number_and_time_coherences_preserved': True,
            'source_prior_complete_mother': raw['whole_original_time_field_queue_mother'],
            'loss_environment_gram': raw['loss_environment_gram'],
            'incoming_time_quantum_density_factorized': False, 'field_density_integrated_over_the_mother': False}

    def common_phase_word_chart(self, word, observation_after_excitation, receipt_seconds, Ready_face_index, member, *, bits=192):
        report = self.field_amplitude(word, observation_after_excitation, receipt_seconds, Ready_face_index, member, bits=bits)
        raw = self.record(); law = _common_line_law(raw['source_generated_zero_line_chart_pulses'], raw['working_common_optical_source'])
        angle = Q(report['source_time_phase_fibre']['two_side_common_line_chart_angles'][0])
        matrix = channel._read_input(report['full_pair_operator'], joint.DIMENSION)
        matrix, rotation = _pair_line_frame(-angle, matrix, bits)
        number = sum(entry['group'][0] == 'D2' for entry in word)
        phase, scalar = gaussian._exponential(0, -number*angle, bits) if number*angle else ((Q(1), Q(0)), Q(0))
        price = Q(report['operator_error_upper'])+rotation+scalar*driven._norm(matrix, bits)
        return {'schema': SCHEMA+'/same-source-common-line-word-chart', 'source_carrier_digest': raw['source_digest'],
            'same_history_complete_clock_digest': self._member(member)['same_history_complete_clock_digest'],
            'source_time_phase_fibre': report['source_time_phase_fibre'], 'photon_word': _copy(word),
            'full_pair_chart_operator': channel._input_record({k: v*dipole.ComplexRadical(*phase) for k, v in matrix.items()}),
            'operator_error_upper': str(field._price_upper(price, bits)), 'original_D2_photon_number': number,
            'source_derived_common_line_law': law, 'source_carrier_angle': str(angle),
            'the_same_source_chart_changes_physical_clock_or_member': False,
            'complete_relative_two_leg_phase_kept': True, 'old_noncompact_drive_price_retained': True}

    def field_state(self, bra_word, ket_word, observation_after_excitation, receipt_seconds, Ready_face_index, member, *, bits=192):
        raw, fibre, left, wa, a, ea = self._word_parts(bra_word, observation_after_excitation, receipt_seconds, Ready_face_index, member, bits)
        other, other_fibre, right, wb, b, eb = self._word_parts(ket_word, observation_after_excitation, receipt_seconds, Ready_face_index, member, bits)
        _require(raw == other and fibre == other_fibre, 'bra and ket must belong to the same source occurrence and time/clock fibre')
        state = _coimage_field_kernel(_matrices(self._terms), left, right, wa, wb)
        error, old, curve, amplitude_product = _kernel_price(Q(raw['whole_preparation_quantum_error_once']),
            Q(raw['same_positive_CEM_mother_mass_upper']), a, ea, b, eb, bits)
        return {'schema': SCHEMA+'/source-quantum-coimage-field-time-density', 'source_carrier_digest': raw['source_digest'],
            'checked_preparation_report_digest': raw['checked_preparation_report_digest'],
            'same_history_complete_clock_digest': self._member(member)['same_history_complete_clock_digest'],
            'source_time_phase_fibre': fibre, 'bra_photon_word': _copy(bra_word), 'ket_photon_word': _copy(ket_word),
            'complete_matter_field_kernel': channel._input_record(state), 'trace_norm_kernel_error': str(field._price_upper(error, bits)),
            'whole_prefix_error_times_point_amplitude_product': str(field._price_upper(old, bits)),
            'finite_field_curve_price_on_source_coimage': str(field._price_upper(curve, bits)),
            'point_amplitude_operator_norm_product_upper': str(field._price_upper(amplitude_product, bits)),
            'time_density_degree': [len(bra_word), len(ket_word)], 'all_matter_coordinates_number_and_time_coherences_preserved': True,
            'source_prior_complete_mother': raw['whole_original_time_field_queue_mother'],
            'loss_environment_gram': raw['loss_environment_gram'],
            'kernel_scope': 'the chosen actual field-action restriction applied to the entire checked quantum coimage',
            'kernel_is_conditional_time_mother_density': False, 'kernel_is_integrated_joint_time_queue_density': False,
            'incoming_time_quantum_density_factorized': False, 'point_kernel_is_integrated_TNI_instrument': False,
            'scalar_bits': bits, 'source_bindings': _bindings(), 'controller_advance': False}

    def verify_field_state(self, report, member):
        raw = self.record(); self._member(member)
        _require(type(report) is dict and report.get('schema') == SCHEMA+'/source-quantum-coimage-field-time-density' and
                 report.get('source_carrier_digest') == raw['source_digest'], 'the same source quantum-coimage field kernel is required')
        fibre = report['source_time_phase_fibre']
        expected = self.field_state(report['bra_photon_word'], report['ket_photon_word'], fibre['elapsed_after_excitation_seconds'],
            fibre['source_receipt_seconds'], fibre['source_Ready_face_index'], member, bits=report['scalar_bits'])
        _require(expected == report, 'source tensor coimage, field words, common frame or paid kernel price changed')
        return True

    def source_tensors(self, member):
        raw = self.record(); point = self._member(member)
        return {'source_record': raw, 'tensor_terms': _matrices(self._terms),
            'whole_upstream_trace_norm_error': Q(raw['whole_preparation_quantum_error_once']),
            'source_centre_trace_norm_upper': Q(raw['same_positive_CEM_mother_mass_upper'])+Q(raw['whole_preparation_quantum_error_once']),
            'same_positive_CEM_mass_upper': Q(raw['same_positive_CEM_mother_mass_upper']),
            'whole_original_time_field_queue_mother': _copy(raw['whole_original_time_field_queue_mother']),
            'source_preparation_end_time_family_seconds': tuple(map(Q, raw['pump_end_time_family_seconds'])),
            'fixed_same_history_complete_clock_member': point, 'source_owned_retarded_generator': self,
            'pre_gate_unobserved_GKSL_coimage_computed': False, 'fine_queue_TV_inferred_from_quantum_price': False}

    def joint_common_line_input_projection(self, member, *, bits=192):
        raw = self.record(); point = self._member(member)
        terms, price = _project_common_line_input(_matrices(self._terms), Q(raw['whole_preparation_quantum_error_once']),
            Q(raw['same_positive_CEM_mother_mass_upper']), bits)
        return {'schema': SCHEMA+'/source-issued-joint-input-projection', 'source_carrier_digest': raw['source_digest'],
            'same_history_complete_clock_digest': point['same_history_complete_clock_digest'],
            'projected_source_tensor_terms': terms, 'source_derived_projection_price': price,
            'projected_quantum_coimage_error': raw['whole_preparation_quantum_error_once'],
            'projection_is_a_new_support_premise': False, 'whole_original_joint_mother': _copy(raw['whole_original_time_field_queue_mother'])}

    def observable_common_phase_square(self, member, *, bits=192):
        raw = self.record(); point = self._member(member)
        law = _common_line_law(raw['source_generated_zero_line_chart_pulses'], raw['working_common_optical_source'])
        projection = self.joint_common_line_input_projection(member, bits=bits)['source_derived_projection_price']
        parent = raw['preparation_source']; original = raw['original_prior_driven_field_source']
        same_age = original['emission_origins_seconds'][0] == original['emission_origins_seconds'][1] and \
            preparation._pump_prefix(parent['original_source_local_plans'], 0, 2) == preparation._pump_prefix(parent['original_source_local_plans'], 1, 2)
        return {'schema': SCHEMA+'/source-issued-observable-common-phase-square', 'source_carrier_digest': raw['source_digest'],
            'same_history_complete_clock_digest': point['same_history_complete_clock_digest'], 'same_complete_source_line_law': law,
            'same_positive_joint_mother_input_projection': projection, 'two_source_legs_share_the_same_phase_age': same_age,
            'relative_phase_step_coordinates_kept': point['two_side_fixed_excitation_phase_steps'],
            'complete_time_mother': _copy(raw['whole_original_time_field_queue_mother']),
            'common_chi_cancels_same_word_final_trace_on_every_time_fibre': law['two_raw_carriers_equal'] and same_age and raw['fixed_pump_clock_member']['restart_policy'] != 'source_PC_policy',
            'full_matter_field_kernel_declared_phase_independent': False,
            'cross_number_kernel_common_phase_rule': 'exp(i*(n_D2_bra-n_D2_ket)*chi) times Ad(U_pair(chi))',
            'source_PC_restart_cells_require_their_actual_clock_profile': raw['fixed_pump_clock_member']['restart_policy'] == 'source_PC_policy',
            'old_noncompact_field_difference_still_priced_by_actual_operator_tail': True,
            'complete_joint_time_queue_kernel_numerically_integrated': False, 'controller_advance': False}


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None)), repr(getattr(value, '__defaults__', None)), repr(getattr(value, '__kwdefaults__', None))


def _signature():
    functions = (product, factorial, _require, _copy, _digest, _freeze_terms, _matrices, _coimage_field_kernel, _kernel_price,
        _common_line_law, _project_common_line_input, _bindings,
        _excitation_step_coordinates, _primitive, _source_H, _line_frame, _pair_line_frame,
        _Gamma_chart_price, _certify_chart, _retarded_images, _excitation_fibre, _excitation_clock_cuts,
        _function, _signature, _check, preparation._line_covariance, preparation._pc_steps,
        preparation.RetardedNativePreparationSource.source_tensors, preparation.RetardedNativePreparationSource.pc_fibre,
        field._source, gaussian._scalar, gaussian._parts, gaussian._piece_integer, gaussian._restore,
        gaussian.GaussianAtomicPulseSource.field_off_tail_price,
        driven._eval, driven._freeze_report, driven._multiply, driven._jump, driven.original._tensor,
        retarded._closed_groups, retarded._recycle, joint.passive_transfer,
        full.exact, full.nonnegative, channel._input_record, dipole.matrix_product)
    methods = tuple(_function(v) for cls in (ExcitationClockMember, RetardedPreparedExcitationFieldSource) for v in vars(cls).values() if callable(v))
    return tuple(map(_function, functions)), methods, SCHEMA, full.DIMENSION, joint.DIMENSION


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and preparation._CHECK is _PREPARATION_CHECK and
             gaussian._CHECK is _GAUSSIAN_CHECK and driven._CHECK is _DRIVEN_CHECK and retarded._CHECK is _RETARDED_CHECK,
             'same-preparation excitation/field source closure changed')
    _PREPARATION_CHECK(); _GAUSSIAN_CHECK(); _DRIVEN_CHECK(); _RETARDED_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
