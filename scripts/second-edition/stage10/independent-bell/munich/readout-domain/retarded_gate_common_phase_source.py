"""The source charge grading factors relative gate counts through one coimage.

This is a scalar instrument readout.  The full conditional field/time/queue
state remains with its original mother and is not replaced by the coimage.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import factorial
import hashlib
import json

import retarded_prepared_excitation_field_source as excitation
import common_optical_readout as optical
import retarded_prepared_gate_source as gate_input

atomic, dipole, full, channel, joint, field = (
    excitation.atomic, excitation.dipole, excitation.full,
    excitation.channel, excitation.joint, excitation.field)
SCHEMA = 'stage10-same-source-common-phase-retarded-count-coimage/v1'
_SOURCE_CHECK = excitation._CHECK
_ISSUED = {}


def require(value, reason):
    if not value:
        raise ValueError(reason)


def copy(value):
    return json.loads(channel._canonical(value))


def digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
            (Path(__file__), Path(__file__).with_name('retarded_gate_common_phase_independent.py'),
             Path(__file__).with_name('CommonPhaseCountCoimage.lean'),
             Path(__file__).with_name('criterion-rha0023.md'),
             Path(excitation.__file__), Path(optical.__file__), Path(gate_input.__file__))}


def grading(pulses, optics):
    original = excitation._common_line_law(pulses, optics)
    projector = excitation.preparation.frame._projector('D2')
    require(len(pulses) == 2, 'both original complete source legs required')
    records = []
    for side, pulse in enumerate(pulses):
        h = excitation.gaussian._matrix(pulse['complete_static_H_per_second'])
        r = excitation.gaussian._matrix(pulse['complete_natural_R_per_second'])
        a = excitation.gaussian._matrix(pulse['source_raising_operator_per_second'])
        require(not excitation.preparation.frame._commutator(projector, h) and
                not excitation.preparation.frame._commutator(projector, r), 'source quiet action must have degree zero')
        require(excitation.preparation.frame._commutator(projector, a) == a, 'source raising action must have degree one')
        for item in pulse['original_physical_natural_jumps']:
            operator = excitation.gaussian._matrix(item['normalized_natural_jump_operator'])
            degree = -int(item['group'][0] == 'D2')
            require(excitation.preparation.frame._commutator(projector, operator) ==
                    {key: degree*z for key, z in operator.items() if degree*z}, 'source bath jump lost its single line degree')
        records.append({'side': side, 'static_entries': len(h), 'loss_entries': len(r),
                        'raising_entries': len(a), 'natural_jumps': len(pulse['original_physical_natural_jumps'])})
    groups = excitation.retarded._closed_groups({'physical_legs': pulses})
    group_rows = []
    for label, rate, modes in groups:
        degree = -int(label[0] == 'D2')
        for _, (side, operator) in modes:
            require(side in (0, 1) and excitation.preparation.frame._commutator(projector, operator) ==
                    {key: degree*z for key, z in operator.items() if degree*z}, 'coherent port modes must share a line degree')
        group_rows.append({'group': list(label), 'degree': degree, 'mode_count': len(modes), 'rate': str(rate)})
    return {'schema': SCHEMA+'/complete-source-generator-grading', 'original_line_law': original,
        'local_inventories': records, 'resolved_port_loss_groups': group_rows,
        'pair_matrix_unit_degree': 'number_D2(row_A,row_B)-number_D2(column_A,column_B)',
        'quiet_natural_loss_port_and_background_degree': 0, 'raising_lowering_degrees': [1, -1],
        'Mark_targets_change_line_degree': False,
        'generator_covariance': 'G_chi(t)=Ad(U_chi) G_0(t) Ad(U_chi)^(-1)',
        'time_ordered_word_degree': 'output degree minus input degree; composition telescopes at every length',
        'trace_on_projected_input_degree': 0,
        'relative_time_count_instrument_covariant': True,
        'all_photon_numbers_and_original_Mark_words_covered': True}


def clock_qualification(raw):
    parent = raw['preparation_source']; previous = raw['original_prior_driven_field_source']
    pulses = raw['source_generated_zero_line_chart_pulses']
    origins = tuple(map(Q, previous['emission_origins_seconds']))
    same_age = (len(origins) == 2 and origins[0] == origins[1] and
                excitation.preparation._pump_prefix(parent['original_source_local_plans'], 0, 2) ==
                excitation.preparation._pump_prefix(parent['original_source_local_plans'], 1, 2))
    same_carrier = Q(pulses[0]['carrier_angular_frequency_per_second']) == Q(pulses[1]['carrier_angular_frequency_per_second'])
    gate = tuple(map(Q, raw['source_gate_offsets_from_pump_end_seconds']))
    flights = tuple(map(Q, raw['flight_seconds']))
    require(len(gate) == len(flights) == 2 and gate[0] >= max(flights) and gate[1] > gate[0], 'original causal gate and both flights required')
    horizon = gate[1]-min(flights)
    policy = raw['fixed_pump_clock_member']['restart_policy']
    require(policy in excitation.preparation.CLOCK_POLICIES, 'original source clock policy required')
    before_expiry = max(map(Q, raw['pump_end_time_family_seconds']))+horizon < Q(
        parent['source_expiry_free_preparation_support']['earliest_possible_recent_expiry_seconds'])
    faces = parent['source_expiry_free_preparation_support']['source_all_Ready_face_PC_updates']
    require(faces, 'all original Ready faces required')
    cuts = [excitation._excitation_clock_cuts(parent, policy, side, Q(0), horizon) for side in range(len(faces))]
    constant = all(len(row) == 2 for row in cuts)
    return {'schema': SCHEMA+'/whole-Ready-clock-qualification', 'same_two_leg_phase_age': same_age,
        'same_raw_carrier': same_carrier, 'restart_policy': policy,
        'complete_relative_gate_seconds': list(map(str, gate)), 'retarded_excitation_horizon_seconds': str(horizon),
        'all_Ready_face_phase_cuts_seconds': [[str(x) for x in row] for row in cuts],
        'common_phase_constant_on_each_whole_gate_fibre': constant,
        'expiry_free_whole_gate_support': before_expiry,
        'relative_count_readout_factors_through_quantum_coimage': same_age and same_carrier and constant and before_expiry,
        'absolute_timestamp_or_joint_queue_readout_factored': False}


def future_tail_price(raw, bits=192):
    """New future operator difference; the earlier coimage price is not a fine-TV bound."""
    earliest = Q(raw['pump_end_time_family_seconds'][0])
    prior = raw['original_prior_driven_field_source']
    clock = raw['reference_clock']; gamma = Q(clock['Gamma_numerical_centre'])
    ratio = max(gamma, Q(clock['angular_Gamma_enclosure_per_second'][1]))/gamma
    total, rows = Q(0), []
    for side, pulse in enumerate(prior['Gaussian_source_legs']):
        after = earliest-Q(prior['emission_origins_seconds'][side])
        x, sigma2 = after-Q(pulse['centre_seconds']), Q(pulse['sigma_squared_seconds'])
        require(sigma2 > 0, 'original positive Gaussian variance required')
        if x > 0:
            z = x*x/(4*sigma2)
            envelope = min(Q(factorial(n), 1)/z**n for n in range(17))
            integral = 2*sigma2*envelope/x
        else:
            _, root = full._sqrt(sigma2.numerator*sigma2.denominator, bits)
            integral = 6*root/sigma2.denominator
        norm = excitation.gaussian._norm(excitation.gaussian._matrix(pulse['source_raising_operator_per_second']), bits)
        price = 4*ratio*norm*integral; total += price
        rows.append({'side': side, 'source_earliest_old_local_cut_seconds': str(after),
            'original_field_tail_integral_upper_seconds': str(integral),
            'source_raising_norm_upper_per_second': str(norm), 'new_future_operator_difference_upper': str(price)})
    mass = Q(raw['same_positive_CEM_mother_mass_upper'])
    return {'schema': SCHEMA+'/new-future-old-field-Duhamel-price', 'source_earliest_pump_end_seconds': str(earliest),
        'source_math_Gamma_upper_ratio': str(ratio), 'sides': rows,
        'future_time_retaining_instrument_difference_per_input_norm': str(total),
        'same_positive_mother_mass_upper': str(mass), 'future_instrument_difference_upper': str(mass*total),
        'past_quantum_coimage_error_reused_as_fine_TV': False,
        'source_law': 'H_old tensor I; commutator norm <=4 norm(raising) g; integrate uniformly over the original mother'}


def count_gate(optics):
    owner = optical.CommonOpticalReadout.from_record(optics)
    gate, proof = owner.bsm_gate(compilation_bits=160)
    marks = gate_input._mark_inventory(gate)
    return {'raw_bsm_gate': gate.record(), 'same_optical_gate_certificate': proof,
        'raw_bsm_source_used_for_count_targets_only': True,
        'physical_gate_clock_owner': 'source_clock_qualification.complete_relative_gate_seconds',
        'complete_Mark_inventory': [{'counts': list(m.counts), 'receipt': m.receipt} for m in marks],
        'four_port_targets': [{'source': {'counts': list(m.counts), 'receipt': m.receipt},
            'targets': [] if m.receipt is not None else
                [{'counts': list(gate.target(m,p).counts), 'receipt': gate.target(m,p).receipt} for p in range(4)]} for m in marks],
        'receipt_coimage_stops_at_first_receipt': True}


def adjoint_images(raw, primitives, observer):
    observer = joint._matrix(observer)
    pending, independent, scalar = {}, {}, Q(0)
    for side, primitive in enumerate(primitives):
        k = excitation.gaussian._matrix(primitive['complete_K_per_second'])
        term = excitation.gaussian._sum(joint._operator_left(observer, side, dipole.matrix_adjoint(k)),
                                       joint._operator_right(observer, side, k))
        field._add(pending, term); field._add(independent, term)
        scalar += 2*Q(primitive['H_scalar_operator_error_upper_per_second'])
        for jump in primitive['original_resolved_natural_jumps']:
            operator = excitation.gaussian._matrix(jump['normalized_natural_jump_operator'])
            term = joint._operator_right(joint._operator_left(observer, side, dipole.matrix_adjoint(operator)), side, operator)
            field._add(independent, term, Q(jump['physical_amplitude_squared_per_second']))
    transfer = tuple(tuple(channel._complex_record(v) for v in row) for row in raw['working_common_optical_source']['generated_four_by_six_transfer'])
    _, _, loss = joint.passive_transfer(transfer); jumps = [dict() for _ in range(4)]
    for _, rate, modes in excitation.retarded._closed_groups({'physical_legs': raw['source_generated_zero_line_chart_pulses']}):
        for mu, (side, first) in modes:
            for nu, (other, second) in modes:
                image = joint._operator_right(joint._operator_left(observer, other, dipole.matrix_adjoint(second)), side, first)
                if loss[nu][mu]: field._add(pending, image, rate*loss[nu][mu])
                for port in range(4):
                    factor = rate*transfer[port][mu]*transfer[port][nu].conjugate()
                    if factor: field._add(jumps[port], image, factor)
    unit = Q(raw['working_atomic_owner']['atomic_base']['seconds_per_unit'])
    beta = [Q(b)/unit for b in raw['working_common_optical_source']['background_rates']]
    field._add(pending, observer, -sum(beta,Q(0)))
    for jump, rate in zip(jumps,beta): field._add(jump, observer, rate)
    complete = dict(pending)
    for jump in jumps: field._add(complete,jump)
    require(complete == independent, 'the complete source adjoint must recover both local natural generators')
    return pending,jumps,complete,scalar


def herald_seed(counts, herald):
    require(herald in ('Psi+','Psi-'), 'original physical herald readout required')
    identity = channel._input_record({(i,i):dipole.ComplexRadical(1) for i in range(joint.DIMENSION)})
    return [{'mark': copy(mark), 'source_trace_observer': identity if mark['receipt'] is not None and
             excitation.retarded.bsm.PATTERNS[mark['receipt']][0] == herald else []}
            for mark in counts['complete_Mark_inventory']]


class CommonPhaseRetardedCountSource:
    def __init__(self, source, member):
        _SOURCE_CHECK()
        require(type(source) is excitation.RetardedPreparedExcitationFieldSource and
                type(member) is excitation.ExcitationClockMember, 'closed same-occurrence excitation source/member required')
        raw = source.record(); point = source._member(member)
        grade = grading(raw['source_generated_zero_line_chart_pulses'], raw['working_common_optical_source'])
        clock = clock_qualification(raw)
        require(clock['relative_count_readout_factors_through_quantum_coimage'],
                'source carrier/clock does not admit a constant common-phase reduction')
        projection = source.joint_common_line_input_projection(member)
        report = json.loads(source._report_json)
        tail = report['continuing_Gaussian_TP_composition_contract']
        require(tail['budget_already_in_whole_native_error'] is True and tail['same_infinite_tail_charged_again'] is False and
                tail['original_infinite_tail_budget'] == raw['preparation_source']['native_infinite_Gaussian_Duhamel_budget'],
                'the actual old noncompact field must retain its original preparation coimage price')
        inherited = Q(raw['whole_preparation_quantum_error_once'])
        require(0 <= Q(tail['original_infinite_tail_budget']) <= inherited, 'old global tail price must be included once')
        old = raw['original_prior_driven_field_source']; steps = point['two_side_fixed_excitation_phase_steps']
        base = Q(old['Gaussian_source_legs'][1]['phase_radians'])-Q(old['Gaussian_source_legs'][0]['phase_radians'])
        alo, ahi = map(Q, steps[0]['phase_step_radians']); blo, bhi = map(Q, steps[1]['phase_step_radians'])
        relative = base+blo-ahi, base+bhi-alo
        self._source, self._member = source, member
        self._terms = excitation._freeze_terms(projection['projected_source_tensor_terms'])
        future = future_tail_price(raw)
        self._value = {'schema': SCHEMA, 'source_excitation_digest': raw['source_digest'],
            'same_history_complete_clock_digest': point['same_history_complete_clock_digest'],
            'reference_clock': copy(raw['reference_clock']),
            'source_generator_grading': grade, 'source_clock_qualification': clock,
            'source_count_gate': count_gate(raw['working_common_optical_source']),
            'relative_fixed_phase_interval': list(map(str, relative)),
            'source_positive_mother_projection': projection['source_derived_projection_price'],
            'whole_preparation_error_once': str(inherited), 'original_preparation_old_field_tail_contract': copy(tail),
            'new_future_old_field_Duhamel_price': future,
            'common_phase_is_a_computational_chart': True, 'old_physical_field_set_to_zero': False,
            'auxiliary_field_has_old_drive_removed_with_new_future_operator_price': True,
            'scalar_relative_first_receipt_readout_consumes_quantum_coimage': True,
            'quantum_marginal_error_lifted_to_fine_queue_TV': False,
            'full_poststate_or_absolute_record_recovered_from_coimage': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False,
            'source_bindings': bindings()}
        self._seal = digest(self._value); _ISSUED[id(self)] = source, member, self._seal, self._terms

    def record(self):
        _SOURCE_CHECK()
        require(type(self) is CommonPhaseRetardedCountSource and set(vars(self)) == {'_source','_member','_terms','_value','_seal'} and
                _ISSUED.get(id(self)) == (self._source, self._member, self._seal, self._terms) and digest(self._value) == self._seal and
                self._value['source_bindings'] == bindings() and self._source.record()['source_digest'] == self._value['source_excitation_digest'] and
                self._source._member(self._member)['same_history_complete_clock_digest'] == self._value['same_history_complete_clock_digest'],
                'same source occurrence, fixed phase coordinates or coimage changed')
        return copy(self._value)

    def source_tensors(self):
        raw = self.record()
        return {'source_record': raw, 'tensor_terms': tuple((dict(a), dict(b)) for a, b in self._terms),
            'scalar_instrument_input_price': Q(raw['whole_preparation_error_once'])+
                Q(raw['source_positive_mother_projection']['joint_mother_projection_trace_norm_upper'])+
                Q(raw['new_future_old_field_Duhamel_price']['future_instrument_difference_upper']),
            'relative_first_receipt_effect_only': True, 'whole_time_queue_state_replaced': False}

    def verify(self):
        import retarded_gate_common_phase_independent as checker
        value = self.record(); raw = self._source.record()
        checker.check_grading(raw['source_generated_zero_line_chart_pulses'], raw['working_common_optical_source'], value['source_generator_grading'])
        checker.clock_check(raw, value['source_clock_qualification'])
        checker.check_future_tail(raw, value['new_future_old_field_Duhamel_price'])
        checker.check_count_gate(value['source_count_gate'], raw['working_common_optical_source'])
        return True

    def _primitives(self, time, bits):
        result = self.record(); raw = self._source.record()
        lo, hi = map(Q, result['relative_fixed_phase_interval']); angles = Q(0), (lo+hi)/2
        primitives = []
        for side, pulse in enumerate(raw['source_generated_zero_line_chart_pulses']):
            elapsed = time-Q(raw['flight_seconds'][side])
            if elapsed < 0:
                continue
            h, error = excitation._source_H(pulse, elapsed, angles[side], bits)
            loss = excitation.gaussian._matrix(pulse['complete_natural_R_per_second'])
            k = excitation.gaussian._sum({key: z*dipole.ComplexRadical(0, -1) for key, z in h.items()},
                                        {key: -z*Q(1, 2) for key, z in loss.items()})
            primitives.append((side, {'complete_K_per_second': channel._input_record(k),
                'H_scalar_operator_error_upper_per_second': str(error),
                'original_resolved_natural_jumps': pulse['original_physical_natural_jumps']}))
        return raw, result, primitives, (hi-lo)/2

    def unobserved_generator_images(self, detector_offset, matrix, *, bits=192):
        excitation.gaussian._precision(bits); time = full.nonnegative(detector_offset)
        raw, result, primitives, radius = self._primitives(time, bits)
        require(min(map(Q, raw['flight_seconds'])) <= time <= Q(raw['source_gate_offsets_from_pump_end_seconds'][0]),
                'source unobserved retarded inlet clock required')
        image, error = gate_input._unobserved_image(primitives, joint._matrix(matrix))
        return {'schema': SCHEMA+'/source-owned-auxiliary-unobserved-generator', 'source_record': result,
            'detector_offset_seconds': str(time), 'active_retarded_sides': [s for s,_ in primitives],
            'complete_generator_image_per_second': channel._input_record(image),
            'source_scalar_image_error_per_second': str(error), 'relative_phase_box_radius': str(radius),
            'source_phase_box_difference_priced': False, 'gate_Mark_initialized': False}

    def source_herald_observer_seed(self, herald):
        raw = self.record()
        return {'source_record':raw,'herald':herald,'complete_mark_observers':herald_seed(raw['source_count_gate'],herald),
                'numerical_response_effect_supplied':False,'boundary_generated_from_original_record_selector':True}

    def adjoint_generator_images(self, detector_offset, observer, *, bits=192):
        excitation.gaussian._precision(bits); time = full.nonnegative(detector_offset)
        raw,result,primitives,radius = self._primitives(time,bits)
        g0,g1 = map(Q,raw['source_gate_offsets_from_pump_end_seconds'])
        require(g0 <= time <= g1 and len(primitives) == 2,'source relative adjoint gate clock required')
        pending,jumps,complete,scalar = adjoint_images(raw,[p for _,p in primitives],observer)
        return {'schema':SCHEMA+'/source-owned-auxiliary-adjoint-generator','source_record':result,
            'detector_offset_seconds':str(time),'no_arrival_adjoint_image_per_second':channel._input_record(pending),
            'four_port_adjoint_images_per_second':[channel._input_record(j) for j in jumps],
            'complete_adjoint_image_per_second':channel._input_record(complete),
            'source_scalar_operator_error_per_second_per_observer_norm':str(scalar),
            'relative_phase_box_radius':str(radius),'source_phase_box_difference_priced':False}

    def generator_images(self, detector_offset, matrix, *, bits=192):
        excitation.gaussian._precision(bits); time = full.nonnegative(detector_offset)
        raw, result, primitives, radius = self._primitives(time, bits)
        gate = tuple(map(Q, raw['source_gate_offsets_from_pump_end_seconds']))
        require(gate[0] <= time <= gate[1] and len(primitives) == 2, 'source relative gate clock required')
        pending, jumps, complete, _, scalar = excitation._retarded_images(raw, [p for _,p in primitives], matrix)
        return {'schema': SCHEMA+'/source-owned-auxiliary-generator', 'source_record': result,
            'detector_offset_seconds': str(time), 'no_arrival_generator_per_second': channel._input_record(pending),
            'four_port_jump_images_per_second': [channel._input_record(j) for j in jumps],
            'complete_generator_per_second': channel._input_record(complete),
            'source_scalar_generator_error_per_second_per_input_norm': str(scalar),
            'relative_phase_box_radius': str(radius), 'source_phase_box_difference_priced': False,
            'physical_field_and_queue_mother_retained_by_original_source': True}
