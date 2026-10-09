"""The checked complete free bank generates the first registered forcing DAG."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import free_density_bank_rha0033 as bank
import registered_tensor_action_rha0034 as tensor

source, trajectory, core = tensor.source, tensor.trajectory, bank.core
HERE, ROOT, paid = bank.HERE, bank.ROOT, bank.paid
SCHEMA = 'stage10-source-complete-first-registered-forcing/rha0034'


def prices(duration, activity, new_free_error, old_input_error, positive_mass, row_norm, gamma_relative):
    t, lam, new, old, mass, norm, delta = map(Q, (duration, activity, new_free_error,
        old_input_error, positive_mass, row_norm, gamma_relative))
    source.require(min(t, lam, new, old, mass, norm, delta) >= 0, 'nonnegative complete source prices required')
    free = 2*t*lam*new
    gamma = t*delta*norm*(mass+old+new)
    return {'new_free_bank_forcing_integral_price': str(source.upper(free)),
        'registered_rate_Gamma_integral_price': str(source.upper(gamma)),
        'whole_new_forcing_integral_price': str(source.upper(free+gamma)),
        'old_input_error_included_in_free_bank_defect': False,
        'central_initial_trace_norm_upper': str(mass+old),
        'old_input_error_payment': 'one whole physical instrument contraction; never per layer',
        'signed_central_initial_tail_mass_upper': str(mass+old)}


def _programs(original, active):
    operators = {}; programs = []; row_norm = Q(0)
    for component in trajectory.COMPONENTS:
        rows = tensor._rows(original, 'registered', component, source.bsm.INITIAL, active)
        compact = []
        for row in tensor.program_record(rows):
            price = source.bsm._entry_norm({(0, 0): source.channel._complex_record(row['coefficient'])}, bits=192)
            for key in ('left_operators', 'right_operators'):
                identities = []
                for value in row[key]:
                    if value is None: identities.append(None); continue
                    identity = source.digest(value); operators[identity] = value; identities.append(identity)
                    price *= source.bsm._entry_norm(trajectory.gaussian._matrix(value), bits=192)
                row[key] = identities
            row_norm += price; compact.append(row)
        programs.append({'component': component if type(component) is str else list(component), 'rows': compact})
    return operators, programs, row_norm


def _curve_inventory():
    proposals = json.loads(paid.paid.frozen(HERE/'free-density-bank-proposals-first-rha0033.1.json'))
    candidates = [row['accepted_curve'] for row in proposals['rows']]
    first = json.loads(paid.paid.frozen(HERE/'free-density-first-rha0032.2.json'))
    proposal = first['untrusted_node_proposal']; path = ROOT/Path(proposal['path']).parent/proposal['curve']['path']
    candidates.append(bank.binding(path))
    return {row['sha256']: row for row in candidates}


def _nodes(current, raw, completed):
    expected = bank.inventory(raw)
    source.require(completed['schema'] == bank.SCHEMA+'/complete' and
        completed['scientific_freeze_commit'] == '204293885ed41cadc002fbf938287611405bac8a' and
        completed['source_bindings'] == bank.bindings(completed['scientific_freeze_commit']) and
        completed['all_local_relative_accuracy_gates_passed'] is True and
        completed['new_uniform_tensor_error_below_old_input_error'] is True and
        [(r['side'], r['factor_index'], r['factor_id']) for r in completed['rows']] == expected,
        'the complete frozen ten-factor free bank must be accepted')
    candidates = _curve_inventory(); reports = {}; nodes = []
    owners = [core.density.GaussianLocalDensitySource(current._law._field._pulses[side]).record() for side in (0, 1)]
    for row in completed['rows']:
        report = json.loads(bank.artifact(row['checked_curve']).read_text()); side, index, factor = row['side'], row['factor_index'], row['factor_id']
        initial = raw['checked_local_density_inventories'][side][index]['complete_retarded_local_endpoint']
        source.require(report['original_density_source'] == owners[side] and
            report['stream_header']['initial_matrix_sha256'] == core.digest(initial) and
            report['stream_header']['source_factor_id'] == factor and report['registered_relative_accuracy_passed'] is True and
            report['whole_new_trace_norm_error'] == row['whole_new_trace_norm_error'], 'free curve source or initial factor changed')
        curve = candidates[report['untrusted_stream']['sha256']]; path = bank.artifact(curve)
        source.require(curve['bytes'] == report['untrusted_stream']['bytes'], 'the forcing must consume the checked curve bytes')
        reports[side, factor] = report
        nodes.append({'side': side, 'factor_index': index, 'factor_id': factor,
            'checked_curve': row['checked_curve'], 'Chebyshev_stream': curve,
            'source_interval_seconds': report['source_interval_seconds'], 'source_density_sha256': core.digest(owners[side]),
            'complete_curve_degree': report['stream_header']['curve_degree'], 'complete_piece_count': report['piece_count']})
    error, _ = bank.tensor_price(raw['source_factor_ids'], reports)
    source.require(Q(completed['whole_new_uniform_free_tensor_error']) == source.upper(error) and
        Q(completed['old_whole_input_error_once']) == Q(raw['whole_retarded_gate_input_error']), 'complete free tensor price changed')
    return nodes


def generate(current):
    source.require(type(current) is paid.inlet.PreparedRetardedGaussianInlet, 'closed original completed current inlet required')
    raw = current.record(); completed = json.loads(paid.paid.frozen(HERE/'free-density-bank-first-rha0033.json'))
    nodes = _nodes(current, raw, completed)
    original = trajectory.RetardedGaussianTrajectorySource(current._law, bits=raw['scalar_bits'])
    split = source.RetardedRegisteredDuhamelSource(original); split_raw = split.record()
    g0, g1 = map(Q, original._value['retarded_source']['gate_seconds']); _, active = original._clock(g0)
    source.require(active == (True, True), 'both original legs must already be active throughout this complete gate')
    operators, programs, norm = _programs(original, active); norm = source.upper(norm)
    field = original._value['retarded_source']['complete_driven_field_source']; legs = field['Gaussian_source_legs']
    clock = field['reference_clock']; centre = Q(clock['Gamma_numerical_centre'])
    lo, hi = map(Q, clock['angular_Gamma_enclosure_per_second']); source.require(0 < lo <= centre <= hi, 'original positive Gamma family required')
    delta = max(centre-lo, hi-centre)/centre
    starts = tuple(g0-Q(a)-Q(b) for a, b in zip(field['flight_seconds'], field['emission_origins_seconds']))
    omega = tuple(Q(leg['carrier_angular_frequency_per_second']) for leg in legs)
    phases = []
    for component in trajectory.COMPONENTS:
        if type(component) is tuple and component[0] == 'cross':
            side, other = component[1:]
            phases.append({'component': list(component), 'angle_at_detector_gate_start': str(-omega[side]*starts[side]+omega[other]*starts[other]),
                'angular_frequency_per_second': str(omega[other]-omega[side]),
                'expression': 'exp(i*(angle_at_detector_gate_start+angular_frequency_per_second*(tau-gate_start)))'})
    for node in nodes:
        side = node['side']
        source.require(list(map(Q, node['source_interval_seconds'])) == [starts[side], starts[side]+g1-g0],
                       'every local curve must retain the same complete detector interval')
    activity = Q(split_raw['complete_activity_source']['source_activity']['registered_total_activity_upper_per_second'])
    pricing = prices(g1-g0, activity, completed['whole_new_uniform_free_tensor_error'],
        raw['whole_retarded_gate_input_error'], raw['source_positive_mass_upper'], norm, delta)
    return {'schema': SCHEMA, 'closed_original_split_sha256': source.digest(split_raw),
        'source_identity': {'source': 'positiveSmoothUnifiedSource', 'root_visit': 10, 'current_tick': 16, 'next_tick': 17},
        'paid_free_bank_sha256': hashlib.sha256((HERE/'free-density-bank-first-rha0033.json').read_bytes()).hexdigest(),
        'retained_parent_time_queue_mother_sha256': source.digest(raw['retained_pump_field_and_queue_mother']),
        'source_detector_interval_seconds': [str(g0), str(g1)], 'source_retarded_local_cuts_seconds': list(map(str, starts)),
        'free_curve_nodes': nodes, 'source_tensor_incidence': raw['source_factor_ids'],
        'operator_nodes': operators, 'original_registered_component_programs': programs, 'source_relative_phase_words': phases,
        'registered_component_sum_norm_per_second_upper': str(source.upper(norm)),
        'Gamma_relative_error_upper': str(delta), 'Gamma_registered_rate_scale_interval': [str(lo/centre), str(hi/centre)],
        'Gamma_chart': 'fixed numerical-centre rotating chart; the original registered rates scale by Gamma/centre',
        'registered_total_activity_upper_per_second': str(activity), 'source_positive_mass_upper': raw['source_positive_mass_upper'],
        'new_uniform_free_tensor_error': completed['whole_new_uniform_free_tensor_error'],
        'old_whole_input_error_once': raw['whole_retarded_gate_input_error'], 'forcing_prices': pricing,
        'forcing_expression': 'sum_component scalar_component(tau) * original_registered_program_component(sum_original_incidence A_left(tau) tensor B_right(tau))',
        'definition_of_local_curve': 'complete checked Chebyshev rotating curve at tau-flight-emission_origin',
        'DAG_operator_rows_act_on_both_complete_local_factors': True, 'quantum_joint_matrix_expanded': False,
        'source_phase_words_numerically_evaluated': False, 'first_registered_time_integral_evaluated': False,
        'forcing_error_scope': 'original retarded atomic/Mark coimage; no fine-history total-variation price',
        'full_control_clock_record_square_certified': False,
        'source_Gaussian_field_cut_off': False, 'inverse_TP_flow_used': False, 'source_marks_or_repeated_emissions_removed': False,
        'full_gate_instrument_or_response_anchor_certified': False, 'actual_hardware_uniquely_identified': False, 'controller_advance': False}
