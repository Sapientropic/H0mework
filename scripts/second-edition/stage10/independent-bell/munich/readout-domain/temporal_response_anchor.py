"""Source-native finite-time herald rows retain the reload waiting information.

The first native window and first BSM rate measure generate F_T.  Every later
control branch is retained, and its exclusion from this finite event follows
from the original raw clock edges.  No effect, response row or determinant is
an input to the producer.
"""
from fractions import Fraction as Q

import atomic_dipole as dipole
import atomic_full_forward as full
import bsm_background_tail as background
import bsm_retry_source as bsm
import fluorescence_channel as channel
import joint_reload_resolvent as native
import joint_reload_source as reload
import next_herald_response as response
import projected_window_cem as projected
import stopped_bsm_programme as stopped
import stopped_history_law as history
import window_cem_source as window


SCHEMA = 'stage10-source-finite-time-next-herald-response/v1'
WITNESS_SCHEMA = 'stage10-first-native-window-first-BSM-curves/v1'


def _copy(value):
    return projected._copy(value)


def _lead(raw):
    return stopped._duration(raw.preparation+raw.excitation+raw.arrival_delay)


def _minimum_ready_delays(source):
    delays = {reload.READY: Q(0)}
    for _ in range(reload.READY):
        previous = dict(delays)
        for stage in range(reload.READY):
            choices = [previous[target] for high in (False, True)
                       if (target := source._next(stage, high)) in previous]
            if choices:
                value = source._window(stage).duration+min(choices)
                delays[stage] = min(delays.get(stage, value), value)
    channel._require(set(delays) == set(range(reload.READY+1)),
                     'every native stage must retain its source path to Ready')
    return delays


def time_support(raw_reload, raw_bsm, *, gate_fraction=Q(1, 2), seconds_per_unit=1):
    source = native._source(raw_reload)
    channel._require(type(raw_bsm) is stopped.StoppedBSMProgramme, 'closed original stopped BSM source required')
    burst = background._from_record('programme', stopped.StoppedBSMProgramme.record(raw_bsm))
    fraction, unit = full.exact(gate_fraction), full.exact(seconds_per_unit)
    channel._require(0 < fraction <= 1 and unit > 0 and unit == burst.gate.seconds_per_unit,
                     'a finite first-gate fraction and the same original physical time unit required')
    channel._require(source._next(0, True) == reload.READY and source._next(0, False) != reload.READY,
                     'original post-CEM diagnostic high/low control edges required')
    first = source._window(0).duration
    lead, gate = _lead(burst), burst.gate.duration
    channel._require(gate > 0, 'positive original BSM gate duration required')
    start, end = first+lead, first+lead+fraction*gate
    following = source._next(0, False)
    delays = _minimum_ready_delays(source)
    pending_start = first+delays[following]+lead
    next_gate = first+lead+gate+stopped._duration(burst.return_phases)+lead
    channel._require(end <= pending_start and end <= next_gate,
                     'finite event reaches an uncomputed native or BSM branch; retain and compute that branch')
    return _copy({'gate_fraction': str(fraction), 'seconds_per_source_unit': str(unit),
        'first_native_window_end_relative_to_current_CEM_end': str(first),
        'first_BSM_gate_support_relative_to_current_CEM_end': [str(start), str(start+gate)],
        'finite_event_right_endpoint': str(end), 'first_gate_restriction': [str(start), str(end)],
        'native_pending_next_stage': following,
        'native_minimum_ready_delays': [{'stage': stage, 'minimum_duration': str(delays[stage])}
                                       for stage in range(reload.READY+1)],
        'native_pending_first_receipt_lower': str(pending_start),
        'next_BSM_gate_first_receipt_lower': str(next_gate),
        'original_native_time_edges': native._time_edges(source, unit),
        'causal_selected_pending_tail_upper': '0',
        'source_rule': 'all original low/high edges complete their raw window before the next stage',
        'BSM_receipt_has_no_endpoint_atoms': 'original stopped success_flux produces a continuous rate measure',
        'actual_scalar_clock_created': False})


def _flow(source, burst, inlet, old, witness, support):
    channel._require(type(witness) is dict and set(witness) ==
                     {'schema', 'native_trial_pieces', 'native_precision', 'BSM_curves'} and
                     witness['schema'] == WITNESS_SCHEMA,
                     'only original window/BSM curve proposals required; target states or rows are not input')
    precision, curves = witness['native_precision'], witness['BSM_curves']
    channel._require(type(precision) is list and len(precision) == 3 and type(curves) is dict and
                     set(curves) == {'multitone_bits', 'phase_certificates', 'gate_certificates'} and
                     type(curves['gate_certificates']) is list and len(curves['gate_certificates']) == 1,
                     'complete first-window precision and exactly one original BSM gate required')
    inherited = old+inlet['local_error']
    certificate = reload.certify_window(source, inlet['state'], witness['native_trial_pieces'],
                     stage=0, upstream_error=inherited, mode_bits=precision[0],
                     coefficient_bits=precision[1], exponential_bits=precision[2])
    endpoint = {(0, count, i, j): dipole.ComplexRadical(Q(a), Q(b))
                for count, i, j, a, b in certificate['counter_poststate_center']}
    ready, pending = {}, {stage: {} for stage in range(reload.READY)}
    for branch in source.projected_window_end(endpoint).values():
        for (stage, counter, i, j), value in branch.items():
            channel._require(stage == reload.READY or counter == 0, 'the original pending counter must reset')
            native._add(ready if stage == reload.READY else pending[stage], {(i, j): value})
    start = Q(support['first_native_window_end_relative_to_current_CEM_end'])
    ingress = {**_copy(curves), 'raw_burst': burst.record(),
        'parent_input_identity': {'original_native_source': source.record(),
                                  'source_inlet': channel._input_record(inlet['state'])},
        'parent_journal': []}
    run = projected._replay_bsm_ingress(ingress, ready, Q(certificate['trace_norm_error_bound']), start)
    result = run.programme_result
    channel._require(len(result.first_receipt_laws) == 1 and
                     result.first_receipt_laws[0].support == tuple(map(Q,
                       support['first_BSM_gate_support_relative_to_current_CEM_end'])),
                     'the rate measure must retain its original source-generated receipt clock')
    measure = result.first_receipt_laws[0].interval(*map(Q, support['first_gate_restriction']))
    next_start = result.remaining_time+_lead(burst)
    channel._require(next_start == Q(support['next_BSM_gate_first_receipt_lower']),
                     'the pending BSM clock must come from the original full first attempt')
    global_error = result.global_time_error
    return _copy({'source_inlet': channel._input_record(inlet['state']),
        'inlet_local_error': str(inlet['local_error']), 'inlet_error': str(inherited),
        'first_native_window_certificate': certificate,
        'complete_ready_matrix': channel._input_record(ready),
        'complete_native_pending': native._block_record(pending),
        'native_pending_source_time': str(start),
        'original_first_BSM_ingress': ingress,
        'whole_four_pattern_restricted_receipt': {
            'poststates': [channel._input_record(matrix) for matrix in measure['poststates']],
            'restriction': support['first_gate_restriction'], 'global_trace_norm_error': str(global_error)},
        'complete_BSM_pending': {'complete_matrix': channel._input_record(result.remaining_pair),
            'source_time': str(result.remaining_time), 'raw_programme': burst.record(),
            **history.continuation_cursor(1)},
        'whole_trace_norm_error': str(global_error),
        'new_native_window_error': str(Q(certificate['trace_norm_error_bound'])-inherited),
        'new_BSM_whole_time_error': str(global_error-Q(certificate['trace_norm_error_bound'])),
        'old_whole_error_paid_once': str(inherited),
        'input_mass': response._mass(inlet['state'], inherited),
        'all_native_and_BSM_pending_retained': True,
        'pending_selected_event_mass_upper': '0', 'gate_end_state_used_as_receipt': False})


def generate_rows(previous_source, detector_report, raw_reload, raw_bsm, witnesses, *, side=0,
                  next_herald='Psi+', gate_fraction=Q(1, 2)):
    channel._require(type(side) is int and side in (0, 1) and next_herald in ('Psi+', 'Psi-'),
                     'original physical side and next herald required')
    channel._require(type(witnesses) is dict and set(witnesses) == {'Phi', 'B'},
                     'both original source curve families required; response rows are not inputs')
    previous, gates, inlets, old = response._inlets(previous_source, detector_report, side)
    source = native._source(raw_reload)
    channel._require(type(raw_bsm) is stopped.StoppedBSMProgramme, 'closed original BSM programme required')
    burst = background._from_record('programme', stopped.StoppedBSMProgramme.record(raw_bsm))
    support = time_support(source, burst, gate_fraction=gate_fraction, seconds_per_unit=previous.seconds_per_unit)
    flows = {name: _flow(source, burst, inlet, old, witnesses[name], support) for name,inlet in inlets.items()}
    for flow in flows.values():
        selected = {}
        for index, matrix in enumerate(flow['whole_four_pattern_restricted_receipt']['poststates']):
            if bsm.PATTERNS[index][0] == next_herald:
                native._add(selected, channel._read_input(matrix, reload.DIMENSION))
        flow['finite_herald_mass'] = response._mass(selected, Q(flow['whole_trace_norm_error']))
    rows = {'a': flows['Phi']['input_mass'], 'b': flows['B']['input_mass'],
            'c': flows['Phi']['finite_herald_mass'], 'e': flows['B']['finite_herald_mass']}
    bands = {name: response._interval(value['interval']) for name,value in rows.items()}
    determinant = response._sub(response._mul(bands['a'], bands['e']), response._mul(bands['b'], bands['c']))
    return _copy({'schema': SCHEMA, 'previous_raw_window_source': previous.record(),
        'original_detector_family_report': detector_report, 'source_recipe': detector_report['source_recipe'],
        'previous_window_interval': detector_report['interval'], 'constant_gate_certificate': gates,
        'raw_future_reload_source': source.record(), 'raw_future_BSM_source': burst.record(),
        'physical_current_side': side, 'physical_next_herald': next_herald,
        'source_time_support': support, 'untrusted_future_curve_witnesses': witnesses,
        'source_flows': flows, 'source_response_rows': rows,
        'determinant_interval': response._record(determinant),
        'strict_determinant_certified': determinant[0] > 0 or determinant[1] < 0,
        'response_equations': {'click': 'd*a+(1-d)*eta*b',
            'click_and_finite_next_herald': 'd*c+(1-d)*eta*e', 'eta': '1-p00 under the original full active gates'},
        'complete_relative_time_recipe': {'current_window_mother': detector_report['source_recipe'],
            'current_window_interval': detector_report['interval'],
            'future_native_edges': support['original_native_time_edges'],
            'finite_first_receipt_restriction': support['first_gate_restriction'],
            'same_operation_on_every_original_mother_time_restriction': True,
            'time_reference': 'elapsed after the current receipt-relative CEM response ends'},
        'seconds_per_source_unit': str(previous.seconds_per_unit),
        'whole_upstream_error': str(old), 'whole_error_paid_once_per_source_flow': True,
        'all_four_BSM_patterns_and_all_pending_retained': True,
        'future_CEM_instrument_applied': False, 'integrated_future_response_used': False,
        'full_history_degeneracy_concluded': False, 'numerical_centres_assumed_positive': False,
        'original_input_positivity_required': True, 'source_recipe_is_physical_membership_certificate': False,
        'actual_next_record_selection_certified': False, 'actual_scalar_clock_created': False,
        'literal_cohort_reconstructed': False, 'actual_hardware_uniquely_identified': False,
        'controller_advance': False})


def verify_rows(report, previous_source=None):
    channel._require(type(report) is dict and report.get('schema') == SCHEMA,
                     'source temporal response certificate required')
    previous = (window.WindowCEMSource.from_record(report['previous_raw_window_source'])
                if previous_source is None else previous_source)
    channel._require(type(previous) is window.WindowCEMSource and
                     previous.record() == report['previous_raw_window_source'], 'same original previous source required')
    rows = report['source_response_rows']
    bands = {name: response._interval(rows[name]['interval']) for name in ('a','b','c','e')}
    determinant = response._sub(response._mul(bands['a'],bands['e']), response._mul(bands['b'],bands['c']))
    channel._require(report['determinant_interval'] == response._record(determinant),
                     'the source determinant arithmetic changed')
    expected = generate_rows(previous, report['original_detector_family_report'],
        reload.JointReloadSource.from_record(report['raw_future_reload_source']),
        background._from_record('programme', report['raw_future_BSM_source']),
        report['untrusted_future_curve_witnesses'], side=report['physical_current_side'],
        next_herald=report['physical_next_herald'], gate_fraction=report['source_time_support']['gate_fraction'])
    channel._require(expected == report, 'time restriction, source row, full pending, price or mother changed')
    return True


def inverse_from_certificate(report, click_response, joint_response):
    verify_rows(report)
    result = response.inverse_intervals({name:value['interval'] for name,value in report['source_response_rows'].items()},
                                       click_response, joint_response)
    return {'source_temporal_response_certificate': report, 'inverse': result,
            'response_CI_source_is_separate': True, 'actual_hardware_uniquely_identified': False,
            'controller_advance': False}
