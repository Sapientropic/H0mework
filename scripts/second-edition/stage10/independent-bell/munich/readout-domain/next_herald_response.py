"""A CEM source produces detector response rows through its native successor.

Phi and the accepted-ion Born map are read from the checked detector family.
Raw reload and full BSM source residuals produce the future herald response.
No future effect matrix, desired response, or empirical probability is input.
"""
from fractions import Fraction as Q

import bsm_background_tail as background
import bsm_resolvent as bsm_future
import bsm_retry_source as bsm
import fluorescence_channel as channel
import joint_reload_resolvent as native
import joint_reload_source as reload
import projected_window_cem as projected
import stopped_bsm_programme as stopped
import window_cem_source as window
import window_detector_family as family


SCHEMA = 'stage10-source-next-herald-detector-response/v1'


def _interval(value):
    channel._require(type(value) in (tuple, list) and len(value) == 2,
                     'ordered exact response interval required')
    a, b = map(Q, value)
    channel._require(a <= b, 'ordered exact response interval required')
    return a, b


def _add(left, right):
    return left[0]+right[0], left[1]+right[1]


def _sub(left, right):
    return left[0]-right[1], left[1]-right[0]


def _mul(left, right):
    corners = [x*y for x in left for y in right]
    return min(corners), max(corners)


def _div(left, right):
    channel._require(right[1] < 0 or right[0] > 0, 'strict determinant sign required')
    return _mul(left, (1/right[1], 1/right[0]))


def _record(pair):
    return list(map(str, pair))


def _mass(matrix, error):
    center, radical = projected._trace(matrix)
    return {'center': str(center), 'trace_radical_error': str(radical),
            'whole_trace_norm_error': str(error), 'interval': _record((center-error-radical, center+error+radical))}


def _full_gate_certificate(source, side):
    checks = []
    for phase in source.phases():
        if phase.ion_rates[side]:
            gates = source.registrations[side].gates(phase.interval_start)
            channel._require(gates == (1, 1),
                             'every active original ion phase needs both full gates for constant eta rows')
            checks.append({'phase_index': phase.index, 'interval_start': str(phase.interval_start),
                           'duration': str(phase.duration), 'electron_and_ion_gates': list(gates),
                           'original_ion_rates': [[i, str(rate)] for i, rate in sorted(phase.ion_rates[side].items())]})
    return {'side': side, 'active_ion_phase_checks': checks,
            'source_partition_checked': source.record()['phase_inventory'],
            'all_active_ion_phases_both_gates': True, 'late_ion_birth_backfilled': False}


def _inlets(previous, report, side):
    channel._require(type(previous) is window.WindowCEMSource, 'closed original window source required')
    source = window.WindowCEMSource.from_record(window.WindowCEMSource.record(previous))
    gates = _full_gate_certificate(source, side)
    carrier = family.WindowDetectorFamily(source)
    vertices = family.WindowDetectorFamily.vertex_states(carrier, report)
    initial = window._read_marked(report['initial_marked_state'])
    channel._require(all(mark == window.INITIAL for mark, _, _ in initial),
                     'fresh unmarked original CEM inlet required; a prior seen bit is not an ion birth')
    phi_vertex = vertices[0, 0]
    index = (3, 0) if side == 0 else (0, 3)
    born_vertex = vertices[index]
    phi = window.forget_marks(phi_vertex['state'])
    born = {}
    for (mark, i, j), value in born_vertex['state'].items():
        if mark.clicks[side] == 1:
            native._add(born, {(i, j): value})
    old = Q(report['upstream_trace_norm_error'])
    return source, gates, {'Phi': {'state': phi, 'local_error': phi_vertex['local_error']},
                          'B': {'state': born, 'local_error': born_vertex['local_error']}}, old


def generate_rows(previous_source, detector_report, raw_reload, raw_bsm, witnesses, *, side=0, next_herald='Psi+'):
    channel._require(type(side) is int and side in (0, 1), 'original physical Alice/Bob side required')
    channel._require(next_herald in ('Psi+', 'Psi-'), 'original physical next herald required')
    channel._require(type(witnesses) is dict and set(witnesses) == {'Phi', 'B'} and
                     all(type(witnesses[name]) is dict and set(witnesses[name]) == {'reload', 'BSM'}
                         for name in witnesses),
                     'two source occupation/curve witnesses required; target response rows are not input')
    source, gates, inlets, old = _inlets(previous_source, detector_report, side)
    channel._require(type(raw_reload) is reload.JointReloadSource and type(raw_bsm) is stopped.StoppedBSMProgramme,
                     'original closed native reload and BSM sources required')
    next_reload = reload.JointReloadSource.from_record(reload.JointReloadSource.record(raw_reload))
    next_bsm = background._from_record('programme', stopped.StoppedBSMProgramme.record(raw_bsm))
    channel._require(source.seconds_per_unit == next_bsm.gate.seconds_per_unit,
                     'previous window and future BSM must share the original physical source unit')
    flows = {}
    for name, inlet in inlets.items():
        pending = {stage: {} for stage in range(reload.READY)}
        pending[0] = inlet['state']
        error = old+inlet['local_error']
        ready = native.certify(next_reload, pending, witnesses[name]['reload'],
                              seconds_per_unit=source.seconds_per_unit, upstream_error=error)
        ready_matrix = channel._read_input(ready['generated_ready_JX'], reload.DIMENSION)
        receipt = bsm_future.certify(next_bsm, ready_matrix, witnesses[name]['BSM'],
                                    upstream_error=ready['ready_trace_norm_error'])
        selected = {}
        for index, matrix in enumerate(receipt['generated_receipt_JX']):
            if bsm.PATTERNS[index][0] == next_herald:
                native._add(selected, channel._read_input(matrix, reload.DIMENSION))
        flows[name] = {'source_inlet': channel._input_record(inlet['state']),
                      'inlet_local_error': str(inlet['local_error']), 'inlet_error': str(error),
                      'reload_resolvent': ready, 'BSM_resolvent': receipt,
                      'input_mass': _mass(inlet['state'], error),
                      'future_herald_mass': _mass(selected, Q(receipt['whole_receipt_trace_norm_error']))}
    rows = {'a': flows['Phi']['input_mass'], 'b': flows['B']['input_mass'],
            'c': flows['Phi']['future_herald_mass'], 'e': flows['B']['future_herald_mass']}
    intervals = {key: _interval(value['interval']) for key, value in rows.items()}
    determinant = _sub(_mul(intervals['a'], intervals['e']), _mul(intervals['b'], intervals['c']))
    strict = determinant[0] > 0 or determinant[1] < 0
    return projected._copy({'schema': SCHEMA, 'previous_raw_window_source': source.record(),
            'original_detector_family_report': detector_report, 'source_recipe': detector_report['source_recipe'],
            'previous_window_interval': detector_report['interval'], 'seconds_per_source_unit': str(source.seconds_per_unit),
            'raw_future_reload_source': next_reload.record(), 'raw_future_BSM_source': next_bsm.record(),
            'untrusted_future_witnesses': witnesses, 'physical_current_side': side, 'physical_next_herald': next_herald,
            'constant_gate_certificate': gates, 'source_flows': flows, 'source_response_rows': rows,
            'determinant_interval': _record(determinant), 'strict_determinant_certified': strict,
            'response_equations': {'click': 'd*a + k*b', 'click_and_next_herald': 'd*c + k*e',
                                  'k': '(1-d)*eta', 'eta': '1-p00 of the original joint registration'},
            'whole_upstream_error': str(old), 'whole_error_paid_once_per_source_flow': True,
            'other_current_side_marks_forgotten': True, 'future_event_before_next_CEM_detector': True,
            'future_CEM_instrument_applied': False, 'response_rows_conditioned_on_fixed_raw_future_sources': True,
            'complete_relative_time_recipe': {'original_window_mother': detector_report['source_recipe'],
                'current_window_interval': detector_report['interval'],
                'future_reload_edges': flows['Phi']['reload_resolvent']['source_relative_time_recurrence'],
                'future_BSM_measure': flows['Phi']['BSM_resolvent']['full_relative_time_measure_recipe'],
                'B_branch_same_raw_time_recipe': True},
            'row_intervals_are_empirical_probabilities': False, 'actual_next_record_selection_certified': False,
            'generic_input_positivity_remains_original_source_contract': True,
            'actual_scalar_clock_created': False, 'literal_cohort_reconstructed': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False})


def verify_rows(report, previous_source=None):
    channel._require(type(report) is dict and report.get('schema') == SCHEMA,
                     'source next-herald response certificate required')
    source = (window.WindowCEMSource.from_record(report['previous_raw_window_source'])
              if previous_source is None else previous_source)
    channel._require(type(source) is window.WindowCEMSource and source.record() == report['previous_raw_window_source'],
                     'same original previous window source required')
    flows, rows = report['source_flows'], report['source_response_rows']
    expected_rows = {'a': flows['Phi']['input_mass'], 'b': flows['B']['input_mass'],
                     'c': flows['Phi']['future_herald_mass'], 'e': flows['B']['future_herald_mass']}
    determinant = _sub(_mul(_interval(rows['a']['interval']), _interval(rows['e']['interval'])),
                       _mul(_interval(rows['b']['interval']), _interval(rows['c']['interval'])))
    channel._require(rows == expected_rows and report['determinant_interval'] == _record(determinant) and
                     report['seconds_per_source_unit'] == str(source.seconds_per_unit),
                     'source row, coefficient or physical source unit changed')
    for name in ('Phi', 'B'):
        channel._require(flows[name]['reload_resolvent']['raw_source'] == report['raw_future_reload_source'] and
                         flows[name]['BSM_resolvent']['raw_source'] == report['raw_future_BSM_source'] and
                         flows[name]['reload_resolvent']['untrusted_occupation_witness'] == report['untrusted_future_witnesses'][name]['reload'] and
                         flows[name]['BSM_resolvent']['untrusted_occupation_witness'] == report['untrusted_future_witnesses'][name]['BSM'],
                         'source future witness or raw programme changed')
    expected = generate_rows(source, report['original_detector_family_report'],
                    reload.JointReloadSource.from_record(report['raw_future_reload_source']),
                    background._from_record('programme', report['raw_future_BSM_source']),
                    report['untrusted_future_witnesses'], side=report['physical_current_side'],
                    next_herald=report['physical_next_herald'])
    channel._require(expected == report, 'source row, coefficient, future witness, mother or time unit changed')
    return True


def inverse_intervals(rows, click_response, joint_response):
    """Conditional rational algebra only; callers must supply valid response CIs."""
    channel._require(type(rows) is dict and set(rows) == {'a', 'b', 'c', 'e'}, 'complete two source response rows required')
    a, b, c, e = (_interval(rows[key]) for key in ('a', 'b', 'c', 'e'))
    p, y = _interval(click_response), _interval(joint_response)
    determinant = _sub(_mul(a, e), _mul(b, c))
    if determinant[0] <= 0 <= determinant[1]:
        return {'status': 'determinant_unresolved', 'determinant_interval': _record(determinant),
                'actual_hardware_uniquely_identified': False}
    d = _div(_sub(_mul(p, e), _mul(b, y)), determinant)
    k = _div(_sub(_mul(a, y), _mul(p, c)), determinant)
    d, k = (max(Q(0), d[0]), min(Q(1), d[1])), (max(Q(0), k[0]), min(Q(1), k[1]))
    if d[0] > d[1] or k[0] > k[1] or d[0]+k[0] > 1:
        return {'status': 'response_domain_empty', 'determinant_interval': _record(determinant),
                'actual_hardware_uniquely_identified': False}
    d, k = (d[0], min(d[1], 1-k[0])), (k[0], min(k[1], 1-d[0]))
    eta = (k[0]/(1-d[0]), min(Q(1), k[1]/(1-d[1]))) if d[1] < 1 else (Q(0), Q(1))
    return {'status': 'physical_response_domain_enclosed', 'determinant_interval': _record(determinant),
            'background_interval': _record(d), 'detected_ionization_factor_interval': _record(k),
            'intrinsic_eta_interval': _record(eta), 'eta_unresolved_at_d_one': d[1] == 1,
            'response_uncertainty_preserved': True, 'finite_frequencies_used_as_probabilities': False,
            'actual_hardware_uniquely_identified': False}


def inverse_from_certificate(report, click_response, joint_response):
    verify_rows(report)
    rows = {key: value['interval'] for key, value in report['source_response_rows'].items()}
    result = inverse_intervals(rows, click_response, joint_response)
    return {'source_response_certificate': report, 'click_response_interval': _record(_interval(click_response)),
            'joint_response_interval': _record(_interval(joint_response)), 'inverse': result,
            'actual_response_CI_source_supplied_here': False, 'actual_parameter_domain_restricted_here': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False}
