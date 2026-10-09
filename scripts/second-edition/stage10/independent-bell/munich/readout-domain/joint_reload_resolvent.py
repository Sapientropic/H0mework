"""Native six-stage reload absorption from source contraction and a residual.

Occupation matrices and their window curves are untrusted proposals.  The
original shared-counter checker generates both KX and JX.  The complete
time measure remains the native transition recipe; its integral is not an
actual scalar clock or a reconstructed literal trap cohort.
"""
from fractions import Fraction as Q
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import bsm_background_tail as background
import fluorescence_channel as channel
import joint_fluorescence_presence as joint
import joint_reload_source as reload


CONTRACTION_SCHEMA = 'stage10-native-joint-reload-background-contraction/v1'
WITNESS_SCHEMA = 'stage10-native-joint-reload-occupation-witness/v1'
SCHEMA = 'stage10-native-joint-reload-resolvent/v1'
CONSUMER_SCHEMA = 'stage10-complete-posterior-native-reload-absorption/v1'


def _copy(value):
    return json.loads(channel._canonical(value))


def _add(target, matrix, factor=1):
    for key, value in matrix.items():
        joint.local._add(target, key, value*factor)


def _entry_norm_upper(matrix, bits):
    total = Q(0)
    for value in matrix.values():
        for part in (value.real, value.imag):
            middle, radius = full.radical_midpoint(part, bits)
            total += abs(middle)+radius
    return total


def _source(value):
    channel._require(type(value) is reload.JointReloadSource,
                     'closed original JointReloadSource required; a threshold tuple is not a source')
    return reload.JointReloadSource.from_record(reload.JointReloadSource.record(value))


def _window_law(window):
    atoms = [background._atomic_law(atom) for atom in window.sources]
    optical = []
    for item in window.collection_record:
        transfer = tuple(tuple(background._complex(v) for v in row) for row in item['matrix'])
        _, gram, complement = joint.passive_transfer(transfer)
        label = tuple(item['label'])
        channel._require(window.undetected_grams[label] == complement and
                         all(gram[i][j]+complement[i][j] == dipole.ComplexRadical(int(i == j))
                             for i in range(6) for j in range(6)),
                         'native observed/unobserved full-pair Gram completeness failed')
        optical.append({'label': list(label), 'passive_complement_schur': background._schur(complement)})
    raw = window.record()
    raw['background_rate'] = '0'
    without = joint.JointCounterGenerator.from_record(raw)
    # The operator identity of the native BG leg is independent of these
    # coordinates.  These include complex coherence and the Empty coordinate.
    matrix = {(0, 0): dipole.ComplexRadical(Q(1, 3)),
              (0, reload.DIMENSION-1): dipole.ComplexRadical(Q(2, 7), Q(3, 5)),
              (reload.DIMENSION-1, 0): dipole.ComplexRadical(Q(2, 7), Q(-3, 5))}
    checks = []
    for count in sorted({0, window.threshold-1, window.threshold}):
        state = window.lift(matrix, counter=count)
        difference = window.action(state)
        _add(difference, without.action(state), -1)
        target = min(count+1, window.threshold)
        expected = {}
        _add(expected, {(count, i, j): v for (i, j), v in matrix.items()}, -window.background_rate)
        _add(expected, {(target, i, j): v for (i, j), v in matrix.items()}, window.background_rate)
        channel._require(difference == expected,
                         'original shared background is not the scalar quantum identity counter leg')
        checks.append({'count': count, 'target': target})
    return {'atomic_trace_laws': atoms, 'passive_environment_groups': optical,
            'counter_rule': 'min(c+1,N); detected photons and independent shared BG never decrease c',
            'background_generator': 'b*(counter_shift-identity) tensor quantum_identity',
            'background_count_probes': checks,
            'quantum_counter_source': 'observed Kraus jumps plus passive unobserved complement; original independent atom baths',
            'background_clock': 'one independent Poisson driver in the original raw window',
            'local_capture_backgrounds_used': False}


def _capture_laws(source):
    results = []
    for side, capture in enumerate(source.captures):
        operators = []
        for ground in reload.GROUND:
            amplitude = capture.couplings[ground]*dipole.sqrt_rational(capture.occupations[ground])
            expected = {(dipole.INDEX[ground], reload.EMPTY): amplitude} if amplitude else {}
            channel._require(capture.birth_operators[ground] == expected,
                             'original capture Kraus operator differs from its raw reservoir source')
            loss = dipole.matrix_product(dipole.matrix_adjoint(expected), expected)
            rate = capture.occupations[ground]*(capture.couplings[ground].real*capture.couplings[ground].real+
                                                capture.couplings[ground].imag*capture.couplings[ground].imag)
            channel._require(loss == ({(reload.EMPTY, reload.EMPTY): dipole.ComplexRadical(rate)} if rate else {}),
                             'capture recycling/loss identity failed')
            operators.append({'ground': dipole.INDEX[ground], 'jump': channel._input_record(expected),
                              'loss': channel._input_record(loss)})
        results.append({'side': side, 'raw_jump_operators': operators,
                        'counter_operation': 'identity; enabled capture is CPTP on the quantum leg at every count'})
    return results


def _time_edges(source, unit):
    return [{'stage': stage, 'raw_window': reload.WINDOW_AT[stage],
             'duration': str(source._window(stage).duration),
             'physical_duration_seconds': str(source._window(stage).duration*unit),
             'low_next': source._next(stage, False), 'high_next': source._next(stage, True),
             'capture_enabled': list(reload.CAPTURE_AT[stage]), 'pending_counter_reset': 0}
            for stage in range(reload.READY)]


def certify_contraction(raw_source, *, seconds_per_unit=1, background_seconds_per_unit=None):
    source = _source(raw_source)
    unit = full.exact(seconds_per_unit)
    channel._require(unit > 0, 'positive raw source physical time unit required')
    bg_unit = unit if background_seconds_per_unit is None else full.exact(background_seconds_per_unit)
    channel._require(bg_unit == unit, 'shared background and native windows must use the same source unit')
    windows, delta = [], Q(1)
    for index, window in enumerate(source.windows):
        x, n = window.background_rate*window.duration, window.threshold
        one = x/(n+x)
        high = one**n
        delta *= high
        windows.append({'raw_window': index, 'threshold': n, 'duration': str(window.duration),
                        'raw_shared_background_rate': str(window.background_rate),
                        'Poisson_parameter': str(x), 'subinterval_duration': str(window.duration/n),
                        'at_least_one_BG_per_subinterval_lower': str(one),
                        'high_count_probability_lower': str(high),
                        'high_count_probability_lower_expression': {'base': str(one), 'exponent': n},
                        'native_source_law': _window_law(window)})
    paths = []
    for start in range(reload.READY):
        stage, stages = start, []
        while stage != reload.READY and len(stages) < 3:
            stages.append(stage)
            stage = source._next(stage, True)
        channel._require(stage == reload.READY,
                         'the original all-high native control path does not reach Ready in three windows')
        paths.append({'start_stage': start, 'high_stages': stages,
                      'raw_windows': [reload.WINDOW_AT[s] for s in stages], 'terminal_stage': stage})
    positive = delta > 0
    return {'schema': CONTRACTION_SCHEMA, 'raw_source': source.record(),
            'seconds_per_source_unit': str(unit), 'background_seconds_per_unit': str(bg_unit),
            'windows': windows, 'capture_laws': _capture_laws(source), 'all_high_paths': paths,
            'three_window_absorption_lower': str(delta), 'three_window_pending_operator_upper': str(1-delta),
            'inverse_trace_norm_upper': str(3/delta) if positive else None,
            'status': 'strict_native_pending_contraction' if positive else 'no_positive_all_high_background_path',
            'source_bound': 'K^3 effect <= (1-delta)I on every positive six-stage full-pair input',
            'inverse_bound': 'sum K^n=(I-K)^-1; group triples to obtain trace-norm upper 3/delta',
            'Poisson_bound': 'exp(x/N)>=1+x/N; one BG in each of N disjoint subintervals suffices',
            'time_edges': _time_edges(source, unit), 'source_bindings': reload._bindings(source),
            'target_stopping_probability_supplied': False, 'target_failure_effect_supplied': False,
            'numerical_centres_assumed_positive': False, 'actual_background_calibrated': False,
            'actual_clock_identified': False, 'actual_hardware_uniquely_identified': False, 'controller_advance': False}


def verify_contraction(report, raw_source=None):
    channel._require(type(report) is dict and report.get('schema') == CONTRACTION_SCHEMA,
                     'native reload source contraction certificate required')
    source = reload.JointReloadSource.from_record(report['raw_source']) if raw_source is None else _source(raw_source)
    channel._require(source.record() == report['raw_source'], 'same complete raw reload source required')
    expected = certify_contraction(source, seconds_per_unit=report['seconds_per_source_unit'],
                                   background_seconds_per_unit=report['background_seconds_per_unit'])
    channel._require(expected == report, 'native reload contraction source, time unit or control changed')
    return True


def _blocks(matrices):
    channel._require(type(matrices) is dict and all(type(s) is int for s in matrices) and
                     set(matrices) == set(range(reload.READY)),
                     'complete six pending stage matrices required')
    return {stage: channel._initial(matrices[stage], reload.DIMENSION) for stage in range(reload.READY)}


def _read_blocks(records):
    channel._require(type(records) is list and len(records) == reload.READY,
                     'complete ordered six-stage matrix record required')
    result = {}
    for stage, item in enumerate(records):
        channel._require(type(item) is dict and set(item) == {'stage', 'complete_matrix'} and
                         type(item['stage']) is int and item['stage'] == stage,
                         'canonical pending stage order required')
        result[stage] = channel._read_input(item['complete_matrix'], reload.DIMENSION)
    return result


def _block_record(blocks):
    return [{'stage': stage, 'complete_matrix': channel._input_record(blocks[stage])}
            for stage in range(reload.READY)]


def certify(raw_source, initial_pending, witness, *, seconds_per_unit=1, upstream_error=0):
    source, rho = _source(raw_source), _blocks(initial_pending)
    contraction = certify_contraction(source, seconds_per_unit=seconds_per_unit)
    channel._require(Q(contraction['three_window_absorption_lower']) > 0,
                     'no positive native BG contraction; the original pending tail must remain')
    channel._require(type(witness) is dict and set(witness) == {'schema', 'occupation', 'precision'} and
                     witness['schema'] == WITNESS_SCHEMA,
                     'occupation matrices and raw trial curves only; a target Ready matrix is not a witness')
    channel._require(type(witness['occupation']) is list and len(witness['occupation']) == reload.READY,
                     'all six occupation stage witnesses required')
    precision = witness['precision']
    channel._require(type(precision) is list and len(precision) == 3, 'original window checker precision triple required')
    mode_bits, coefficient_bits, exponential_bits = precision
    pending, ready, occupations, certificates = {s: {} for s in range(reload.READY)}, {}, {}, []
    local_error = Q(0)
    for stage, item in enumerate(witness['occupation']):
        channel._require(type(item) is dict and set(item) == {'stage', 'complete_matrix', 'trial_pieces'} and
                         type(item['stage']) is int and item['stage'] == stage,
                         'ordered complete raw occupation curve required')
        matrix = channel._read_input(item['complete_matrix'], reload.DIMENSION)
        occupations[stage] = matrix
        certificate = reload.certify_window(source, matrix, item['trial_pieces'], stage=stage, upstream_error=0,
                            mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
        local_error += Q(certificate['trace_norm_error_bound'])
        endpoint = {(stage, c, i, j): dipole.ComplexRadical(Q(a), Q(b))
                    for c, i, j, a, b in certificate['counter_poststate_center']}
        for branch in source.projected_window_end(endpoint).values():
            for (following, counter, i, j), value in branch.items():
                channel._require(following == reload.READY or counter == 0,
                                 'native pending boundary must reset the original shared counter')
                _add(ready if following == reload.READY else pending[following], {(i, j): value})
        certificates.append(certificate)
    residual = {}
    for stage in range(reload.READY):
        residual[stage] = dict(rho[stage])
        _add(residual[stage], pending[stage])
        _add(residual[stage], occupations[stage], -1)
    residual_norm = sum((_entry_norm_upper(matrix, coefficient_bits) for matrix in residual.values()), Q(0))
    amplification = Q(contraction['inverse_trace_norm_upper'])
    inherited = full.nonnegative(upstream_error)
    occupation_error = amplification*(inherited+residual_norm+local_error)
    numerical_error = residual_norm+local_error
    # F=JR=sum J K^n is CPTP: trace telescopes and K^n vanishes by
    # the raw contraction.  Hence ||F r+F e_K+e_J|| <= ||r||+E_joint.
    # This pays the joint endpoint price once and avoids amplifying final
    # Ready flux by the occupation resolvent norm.
    return _copy({'schema': SCHEMA, 'raw_source': source.record(),
            'seconds_per_source_unit': str(full.exact(seconds_per_unit)), 'source_contraction': contraction,
            'initial_pending': _block_record(rho), 'untrusted_occupation_witness': witness,
            'window_certificates': certificates, 'generated_pending_KX': _block_record(pending),
            'generated_ready_JX': channel._input_record(ready), 'residual': _block_record(residual),
            'residual_entry_norm_upper': str(residual_norm), 'joint_KX_JX_window_error': str(local_error),
            'inverse_trace_norm_upper': str(amplification), 'occupation_trace_norm_error': str(occupation_error),
            'new_resolvent_ready_error': str(numerical_error),
            'upstream_trace_norm_error': str(inherited), 'ready_trace_norm_error': str(inherited+numerical_error),
            'residual_equation': 'X=rho+KX on the complete six-stage pending direct sum',
            'ready_law': 'J(I-K)^-1 rho; all ready flux, not occupancy-conditioned flux',
            'occupation_error_rule': '(3/delta)*(upstream + residual_center_norm + joint_window_error)',
            'error_rule': 'upstream + residual_center_norm + joint_window_error; complete Ready absorption is CPTP',
            'whole_input_error_transport': 'complete future absorption is CPTP; upstream error is paid once without inverse amplification',
            'source_relative_time_recurrence': contraction['time_edges'],
            'ready_matrix_is_time_integrated': True, 'time_resolved_numerical_measure_certified': False,
            'numerical_centres_assumed_CP': False, 'input_positivity_certified_here': False,
            'target_ready_matrix_supplied': False, 'solver_reexecuted_by_checker': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False})


def verify_certificate(report, raw_source=None, initial_pending=None):
    channel._require(type(report) is dict and report.get('schema') == SCHEMA, 'native reload resolvent certificate required')
    source = reload.JointReloadSource.from_record(report['raw_source']) if raw_source is None else _source(raw_source)
    channel._require(source.record() == report['raw_source'], 'same original reload source required')
    rho = _read_blocks(report['initial_pending']) if initial_pending is None else _blocks(initial_pending)
    channel._require(_block_record(rho) == report['initial_pending'], 'same complete pending source state required')
    expected = certify(source, rho, report['untrusted_occupation_witness'],
                       seconds_per_unit=report['seconds_per_source_unit'], upstream_error=report['upstream_trace_norm_error'])
    channel._require(expected == report, 'source occupation residual, full Ready flux or error changed')
    return True


def _continuation(value, report):
    import projected_reload_continuation as continuation
    channel._require(type(value) is continuation.ProjectedReloadContinuation,
                     'closed verified posterior reload continuation required; a pending matrix is not a source')
    record = continuation.ProjectedReloadContinuation.record(value)
    # Reconstruct only this small action inlet.  Reuse the verified posterior;
    # do not rerun its forward producer.  Fresh methods cannot be replaced by
    # instance callbacks on the incoming object.
    fresh = continuation.ProjectedReloadContinuation(value.posterior,
                    reload.JointReloadSource.from_record(record['raw_joint_source']))
    channel._require(continuation.ProjectedReloadContinuation.record(fresh) == record,
                     'posterior reload hardware, inlet matrix, root price or relative clock changed')
    continuation.ProjectedReloadContinuation.verify(fresh, report)
    return fresh, record


def absorb_continuation(continuation, native_report, witness):
    source, record = _continuation(continuation, native_report)
    pending, finite_ready = {s: {} for s in range(reload.READY)}, {}
    for face in native_report['pending']:
        stage = face['stage']
        channel._require(type(stage) is int and 0 <= stage < reload.READY,
                         'all original pending stage faces required')
        _add(pending[stage], channel._read_input(face['complete_matrix'], reload.DIMENSION))
    for face in native_report['ready']:
        channel._require(face['stage'] == reload.READY, 'the original finite Ready faces must retain their native stage')
        _add(finite_ready, channel._read_input(face['complete_matrix'], reload.DIMENSION))
    inherited = Q(native_report['global_trace_norm_error'])
    proof = certify(source.source, pending, witness, seconds_per_unit=source.seconds_per_unit,
                    upstream_error=inherited)
    total = dict(finite_ready)
    _add(total, channel._read_input(proof['generated_ready_JX'], reload.DIMENSION))
    mother = record['source_inlet']['time_state_mother_record']
    return _copy({'schema': CONSUMER_SCHEMA, 'source_record': record,
            'original_native_report': native_report, 'source_resolvent': proof,
            'original_finite_ready': channel._input_record(finite_ready),
            'complete_future_ready_matrix': channel._input_record(total),
            'global_trace_norm_error': proof['ready_trace_norm_error'],
            'old_whole_error_paid_once': str(inherited),
            'new_resolvent_ready_error': proof['new_resolvent_ready_error'],
            'time_state_mother_record': mother,
            'complete_relative_time_measure_recipe': {
                'original_ready_faces': native_report['ready'], 'original_pending_faces': native_report['pending'],
                'raw_source': proof['raw_source'], 'native_time_edges': proof['source_relative_time_recurrence'],
                'measure': 'preserve finite Ready; from each pending time restriction apply J K^n for every n>=0 with each native window shift',
                'Laplace_recipe': 'J(z)*(I-K(z))^-1; every low/high CP edge is multiplied by exp(-z*its raw duration)',
                'convergence': 'the original all-high BG path bounds pending after each triple by (1-delta)^n',
                'mother_action': 'apply the same raw CP edge action to every original mother time restriction'},
            'native_pending_absorbed_by_same_source': True, 'all_original_ready_and_pending_faces_consumed': True,
            'complete_future_ready_state_enclosed': True, 'ready_matrix_is_time_integrated': True,
            'time_resolved_numerical_measure_certified': False,
            'clock_scope': 'receipt-relative homogeneous native source; actual timestamp spectrum remains in the mother',
            'actual_scalar_clock_created': False, 'scalar_midpoint_used': False,
            'literal_cohort_reconstructed': False, 'ready_implies_actual_double_occupancy': False,
            'physical_probability_interpretation': 'positive complete posterior propagated by the original whole absorption CPTP map',
            'actual_hardware_uniquely_identified': False, 'controller_advance': False})


def verify_absorption(report, continuation=None):
    import projected_reload_continuation as native
    channel._require(type(report) is dict and report.get('schema') == CONSUMER_SCHEMA,
                     'same-posterior native absorption certificate required')
    source = native.ProjectedReloadContinuation.from_record(report['source_record']) if continuation is None else continuation
    expected = absorb_continuation(source, report['original_native_report'],
                                   report['source_resolvent']['untrusted_occupation_witness'])
    channel._require(expected == report, 'same mother, whole price, complete Ready output or original time measure changed')
    return True
