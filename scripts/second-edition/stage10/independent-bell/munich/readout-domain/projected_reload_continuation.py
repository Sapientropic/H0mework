"""Verified full-history posterior -> the same native joint reload action.

The numerical inlet is the source's complete stage/counter/pair coimage.
Receipt-time spectra remain in the posterior mother; native window durations
only add a common relative shift.  No atom epoch or literal TrapHistory is
constructed from an Empty coordinate.
"""
from fractions import Fraction as Q

import atomic_dipole as dipole
import fluorescence_channel as channel
import joint_reload_programme as programme
import joint_reload_source as reload
import projected_window_cem as projected


SCHEMA = 'stage10-posterior-native-reload-continuation/v1'


def _posterior_class(posterior):
    import complete_history_posterior as history
    import window_posterior_support as support
    kind = type(posterior)
    channel._require(kind in (history.CompleteHistoryPosterior, support.SupportedHistoryPosterior),
                     'closed verified complete-history posterior required; target matrices are not input')
    return kind


class ProjectedReloadContinuation:
    def __init__(self, posterior, raw_joint_source=None):
        kind = _posterior_class(posterior)
        kind.verify(posterior)
        raw = posterior.source.hardware_record()['raw_reload']
        source = reload.JointReloadSource.from_record(raw['raw_source']) if raw_joint_source is None else raw_joint_source
        channel._require(type(source) is reload.JointReloadSource and source.record() == raw['raw_source'],
                         'the posterior and next reload must share the complete original hardware source')
        self.posterior = posterior
        self.source = reload.JointReloadSource.from_record(source.record())
        self.seconds_per_unit = Q(raw['seconds_per_source_unit'])
        self._posterior_record = projected._copy(kind.record(posterior))
        self._inlet = self._read_inlet()

    def _read_inlet(self):
        kind = _posterior_class(self.posterior)
        kind.verify(self.posterior)
        channel._require(kind.record(self.posterior) == self._posterior_record,
                         'the original observed posterior or history source changed')
        inlet = kind.next_reload_input(self.posterior, self.source)
        kind.verify(self.posterior)
        channel._require(inlet['source_posterior'] is self.posterior,
                         'next action must retain the actual verified posterior mother')
        state = inlet['state']
        self.source._projected_blocks(state)
        channel._require(all(key[:2] == (0, 0) for key in state),
                         'original post-CEM native diagnostic and reset counter required')
        matrix = {}
        for (_, _, i, j), value in state.items():
            projected._add(matrix, {(i, j): dipole.complex_exact(value)})
        matrix = channel._initial(matrix, reload.DIMENSION)
        error = Q(inlet['upstream_trace_norm_error'])
        channel._require(error >= 0, 'retained whole posterior trace-norm error required')
        record = self._posterior_record
        expected_matrix = record.get('normalized_center', record.get('normalized_coimage'))
        expected_error = (record['normalizer']['posterior_trace_norm_error'] if 'normalizer' in record
                          else record['trace_norm_error'])
        mother = record.get('time_state_mother_record', record.get('unresolved_time_state_mother'))
        channel._require(channel._input_record(matrix) == expected_matrix and error == Q(expected_error) and
                         inlet['time_state_mother_record'] == mother and
                         Q(inlet['source_relative_start']) == Q(mother['common_response_end_shift']) and
                         Q(inlet['seconds_per_source_unit']) == self.seconds_per_unit,
                         'native inlet must equal the same sealed posterior state, price and time mother')
        result = {'complete_matrix': channel._input_record(matrix), 'upstream_trace_norm_error': str(error),
                'source_relative_start': str(Q(inlet['source_relative_start'])),
                'time_state_mother_record': projected._copy(inlet['time_state_mother_record']),
                'cohort_reconstructed': False}
        if 'source_support_proof' in inlet:
            result.update(source_support_proof=projected._copy(inlet['source_support_proof']),
                          exact_rank_one_coimage_generated=inlet['exact_rank_one_coimage_generated'],
                          parent_unknown_tail_and_price_retained=inlet['parent_unknown_tail_and_price_retained'])
        return result

    def record(self):
        return projected._copy({'schema': SCHEMA, 'original_posterior': self._posterior_record,
                    'raw_joint_source': self.source.record(), 'seconds_per_source_unit': str(self.seconds_per_unit),
                    'source_inlet': self._inlet,
                    'clock': 'original posterior time/state measure plus generated relative window durations',
                    'native_control': 'same stage/shared-counter source; each pending boundary resets its count',
                    'arbitrary_initial_matrix_allowed': False, 'literal_cohort_reconstructed': False,
                    'actual_hardware_uniquely_identified': False, 'controller_advance': False})

    def hardware_record(self):
        return projected._copy(self.posterior.source.hardware_record())

    @classmethod
    def from_record(cls, record):
        import complete_history_posterior as history
        import window_posterior_support as support
        channel._require(type(record) is dict and record.get('schema') == SCHEMA,
                         'closed observed-posterior native continuation record required')
        raw = record['original_posterior']
        kind = {history.SCHEMA: history.CompleteHistoryPosterior,
                support.SCHEMA: support.SupportedHistoryPosterior}.get(raw.get('schema'))
        channel._require(kind is not None, 'closed named posterior source record required')
        posterior = kind.from_record(raw)
        source = reload.JointReloadSource.from_record(record['raw_joint_source'])
        result = cls(posterior, source)
        channel._require(result.record() == record,
                         'original posterior, native hardware, time mother or source inlet changed')
        return result

    def run(self, *, windows, trial_provider=None, taylor_order=6,
            mode_bits=60, coefficient_bits=160, exponential_bits=160):
        channel._require(type(windows) is int and windows >= 0, 'finite nonnegative native window count required')
        inlet = self._read_inlet()
        channel._require(inlet == self._inlet, 'posterior source state, time spectrum or error changed')
        source = reload.JointReloadSource.from_record(self.source.record())
        matrix = channel._read_input(inlet['complete_matrix'], reload.DIMENSION)
        origin = Q(inlet['source_relative_start'])
        channel._require(origin >= 0, 'receipt-relative response end must be nonnegative')
        pending, ready, steps = {(0, origin): matrix}, {}, []
        local_error = Q(0)
        inherited = Q(inlet['upstream_trace_norm_error'])
        for depth in range(windows):
            following, level = {}, []
            for (stage, elapsed), state in sorted(pending.items()):
                if not state:
                    continue
                pieces = (programme.taylor_trials(source, stage, state, order=taylor_order,
                                mode_bits=mode_bits, coefficient_bits=coefficient_bits) if trial_provider is None
                          else trial_provider(depth, stage, elapsed, dict(state)))
                certificate = reload.certify_window(source, state, pieces, stage=stage, upstream_error=0,
                                mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
                end = elapsed+Q(certificate['duration'])
                local_error += Q(certificate['trace_norm_error_bound'])
                endpoint = {(stage, counter, i, j): dipole.ComplexRadical(Q(a), Q(b))
                            for counter, i, j, a, b in certificate['counter_poststate_center']}
                outputs = source.projected_window_end(endpoint)
                for values in outputs.values():
                    for (next_stage, counter, i, j), value in values.items():
                        if next_stage == reload.READY:
                            target = ready.setdefault(end, {})
                        else:
                            channel._require(counter == 0, 'native pending boundary must reset its shared counter')
                            target = following.setdefault((next_stage, end), {})
                        projected._add(target, {(i, j): value})
                level.append({'depth': depth, 'stage': stage, 'relative_start': str(elapsed),
                              'relative_end': str(end), 'certificate': certificate,
                              'native_control': projected._copy(source.record()['control_inventory'][stage])})
            pending = following
            steps.append(level)
        total = component_sum(list(ready.values())+list(pending.values()))
        before, eb = projected._trace(matrix)
        after, ea = projected._trace(total)
        channel._require(abs(after-before) <= local_error+eb+ea,
                         'complete ready/pending source trace excludes the original posterior')
        global_error = inherited+local_error
        def face(stage, elapsed, state):
            mass, radical = projected._trace(state)
            return {'stage': stage, 'relative_window_elapsed': str(elapsed-origin),
                    'source_time': str(elapsed), 'source_relative_time': str(elapsed),
                    'source_time_is_receipt_relative': True,
                    'clock_scope': 'relative to each original receipt; actual time remains in the mother spectrum',
                    'relative_physical_elapsed_seconds': str((elapsed-origin)*self.seconds_per_unit),
                    'time_state_mother_record': inlet['time_state_mother_record'],
                    'time_state_transport': 'apply this native source action to every original mother time restriction, then shift by elapsed',
                    'actual_scalar_clock_created': False, 'complete_matrix': channel._input_record(state),
                    'trace_center': str(mass),
                    'trace_bounds_using_shared_error': [str(mass-global_error-radical), str(mass+global_error+radical)]}
        return projected._copy({'schema': SCHEMA, 'source_record': self.record(), 'windows_observed': windows,
                    'steps': steps, 'ready': [face(reload.READY, t, state) for t, state in sorted(ready.items())],
                    'pending': [face(stage, t, state) for (stage, t), state in sorted(pending.items())],
                    'input_trace_center': str(before), 'ready_plus_pending_trace_center': str(after),
                    'upstream_trace_norm_error': str(inherited), 'new_local_residual_error': str(local_error),
                    'global_trace_norm_error': str(global_error),
                    'precision': [mode_bits, coefficient_bits, exponential_bits],
                    'whole_posterior_error_paid_once': True, 'all_pending_branches_retained': True,
                    'original_time_spectrum_retained': True, 'scalar_midpoint_used': False,
                    'literal_cohort_reconstructed': False, 'ready_implies_actual_double_occupancy': False,
                    'fuel_exhaustion_is_terminal': False, 'solver_reexecuted_by_checker': False,
                    'actual_hardware_uniquely_identified': False, 'controller_advance': False})

    def verify(self, report):
        channel._require(type(report) is dict and report.get('source_record') == self.record(),
                         'same observed posterior and original reload hardware required')
        cursor = iter(item for level in report['steps'] for item in level)
        def trials(depth, stage, elapsed, matrix):
            item = next(cursor, None)
            channel._require(item is not None and (item['depth'], item['stage'], Q(item['relative_start'])) ==
                             (depth, stage, elapsed), 'complete native source window order required')
            return item['certificate']['trial_pieces']
        bits, coefficient_bits, exponential_bits = report['precision']
        expected = self.run(windows=report['windows_observed'], trial_provider=trials,
                            mode_bits=bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
        channel._require(next(cursor, None) is None and expected == report,
                         'posterior source continuation, complete pending or time recipe changed')
        return True


def component_sum(matrices):
    result = {}
    for matrix in matrices:
        projected._add(result, matrix)
    return result
