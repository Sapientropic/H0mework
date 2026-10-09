"""Whole native reload source -> all ready receipts and unresolved continuations.

Ready restrictions and the original pending restrictions share one parent
error.  Every ready branch supplies its checked complete BSM instrument.
Receipt-relative homogeneity permits a common response on their summed quantum
measure; all original clocks, curves and native control recipes stay in the
mother.  No literal cohort is reconstructed from the numerical coimage.
"""
from fractions import Fraction as Q

import fluorescence_channel as channel
import projected_history_law as component
import projected_window_cem as projected
import stopped_history_law as stopped


SCHEMA = 'stage10-all-ready-native-source-history-CEM-law/v1'


class AllReadyHistoryLaw(stopped.StoppedHistoryLaw):
    def __init__(self, components):
        channel._require(type(components) is tuple and components and
                         all(type(item) is stopped.StoppedHistoryLaw for item in components),
                         'all original closed StoppedHistoryLaw ready components required')
        sources = tuple(stopped.StoppedHistoryLaw.from_record(item.record()) for item in components)
        self._initialize(sources)

    def _initialize(self, sources):
        first = sources[0]
        mother = first.component.mother
        parent = projected._copy(mother.parent_report)
        parent_programme = projected._copy(mother.parent_programme_record)
        model, window_source = first.hardware_record(), mother.source.record()
        indices = []
        for source in sources:
            current = source.component.mother
            channel._require(current.parent_report == parent and
                             current.parent_programme_record == parent_programme,
                             'every ready component must have the same complete native parent')
            channel._require(source.hardware_record() == model and current.source.record() == window_source,
                             'one raw hardware, full burst, shared measurement and window source required')
            indices.append(current.ready_index)
        channel._require(sorted(indices) == list(range(len(parent['ready']))),
                         'every original ready face must occur exactly once; hidden selection is forbidden')
        self.components = tuple(source for _, source in sorted(zip(indices, sources)))
        self.component = self.components[0].component
        self.parent_report, self.parent_programme_record = parent, parent_programme
        self.root_error = Q(parent['global_trace_norm_error'])
        self.time_prices = tuple(source.programme.global_time_error-self.root_error for source in self.components)
        self.terminal_prices = tuple(source.programme.global_terminal_error-self.root_error for source in self.components)
        channel._require(all(price >= 0 for price in self.time_prices+self.terminal_prices),
                         'ready BSM prices must preserve the complete common parent error')
        self.global_time_error = self.root_error+sum(self.time_prices, Q(0))
        self.global_terminal_error = self.root_error+sum(self.terminal_prices, Q(0))
        self._verified_report_snapshot = None

    def record(self):
        return projected._copy({'schema': SCHEMA, 'ready_components': [source.record() for source in self.components],
                'native_parent_programme': self.parent_programme_record,
                'complete_native_parent': self.parent_report,
                'ready_inventory': list(range(len(self.parent_report['ready']))),
                'receipt_selection': 'all original ready faces and every checked first receipt',
                'common_parent_error': str(self.root_error),
                'new_BSM_time_prices': list(map(str, self.time_prices)),
                'new_BSM_terminal_prices': list(map(str, self.terminal_prices)),
                'window_linearity': 'Phi(sum of all ready receipt measures) in the same receipt-relative clock',
                'native_pending_retained': True, 'literal_cohort_reconstructed': False,
                'all_native_ready_components_consumed': True,
                'original_unconditioned_next_record_law_certified': False,
                'complete_record_clock_square_certified': False,
                'actual_hardware_uniquely_identified': False, 'controller_advance': False})

    @classmethod
    def from_record(cls, record):
        channel._require(type(record) is dict and record.get('schema') == SCHEMA,
                         'whole original all-ready history source required')
        channel._require(type(record.get('ready_components')) is list and record['ready_components'],
                         'complete original ready component records required')
        result = object.__new__(cls)
        result._initialize(tuple(stopped.StoppedHistoryLaw.from_record(raw) for raw in record['ready_components']))
        channel._require(result.record() == record, 'whole native parent, ready inventory or source prices changed')
        return result

    def hardware_record(self):
        return projected._copy(self.component.hardware_record())

    def receipt_measure(self, restrictions=None):
        channel._require(restrictions is None or type(restrictions) in (tuple, list) and
                         len(restrictions) == len(self.components),
                         'one original receipt restriction family per ready face required')
        states, addresses = tuple({} for _ in range(4)), []
        for ready_index, source in enumerate(self.components):
            measure = source.receipt_measure(None if restrictions is None else restrictions[ready_index])
            for target, matrix in zip(states, measure['poststates']):
                projected._add(target, matrix)
            addresses.extend({'ready_index': ready_index, **item} for item in measure['component_addresses'])
        return {'poststates': states, 'component_addresses': addresses,
                'global_trace_norm_error': self.global_time_error,
                'common_parent_error_paid_once': True,
                'whole_stopped_CP_direct_sum_price_used': True,
                'component_inherited_errors_summed': False}

    def pending_tail(self):
        bsm_tails = [{'ready_index': index, **source.pending_tail()}
                     for index, source in enumerate(self.components)]
        pending = projected._copy(self.parent_report['pending'])
        matrix = component._sum([source.programme.remaining_pair for source in self.components]+
                    [channel._read_input(item['complete_matrix'], projected.reload.DIMENSION) for item in pending])
        mass, radical = projected._trace(matrix)
        raw = projected.reload.JointReloadSource.from_record(self.parent_programme_record['raw_source'])
        for face in pending:
            stage = face['stage']
            channel._require(type(stage) is int and 0 <= stage < projected.reload.READY,
                             'original pending native reload stage required')
            face['initial_counter'] = 0
            face['source_control'] = projected._copy(raw.record()['control_inventory'][stage])
        return projected._copy({'BSM_pending': bsm_tails, 'native_reload_pending': pending,
                'raw_reload_programme': self.parent_programme_record,
                'trace_center': str(mass), 'trace_radical_error': str(radical),
                'common_parent_error': str(self.root_error),
                'new_BSM_terminal_prices': list(map(str, self.terminal_prices)),
                'global_terminal_error': str(self.global_terminal_error),
                'future_receipt_mass_upper': str(max(Q(0), mass+radical+self.global_terminal_error)),
                'all_original_pending_matrices_clocks_and_controls_retained': True,
                'component_error_views_summed': False, 'common_parent_error_paid_once': True,
                'quantum_matrix_sum_role': 'trace readout only; distinct physical clocks remain in their branches',
                'source_can_fail_to_stop': True, 'fuel_exhaustion_is_terminal': False,
                'tail_center_PSD_certified': False, 'input_positive_source_required': True,
                'literal_cohort_reconstructed': False})

    def response_commutation(self):
        """Exact source generator/OR squares on the complete ready restrictions.

        Window sources are closed linear GKSL maps.  Pinching, time-ordered
        propagation, background OR and outcome restriction therefore preserve
        these sums.  Curves and error prices remain outside the exact square.
        """
        import window_cem_source as window
        measures = [source.receipt_measure() for source in self.components]
        inventory = []
        for settings in component.SETTINGS:
            source = self._window_source(settings)
            checked = 0
            for pattern in range(4):
                for mask in projected.MASKS:
                    initial = [projected.project(measure['poststates'][pattern], mask) for measure in measures]
                    marked = [{(window.INITIAL, i, j): value for (i, j), value in matrix.items()}
                              for matrix in initial]
                    summed = {}
                    for matrix in marked:
                        projected._add(summed, matrix)
                    for phase in source.phases():
                        separate = {}
                        for matrix in marked:
                            projected._add(separate, phase.action(matrix))
                        channel._require(phase.action(summed) == separate,
                                         'same raw marked generator does not preserve the ready sum')
                        checked += 1
                    separate = {}
                    for matrix in marked:
                        projected._add(separate, source.background_action(matrix))
                    channel._require(source.background_action(summed) == separate,
                                     'same raw background OR does not preserve the ready sum')
                    checked += 1
            inventory.append({'settings': list(settings), 'raw_window_source': source.record(),
                              'source_generator_and_OR_squares_checked': checked})
        return {'same_receipt_relative_origin': '0',
                'same_clock_unit': str(self.component.mother.source.seconds_per_unit),
                'complete_occupancy_projection': projected.projection_inventory(),
                'ready_restrictions_checked': len(measures), 'command_inventory': inventory,
                'closure': 'linear GKSL propagation, CP pinching/OR and classical restriction compose',
                'time_spectra_retained_in_mother': True, 'scalar_midpoint_used': False,
                'original_source_operations_checked': True}

    def _assemble(self, measure, reports, precision):
        result = super()._assemble(measure, reports, precision)
        result.update(schema=SCHEMA, common_parent_error_paid_once=True,
                      all_native_ready_components_consumed=True,
                      original_native_reload_pending_consumed=True,
                      one_source_ready_restriction_future_law_certified=False,
                      all_ready_native_source_future_law_enclosed=True,
                      linear_response_on_whole_receipt_measure_certified=True,
                      source_response_commutation=self.response_commutation())
        return result
