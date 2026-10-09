"""Complete stopped BSM instrument -> future CEM laws with an honest tail.

All first-receipt components are combined before response and normalization.
One source-time error covers that whole measure.  Remaining matter is a
positive unknown continuation, including possible nontermination; finite fuel
does not convert it to a receipt or to a fixed waiting-time law.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import sys
from types import ModuleType

import fluorescence_channel as channel
import history_prefix
import interval_prefix
import projected_history_law as component
import projected_window_cem as projected
import window_cem_source as window


SCHEMA = 'stage10-complete-stopped-history-CEM-law/v1'


def _verification_code(source):
    """Version the executed local checker closure, not the physical occurrence."""
    directory = Path(__file__).resolve().parent
    waiting = [sys.modules[__name__], sys.modules[type(source).__module__]]
    modules = {}
    while waiting:
        module = waiting.pop()
        if module.__name__ in modules:
            continue
        path = getattr(module, '__file__', None)
        if path is None or Path(path).resolve().parent != directory:
            continue
        modules[module.__name__] = module
        waiting.extend(value for value in vars(module).values() if isinstance(value, ModuleType))
        waiting.extend(sys.modules[value.__module__] for value in vars(module).values()
                       if callable(value) and getattr(value, '__module__', None) in sys.modules)
    records = []
    for name, module in sorted(modules.items()):
        bindings = []
        for label, value in sorted(vars(module).items()):
            if callable(value):
                bindings.append((label, id(value), id(getattr(value, '__code__', None)),
                                 repr(getattr(value, '__defaults__', None)), repr(getattr(value, '__kwdefaults__', None))))
                if isinstance(value, type):
                    for attribute, member in sorted(vars(value).items()):
                        functions = ((member.fget, member.fset, member.fdel) if isinstance(member, property)
                                     else (getattr(member, '__func__', member),))
                        for position, function in enumerate(functions):
                            if callable(function):
                                bindings.append((label+'.'+attribute+str(position), id(function), id(getattr(function, '__code__', None)),
                                                 repr(getattr(function, '__defaults__', None)),
                                                 repr(getattr(function, '__kwdefaults__', None))))
        path = Path(module.__file__).resolve()
        records.append((name, hashlib.sha256(path.read_bytes()).digest(), tuple(bindings)))
    operations = tuple((name, id(getattr(getattr(source, name), '__func__', getattr(source, name))))
                       for name in ('forecast', '_window', '_assemble', 'receipt_measure', 'pending_tail', 'record'))
    constants = tuple(repr(value) for value in (
        projected.bsm.PATTERNS, component.HERALDS, component.SETTINGS, window.REGISTRATION_ORDER,
        projected.MASKS, projected.reload.READY, projected.reload.WINDOW_AT, projected.reload.CAPTURE_AT,
        projected.reload.NEXT_AT, interval_prefix.CONTEXTS, interval_prefix.ORDER,
        sys.modules[interval_prefix.Directed.__module__].WEIGHTS))
    return tuple(records), operations, constants


def continuation_cursor(attempt_ordinal):
    channel._require(type(attempt_ordinal) is int and attempt_ordinal >= 0,
                     'source-generated nonnegative attempt ordinal required')
    return {'attempt_ordinal':attempt_ordinal,'next_cycle':attempt_ordinal%40+1,
            'next_block':attempt_ordinal//40,
            'last_forty_attempt_recooling_already_consumed':attempt_ordinal > 0 and attempt_ordinal%40 == 0}


class StoppedHistoryLaw:
    def __init__(self, source_component):
        channel._require(type(source_component) is component.ProjectedHistoryLaw,
                         'closed shared-hardware history component required')
        self._initialize(component.ProjectedHistoryLaw.from_record(source_component.record()))

    def _initialize(self, source_component):
        self.component = source_component
        mother = self.component.mother
        channel._require(mother.burst_ingress is not None, 'complete original stopped burst ingress required')
        self.ingress = projected._copy(mother.burst_ingress)
        face = mother.parent_report['ready'][mother.ready_index]
        self.run = projected._replay_bsm_ingress(self.ingress,
                channel._read_input(face['complete_matrix'], projected.reload.DIMENSION),
                Q(mother.parent_report['global_trace_norm_error']), Q(face['source_time']))
        self.programme = self.run.programme_result
        self._verified_report_snapshot = None

    def record(self):
        return {'schema': SCHEMA, 'source_component': self.component.record(),
                'receipt_components': len(self.programme.first_receipt_laws),
                'receipt_selection': 'all original first CP receipts; seed receipt_index does not select the law',
                'window_linearity': 'same receipt-relative CP response applied to the sum of mother measures',
                'source_time_price': 'one original global_time_error for all receipts and surviving source',
                'tail': 'full surviving matrix/time/raw programme; positive unknown continuation or no stop',
                'ready_scope': 'one source-generated ready restriction, with its complete native parent retained',
                'all_native_ready_components_consumed': False,
                'original_unconditioned_next_record_law_certified': False,
                'complete_record_clock_square_certified': False,
                'actual_hardware_uniquely_identified': False, 'controller_advance': False}

    @classmethod
    def from_record(cls, record):
        channel._require(type(record) is dict and record.get('schema') == SCHEMA,
                         'complete stopped source record required')
        result = object.__new__(cls)
        result._initialize(component.ProjectedHistoryLaw.from_record(record['source_component']))
        channel._require(result.record() == record, 'same stopped source, parent or scope required')
        return result

    def hardware_record(self):
        return self.component.hardware_record()

    def receipt_measure(self, restrictions=None):
        """Every B reads the same full mother measure; no scalar clock proxy."""
        laws = self.programme.first_receipt_laws
        channel._require(restrictions is None or type(restrictions) in (tuple, list) and len(restrictions) == len(laws),
                         'one original interval restriction per receipt component required')
        states, addresses = tuple({} for _ in range(4)), []
        for index, law in enumerate(laws):
            bounds = law.support if restrictions is None else tuple(map(Q, restrictions[index]))
            channel._require(len(bounds) == 2, 'original ordered source-time interval required')
            measure = law.interval(*bounds)
            for target, matrix in zip(states, measure['poststates']):
                projected._add(target, matrix)
            addresses.append({'receipt_index': index, 'source_support': list(map(str, law.support)),
                              'restriction': list(map(str, bounds))})
        # Original induction transports prefix error once through success-time
        # plus failure instrument.  Each step adds pre, gate/failure, return and
        # its new rate-curve price; per-component inherited errors are copies.
        return {'poststates': states, 'component_addresses': addresses,
                'global_trace_norm_error': self.programme.global_time_error,
                'whole_stopped_CP_direct_sum_price_used': True,
                'component_inherited_errors_summed': False}

    def pending_tail(self):
        mass, radical = projected._trace(self.programme.remaining_pair)
        error = self.programme.global_terminal_error
        return {**continuation_cursor(len(self.ingress['gate_certificates'])),
                'complete_matrix': channel._input_record(self.programme.remaining_pair),
                'source_time': str(self.programme.remaining_time),
                'seconds_per_source_unit': str(self.component.mother.source.seconds_per_unit),
                'trace_center': str(mass), 'trace_radical_error': str(radical),
                'global_terminal_error': str(error),
                'future_receipt_mass_upper': str(max(Q(0), mass+radical+error)),
                'raw_continuation_programme': self.ingress['raw_burst'],
                'failure_control': 'original final failure branch; continue finite bursts without re-normalization',
                'source_can_fail_to_stop': True, 'fuel_exhaustion_is_terminal': False,
                'tail_center_PSD_certified': False, 'input_positive_source_required': True}

    def _window_source(self, settings):
        programs = self.component.measurement.compile(settings)
        base = self.component.mother.source
        channel._require(self.component.measurement.detector.backgrounds == base.backgrounds,
                         'one shared raw detector source required for all commands')
        return window.WindowCEMSource(*(program.segments for program in programs),
                registrations=base.registrations, backgrounds=base.backgrounds,
                logic_deadlines=base.logic_deadlines, seconds_per_unit=base.seconds_per_unit,
                interval_start=base.interval_start)

    def _window(self, settings, measure, *, trial_provider=None, taylor_order=6,
                mode_bits=60, coefficient_bits=160, exponential_bits=160):
        source = self._window_source(settings)
        packets, extra = [], Q(0)
        for pattern, matrix in enumerate(measure['poststates']):
            for mask in projected.MASKS:
                initial = projected.project(matrix, mask)
                marked = {(window.INITIAL, i, j): value for (i, j), value in initial.items()}
                certificates = []
                if initial:
                    for phase in source.phases():
                        pieces = (projected.taylor_trials(phase, marked, order=taylor_order, mode_bits=mode_bits,
                                      coefficient_bits=coefficient_bits) if trial_provider is None else
                                  trial_provider(settings, pattern, mask, phase.index, dict(marked)))
                        report = window.certify_step(phase, marked, pieces, upstream_error=0,
                                      mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
                        marked, price = window.marked_poststate(report)
                        extra += price
                        certificates.append(report)
                    marked = source.background_action(marked)
                packets.append({'pattern_index': pattern, 'physical_herald': projected.bsm.PATTERNS[pattern][0],
                                'entering_occupancy': list(mask), 'initial_matrix': channel._input_record(initial),
                                'phase_certificates': certificates,
                                'complete_marked_matrix': window._marked_record(window._initial_marked(marked))})
        return {'settings': list(settings), 'raw_window_source': source.record(), 'packets': packets,
                'window_local_error': str(extra),
                'global_trace_norm_error': str(measure['global_trace_norm_error']+extra),
                'whole_mu_source_error_paid_once': True, 'response_before_current_outcome_selection': True}

    def _assemble(self, measure, reports, precision):
        channel._require(len(reports) == 4, 'all four source-generated command responses required')
        mu_error = full_error = Q(measure['global_trace_norm_error'])
        tail = self.pending_tail()
        tail_upper = Q(tail['future_receipt_mass_upper'])
        normalizers = []
        for herald in component.HERALDS:
            state = component._sum(matrix for index, matrix in enumerate(measure['poststates'])
                                  if projected.bsm.PATTERNS[index][0] == herald)
            mass, radical = projected._trace(state)
            error = mu_error+radical
            channel._require(mass-error > 0, 'complete stopped herald source normalizer is unresolved')
            normalizers.append((mass, error))
        rows, payments = [], []
        for settings, report in zip(component.SETTINGS, reports):
            channel._require(tuple(report['settings']) == settings and report['raw_window_source'] == self._window_source(settings).record(),
                             'same source-generated future command order required')
            payment = component._price(self.component.measurement.compile(settings), measure)
            payments.append(str(payment))
            event_error = mu_error+Q(report['window_local_error'])+payment
            for h, herald in enumerate(component.HERALDS):
                denominator, denominator_error = normalizers[h]
                for clicks in window.REGISTRATION_ORDER:
                    state = component._selected(report, herald, clicks)
                    mass, radical = projected._trace(state)
                    price = event_error+radical
                    lower = max(Q(0), (mass-price)/(denominator+denominator_error+tail_upper))
                    upper = min(Q(1), (mass+price+tail_upper)/(denominator-denominator_error))
                    channel._require(lower <= upper, 'complete first-stop/tail probability enclosure is empty')
                    rows.append({'h':h,'a':settings[0],'b':settings[1],'x':clicks[0],'y':clicks[1],
                                 'probability_interval':list(map(str,(lower,upper))),
                                 'finite_event_center':str(mass),'finite_event_error':str(price)})
        rows.sort(key=lambda row: tuple(row[k] for k in ('h','a','b','x','y')))
        table = component.ProjectedHistoryLaw._table(rows)
        return {'schema':SCHEMA,'source_record':self.record(),'whole_receipt_measure':{
                       'poststates':[channel._input_record(matrix) for matrix in measure['poststates']],
                       'component_addresses':measure['component_addresses'],
                       'global_trace_norm_error':str(full_error),
                       'component_inherited_errors_summed':False},
                'setting_reports':reports,'source_probability_enclosures':rows,
                'command_substitution_payments':payments,
                'finite_herald_normalizers':[{'center':str(m),'error':str(e)} for m,e in normalizers],
                'complete_pending_tail':tail,'precision':list(precision),'complete_contexts':len(table),
                'all_original_receipt_components_consumed':True,
                'all_current_outcomes_generated_before_selection':True,
                'finite_receipt_rows_not_renormalized_separately':True,
                'positive_unknown_tail_included_in_probability_bounds':True,
                'whole_upstream_source_time_error_paid_once':True,
                'quantum_time_measure_preserved_by_mother':True,
                'source_certain_to_eventually_stop':False,
                'one_source_ready_restriction_future_law_certified':True,
                'original_unconditioned_next_record_law_certified':False,
                'complete_record_clock_square_certified':False,
                'actual_hardware_uniquely_identified':False,'controller_advance':False}

    def forecast(self, *, trial_provider=None, taylor_order=6, mode_bits=60,
                 coefficient_bits=160, exponential_bits=160):
        measure = self.receipt_measure()
        reports = [self._window(settings,measure,trial_provider=trial_provider,taylor_order=taylor_order,
                              mode_bits=mode_bits,coefficient_bits=coefficient_bits,exponential_bits=exponential_bits)
                   for settings in component.SETTINGS]
        return self._assemble(measure,reports,(mode_bits,coefficient_bits,exponential_bits))

    def verify(self, report):
        channel._require(type(report) is dict and report.get('source_record') == self.record(),
                         'same complete source burst and hardware required')
        snapshot = channel._canonical(report), _verification_code(self)
        if getattr(self, '_verified_report_snapshot', None) == snapshot:
            return True
        channel._require(len(report['setting_reports']) == 4, 'complete future command inventory required')
        saved = {}
        for item in report['setting_reports']:
            settings = tuple(item['settings'])
            for packet in item['packets']:
                key = settings,packet['pattern_index'],tuple(packet['entering_occupancy'])
                channel._require(key not in saved, 'duplicate source command/pattern/occupancy packet')
                saved[key] = packet
        def trials(settings, pattern, mask, phase, matrix):
            return saved[settings,pattern,mask]['phase_certificates'][phase]['trial_pieces']
        fresh = type(self).from_record(report['source_record'])
        bits, coefficient_bits, exponential_bits = report['precision']
        expected = fresh.forecast(trial_provider=trials,mode_bits=bits,coefficient_bits=coefficient_bits,
                                  exponential_bits=exponential_bits)
        channel._require(expected == report, 'whole first-stop/tail law or generated probability changed')
        self._verified_report_snapshot = snapshot
        return True

    def probability_table(self, report):
        self.verify(report)
        return component.ProjectedHistoryLaw._table(report['source_probability_enclosures'])

    def seal_prediction(self, report, consumer, *, model_record):
        channel._require(type(consumer) in (history_prefix.HistoryPrefixChecker,history_prefix.HistoryPrefixes),
                         'original dual predictable-history consumer required')
        channel._require(model_record == self.hardware_record(), 'one unchanged raw hardware model required')
        table = self.probability_table(report)
        return consumer.predict(table,model_record=model_record,parent_history={
                    'complete_source':report['source_record'],'forecast_sha256':channel._digest(report)})
