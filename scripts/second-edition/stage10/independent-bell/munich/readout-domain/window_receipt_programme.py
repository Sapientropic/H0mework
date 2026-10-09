"""First BSM time/state law -> window-resolved CEM -> native joint reload.

Every interval consumes the original matrix-valued receipt measure.  The
receipt-relative waveform is time homogeneous, so this preserves the whole
time law rather than replacing it with a support box and terminal density.
"""
from dataclasses import dataclass
from fractions import Fraction as Q

import atomic_dipole as dipole
import atomic_full_forward as full
import certified_bsm_programme as certified
import fluorescence_channel as channel
import receipt_triggered_programme as response
import window_cem_source as window


@dataclass(frozen=True)
class Interval:
    raw_source: dict
    receipt_interval: tuple
    reports: tuple
    global_trace_norm_error: Q
    receipt_trace_norm_error: Q
    local_response_trace_norm_error: Q


@dataclass(frozen=True)
class TrapImage:
    source_interval: Interval
    branches: tuple
    global_trace_norm_error: Q


def polynomial_trials(source, initial, histories, order):
    channel._require(type(order) is int and 0 <= order <= 64, 'finite untrusted polynomial order required')
    matrix, families = source.lift(initial, trap_histories=histories), []
    quantum = 1 << 60
    for phase in source.phases():
        kernel = window.SourceKernel(phase)
        coefficients = {(window.mark_index(mark), i, j): tuple(full.radical_midpoint(part, 160)[0]
                         for part in (value.real, value.imag)) for (mark, i, j), value in matrix.items()}
        polynomial = []
        for degree in range(order+1):
            polynomial.append([[c, i, j, round(a*quantum), round(b*quantum)]
                               for (c, i, j), (a, b) in sorted(coefficients.items())
                               if round(a*quantum) or round(b*quantum)])
            coefficients = {key: (a*phase.duration/(degree+1), b*phase.duration/(degree+1))
                            for key, (a, b) in kernel.action(coefficients).items()}
        pieces = [{'duration': str(phase.duration), 'modes': [{'lambda': [0, 0], 'coefficients': polynomial}]}]
        report = window.certify_step(phase, matrix, pieces)
        matrix, _ = window.marked_poststate(report)
        families.append(pieces)
    return families


class WindowReceiptProgramme:
    def __init__(self, receipt_law, source, *, trap_histories, source_journal=()):
        channel._require(type(receipt_law) is certified.ReceiptMeasure and type(source) is window.WindowCEMSource,
                         'original receipt law and closed raw window source required')
        self.law = certified.ReceiptMeasure(receipt_law.certificate, full.exact(receipt_law.start_time),
                                           full.nonnegative(receipt_law.inherited_error))
        self.law.interval()
        self.source = window.WindowCEMSource.from_record(source.record())
        parent = window.cem._histories(trap_histories)
        self.histories = window._read_histories(list(parent))
        channel._require(self.source.interval_start == 0, 'waveform must use the original receipt as its relative origin')
        from bsm_retry_source import BSMSource
        original = BSMSource.from_record(self.law.certificate['raw_source'])
        channel._require(original.seconds_per_unit == self.source.seconds_per_unit,
                         'receipt and window response must share the same physical time unit')
        channel._require(type(source_journal) is tuple, 'immutable source journal required')
        self.journal = source_journal
        self.public_control_binding = None

    @classmethod
    def from_public_response(cls, raw_response, registrations, settings):
        channel._require(type(raw_response) is response.ReceiptTriggeredProgramme,
                         'original source-owned public timing response required')
        first, second = raw_response.measurement.compile(settings)
        events = raw_response.timing.events()
        unit = raw_response.timing.seconds_per_unit
        channel._require(type(registrations) is tuple and len(registrations) == 2, 'two raw side registration sources required')
        for side, registration in enumerate(registrations):
            record = window.FragmentRegistration.from_record(registration.record())
            channel._require(record.electron_window[1]-record.electron_window[0] == (240 if side == 0 else 160)*response.NS/unit and
                             record.ion_window[1]-record.ion_window[0] == (240 if side == 0 else 220)*response.NS/unit and
                             record.ion_window[1] == events[side]['ion_acceptance_window_closes'],
                             'raw fragment windows differ from the registered SI lengths or ion endpoint')
        source = window.WindowCEMSource(first.segments, second.segments, registrations=registrations,
                      backgrounds=raw_response.measurement.detector.backgrounds,
                      logic_deadlines=tuple(side['CEM_logic_deadline'] for side in events), seconds_per_unit=unit)
        result = cls(raw_response.law, source, trap_histories=raw_response.histories,
                     source_journal=raw_response.journal)
        result.public_control_binding = {'raw_response': raw_response.record(), 'settings': list(settings)}
        return result

    def record(self):
        return {'schema': 'stage10-first-receipt-window-response-source/v1',
                'receipt_law': {'certificate': self.law.certificate, 'start_time': str(self.law.start_time),
                                'inherited_error': str(self.law.inherited_error)},
                'raw_window_source': self.source.record(), 'trap_histories': list(window.cem._histories(self.histories)),
                'public_control_binding': self.public_control_binding,
                'source_journal': list(self.journal), 'time_restriction': 'Phi(mu(B)) for every original interval B',
                'response_depends_on_absolute_receipt_time': False, 'legacy_effective_eta_reapplied': False,
                'actual_complete_record_square_certified': False, 'actual_hardware_uniquely_identified': False,
                'controller_advance': False}

    @classmethod
    def from_record(cls, record):
        channel._require(type(record) is dict and record.get('schema') == 'stage10-first-receipt-window-response-source/v1',
                         'closed receipt/window source record required')
        law = record['receipt_law']
        control = record['public_control_binding']
        raw = window.WindowCEMSource.from_record(record['raw_window_source'])
        if control is None:
            source = cls(certified.ReceiptMeasure(law['certificate'], Q(law['start_time']), Q(law['inherited_error'])),
                         raw, trap_histories=window._read_histories(record['trap_histories']),
                         source_journal=tuple(record['source_journal']))
        else:
            channel._require(set(control) == {'raw_response', 'settings'}, 'original public control source binding required')
            source = cls.from_public_response(response.ReceiptTriggeredProgramme.from_record(control['raw_response']),
                                             raw.registrations, tuple(control['settings']))
        channel._require(source.record() == record, 'receipt/window source identity changed')
        return source

    def interval(self, left=None, right=None, *, trial_families=None, taylor_order=8):
        receipt = self.law.interval(left, right)
        inherited = receipt['global_trace_norm_error']
        channel._require(trial_families is None or type(trial_families) is list and len(trial_families) == 4,
                         'all four source pattern trial families required')
        reports, extra = [], Q(0)
        for pattern, initial in enumerate(receipt['poststates']):
            pieces = polynomial_trials(self.source, initial, self.histories, taylor_order) if trial_families is None else trial_families[pattern]
            report = window.certify(self.source, initial, pieces, trap_histories=self.histories, upstream_error=inherited)
            extra += Q(report['trace_norm_error_bound'])-inherited
            reports.append(report)
        return Interval(self.record(), receipt['time_support'], tuple(reports), inherited+extra, inherited, extra)

    def verify(self, result):
        channel._require(type(result) is Interval and result.raw_source == self.record(), 'same complete window/receipt interval required')
        fresh = type(self).from_record(result.raw_source)
        expected = fresh.interval(*result.receipt_interval, trial_families=[r['trial_families'] for r in result.reports])
        channel._require(expected == result, 'receipt interval, generated poststate or whole error changed')
        return True

    def next_trap_inputs(self, result):
        self.verify(result)
        branches = []
        from bsm_retry_source import PATTERNS
        for pattern, report in enumerate(result.reports):
            for observation in self.source.observations(report):
                clicks = observation['clicks']
                branches.append({'pattern_index': pattern, 'herald': PATTERNS[pattern][0], 'clicks': clicks,
                                 'receipt_interval': result.receipt_interval,
                                 'original_receipt_law': self.law,
                                 'logic_deadline_supports': tuple(tuple(t+delay for t in result.receipt_interval)
                                                                for delay in self.source.logic_deadlines),
                                 'source_journal': self.journal,
                                 'trap_input': self.source.coarsen(report, clicks=clicks)})
        return TrapImage(result, tuple(branches), result.global_trace_norm_error)
