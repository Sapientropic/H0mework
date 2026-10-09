"""Verified ready vacancy sectors -> first receipt -> full marked CEM coimage.

Entering occupancy is a restriction of the original ready matrix.  It is
retained through the CEM bath, so a pre-existing Empty coordinate is never
registered as a newly born ion.  The mother keeps the native reload recipe;
the numerical coimage supplies no invented cohort or atom epoch.
"""
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import bsm_channel as bsm_channel
import bsm_retry_source as bsm
import certified_bsm_programme as certified
import fluorescence_channel as channel
import joint_reload_programme as reload_programme
import joint_reload_source as reload
import joint_fluorescence_presence as joint
import optical_multitone as optical
import stopped_bsm_programme as stopped
import window_cem_source as window


SCHEMA = 'stage10-ready-receipt-projected-window-CEM/v1'
MASKS = tuple(product((False, True), repeat=2))


def _copy(value):
    return json.loads(channel._canonical(value))


def _optical_programme(record):
    tones = tuple(optical.Tone(item['name'], item['line'], Q(item['angular_frequency_in_common_reciprocal_time_unit']),
                  {int(q): channel._complex_record(value) for q, value in item['field_at_local_time_zero'].items()})
                  for item in record['tones'])
    source = optical.Programme(full.Segment.from_record(record['base']), tones)
    channel._require(source.record() == record, 'original multitone source identity required')
    return source


def _phase(record, multitone_bits):
    if record['origin'] is None:
        phase = stopped.RawPairPhase(*(full.Segment.from_record(raw) for raw in record['raw_segments']))
    else:
        origin = record['origin']
        first, second = map(_optical_programme, origin['multitone_programmes'])
        cells = origin['source_cells']
        channel._require(cells[0]['start'] == cells[1]['start'] and cells[0]['end'] == cells[1]['end'],
                         'same raw two-side multitone cell required')
        phase = stopped.RawPairPhase.from_multitone(first, second, Q(cells[0]['start']), Q(cells[0]['end']), bits=multitone_bits)
    channel._require(phase.record() == record, 'source-generated raw phase or Duhamel model price changed')
    return phase


def _burst(record, multitone_bits):
    raw = stopped.StoppedBSMProgramme([_phase(p, multitone_bits) for p in record['preparation']],
                [_phase(p, multitone_bits) for p in record['excitation']], bsm.BSMSource.from_record(record['gate']),
                [_phase(p, multitone_bits) for p in record['return_phases']],
                [_phase(p, multitone_bits) for p in record['recooling_phases']],
                arrival_delay_phases=[_phase(p, multitone_bits) for p in record['arrival_delay_phases']],
                control_policy=record['return_endpoint_policy'])
    channel._require(raw.record() == record, 'original complete burst programme required')
    return raw


def _replay_bsm_ingress(ingress, initial, input_error, start_time):
    """Pure replay of original full preparation, every retry, return and recool."""
    raw = _burst(ingress['raw_burst'], ingress['multitone_bits'])
    bsm_occupancy_certificate(raw.gate)
    for phase in raw.preparation+raw.excitation+raw.arrival_delay+raw.return_phases+raw.recooling:
        for atom in (joint._source(phase.first), joint._source(phase.second)):
            channel._require(not any(atom.program.ion_rates.values()), 'burst ion birth needs resolved departure provenance')
            _commutes_empty(atom.hamiltonian)
            for jump in atom.jumps:
                _commutes_empty(jump.matrix)
    phases = iter(ingress['phase_certificates'])
    gates = ingress['gate_certificates']
    count = len(gates)
    channel._require(type(count) is int and count > 0 and (count <= 40 or count % 40 == 0),
                     'original finite burst or complete forty-attempt blocks required')
    attempts, blocks = (count, 1) if count <= 40 else (40, count//40)
    state, clock = channel._initial(initial, reload.DIMENSION), full.exact(start_time)
    terminal_error = time_error = full.nonnegative(input_error)
    stops, laws, events = [], [], list(ingress['parent_journal'])

    def evolve(raw_phases, matrix):
        price = Q(0)
        for phase in raw_phases:
            if not phase.duration:
                continue
            report = next(phases, None)
            channel._require(report is not None, 'every source-generated raw phase needs its original certificate')
            source = joint.JointCounterGenerator(phase.first, phase.second, threshold=1,
                         background_rate=0, collection=((0, 0, 0, 0, 0, 0),))
            payment = phase.model_error*(bsm._entry_norm(matrix)+price)
            channel.verify_certificate(report, source, matrix, upstream_error=price+payment)
            channel._require(report['initial_counter'] == 0, 'unobserved atomic phase starts with reset zero counter')
            matrix, price = channel.poststate(report)
        return matrix, price

    for block in range(blocks):
        for cycle in range(1, attempts+1):
            index = block*attempts+cycle-1
            before = raw.preparation+raw.excitation+raw.arrival_delay
            state, pre_price = evolve(before, state)
            clock += stopped._duration(before)
            events.append({'kind': 'raw-preparation-excitation', 'block': block, 'cycle': cycle,
                           'gate_start_time': clock, 'phases': tuple(p.record() for p in before)})
            certificate = gates[index]
            bsm_channel.verify_certificate(certificate, raw.gate, state, upstream_error=0)
            channel._require(Q(certificate['duration']) == raw.gate.duration, 'whole original gate required')
            gate_price = Q(certificate['trace_norm_error_bound'])
            law = certified.ReceiptMeasure(certificate, clock, max(terminal_error, time_error)+pre_price)
            laws.append(law)
            receipt = law.interval()
            ready_time = clock+raw.gate.duration+stopped._duration(raw.return_phases)
            return_price = Q(0)
            for pattern in range(4):
                center = {(i, j): dipole.ComplexRadical(Q(a), Q(b))
                          for i, j, a, b in certificate['patterns'][pattern]['poststate_center']}
                returned, price = evolve(raw.return_phases, center)
                return_price += price
                stops.append(stopped.StopSnapshot(block, cycle, pattern, bsm.PATTERNS[pattern][0], law.support,
                     receipt['poststates'][pattern], returned, ready_time, ingress['parent_input_identity'], None,
                     tuple(events)+({'kind':'first-bsm-receipt','pattern_index':pattern,
                       'herald':bsm.PATTERNS[pattern][0], 'receipt_time_support':law.support,
                       'signal_return_time':ready_time,'seconds_per_common_time_unit':str(raw.gate.seconds_per_unit)},)))
            failed, _ = bsm_channel.poststate(certificate, 'failure')
            continuation = raw.return_phases+(raw.recooling if cycle == 40 else ())
            state, price = evolve(continuation, failed)
            return_price += price
            terminal_error += pre_price+gate_price+return_price
            time_error += pre_price+gate_price+return_price+receipt['local_curve_error']
            clock = ready_time+(stopped._duration(raw.recooling) if cycle == 40 else 0)
            events.append({'kind':'failed-bsm-continuation','block':block,'cycle':cycle,'next_time':clock,
                           'recooling_applied':cycle == 40,'raw_phases':tuple(p.record() for p in continuation)})
    channel._require(next(phases, None) is None, 'no extra unrelated phase certificates allowed')
    record = {**raw.record(), 'propagation_backend':'closed source residuals; BDF trials untrusted',
              'receipt_snapshots':'same-curve first CP-rate integrals, not gate-end success states'}
    result = stopped.ProgrammeResult(tuple(stops), tuple(laws), state, clock, terminal_error, time_error,
                record, ingress['parent_input_identity'], None, tuple(events))
    return certified.Run(result, tuple(ingress['phase_certificates']), tuple(gates))


def occupancy(index):
    channel._require(type(index) is int and 0 <= index < reload.DIMENSION,
                     'original complete 33-by-33 pair address required')
    return tuple(i != dipole.ION for i in divmod(index, 33))


def project(matrix, mask):
    channel._require(type(mask) is tuple and mask in MASKS and all(type(bit) is bool for bit in mask),
                     'two source occupancy bits required')
    return {(i, j): value for (i, j), value in channel._initial(matrix, reload.DIMENSION).items()
            if occupancy(i) == occupancy(j) == mask}


@lru_cache(maxsize=1)
def projection_inventory():
    """Exact four diagonal CP columns on the entire pair matrix-unit inventory."""
    labels = tuple(occupancy(i) for i in range(reload.DIMENSION))
    dimensions = tuple(labels.count(mask) for mask in MASKS)
    checked, retained = 0, [0]*4
    for i, left in enumerate(labels):
        channel._require(sum(int(left == mask) for mask in MASKS) == 1,
                         'four generated orthogonal projectors must sum to identity')
        for right in labels:
            coefficients = tuple(int(left == mask and right == mask) for mask in MASKS)
            channel._require(sum(coefficients) == int(left == right), 'complete CP pinching column mismatch')
            for k, coefficient in enumerate(coefficients):
                retained[k] += coefficient
            checked += 1
    channel._require(tuple(retained) == tuple(d*d for d in dimensions), 'all occupancy block dimensions required')
    return {'pair_dimension': reload.DIMENSION, 'local_dimension': 33, 'empty_coordinate': dipole.ION,
            'occupancy_masks': [list(mask) for mask in MASKS], 'sector_dimensions': list(dimensions),
            'full_pair_matrix_columns_checked': checked, 'retained_block_columns': retained,
            'CP_operators': 'four original diagonal P_A tensor P_B; orthogonal and sum to identity',
            'cohort_identity_recovered': False}


def _commutes_empty(operator):
    channel._require(all((i == dipole.ION) == (j == dipole.ION)
                         for (i, j), value in operator.items() if value),
                     'raw operator changes a pre-CEM vacancy sector')
    return len(operator)


def bsm_occupancy_certificate(raw_source):
    channel._require(type(raw_source) is bsm.BSMSource, 'closed original BSM source required')
    source = bsm.BSMSource.from_record(raw_source.record())
    atoms = []
    for side, atom in enumerate(source.source.sources):
        channel._require(not any(atom.program.ion_rates.values()),
                         'pre-CEM ion births require resolved departure provenance')
        h = _commutes_empty(atom.hamiltonian)
        natural = sum(_commutes_empty(jump.matrix) for jump in atom.jumps)
        channel._require(atom.outgoing[dipole.ION] == 0, 'source Empty restriction must remain absorbing')
        atoms.append({'side': side, 'raw_atom': atom.program.record(),
                      'Hamiltonian_entries_checked': h, 'natural_operator_entries_checked': natural,
                      'natural_operators_checked': len(atom.jumps), 'ion_rates_zero': True})
    detected = sum(_commutes_empty(operator) for _, operators in source.source.detected_operators
                   for operator in operators)
    return {'schema': 'stage10-original-BSM-occupancy-invariance/v1', 'raw_source': source.record(),
            'atoms': atoms, 'APD_operator_entries_checked': detected,
            'all_original_H_natural_APD_operators_commute_with_each_side_vacancy': True,
            'background_identity_preserves_occupancy': True,
            'source_mark_updates_do_not_change_occupancy': True,
            'whole_four_sector_CPTP_intertwining': True, 'cohort_recovered': False}


def _add(target, values):
    for key, value in values.items():
        window.local._add(target, key, value)


def _trace(matrix):
    value = sum((v for (i, j), v in matrix.items() if i == j), dipole.ComplexRadical())
    channel._require(not value.imag, 'Hermitian complete matrix trace required')
    center, error = full.radical_midpoint(value.real, 160)
    return center, error


def _initial_gate_matrix(law):
    original = bsm_channel._read_initial(law.certificate['initial_marked_state'])
    channel._require(all(mark == bsm.INITIAL for mark, _, _ in original),
                     'fresh original gate ingress required; no prior receipt reclassification')
    return {(i, j): value for (_, i, j), value in original.items()}


def taylor_trials(phase, matrix, *, order=6, mode_bits=60, coefficient_bits=160):
    channel._require(type(order) is int and 0 <= order <= 32, 'finite untrusted source trial order required')
    kernel, quantum = window.SourceKernel(phase, coefficient_bits), 1 << mode_bits
    coefficients = {(window.mark_index(mark), i, j): tuple(full.radical_midpoint(part, coefficient_bits)[0]
                    for part in (v.real, v.imag)) for (mark, i, j), v in matrix.items()}
    polynomial = []
    for degree in range(order+1):
        polynomial.append([[c, i, j, round(a*quantum), round(b*quantum)]
                           for (c, i, j), (a, b) in sorted(coefficients.items())
                           if round(a*quantum) or round(b*quantum)])
        coefficients = {key: (a*phase.duration/(degree+1), b*phase.duration/(degree+1))
                        for key, (a, b) in kernel.action(coefficients).items()}
    return [{'duration': str(phase.duration), 'modes': [{'lambda': [0, 0], 'coefficients': polynomial}]}]


class ProjectedWindowCEM:
    def __init__(self, source, law, parent_programme, parent_report, ready_index, *, burst_ingress=None):
        channel._require(type(source) is window.WindowCEMSource and type(law) is certified.ReceiptMeasure and
                         type(parent_programme) is reload_programme.JointReloadProgramme,
                         'closed window, original receipt measure and native ready parent required')
        parent_report = _copy(parent_report)
        parent_programme.verify(parent_report)
        channel._require(type(ready_index) is int and 0 <= ready_index < len(parent_report['ready']),
                         'source-generated original ready face required')
        self.source = window.WindowCEMSource.from_record(source.record())
        self.law = certified.ReceiptMeasure(_copy(law.certificate), full.exact(law.start_time), full.nonnegative(law.inherited_error))
        self.law.interval()
        raw_bsm = bsm.BSMSource.from_record(self.law.certificate['raw_source'])
        self.invariance = bsm_occupancy_certificate(raw_bsm)
        face = parent_report['ready'][ready_index]
        unit = Q(parent_report['source_record']['seconds_per_source_unit'])
        channel._require(unit == raw_bsm.seconds_per_unit == self.source.seconds_per_unit,
                         'ready, BSM and window must share the original physical time unit')
        channel._require(self.source.interval_start == 0, 'window waveform must retain original receipt origin')
        self.burst_ingress = None if burst_ingress is None else _copy(burst_ingress)
        if self.burst_ingress is None:
            channel._require(channel._input_record(_initial_gate_matrix(self.law)) == face['complete_matrix'],
                             'receipt gate must consume the complete original ready matrix')
            channel._require(self.law.start_time == Q(face['source_time'])+raw_bsm.interval_start,
                             'receipt must be generated at the original ready gate clock')
            error = self.law.inherited_error+Q(self.law.certificate['upstream_trace_norm_error'])
            channel._require(error >= Q(parent_report['global_trace_norm_error']),
                             'receipt must retain the whole upstream ready error price')
        else:
            replay = _replay_bsm_ingress(self.burst_ingress,
                 channel._read_input(face['complete_matrix'], reload.DIMENSION),
                 Q(parent_report['global_trace_norm_error']), Q(face['source_time']))
            selected = self.burst_ingress['receipt_index']
            channel._require(type(selected) is int and 0 <= selected < len(replay.programme_result.first_receipt_laws),
                             'original source-generated burst receipt address required')
            channel._require(self.law == replay.programme_result.first_receipt_laws[selected],
                             'receipt must consume original full preparation, retries and error clock')
        initial = _initial_gate_matrix(self.law)
        pinched = {}
        for mask in MASKS:
            _add(pinched, project(initial, mask))
        channel._require(pinched == initial, 'ready ingress must belong to the source vacancy block algebra')
        self.parent_programme_record = parent_programme.record()
        self.parent_report, self.ready_index = parent_report, ready_index

    @classmethod
    def from_bsm_run(cls, source, parent_programme, parent_report, ready_index, raw_burst, run,
                     *, receipt_index=0, multitone_bits=160):
        channel._require(type(raw_burst) is stopped.StoppedBSMProgramme and type(run) is certified.Run,
                         'original raw burst and complete certified run required')
        channel._require(run.programme_result.trap_histories is None,
                         'numeric coimage run must not assert reconstructed literal cohorts')
        journal = run.programme_result.journal
        first = next((i for i, event in enumerate(journal) if event.get('kind') == 'raw-preparation-excitation'), None)
        channel._require(first is not None, 'original raw burst preparation trace required')
        ingress = {'raw_burst': raw_burst.record(), 'multitone_bits': multitone_bits,
                   'phase_certificates': run.phase_certificates, 'gate_certificates': run.gate_certificates,
                   'parent_journal': journal[:first], 'parent_input_identity': run.programme_result.parent_input_identity,
                   'receipt_index': receipt_index}
        parent_programme.verify(parent_report)
        channel._require(type(ready_index) is int and 0 <= ready_index < len(parent_report['ready']),
                         'source-generated original ready face required')
        face = parent_report['ready'][ready_index]
        expected = _replay_bsm_ingress(ingress, channel._read_input(face['complete_matrix'], reload.DIMENSION),
                     Q(parent_report['global_trace_norm_error']), Q(face['source_time']))
        channel._require(expected == run, 'complete original BSM preparation/retry run changed')
        channel._require(type(receipt_index) is int and 0 <= receipt_index < len(run.programme_result.first_receipt_laws),
                         'original finite receipt index required')
        return cls(source, run.programme_result.first_receipt_laws[receipt_index], parent_programme,
                   parent_report, ready_index, burst_ingress=ingress)

    def record(self):
        return _copy({'schema': SCHEMA, 'raw_window_source': self.source.record(),
                'original_receipt_measure': {'certificate': self.law.certificate, 'start_time': str(self.law.start_time),
                                            'inherited_error': str(self.law.inherited_error)},
                'native_reload_parent': {'programme': self.parent_programme_record,
                                         'report': self.parent_report, 'ready_index': self.ready_index},
                'original_BSM_occupancy_certificate': self.invariance,
                'complete_occupancy_projection': projection_inventory(),
                'verified_complete_burst_ingress': self.burst_ingress,
                'ready_to_gate_scope': ('direct original gate ingress' if self.burst_ingress is None else
                        'complete original preparation/excitation/arrival, every failed retry/return and fortieth recooling'),
                'successful_receipt_semantics': 'original first CP rate; returned gate-end success state is not substituted',
                'time_state_reader': 'Phi(mu(B)) with original mother measure; no scalar midpoint',
                'cohort_recovered_from_projection': False, 'actual_hardware_uniquely_identified': False,
                'complete_record_clock_square_certified': False, 'controller_advance': False})

    @classmethod
    def from_record(cls, record):
        channel._require(type(record) is dict and record.get('schema') == SCHEMA, 'registered ready/receipt/window source required')
        law, parent = record['original_receipt_measure'], record['native_reload_parent']
        result = cls(window.WindowCEMSource.from_record(record['raw_window_source']),
                     certified.ReceiptMeasure(law['certificate'], Q(law['start_time']), Q(law['inherited_error'])),
                     reload_programme.JointReloadProgramme.from_record(parent['programme']),
                     parent['report'], parent['ready_index'], burst_ingress=record['verified_complete_burst_ingress'])
        channel._require(result.record() == record, 'same mother source, ready or time-measure identity required')
        return result

    def interval(self, left=None, right=None, *, trial_provider=None, taylor_order=6,
                 mode_bits=60, coefficient_bits=160, exponential_bits=160):
        source_record = self.record()
        source = window.WindowCEMSource.from_record(source_record['raw_window_source'])
        receipt = self.law.interval(left, right)
        inherited, extra, packets = receipt['global_trace_norm_error'], Q(0), []
        for pattern, input_matrix in enumerate(receipt['poststates']):
            for mask in MASKS:
                initial = project(input_matrix, mask)
                marked = {(window.INITIAL, i, j): value for (i, j), value in initial.items()}
                reports = []
                if initial:
                    for phase in source.phases():
                        pieces = (taylor_trials(phase, marked, order=taylor_order, mode_bits=mode_bits,
                                                coefficient_bits=coefficient_bits) if trial_provider is None else
                                  trial_provider(pattern, mask, phase.index, dict(marked)))
                        report = window.certify_step(phase, marked, pieces, upstream_error=0,
                                mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
                        marked, error = window.marked_poststate(report)
                        extra += error
                        reports.append(report)
                    marked = source.background_action(marked)
                packets.append({'pattern_index': pattern, 'physical_herald': bsm.PATTERNS[pattern][0],
                                'entering_occupancy': list(mask), 'initial_matrix': channel._input_record(initial),
                                'phase_certificates': reports,
                                'complete_marked_matrix': window._marked_record(window._initial_marked(marked))})
        initial_total, terminal_total = {}, {}
        for matrix in receipt['poststates']:
            _add(initial_total, matrix)
        for packet in packets:
            for (_, i, j), value in window._read_marked(packet['complete_marked_matrix']).items():
                _add(terminal_total, {(i, j): value})
        before, eb = _trace(initial_total)
        after, ea = _trace(terminal_total)
        channel._require(abs(after-before) <= extra+eb+ea,
                         'whole marked window and all vacancy sectors must retain source trace')
        return {'schema': SCHEMA, 'source_record': source_record, 'receipt_time_support': list(map(str, receipt['time_support'])),
                'packets': packets, 'whole_receipt_error': str(inherited), 'window_local_error': str(extra),
                'global_trace_norm_error': str(inherited+extra), 'input_trace_center': str(before),
                'terminal_trace_center': str(after), 'precision': [mode_bits, coefficient_bits, exponential_bits],
                'whole_upstream_error_paid_once': True, 'all_four_occupancy_sectors_and_patterns_retained': True,
                'source_background_applied_once': True, 'new_ION_birth_distinguished_from_initial_Empty': True,
                'numeric_carrier_is_literal_cohort': False, 'input_center_PSD_certified': False,
                'physical_probability_interpretation_requires_positive_source': True,
                'solver_reexecuted_by_checker': False, 'actual_hardware_uniquely_identified': False,
                'complete_record_clock_square_certified': False, 'controller_advance': False}

    def verify(self, report):
        channel._require(type(report) is dict and report.get('source_record') == self.record(),
                         'same original ready/receipt/window source required')
        fresh = type(self).from_record(report['source_record'])
        saved = {(item['pattern_index'], tuple(item['entering_occupancy'])): item for item in report['packets']}
        channel._require(len(saved) == 16, 'complete four-pattern four-occupancy packet inventory required')
        def trials(pattern, mask, phase, matrix):
            return saved[pattern, mask]['phase_certificates'][phase]['trial_pieces']
        bits, coefficient_bits, exponential_bits = report['precision']
        expected = fresh.interval(*map(Q, report['receipt_time_support']), trial_provider=trials,
                                 mode_bits=bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
        channel._require(expected == report, 'complete projected window source certificate mismatch')
        return True

    def next_reload_face(self, report, source, *, clicks=None, herald=None):
        self.verify(report)
        channel._require(type(source) is reload.JointReloadSource, 'closed original reload source required')
        source = reload.JointReloadSource.from_record(source.record())
        channel._require(clicks is None or type(clicks) is tuple and clicks in window.REGISTRATION_ORDER
                         and all(type(bit) is int for bit in clicks), 'original two click bits required')
        channel._require(herald is None or herald in ('Psi+', 'Psi-'), 'original physical herald required')
        state, branches = {}, []
        for packet in report['packets']:
            if herald is not None and packet['physical_herald'] != herald:
                continue
            mask = tuple(packet['entering_occupancy'])
            for (mark, i, j), value in window._read_marked(packet['complete_marked_matrix']).items():
                if clicks is not None and mark.clicks != clicks:
                    continue
                departed = tuple(mask[side] and divmod(i, 33)[side] == dipole.ION for side in (0, 1))
                channel._require(all((divmod(i, 33)[side] == dipole.ION) == (divmod(j, 33)[side] == dipole.ION)
                                    for side in (0, 1)), 'complete generated neutral/ION block algebra required')
                channel._require(all(mask[side] or divmod(i, 33)[side] == dipole.ION for side in (0, 1)),
                                 'initial Empty cannot gain a new atom without capture')
                _add(state, {(0, 0, i, j): value})
                branches.append({'pattern_index': packet['pattern_index'], 'physical_herald': packet['physical_herald'],
                                 'entering_occupancy': list(mask), 'clicks': list(mark.clicks),
                                 'source_new_departure_sides': list(departed), 'matrix_address': [i, j]})
        source._projected_blocks(state)
        terminal_delay = self.source.interval_start+self.source.duration
        return {'state': state, 'global_trace_norm_error': Q(report['global_trace_norm_error']),
                'source_start_time_support': tuple(Q(t)+terminal_delay for t in report['receipt_time_support']),
                'seconds_per_source_unit': self.source.seconds_per_unit,
                'raw_reload_source': source.record(), 'mother_window': report, 'mother_branch_restrictions': branches,
                'receipt_time_measure_kept_by_parent': True, 'index32_at_reload_is_Empty': True,
                'literal_cohort_reconstructed': False, 'actual_hardware_uniquely_identified': False}

    def reload_window(self, report, source, *, clicks=None, herald=None, trial_pieces=None, taylor_order=6):
        """Direct native stage-zero consumer; no fabricated TrapHistory inlet."""
        face = self.next_reload_face(report, source, clicks=clicks, herald=herald)
        source = reload.JointReloadSource.from_record(face['raw_reload_source'])
        matrix = {(i, j): value for (_, _, i, j), value in face['state'].items()}
        pieces = (reload_programme.taylor_trials(source, 0, matrix, order=taylor_order)
                  if trial_pieces is None else trial_pieces)
        certificate = reload.certify_window(source, matrix, pieces, stage=0, upstream_error=0)
        endpoint = {(0, c, i, j): dipole.ComplexRadical(Q(a), Q(b))
                    for c, i, j, a, b in certificate['counter_poststate_center']}
        return {'source_parent': face, 'window_certificate': certificate,
                'source_next': source.projected_window_end(endpoint),
                'source_next_time_support': tuple(t+Q(certificate['duration']) for t in face['source_start_time_support']),
                'global_trace_norm_error': face['global_trace_norm_error']+Q(certificate['trace_norm_error_bound']),
                'whole_upstream_error_paid_once': True, 'literal_cohort_reconstructed': False}
