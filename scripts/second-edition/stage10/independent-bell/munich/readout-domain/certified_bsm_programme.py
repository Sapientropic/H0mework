"""Complete raw BSM retry programmes checked through source residual curves.

Stiff physical atomic widths use the existing untrusted BDF producer and
closed source checkers.  Failure retains the complete pair state.  A receipt
snapshot is the integral of the first-receipt CP rate, distinct from the
received state propagated through the rest of the gate and signal return.
"""
from dataclasses import dataclass
from fractions import Fraction as Q

import atomic_dipole as dipole
import atomic_full_forward as full
import bsm_channel as marked
import bsm_retry_source as bsm
import fluorescence_channel as channel
import joint_fluorescence_presence as joint
import stopped_bsm_programme as programme


def _norm(matrix):
    return bsm._entry_norm(matrix)


@dataclass(frozen=True)
class ReceiptMeasure:
    certificate: dict
    start_time: Q
    inherited_error: Q = Q(0)

    @property
    def support(self):
        return self.start_time, self.start_time+Q(self.certificate['duration'])

    def interval(self, left=None, right=None):
        """Same-curve first-receipt time/state measure, without a solver."""
        marked.verify_certificate(self.certificate)
        left = self.support[0] if left is None else full.exact(left)
        right = self.support[1] if right is None else full.exact(right)
        if not self.support[0] <= left <= right <= self.support[1]:
            raise ValueError('first-receipt interval outside certified raw gate')
        source = bsm.BSMSource.from_record(self.certificate['raw_source'])
        kernel = marked.SourceKernel(source, self.certificate['coefficient_bits'])
        bound = sum(max(atom.outgoing) for atom in source.source.sources)+sum(source.background_rates)
        input_error = full.nonnegative(self.inherited_error)+Q(self.certificate['upstream_trace_norm_error'])
        price = Q(self.certificate['initial_radical_error'])
        result, elapsed, integrated_error = tuple({} for _ in bsm.PATTERNS), Q(0), Q(0)
        quantum = 1 << self.certificate['mode_bits']
        for piece, paid in zip(self.certificate['trial_pieces'], self.certificate['piece_error_records']):
            width = Q(piece['duration'])
            price += sum(Q(paid[key]) for key in ('initial_join_error', 'source_residual_error',
                                                'radical_coefficient_error', 'scalar_exponential_error'))
            a = max(Q(0), left-self.start_time-elapsed)
            z = min(width, right-self.start_time-elapsed)
            if a < z:
                integrated_error += bound*(z-a)*price
                for mode in piece['modes']:
                    if mode['lambda'] != [0, 0]:
                        raise ValueError('receipt integration consumes registered polynomial BDF curves')
                    for k, raw_matrix in enumerate(mode['coefficients']):
                        coefficient = channel._hermitian(channel._coefficient(raw_matrix, quantum, kernel))
                        state = {(marked.index_mark(c), i, j): dipole.ComplexRadical(r, s)
                                 for (c, i, j), (r, s) in coefficient.items()}
                        weight = width*((z/width)**(k+1)-(a/width)**(k+1))/(k+1)
                        for branch in source.success_flux(state, at_time=source.interval_start+elapsed):
                            target = result[branch['target_mark'].receipt]
                            for key, value in branch['poststate_rate'].items():
                                bsm.local._add(target, key, weight*value)
            elapsed += width
        # The exact stopped CP time instrument transports its input error with
        # norm at most one.  Only the new curve residual uses the rate norm B.
        return {'poststates': result, 'time_support': (left, right),
                'global_trace_norm_error': input_error+integrated_error,
                'local_curve_error': integrated_error,
                'error_scope': 'whole four-pattern first-receipt time/state direct sum',
                'source_initial_and_complete_curve_verified': True, 'solver_executed': False}


@dataclass(frozen=True)
class Run:
    programme_result: programme.ProgrammeResult
    phase_certificates: tuple
    gate_certificates: tuple


class CertifiedBSMProgramme:
    def __init__(self, raw_programme):
        if type(raw_programme) is not programme.StoppedBSMProgramme:
            raise TypeError('closed raw stopped BSM programme required')
        self.raw = programme.StoppedBSMProgramme(raw_programme.preparation, raw_programme.excitation,
                    raw_programme.gate, raw_programme.return_phases, raw_programme.recooling,
                    arrival_delay_phases=raw_programme.arrival_delay, control_policy=raw_programme.control_policy)

    def run(self, initial, *, attempts=40, blocks=1, input_error=0, start_time=0,
            parent_input_identity=None, trap_histories=None, journal=(),
            rtol=1e-10, atol=1e-13, max_coordinates=50000):
        import fluorescence_channel_search as atomic_search
        import bsm_channel_search as gate_search
        if (type(attempts) is not int or not 1 <= attempts <= bsm.BURST_CYCLES or type(blocks) is not int or
                blocks < 1 or (blocks > 1 and attempts != bsm.BURST_CYCLES)):
            raise ValueError('finite raw bursts; repeated blocks require all forty attempts')
        state, clock = channel._initial(initial, joint.DIMENSION), full.exact(start_time)
        if type(journal) is not tuple:
            raise ValueError('immutable parent source journal required')
        if trap_histories is not None:
            from cem_pair_source import _histories
            _histories(trap_histories)
        terminal_error = time_error = full.nonnegative(input_error)
        stops, laws, events, phase_reports, gate_reports = [], [], list(journal), [], []
        raw = self.raw

        def constant_curve(matrix, width):
            quantum = 1 << 60
            entries = []
            for key, value in sorted(matrix.items()):
                a, _ = full.radical_midpoint(value.real, 160)
                b, _ = full.radical_midpoint(value.imag, 160)
                r, s = round(a*quantum), round(b*quantum)
                if r or s:
                    entries.append([*key, r, s])
            return [{'duration': str(width), 'modes': [{'lambda': [0, 0], 'coefficients': [entries]}]}]

        def evolve(phases, matrix):
            local_error = Q(0)
            for phase in phases:
                if phase.duration == 0:
                    continue
                source = joint.JointCounterGenerator(phase.first, phase.second, threshold=1,
                                                     background_rate=0, collection=((0, 0, 0, 0, 0, 0),))
                payment = phase.model_error*(_norm(matrix)+local_error)
                if not source.independent_atomic_action(matrix):
                    report = channel.certify(source, matrix,
                        constant_curve({(0, i, j): value for (i, j), value in matrix.items()}, source.duration),
                        upstream_error=local_error+payment)
                else:
                    report = atomic_search.predict(source, matrix, upstream_error=local_error+payment,
                                                rtol=rtol, atol=atol, max_coordinates=max_coordinates)
                channel.verify_certificate(report, source, matrix, upstream_error=local_error+payment)
                phase_reports.append(report)
                matrix, local_error = channel.poststate(report)
            return matrix, local_error

        for block in range(blocks):
            for cycle in range(1, attempts+1):
                before = raw.preparation+raw.excitation+raw.arrival_delay
                state, pre_price = evolve(before, state)
                clock += programme._duration(before)
                events.append({'kind': 'raw-preparation-excitation', 'block': block, 'cycle': cycle,
                               'gate_start_time': clock, 'phases': tuple(phase.record() for phase in before)})
                if not raw.gate.action(raw.gate.lift(state)):
                    certificate = marked.certify(raw.gate, state,
                        constant_curve({(marked.mark_index(bsm.INITIAL), i, j): value for (i, j), value in state.items()}, raw.gate.duration))
                else:
                    certificate = gate_search.predict(raw.gate, state, upstream_error=0,
                              rtol=rtol, atol=atol, max_coordinates=max_coordinates)
                marked.verify_certificate(certificate, raw.gate, state)
                gate_reports.append(certificate)
                gate_price = Q(certificate['trace_norm_error_bound'])
                law = ReceiptMeasure(certificate, clock, max(terminal_error, time_error)+pre_price)
                laws.append(law)
                receipt = law.interval()
                ready_time = clock+raw.gate.duration+programme._duration(raw.return_phases)
                return_prices = Q(0)
                for pattern in range(4):
                    center = {(i, j): dipole.ComplexRadical(Q(a), Q(b))
                              for i, j, a, b in certificate['patterns'][pattern]['poststate_center']}
                    returned, price = evolve(raw.return_phases, center)
                    return_prices += price
                    stops.append(programme.StopSnapshot(block, cycle, pattern, bsm.PATTERNS[pattern][0],
                        law.support, receipt['poststates'][pattern], returned, ready_time,
                        parent_input_identity, trap_histories, tuple(events)+({'kind': 'first-bsm-receipt',
                        'pattern_index': pattern, 'herald': bsm.PATTERNS[pattern][0],
                        'receipt_time_support': law.support, 'signal_return_time': ready_time,
                        'seconds_per_common_time_unit': str(raw.gate.seconds_per_unit)},)))
                failed, _ = marked.poststate(certificate, 'failure')
                continuation = raw.return_phases+(raw.recooling if cycle == bsm.BURST_CYCLES else ())
                state, price = evolve(continuation, failed)
                return_prices += price
                terminal_error += pre_price+gate_price+return_prices
                time_error += pre_price+gate_price+return_prices+receipt['local_curve_error']
                clock = ready_time+(programme._duration(raw.recooling) if cycle == bsm.BURST_CYCLES else 0)
                events.append({'kind': 'failed-bsm-continuation', 'block': block, 'cycle': cycle,
                               'next_time': clock, 'recooling_applied': cycle == bsm.BURST_CYCLES,
                               'raw_phases': tuple(phase.record() for phase in continuation)})
        record = {**raw.record(), 'propagation_backend': 'closed source residuals; BDF trials untrusted',
                  'receipt_snapshots': 'same-curve first CP-rate integrals, not gate-end success states'}
        result = programme.ProgrammeResult(tuple(stops), tuple(laws), state, clock, terminal_error, time_error,
                    record, parent_input_identity, trap_histories, tuple(events))
        return Run(result, tuple(phase_reports), tuple(gate_reports))
