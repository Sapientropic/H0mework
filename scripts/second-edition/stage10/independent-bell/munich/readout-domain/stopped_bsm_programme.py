"""Source-controlled finite BSM bursts, first receipts, and full-state retries.

All quantum operations come from raw full33 phases and the existing four-port
BSM source.  A successful receipt ends retries, not atomic evolution: the
receipt snapshot and the state at the raw signal-return endpoint are separate
readouts of the same generated process.  No success probability or prepared
state is supplied.  Numerical objects are source outputs, not untrusted
certificates.  Whole direct-sum error prices include absent sparse coordinates.
"""
from dataclasses import dataclass, field, replace
from fractions import Fraction as Q
from math import comb, factorial

import atomic_dipole as dipole
import atomic_full_forward as full
import bsm_retry_source as bsm
import optical_multitone as optical
from trap_reload_source import TrapHistory


ZERO = dipole.ComplexRadical()


def _add(target, source, coefficient=1):
    for key, value in source.items():
        bsm.local._add(target, key, coefficient * value)


def _trace(matrix):
    value = bsm.joint._trace(matrix)
    if value.imag:
        raise ValueError("Hermitian programme image must have real trace")
    return value.real


@dataclass(frozen=True)
class RawPairPhase:
    first: full.Segment
    second: full.Segment
    model_error: Q = field(init=False, default=Q(0))
    origin: dict | None = field(init=False, default=None)

    def __post_init__(self):
        if type(self.first) is not full.Segment or type(self.second) is not full.Segment:
            raise TypeError("two original raw full33 Segments required")
        if self.first.duration != self.second.duration:
            raise ValueError("two-side raw phase duration must agree")
        object.__setattr__(self, "first", full.Segment.from_record(self.first.record()))
        object.__setattr__(self, "second", full.Segment.from_record(self.second.record()))

    @property
    def duration(self):
        return self.first.duration

    def record(self):
        return {"raw_segments": [self.first.record(), self.second.record()],
                "model_trace_norm_error": str(self.model_error), "origin": self.origin}

    @classmethod
    def from_multitone(cls, first, second, start, end, *, bits=160):
        if type(first) is not optical.Programme or type(second) is not optical.Programme:
            raise TypeError("two raw simultaneous-multitone programmes required")
        a, b = first.compile_cell(start, end, bits=bits), second.compile_cell(start, end, bits=bits)
        result = cls(a.segment, b.segment)
        object.__setattr__(result, "model_error", a.trace_norm_error+b.trace_norm_error)
        object.__setattr__(result, "origin", {"multitone_programmes": [first.record(), second.record()],
                                            "source_cells": [a.record(), b.record()]})
        return result


def _phases(values, *, nonempty=False):
    if type(values) not in (tuple, list) or (nonempty and not values):
        raise ValueError("ordered raw pair-phase inventory required")
    result = []
    for value in values:
        if type(value) is RawPairPhase:
            result.append(value)
        elif type(value) in (tuple, list) and len(value) == 2:
            result.append(RawPairPhase(*value))
        else:
            raise TypeError("raw pair phase; no target channel or density accepted")
    return tuple(result)


def _duration(phases):
    return sum((phase.duration for phase in phases), Q(0))


def _evolve(phases, state, order):
    state, error = bsm.joint._matrix(state), Q(0)
    for phase in phases:
        model = phase.model_error * bsm._entry_norm(state)
        image = bsm.evolve_pair(phase.first, phase.second, state, order=order)
        state, error = image.state, error+image.trace_norm_error+model
    return state, error


def _jets(source, initial, order):
    result = [source.lift(initial)]
    if not bsm._hermitian(result[0]):
        raise ValueError("Hermitian same-source full pair input required")
    for _ in range(order+1):
        result.append(source.action(result[-1]))
    return tuple(result)


def _gate_image(source, jets, order):
    centre = {}
    for n in range(order+1):
        _add(centre, jets[n], source.duration**n / factorial(n))
    error = source.duration**(order+1) * bsm._entry_norm(jets[order+1]) / factorial(order+1)
    return bsm.Image(centre, error, source.duration, source.record())


def _flux(source, state):
    """Complete four-pattern CP map; the bound also covers missing marks."""
    result = tuple({} for _ in bsm.PATTERNS)
    for mark, matrix in source.blocks(state).items():
        if mark.receipt is not None:
            continue
        for port in range(4):
            target = source.target(mark, port)
            if target.receipt is not None:
                _add(result[target.receipt], source.port_action(matrix, port))
    return result


def _time_monomial(a, b, duration, left_power, right_power):
    """Exact integral of t^k (T-t)^m on one source time interval."""
    return sum(((-1)**j*comb(right_power, j)*duration**(right_power-j)*
                (b**(left_power+j+1)-a**(left_power+j+1))/(left_power+j+1)
                for j in range(right_power+1)), Q(0))


@dataclass(frozen=True)
class FirstReceiptLaw:
    source: bsm.BSMSource
    start_time: Q
    flux_jets: tuple
    derivative_norm: Q
    upstream_error: Q
    return_phases: tuple
    order: int

    @property
    def support(self):
        return self.start_time, self.start_time+self.source.duration

    @property
    def norm_bound(self):
        return sum(max(source.outgoing) for source in self.source.source.sources) + sum(self.source.background_rates)

    def _coordinate(self, time):
        time = full.exact(time)
        if not self.support[0] <= time <= self.support[1]:
            raise ValueError("first receipt query must lie in its same-source gate support")
        return time-self.start_time

    def density(self, at_time, *, at_signal_return=False):
        if type(at_signal_return) is not bool:
            raise TypeError("explicit signal-return readout selector required")
        t = self._coordinate(at_time)
        states = tuple({} for _ in bsm.PATTERNS)
        for n, values in enumerate(self.flux_jets):
            for target, value in zip(states, values):
                _add(target, value, t**n / factorial(n))
        error = self.norm_bound * (self.upstream_error + t**self.order*self.derivative_norm/factorial(self.order))
        if at_signal_return:
            first, second = (source.program for source in self.source.source.sources)
            remaining_gate = RawPairPhase(replace(first, duration=self.source.duration-t),
                                          replace(second, duration=self.source.duration-t))
            transported, numerical = [], Q(0)
            for state in states:
                result, price = _evolve((remaining_gate,)+self.return_phases, state, self.order)
                transported.append(result)
                numerical += price
            states, error = tuple(transported), error+numerical
        return {"at_time": full.exact(at_time), "poststate_rates": states,
                "rate_centres": tuple(_trace(state) for state in states),
                "global_trace_norm_error": error,
                "error_scope": "whole four-pattern CP-rate direct sum, including missing sparse coordinates",
                "at_signal_return": at_signal_return}

    def interval(self, left=None, right=None, *, at_signal_return=False):
        if type(at_signal_return) is not bool:
            raise TypeError("explicit signal-return readout selector required")
        left = self.support[0] if left is None else full.exact(left)
        right = self.support[1] if right is None else full.exact(right)
        a, b = self._coordinate(left), self._coordinate(right)
        if a > b:
            raise ValueError("ordered first-receipt time interval required")
        states = tuple({} for _ in bsm.PATTERNS)
        for n, values in enumerate(self.flux_jets):
            for target, value in zip(states, values):
                _add(target, value, (b**(n+1)-a**(n+1))/factorial(n+1))
        error = self.norm_bound * ((b-a)*self.upstream_error +
                (b**(self.order+1)-a**(self.order+1))*self.derivative_norm/factorial(self.order+1))
        if at_signal_return:
            # The physical gate law after the first receipt is the original
            # atom action with its future detector marks forgotten.  Integrate
            # the same source time together with that remaining physical action.
            transported = tuple({} for _ in bsm.PATTERNS)
            transport_error = Q(0)
            action = self.source.source.independent_atomic_action
            for k, values in enumerate(self.flux_jets):
                derivatives = values
                for m in range(self.order+1):
                    weight = _time_monomial(a, b, self.source.duration, k, m)/factorial(k)/factorial(m)
                    for target, value in zip(transported, derivatives):
                        _add(target, value, weight)
                    derivatives = tuple(action(value) for value in derivatives)
                weight = _time_monomial(a, b, self.source.duration, k, self.order+1)/factorial(k)/factorial(self.order+1)
                transport_error += weight*sum((bsm._entry_norm(value) for value in derivatives), Q(0))
            returned, numerical = [], Q(0)
            for state in transported:
                value, price = _evolve(self.return_phases, state, self.order)
                returned.append(value)
                numerical += price
            states, error = tuple(returned), error+transport_error+numerical
        return {"time_support": (left, right), "poststates": states,
                "probability_centres": tuple(_trace(state) for state in states),
                "global_trace_norm_error": error,
                "error_scope": "whole four-pattern time measure, including missing sparse coordinates",
                "at_signal_return": at_signal_return}


@dataclass(frozen=True)
class StopSnapshot:
    block_index: int
    cycle_index: int
    pattern_index: int
    herald: str
    receipt_time_support: tuple
    poststate_at_receipt: dict
    poststate_at_signal_return: dict
    signal_return_time: Q
    parent_input_identity: object
    trap_histories: tuple | None
    journal: tuple


@dataclass(frozen=True)
class ProgrammeResult:
    stops: tuple
    first_receipt_laws: tuple
    remaining_pair: dict
    remaining_time: Q
    global_terminal_error: Q
    global_time_error: Q
    source_record: dict
    parent_input_identity: object
    trap_histories: tuple | None
    journal: tuple

    def measurement_inputs(self):
        """Literal full-pair inlet; physical Psi labels remain unmapped."""
        return tuple({"poststate": stop.poststate_at_signal_return,
                      "poststate_at_receipt": stop.poststate_at_receipt,
                      "physical_dimension": bsm.joint.DIMENSION, "herald": stop.herald,
                      "pattern_index": stop.pattern_index, "block_index": stop.block_index,
                      "cycle_index": stop.cycle_index, "receipt_time_support": stop.receipt_time_support,
                      "signal_return_time": stop.signal_return_time,
                      "trace_norm_error_upper": self.global_terminal_error,
                      "receipt_snapshot_trace_norm_error_upper": self.global_time_error,
                      "error_scope": "one shared whole terminal direct-sum budget; do not sum copies",
                      "parent_input_identity": stop.parent_input_identity,
                      "trap_histories": stop.trap_histories, "journal": stop.journal}
                     for stop in self.stops)

    def shared_apd_inputs(self):
        return self.measurement_inputs()


class StoppedBSMProgramme:
    def __init__(self, preparation, excitation, gate, return_phases, recooling_phases, *,
                 arrival_delay_phases=(), control_policy="fixed_excitation_offset"):
        if type(gate) is not bsm.BSMSource:
            raise TypeError("original raw four-port BSM source required")
        self.gate = bsm.BSMSource.from_record(gate.record())
        self.preparation = _phases(preparation, nonempty=True)
        self.excitation = _phases(excitation, nonempty=True)
        self.arrival_delay = _phases(arrival_delay_phases)
        self.return_phases = _phases(return_phases, nonempty=True)
        self.recooling = _phases(recooling_phases, nonempty=True)
        if control_policy != "fixed_excitation_offset":
            raise ValueError("explicit fixed-excitation-offset raw return policy required")
        self.control_policy = control_policy
        if self.gate.interval_start != self.gate.gate_start or self.gate.duration != self.gate.gate_end-self.gate.gate_start:
            raise ValueError("complete source gate required; partial cells need their programme assembler")
        if self.gate.gate_start < 0 or _duration(self.arrival_delay) != self.gate.gate_start:
            raise ValueError("raw pre-arrival atomic phases must pay the exact gate-start delay")
        self.return_duration = bsm.RETURN_SECONDS/self.gate.seconds_per_unit
        if self.gate.gate_end+_duration(self.return_phases) != self.return_duration:
            raise ValueError("gate and raw return remainder must equal the 2016 7.3 us excitation wait")
        if _duration(self.recooling) != bsm.RECOOL_SECONDS/self.gate.seconds_per_unit:
            raise ValueError("fortieth-failure raw recooling must last exactly 350 us")

    def record(self):
        return {"schema": "rb87-source-stopped-bsm-programme/v1", "gate": self.gate.record(),
                "preparation": [phase.record() for phase in self.preparation],
                "excitation": [phase.record() for phase in self.excitation],
                "arrival_delay_phases": [phase.record() for phase in self.arrival_delay],
                "return_phases": [phase.record() for phase in self.return_phases],
                "recooling_phases": [phase.record() for phase in self.recooling],
                "return_endpoint_policy": self.control_policy, "burst_cycles": bsm.BURST_CYCLES,
                "receipt_clock": "same generated first CP jump in its full arrival gate",
                "parent_cohort_policy": "preserve parent identity/history; index32 does not decide departure or birth",
                "loss_control": "parent source owns presence/reload interventions between finite bursts",
                "finite_repetition": "same fixed raw burst without an external intervention",
                "target_prepared_state_supplied": False, "success_probability_supplied": False,
                "actual_programme_identified": False, "actual_hardware_uniquely_identified": False,
                "controller_advance": False, "centre_complete_positivity_claimed": False}

    def run(self, initial_full_pair, *, attempts=40, blocks=1, order=4, input_error=0,
            start_time=0, parent_input_identity=None, trap_histories=None, journal=()):
        if type(attempts) is not int or not 1 <= attempts <= bsm.BURST_CYCLES:
            raise ValueError("finite burst attempt count in [1,40] required")
        if type(blocks) is not int or blocks < 1 or (blocks > 1 and attempts != bsm.BURST_CYCLES):
            raise ValueError("repeat only complete 40-attempt source blocks")
        if type(order) is not int or not 1 <= order <= 16:
            raise ValueError("finite exact source order in [1,16] required")
        if trap_histories is not None and (type(trap_histories) is not tuple or len(trap_histories) != 2 or
                                          any(type(history) is not TrapHistory for history in trap_histories)):
            raise TypeError("literal two parent source TrapHistories required")
        if type(journal) is not tuple:
            raise TypeError("immutable parent source journal required")
        state, clock = bsm.joint._matrix(initial_full_pair), full.exact(start_time)
        if not bsm._hermitian(state):
            raise ValueError("Hermitian full pair source input required")
        terminal_error = time_error = full.nonnegative(input_error)
        stops, laws, events = [], [], list(journal)
        for block in range(blocks):
            for cycle in range(1, attempts+1):
                before = tuple(self.preparation+self.excitation+self.arrival_delay)
                state, pre_error = _evolve(before, state, order)
                clock += _duration(before)
                events.append({"kind": "raw-preparation-excitation", "block": block, "cycle": cycle,
                               "gate_start_time": clock, "phases": tuple(phase.record() for phase in before)})
                jets = _jets(self.gate, state, order)
                image = _gate_image(self.gate, jets, order)
                law = FirstReceiptLaw(self.gate, clock, tuple(_flux(self.gate, jets[n]) for n in range(order)),
                                      bsm._entry_norm(jets[order]), max(terminal_error, time_error)+pre_error,
                                      self.return_phases, order)
                laws.append(law)
                snapshots = law.interval()["poststates"]
                at_gate_end = tuple({} for _ in bsm.PATTERNS)
                for mark, matrix in self.gate.blocks(image.state).items():
                    if mark.receipt is not None:
                        _add(at_gate_end[mark.receipt], matrix)
                ready_time = clock+self.gate.duration+_duration(self.return_phases)
                success_error = Q(0)
                for pattern, at_receipt, at_end in zip(range(4), snapshots, at_gate_end):
                    returned, price = _evolve(self.return_phases, at_end, order)
                    success_error += price
                    stops.append(StopSnapshot(block, cycle, pattern, bsm.PATTERNS[pattern][0], law.support,
                                              at_receipt, returned, ready_time, parent_input_identity,
                                              trap_histories, tuple(events)+({"kind": "first-bsm-receipt",
                                                  "pattern_index": pattern, "herald": bsm.PATTERNS[pattern][0],
                                                  "seconds_per_common_time_unit": str(self.gate.seconds_per_unit),
                                                  "receipt_time_support": law.support, "signal_return_time": ready_time},)))
                continuation = self.return_phases+(self.recooling if cycle == bsm.BURST_CYCLES else ())
                failed = self.gate.observations(image.state)["failure_poststate"]
                result = bsm.continue_failed_attempt(self.gate, image,
                            [(phase.first, phase.second) for phase in continuation],
                            completed_cycles=cycle, order=order)
                next_image = result["next_pair_image"]
                model_price = sum((phase.model_error for phase in continuation), Q(0))*bsm._entry_norm(failed)
                continuation_error = next_image.trace_norm_error+model_price
                terminal_error += pre_error+continuation_error+success_error
                # The stopped time measure and complete surviving state form
                # one CP instrument.  Prefix error is paid once, across all
                # attempts/receipts, including centres absent from the sparse map.
                snapshot_error = law.norm_bound*self.gate.duration**(order+1)*law.derivative_norm/factorial(order+1)
                time_error += pre_error+continuation_error+snapshot_error
                state, clock = next_image.state, ready_time+(_duration(self.recooling) if result["recooling_due"] else 0)
                events.append({"kind": "failed-bsm-continuation", "block": block, "cycle": cycle,
                               "next_time": clock, "recooling_applied": result["recooling_due"],
                               "raw_phases": tuple(phase.record() for phase in continuation)})
        return ProgrammeResult(tuple(stops), tuple(laws), state, clock, terminal_error, time_error,
                               self.record(), parent_input_identity, trap_histories, tuple(events))

    def repeat_block(self, initial_full_pair, blocks, **kwargs):
        return self.run(initial_full_pair, attempts=bsm.BURST_CYCLES, blocks=blocks, **kwargs)
