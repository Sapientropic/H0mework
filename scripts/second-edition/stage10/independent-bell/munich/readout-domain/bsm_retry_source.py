"""Raw full33 pair source for four-port BSM attempts and stateful retries.

SI I.B of https://arxiv.org/html/1611.04604v2 specifies a 120 ns arrival
gate, a 7.3 us excitation-to-return wait, and 350 us recooling after 40 failed
preparation/excitation cycles.  The conversion from seconds to the common
atomic time unit is a raw parameter.  No success probability, waiting kernel,
prepared density or successful-excitation condition is supplied.

This is a Markov, instantaneous common-output optical model.  Original bath
groups remain orthogonal, while both sides interfere inside one group.  APD
marks count registered jumps, with two meaning at least two; no dead-time model
is asserted.  A raw FPGA pattern priority resolves a possible multiple-click
ambiguity.  The first receipt is retained while atoms and all ports continue.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from math import factorial

import atomic_dipole as dipole
import atomic_full_forward as full
import atom_photon_source as optics
import fluorescence_presence as local
import joint_fluorescence_presence as joint


ZERO = dipole.ComplexRadical()
PORTS = ((1, "perp"), (1, "parallel"), (2, "perp"), (2, "parallel"))
PATTERNS = tuple((name, tuple(PORTS.index(port) for port in ports))
                 for name, ports in optics.HERALD_PATTERNS)
GATE_SECONDS = Q(120, 10**9)
RETURN_SECONDS = Q(73, 10**7)
RECOOL_SECONDS = Q(350, 10**6)
BURST_CYCLES = 40


def _positive(value):
    value = full.exact(value)
    if value <= 0:
        raise ValueError("positive raw clock conversion required")
    return value


def _rates(values, *, probabilities=False):
    if type(values) not in (tuple, list) or len(values) != 4:
        raise ValueError("complete four-physical-APD primitive inventory required")
    values = tuple(full.nonnegative(value) for value in values)
    if probabilities and any(value > 1 for value in values):
        raise ValueError("physical APD efficiency exceeds one")
    return values


def optical_transfer(collection_a, collection_b, splitter, efficiencies):
    """Generate four physical outputs from raw passive collection and Bose BS."""
    collections = tuple(map(optics.collection_matrix, (collection_a, collection_b)))
    splitter, efficiencies = optics.beam_splitter_matrix(splitter), _rates(efficiencies, probabilities=True)
    return tuple(tuple(splitter[port][side] * collections[side][pol][q] *
                       dipole.sqrt_rational(efficiencies[2*port+pol])
                       for side in range(2) for q in range(3))
                 for port in range(2) for pol in range(2))


@dataclass(frozen=True)
class Mark:
    counts: tuple = (0, 0, 0, 0)
    receipt: int | None = None

    def __post_init__(self):
        if (type(self.counts) is not tuple or len(self.counts) != 4 or
                any(type(value) is not int or not 0 <= value <= 2 for value in self.counts)):
            raise ValueError("four source APD marks with 2 meaning at least 2 required")
        if self.receipt is not None:
            if type(self.receipt) is not int or not 0 <= self.receipt < len(PATTERNS):
                raise ValueError("first source-generated BSM pattern receipt required")
            if not all(self.counts[port] for port in PATTERNS[self.receipt][1]):
                raise ValueError("receipt ports absent from its retained click history")
        elif any(all(self.counts[port] for port in ports) for _, ports in PATTERNS):
            raise ValueError("supported pair cannot occur without its first BSM receipt")


INITIAL = Mark()


def _entry_norm(matrix, *, bits=80):
    return sum((sum(abs(coefficient) * full._sqrt(root, bits)[1]
                    for root, coefficient in part.terms)
                for value in matrix.values() for part in (value.real, value.imag)), Q(0))


def _hermitian(matrix):
    return all(matrix.get(key[:-2] + (key[-1], key[-2]), ZERO) == value.conjugate()
               for key, value in matrix.items())


def _taylor(initial, action, duration, order, input_error):
    """Hermitian CPTP remainder: t^(n+1)||G^(n+1)X||_1/(n+1)!.

    The direct-sum trace norm is bounded by entry l1.  The polynomial centre
    need not be positive.  The bound uses contraction of the generated source,
    and does not assume the centre is itself a quantum channel.
    """
    if type(order) is not int or not 0 <= order <= 16:
        raise ValueError("finite raw source Taylor order in [0,16] required")
    duration, input_error = full.nonnegative(duration), full.nonnegative(input_error)
    if not _hermitian(initial):
        raise ValueError("Hermitian source poststate required for contraction bound")
    derivative, centre = initial, dict(initial)
    for n in range(1, order + 2):
        derivative = action(derivative)
        if n <= order:
            for key, value in derivative.items():
                local._add(centre, key, (duration**n / factorial(n)) * value)
    error = input_error + duration**(order+1) * _entry_norm(derivative) / factorial(order+1)
    return centre, error


@dataclass(frozen=True)
class Image:
    state: dict
    trace_norm_error: Q
    duration: Q
    source_record: dict


class BSMSource:
    physical_dimension = joint.DIMENSION

    def __init__(self, first, second, *, seconds_per_unit, collection_a, collection_b,
                 efficiencies, background_rates, splitter=None, pattern_priority=(0, 1, 2, 3),
                 gate_start=0, interval_start=None):
        self.seconds_per_unit = _positive(seconds_per_unit)
        self.gate_start = full.exact(gate_start)
        self.interval_start = self.gate_start if interval_start is None else full.exact(interval_start)
        self.gate_end = self.gate_start + GATE_SECONDS / self.seconds_per_unit
        self.background_rates = _rates(background_rates)
        if (type(pattern_priority) not in (tuple, list) or len(pattern_priority) != 4 or
                any(type(index) is not int for index in pattern_priority) or set(pattern_priority) != set(range(4))):
            raise ValueError("raw FPGA priority must permute all four supported patterns")
        self.pattern_priority = tuple(pattern_priority)
        self.collections = tuple(map(optics.collection_matrix, (collection_a, collection_b)))
        self.splitter = optics.beam_splitter_matrix(optics.balanced_beam_splitter() if splitter is None else splitter)
        self.efficiencies = _rates(efficiencies, probabilities=True)
        transfer = optical_transfer(*self.collections, self.splitter, self.efficiencies)
        self.source = joint.JointCounterGenerator(first, second, threshold=1,
                                                 background_rate=0, collection=transfer)
        self.duration = self.source.duration
        if not self.gate_start <= self.interval_start < self.interval_start+self.duration <= self.gate_end:
            raise ValueError("raw source interval must lie in the fixed 2016 120 ns arrival gate")
        self.operators = tuple(tuple(operators for label, operators in self.source.detected_operators
                                     if label[-1] == port) for port in range(4))

    def target(self, mark, port):
        if type(mark) is not Mark or type(port) is not int or not 0 <= port < 4:
            raise ValueError("retained source mark and physical APD port required")
        counts = tuple(min(value+int(i == port), 2) for i, value in enumerate(mark.counts))
        receipt = mark.receipt
        if receipt is None:
            for pattern in self.pattern_priority:
                first, second = PATTERNS[pattern][1]
                if ((port == first and mark.counts[second]) or
                        (port == second and mark.counts[first])):
                    receipt = pattern
                    break
        return Mark(counts, receipt)

    def port_action(self, matrix, port):
        """CP sum over orthogonal environments; interference stays inside each."""
        if type(port) is not int or not 0 <= port < 4:
            raise ValueError("one of four physical APD ports required")
        matrix, result = joint._matrix(matrix), {}
        for operators in self.operators[port]:
            left = local._sum(joint._operator_left(matrix, 0, operators[0]),
                              joint._operator_left(matrix, 1, operators[1]))
            result = local._sum(result, local._sum(
                joint._operator_right(left, 0, dipole.matrix_adjoint(operators[0])),
                joint._operator_right(left, 1, dipole.matrix_adjoint(operators[1]))))
        for key, value in matrix.items():
            local._add(result, key, self.background_rates[port] * value)
        return result

    def lift(self, poststate, mark=INITIAL):
        if type(mark) is not Mark:
            raise ValueError("same attempt source mark required")
        return {(mark, i, j): value for (i, j), value in joint._matrix(poststate).items()}

    def blocks(self, state):
        if type(state) is not dict:
            raise TypeError("source marked sparse joint state required")
        result = {}
        for key, value in state.items():
            if type(key) is not tuple or len(key) != 3 or type(key[0]) is not Mark:
                raise ValueError("source BSM mark and original pair matrix address required")
            checked = joint._matrix({key[1:]: value})
            if checked:
                result.setdefault(key[0], {}).update(checked)
        return result

    def action(self, state):
        result = {}
        for mark, matrix in self.blocks(state).items():
            stay = self.source.independent_atomic_action(matrix)
            for port in range(4):
                move = self.port_action(matrix, port)
                for key, value in move.items():
                    local._add(stay, key, -value)
                target = self.target(mark, port)
                for (i, j), value in move.items():
                    local._add(result, (target, i, j), value)
            for (i, j), value in stay.items():
                local._add(result, (mark, i, j), value)
        return result

    def forget_marks(self, state):
        result = {}
        for matrix in self.blocks(state).values():
            result = local._sum(result, matrix)
        return result

    def observations(self, state):
        success, failure, branches = {"Psi-": {}, "Psi+": {}}, {}, []
        for mark, matrix in self.blocks(state).items():
            weight = joint._trace(matrix)
            if mark.receipt is None:
                failure = local._sum(failure, matrix)
                kind = "no_click" if not any(mark.counts) else (
                    "single_click" if sum(mark.counts) == 1 else "nonherald_multiple")
            else:
                kind = PATTERNS[mark.receipt][0]
                success[kind] = local._sum(success[kind], matrix)
            branches.append({"mark": mark, "kind": kind, "weight": weight, "poststate": matrix})
        total = local._sum(failure, local._sum(*success.values()))
        return {"branches": tuple(branches), "success": success, "failure_poststate": failure,
                "failure_weight": joint._trace(failure), "total_weight": joint._trace(total),
                "unconditional_poststate": total}

    def success_flux(self, state, *, at_time, input_error=0):
        """First-receipt CP-rate readout of the supplied same-source state.

        The time coordinate labels this readout.  It does not certify the
        supplied state's evolution from the interval's initial state.
        """
        at_time = full.exact(at_time)
        input_error = full.nonnegative(input_error)
        if not self.interval_start <= at_time <= self.interval_start+self.duration:
            raise ValueError("same raw source time inside the current gate interval required")
        result = []
        for mark, matrix in self.blocks(state).items():
            if mark.receipt is not None:
                continue
            for port in range(4):
                target = self.target(mark, port)
                if target.receipt is not None:
                    poststate = self.port_action(matrix, port)
                    # Port R_d <= total original two-atom loss by passive
                    # observed/unobserved completeness; background adds b_d I.
                    norm_bound = sum(max(source.outgoing) for source in self.source.sources) + self.background_rates[port]
                    result.append({"at_time": at_time, "source_mark": mark, "target_mark": target,
                                   "detector": PORTS[port], "herald": PATTERNS[target.receipt][0],
                                   "rate": joint._trace(poststate), "poststate_rate": poststate,
                                   "CP_rate_trace_norm_bound": norm_bound,
                                   "rate_and_poststate_error_upper": norm_bound * input_error})
        return tuple(result)

    def taylor(self, state, *, order=8, duration=None, input_error=0):
        duration = self.duration if duration is None else full.nonnegative(duration)
        if duration > self.duration:
            raise ValueError("evolution exceeds its raw source interval")
        state = {
            (mark, i, j): value for mark, matrix in self.blocks(state).items()
            for (i, j), value in matrix.items()}
        centre, error = _taylor(state, self.action, duration, order, input_error)
        return Image(centre, error, duration, self.record())

    def restart_failure(self, state):
        """Clear only failed attempt's classical gate marks, keeping all atoms."""
        return self.lift(self.observations(state)["failure_poststate"])

    def record(self):
        return {"schema": "rb87-full-pair-bsm-retry-source/v1", "physical_dimension": self.physical_dimension,
                "source": self.source.record(), "ports": [list(port) for port in PORTS],
                "background_rates": list(map(str, self.background_rates)),
                "raw_collections": [[[value.serialize() for value in row] for row in matrix] for matrix in self.collections],
                "raw_beam_splitter": [[value.serialize() for value in row] for row in self.splitter],
                "raw_APD_efficiencies": list(map(str, self.efficiencies)),
                "seconds_per_common_time_unit": str(self.seconds_per_unit),
                "arrival_gate_seconds": str(GATE_SECONDS), "gate_start": str(self.gate_start),
                "gate_end": str(self.gate_end), "interval_start": str(self.interval_start),
                "pattern_priority": list(self.pattern_priority), "counts": "0, 1, at least 2 per physical APD",
                "receipt": "first supported pair; atoms and every port continue after receipt",
                "unconditional_source": "original independent full33 atomic baths; exact mark-forgetting identity",
                "APD_hypothesis": "registered jumps, no dead time or afterpulse memory",
                "propagation_hypothesis": "Markov instantaneous common optical output, fixed passive transfer",
                "target_prepared_state_supplied": False, "success_probability_supplied": False,
                "actual_programme_identified": False, "actual_hardware_uniquely_identified": False,
                "controller_advance": False}

    @classmethod
    def from_record(cls, record):
        if type(record) is not dict or record.get("schema") != "rb87-full-pair-bsm-retry-source/v1":
            raise ValueError("registered raw BSM source record required")

        def scalar(value):
            return dipole.ComplexRadical(*(dipole.Radical({int(root): full.exact(coefficient)
                                                          for root, coefficient in value[part].items()})
                                           for part in ("real", "imag")))

        collections = tuple(tuple(tuple(map(scalar, row)) for row in matrix) for matrix in record["raw_collections"])
        if len(collections) != 2:
            raise ValueError("two original raw collection programmes required")
        first, second = (full.Segment.from_record(item) for item in record["source"]["programmes"])
        source = cls(first, second, seconds_per_unit=record["seconds_per_common_time_unit"],
                     collection_a=collections[0], collection_b=collections[1],
                     efficiencies=record["raw_APD_efficiencies"], background_rates=record["background_rates"],
                     splitter=tuple(tuple(map(scalar, row)) for row in record["raw_beam_splitter"]),
                     pattern_priority=record["pattern_priority"], gate_start=record["gate_start"],
                     interval_start=record["interval_start"])
        if source.record() != record:
            raise ValueError("raw BSM optics, bath, clock or scope record mismatch")
        return source


def evolve_pair(first, second, poststate, *, order=8, input_error=0):
    """Raw preparation/excitation/recooling on the same full pair poststate."""
    source = joint.JointCounterGenerator(first, second, threshold=1, background_rate=0,
                                        collection=((0,) * 6,))
    centre, error = _taylor(joint._matrix(poststate), source.independent_atomic_action,
                            source.duration, order, input_error)
    return Image(centre, error, source.duration, {"schema": "rb87-raw-pair-evolution/v1",
                                               "programmes": [first.record(), second.record()]})


def continue_failed_attempt(gate, image, phases, *, completed_cycles, order=8, input_error=0):
    """Apply raw continuation phases to failure, without a target-state reset.

    Phase construction supplies the physical programme, not a success law.
    Forty failures make recooling due; the consumer then feeds its raw cooling
    Segments through the same evolve_pair mouth before the next excitation.
    """
    if type(gate) is not BSMSource or type(image) is not Image:
        raise ValueError("same generated BSM source and finite source image required")
    if image.source_record != gate.record():
        raise ValueError("source image belongs to another raw BSM gate")
    if (gate.interval_start != gate.gate_start or image.duration != gate.gate_end-gate.gate_start):
        raise ValueError("failed continuation requires a complete original arrival gate image")
    if type(completed_cycles) is not int or not 1 <= completed_cycles <= BURST_CYCLES:
        raise ValueError("completed preparation-excitation cycles in the current burst required")
    if type(phases) not in (tuple, list) or any(type(phase) not in (tuple, list) or len(phase) != 2 for phase in phases):
        raise ValueError("ordered pairs of raw full33 continuation phases required")
    state = gate.observations(image.state)["failure_poststate"]
    error, duration = image.trace_norm_error + full.nonnegative(input_error), Q(0)
    for first, second in phases:
        result = evolve_pair(first, second, state, order=order, input_error=error)
        state, error, duration = result.state, result.trace_norm_error, duration+result.duration
    return {"next_pair_image": Image(state, error, duration, {
                "schema": "rb87-raw-failed-attempt-continuation/v1", "gate_source": gate.record(),
                "phases": [[first.record(), second.record()] for first, second in phases]}),
            "recooling_due": completed_cycles == BURST_CYCLES,
            "return_wait_in_common_units": RETURN_SECONDS / gate.seconds_per_unit,
            "recooling_in_common_units": RECOOL_SECONDS / gate.seconds_per_unit,
            "quantum_state_reset": False, "success_probability_supplied": False}
