"""Ion-born gate response from an independently checked full33 trial curve.

For the absorbing raw source, R=G*PiION is the resolved ion-rate diagonal.
Each accepted birth interval contributes kappa*(J(hi)-J(lo)), where
J(t)=exp(t*G*)PiION.  This integral is positive, even for varying gates;
terminal ION is never registered again.  The output is a probability effect,
not a replacement for the window source's retained physical poststate.
"""
from dataclasses import replace
from fractions import Fraction as Q
import hashlib
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import atomic_modes as modes_kernel
import fluorescence_presence as local
import raw_command_family as commands
import window_cem_source as window


SCHEMA = "stage10-ion-born-gated-atomic-response/v1"
ZERO = dipole.ComplexRadical()


def _require(condition, reason):
    if not condition:
        raise ValueError(reason)


def _digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def _raw(segment):
    _require(type(segment) is full.Segment, "closed raw full33 Segment required")
    return full.Segment.from_record(segment.record())


def _registration(registration):
    _require(type(registration) is window.FragmentRegistration, "closed raw FragmentRegistration required")
    return window.FragmentRegistration.from_record(registration.record())


def _command_program(record, bits):
    _require(type(record) is dict and type(record.get("segments")) is list and len(record["segments"]) == 1,
             "one raw command-compiled Segment required")

    def complex_value(value):
        return dipole.ComplexRadical(*(dipole.Radical({int(root): Q(coefficient) for root, coefficient in value[part].items()})
                                      for part in ("real", "imag")))

    transfer = {int(q): tuple(complex_value(value) for value in row) for q, row in record["transfer"].items()}
    templates = [replace(full.Segment.from_record(item), fields_r=dict.fromkeys(dipole.Q_COMPONENTS, 0))
                 for item in record["segments"]]
    rebuilt = commands.compile_commands(transfer, templates, record["command"]["angle"], bits)
    _require(rebuilt.record() == record, "raw command source or its paid Hamiltonian bound changed")
    return rebuilt


def _hermitian(matrix):
    result = {}
    for i, j in set(matrix) | {(j, i) for i, j in matrix}:
        a, b = matrix.get((i, j), (Q(0), Q(0)))
        c, d = matrix.get((j, i), (Q(0), Q(0)))
        full._add(result, (i, j), (a+c)/2, (b-d)/2)
    return result


def _record(matrix):
    return [[i, j, str(a), str(b)] for (i, j), (a, b) in sorted(matrix.items())]


def _read_matrix(record):
    return {(i, j): (Q(a), Q(b)) for i, j, a, b in record}


def _intervals(matrix, basis, error, diagonal_bounds):
    result = []
    for i in basis:
        row = []
        for j in basis:
            a, b = matrix.get((i, j), (Q(0), Q(0)))
            low, high = a-error, a+error
            if i == j:
                low, high = max(diagonal_bounds[0], low), min(diagonal_bounds[1], high)
                _require(low <= high, "mode enclosure misses the source positive-effect bound")
            row.append({"real": [str(low), str(high)],
                        "imag": ["0", "0"] if i == j else [str(b-error), str(b+error)]})
        result.append(row)
    return result


def _qubit(matrix):
    exact = {key: dipole.ComplexRadical(a, b) for key, (a, b) in matrix.items()}
    return {key: (value.real.as_rational(), value.imag.as_rational())
            for key, value in dipole.qubit_restriction(exact).items()}


def _qubit_intervals(matrix, error, diagonal_bounds):
    rows = _intervals(_qubit(matrix), (0, 1), error, diagonal_bounds)
    return {"00": rows[0][0]["real"], "11": rows[1][1]["real"],
            "01": rows[0][1], "10": rows[1][0]}


def _dark_effect(click, born):
    a, b = commands.Interval.read(click["00"]), commands.Interval.read(click["11"])
    re, im = (commands.Interval.read(click["01"][name]) for name in ("real", "imag"))
    zero = commands.Interval(0, 0)
    off = commands.ComplexInterval(-2*re, -2*im)
    operator = ((commands.ComplexInterval(1-2*a, zero), off),
                (off.conjugate(), commands.ComplexInterval(1-2*b, zero)))
    metadata = {**born, "observable": "window-resolved ion-born registration response",
                "terminal_ION_registration_reapplied": False}
    return commands.DetectorEffect(operator, {"mu": 1-a-b, "u": -2*re,
                                             "v": 2*im, "z": b-a}, metadata)


def _partition(segment, registration, start):
    end = start+segment.duration
    edges = sorted({start, end} | {edge for edge in registration.shifted_edges() if start < edge < end})
    return [{"interval_start": str(left), "duration": str(right-left),
             "gates": list(registration.gates(left)), "kappa": str(registration.kappa(left))}
            for left, right in zip(edges, edges[1:])]


def _response_intervals(partition, start):
    result = []
    for item in partition:
        left, width, kappa = map(Q, (item["interval_start"], item["duration"], item["kappa"]))
        right = left+width
        if result and result[-1][2] == kappa:
            result[-1] = result[-1][0], right-start, kappa
        else:
            result.append((left-start, right-start, kappa))
    return tuple(result)


def _native_law(segment, registration, start, partition, flux_checked=None):
    """Check the complete source coefficients, including the native marked flux.

    The partner has identity action; local matrix-unit coefficient identities
    therefore tensor with every partner matrix unit in the native pair source.
    No evolved state or target effect enters this check.
    """
    atom = local.CounterGenerator(segment, threshold=1, background_rate=0,
                                  efficiencies={jump.label: 0 for jump in local.natural_channels(segment)})
    ion = dipole.ION
    _require(not atom.outgoing[ion] and
             all(ion not in (i, j) or i == j for i, j in atom.hamiltonian), "raw ION is not absorbing")
    rates = {dipole.INDEX[state]: rate for state, rate in segment.ion_rates.items() if rate}
    born = {(i, i): dipole.ComplexRadical(rate) for i, rate in rates.items()}
    # All 1089 source coordinates of G*PiION are checked from exact GKSL terms.
    derivative = {}
    for (target, other_target, i, j), value in atom.recycling.items():
        if target == other_target == ion:
            local._add(derivative, (i, j), value.conjugate())
    _require(derivative == born, "exact adjoint PiION differs from raw ion-born flux")
    _require(all(ion not in (i, j) for i, j in born), "born flux has an initial-ION term")
    upper = max((Q(item["kappa"]) for item in partition), default=Q(0))
    eta = 1-registration.probabilities[0]
    _require(0 <= upper <= eta <= 1, "raw joint registration has no positive gate bound")
    if not segment.duration:
        return {"exact_born_observable": [[i, j, value.serialize()] for (i, j), value in sorted(born.items())],
                "complete_source_coordinates": full.COMPLEX_COORDINATES,
                "native_partition_checked": True, "native_flux_coefficients_checked": 0,
                "native_marked_columns_checked": 0,
                "maximum_kappa": str(upper), "absorbing_ION": True}
    end = max(start+segment.duration, registration.electron_window[1], registration.ion_window[1])
    idle = replace(segment, duration=end-start, fields_r=dict.fromkeys(dipole.Q_COMPONENTS, 0),
                   fields_c=dict.fromkeys(dipole.Q_COMPONENTS, 0),
                   detunings=dict.fromkeys(segment.detunings, 0),
                   gammas=dict.fromkeys(full.WIDTHS, 0), ion_rates=dict.fromkeys(full.EXCITED, 0))
    waveform = (segment,) if end == start+segment.duration else (segment, replace(idle, duration=end-start-segment.duration))
    no_registration = window.FragmentRegistration((1, 0, 0, 0), 0, 0, (start, end), (start, end))
    native = window.WindowCEMSource(waveform, (idle,), registrations=(registration, no_registration),
                                   backgrounds=(0, 0), logic_deadlines=(end, end),
                                   seconds_per_unit=1, interval_start=start)
    actual = [{"interval_start": item["interval_start"], "duration": item["duration"],
               "gates": item["gates"][0], "kappa": item["kappas"][0]}
              for item in native.partition if Q(item["interval_start"]) < start+segment.duration]
    _require(actual == partition, "local gate partition differs from native window source")
    checked, marked_checked = flux_checked, 0
    for phase in native.phases():
        if phase.interval_start >= start+segment.duration:
            continue
        _require(phase.ion_rates[0] == rates and phase.kappas[0] == registration.kappa(phase.interval_start),
                 "native marked birth source changed")
        native_atom = phase.sources[0]
        _require(native_atom.hamiltonian == atom.hamiltonian and native_atom.recycling == atom.recycling and
                 native_atom.outgoing == atom.outgoing, "native phase changes the original physical atom action")
        seen = window.Mark((1, 0))
        for excited, rate in rates.items():
            row, target = 33*excited, 33*ion
            value = dipole.ComplexRadical(0, 1)
            action = phase.action({(window.INITIAL, row, row): value})
            clicked = {(i, j): coefficient for (mark, i, j), coefficient in action.items() if mark == seen}
            expected = {(target, target): phase.kappas[0]*rate*value} if phase.kappas[0] else {}
            _require(clicked == expected and all(mark in (window.INITIAL, seen) for mark, _, _ in action),
                     "native marked action differs from the accepted born flux")
            _require(window.forget_marks(action) == phase.independent_atomic_action({(row, row): value}),
                     "native marking changes the original physical poststate action")
            marked_checked += 1
        _require(not phase.action({(window.INITIAL, 33*ion, 33*ion): 1}),
                 "native marked action refills previously born terminal ION")
        marked_checked += 1
        # The native ion channel is diagonal in the emitting atom, and leaves
        # the partner's entire complex matrix unchanged.
        if checked is None:
            checked = 0
            for excited, rate in rates.items():
                for i in range(full.DIMENSION):
                    for j in range(full.DIMENSION):
                        source_key = (33*excited+i, 33*excited+j)
                        target_key = (33*ion+i, 33*ion+j)
                        image = phase.ion_birth_action({source_key: dipole.ComplexRadical(0, 1)}, 0)
                        _require(image == {target_key: dipole.ComplexRadical(0, rate)},
                                 "native ion jump loses a full-complex partner coordinate")
                        checked += 1
    return {"exact_born_observable": [[i, j, value.serialize()] for (i, j), value in sorted(born.items())],
            "complete_source_coordinates": full.COMPLEX_COORDINATES,
            "native_partition_checked": True, "native_flux_coefficients_checked": checked,
            "native_marked_columns_checked": marked_checked,
            "maximum_kappa": str(upper), "absorbing_ION": True}


class GatedAtomicSource:
    """Shared residual check for one raw generator and reusable prefix modes."""

    def __init__(self, segment, witness, *, coefficient_bits=160, exponential_bits=160):
        self.segment = _raw(segment)
        _require(type(witness) is dict and set(witness) == {"raw_program", "mode_bits", "modes"},
                 "raw mode witness required; a target effect is not input")
        self.witness = json.loads(json.dumps(witness))
        old = full.Segment.from_record(self.witness["raw_program"])
        _require(old.record() == self.witness["raw_program"], "canonical raw mode source required")
        first, second = self.segment.record(), old.record()
        first.pop("duration"); second.pop("duration")
        _require(first == second and self.segment.duration <= old.duration,
                 "mode witness belongs to a different raw generator or uncovered duration")
        self.mode_bits, self.witness_duration = self.witness["mode_bits"], old.duration
        _require(type(self.mode_bits) is int and 32 <= self.mode_bits <= 256, "registered mode dyadic precision required")
        _require(type(exponential_bits) is int and 64 <= exponential_bits <= 1024, "registered scalar precision required")
        self.coefficient_bits, self.exponential_bits = coefficient_bits, exponential_bits
        self.generator = full.Generator(self.segment, coefficient_bits)
        self.quantum = 1 << self.mode_bits
        _require(type(self.witness["modes"]) is list and self.witness["modes"], "nonempty raw trial mode inventory required")
        initial, residual_sum, records, terms = {}, Q(0), [], []
        for item in self.witness["modes"]:
            _require(type(item) is dict and set(item) == {"lambda", "matrix"}, "raw mode identity required")
            _require(type(item["lambda"]) is list and len(item["lambda"]) == 2 and
                     all(type(value) is int for value in item["lambda"]), "dyadic complex mode exponent required")
            lr, li = item["lambda"]
            _require(Q(lr, self.quantum)*self.segment.duration <= Q(1, 2), "bounded mode growth required")
            matrix = modes_kernel._matrix(item["matrix"], self.quantum)
            action = modes_kernel.adjoint_integer_action(self.generator, matrix)
            norm = residual = Q(0)
            for key in set(matrix) | set(action):
                a, b = matrix.get(key, (0, 0)); u, v = action.get(key, (0, 0))
                residual += abs(Q(u, self.generator.denominator*self.quantum)-Q(lr*a-li*b, self.quantum**2))
                residual += abs(Q(v, self.generator.denominator*self.quantum)-Q(li*a+lr*b, self.quantum**2))
                norm += Q(abs(a)+abs(b), self.quantum)
                full._add(initial, key, Q(a, self.quantum), Q(b, self.quantum))
            terms.append((lr, li, matrix, norm))
            residual_sum += residual
            records.append({"entry_norm_bound": str(norm), "residual_entry_norm_bound": str(residual)})
        initial_error = sum((abs(a-int(key == (dipole.ION, dipole.ION)))+abs(b)
                             for key, (a, b) in initial.items()), Q(0))
        if (dipole.ION, dipole.ION) not in initial:
            initial_error += 1
        self.initial_error, self.residual_sum = initial_error, residual_sum
        self.terms, self.mode_error_records = tuple(terms), records
        self._curves = {Q(0): ({(dipole.ION, dipole.ION): (Q(1), Q(0))}, Q(0), Q(0))}
        self._laws, self._flux_checked = {}, None

    def _curve(self, time):
        if time not in self._curves:
            matrix, exponential_error = {}, Q(0)
            for lr, li, term, norm in self.terms:
                scalar, error = modes_kernel.complex_exponential(Q(lr, self.quantum)*time,
                                                                Q(li, self.quantum)*time,
                                                                bits=self.exponential_bits)
                for key, (a, b) in term.items():
                    full._add(matrix, key, (a*scalar[0]-b*scalar[1])/self.quantum,
                              (b*scalar[0]+a*scalar[1])/self.quantum)
                exponential_error += norm*error
            error = (self.initial_error+2*time*self.residual_sum+
                     time*self.generator.generator_difference_bound+exponential_error)
            self._curves[time] = _hermitian(matrix), error, exponential_error
        return self._curves[time]

    def certify(self, registration, *, duration=None, background=0, interval_start=0):
        registration = _registration(registration)
        duration = self.segment.duration if duration is None else full.nonnegative(duration)
        _require(duration <= self.segment.duration, "prefix exceeds checked raw source duration")
        raw = replace(self.segment, duration=duration)
        start, background = full.nonnegative(interval_start), commands.probability(background)
        partition = _partition(raw, registration, start)
        law_key = _digest([raw.record(), registration.record(), str(start)])
        if law_key not in self._laws:
            self._laws[law_key] = _native_law(raw, registration, start, partition, self._flux_checked)
            if duration:
                self._flux_checked = self._laws[law_key]["native_flux_coefficients_checked"]
        law = self._laws[law_key]
        response, error, differences = {}, Q(0), []
        for lo, hi, kappa in _response_intervals(partition, start):
            if not kappa:
                differences.append({"lo": str(lo), "hi": str(hi), "kappa": "0", "difference_error_bound": "0"})
                continue
            left, left_error, _ = self._curve(lo)
            right, right_error, _ = self._curve(hi)
            for key in set(left) | set(right):
                a, b = left.get(key, (Q(0), Q(0))); c, d = right.get(key, (Q(0), Q(0)))
                if dipole.ION not in key:
                    full._add(response, key, kappa*(c-a), kappa*(d-b))
            payment = kappa*(left_error+right_error)
            error += payment
            differences.append({"lo": str(lo), "hi": str(hi), "kappa": str(kappa),
                                "lo_curve_error": str(left_error), "hi_curve_error": str(right_error),
                                "difference_error_bound": str(payment)})
        _require(full._hermitian(response), "complete gated response is not Hermitian")
        upper = Q(law["maximum_kappa"])
        click = {key: ((1-background)*a, (1-background)*b) for key, (a, b) in response.items()}
        for i in range(full.DIMENSION):
            full._add(click, (i, i), background)
        click_error = (1-background)*error
        qubit_born = _qubit_intervals(response, error, (Q(0), upper))
        qubit_click = _qubit_intervals(click, click_error, (background, background+(1-background)*upper))
        ground = [dipole.INDEX[dipole.State("ground", 1, m)] for m in (-1, 0, 1)]
        result = {"schema": SCHEMA, "raw_program": raw.record(), "raw_registration": registration.record(),
                "raw_program_sha256": full._program_digest([raw.record()]), "mode_witness_sha256": _digest(self.witness),
                "witness_duration": str(self.witness_duration), "checked_duration": str(self.segment.duration),
                "mode_bits": self.mode_bits, "coefficient_bits": self.coefficient_bits, "exponential_bits": self.exponential_bits,
                "mode_count": len(self.terms), "mode_error_records": self.mode_error_records,
                "initial_operator_error": str(self.initial_error), "residual_entry_norm_bound": str(self.residual_sum),
                "source_generator_difference_bound": str(self.generator.generator_difference_bound),
                "interval_start": str(start), "duration": str(duration), "background": str(background),
                "intrinsic_fragment_efficiency": str(1-registration.probabilities[0]),
                "gate_partition": partition, "difference_error_records": differences, "native_source_law": law,
                "born_effect_center": _record(response), "operator_error_bound": str(error),
                "click_effect_center": _record(click), "click_operator_error_bound": str(click_error),
                "source_qubit_born_effect": qubit_born, "source_qubit_click_effect": qubit_click,
                "source_qubit_dark_effect": _dark_effect(qubit_click, qubit_born).record(),
                "ground_basis": ground, "ground_F1_born_effect": _intervals(response, ground, error, (Q(0), upper)),
                "physical_dimension": full.DIMENSION, "observable_complex_coordinates": full.COMPLEX_COORDINATES,
                "positive_effect_bound": {"lower": "0", "upper": str(upper), "upper_support": "neutral projector",
                                          "law": "positive CP birth integral; sum of increments <= neutral projector"},
                "ION_rows_exactly_zero": True, "initial_occupied_neutral_required": True,
                "full_complex_effect_retained": True, "physical_poststate_replaced": False,
                "background_composed_once": True, "terminal_ION_registration_reapplied": False,
                "eigenvector_correctness_assumed": False, "target_effect_supplied": False,
                "error_transport": "unital CP adjoint curve contraction; sum of weighted difference bounds",
                "solver_reexecuted_by_checker": False, "actual_hardware_uniquely_identified": False,
                "controller_advance": False}
        return json.loads(json.dumps(result))

    def certify_command_program(self, program, registration, *, duration=None, background=0,
                                interval_start=0, command_bits=240):
        """Pay a reconstructed raw command's error in the complete marked source.

        Both exact-command and midpoint marked generators are CPTP and differ
        only by the same Hamiltonian on each classical block.  Duhamel gives
        2*T*||delta H|| once for the whole interval.  A constant kappa uses
        the exact reduction E=kappa*(J(T)-PiION), preserving the old payment.
        """
        _require(type(program) is commands.CommandProgram, "closed raw CommandProgram required")
        rebuilt = _command_program(program.record(), command_bits)
        _require(rebuilt.segments[0].record() == self.segment.record(), "command programme has a different raw Segment")
        report = self.certify(registration, duration=duration, background=background, interval_start=interval_start)
        chosen_duration = Q(report["duration"])
        template = replace(rebuilt.segments[0], duration=chosen_duration, fields_r=dict.fromkeys(dipole.Q_COMPONENTS, 0))
        prefix = commands.compile_commands(rebuilt.transfer, [template], rebuilt.command.angle, command_bits)
        _require(prefix.segments[0].record() == report["raw_program"], "command prefix changes the raw generator")
        kappas = {Q(item["kappa"]) for item in report["gate_partition"]}
        factor = next(iter(kappas)) if len(kappas) == 1 else Q(1)
        if not kappas:
            factor = Q(0)
        command_error = factor*prefix.command_trace_norm_error
        curve_error = Q(report["operator_error_bound"])
        total_error = curve_error+command_error
        born = _read_matrix(report["born_effect_center"])
        click = _read_matrix(report["click_effect_center"])
        background = Q(report["background"])
        upper = Q(report["positive_effect_bound"]["upper"])
        click_error = (1-background)*total_error
        qubit_born = _qubit_intervals(born, total_error, (Q(0), upper))
        qubit_click = _qubit_intervals(click, click_error, (background, background+(1-background)*upper))
        return {**report, "command_program": rebuilt.record(), "command_bits": command_bits,
                "raw_command_trace_norm_error": str(prefix.command_trace_norm_error),
                "command_gate_factor": str(factor), "command_source_operator_error": str(command_error),
                "curve_operator_error_bound": str(curve_error), "operator_error_bound": str(total_error),
                "click_operator_error_bound": str(click_error),
                "source_qubit_born_effect": qubit_born, "source_qubit_click_effect": qubit_click,
                "source_qubit_dark_effect": _dark_effect(qubit_click, qubit_born).record(),
                "ground_F1_born_effect": _intervals(born, report["ground_basis"], total_error, (Q(0), upper)),
                "command_error_transport": "one full-mark CPTP Hamiltonian Duhamel payment; exact constant-gate scaling"}


def certify(segment, registration, witness, *, background=0, interval_start=0,
            coefficient_bits=160, exponential_bits=160):
    return GatedAtomicSource(segment, witness, coefficient_bits=coefficient_bits,
                             exponential_bits=exponential_bits).certify(
                                 registration, background=background, interval_start=interval_start)


def certify_command_program(program, registration, witness, *, duration=None, background=0,
                            interval_start=0, command_bits=240, coefficient_bits=160, exponential_bits=160):
    _require(type(program) is commands.CommandProgram and len(program.segments) == 1,
             "one closed raw CommandProgram required")
    source = GatedAtomicSource(program.segments[0], witness, coefficient_bits=coefficient_bits,
                               exponential_bits=exponential_bits)
    return source.certify_command_program(program, registration, duration=duration, background=background,
                                          interval_start=interval_start, command_bits=command_bits)


def verify_certificate(report, witness, *, segment=None, registration=None, command_program=None):
    _require(type(report) is dict and report.get("schema") == SCHEMA, "ion-born gated response certificate required")
    raw = full.Segment.from_record(report["raw_program"]) if segment is None else _raw(segment)
    registration = window.FragmentRegistration.from_record(report["raw_registration"]) if registration is None else _registration(registration)
    _require(raw.record() == report["raw_program"] and registration.record() == report["raw_registration"],
             "gated response raw source mismatch")
    checked = replace(raw, duration=Q(report["checked_duration"]))
    source = GatedAtomicSource(checked, witness, coefficient_bits=report["coefficient_bits"],
                               exponential_bits=report["exponential_bits"])
    if "command_program" in report:
        rebuilt = _command_program(report["command_program"], report["command_bits"])
        if command_program is not None:
            _require(type(command_program) is commands.CommandProgram and command_program.record() == rebuilt.record(),
                     "gated response command source mismatch")
        expected = source.certify_command_program(rebuilt, registration, duration=raw.duration,
                                                  background=report["background"], interval_start=report["interval_start"],
                                                  command_bits=report["command_bits"])
    else:
        _require(command_program is None, "certificate omits the commanded source")
        expected = source.certify(registration, duration=raw.duration, background=report["background"],
                                  interval_start=report["interval_start"])
    _require(expected == report, "gated response certificate mismatch")
    return True


def detector_effect(report, witness):
    """Independently check, then expose the existing complete joint consumer API."""
    verify_certificate(report, witness)
    return _dark_effect(report["source_qubit_click_effect"], report["source_qubit_born_effect"])
