"""原 full33 pair 的电离出生、飞行和窗口注册源。

全部时间相对同一 receipt 原点，单位由 seconds_per_unit 给出。Mark 的四个
地址表示“此次出生被分配到截止前的可接受碎片”，不是中间时刻已到达的点击。
最终 CEM logic 截止才加入各侧 background。窗口不改物理电离率或原后态。
电子/离子注册保留 raw joint 四分支；不接受目标 effect、任意 G 或完成的后态。
"""
from dataclasses import dataclass, replace
from fractions import Fraction as Q
from itertools import product
import hashlib
import json
from pathlib import Path

import atomic_dipole as dipole
import atomic_full_forward as full
import fluorescence_presence as local
import joint_fluorescence_presence as joint
import fluorescence_channel as channel
import cem_pair_source as cem
import trap_reload_source as trap


ZERO = dipole.ComplexRadical()
SOURCE_SCHEMA = "rb87-window-resolved-pair-CEM-source/v1"
PHASE_SCHEMA = "rb87-window-resolved-pair-CEM-phase/v1"
SCHEMA = "stage10-window-resolved-pair-CEM-enclosure/v1"
STEP_SCHEMA = "stage10-window-resolved-pair-CEM-step-enclosure/v1"
REGISTRATION_ORDER = ((0, 0), (0, 1), (1, 0), (1, 1))


def _require(condition, reason):
    channel._require(condition, reason)


@dataclass(frozen=True)
class Mark:
    clicks: tuple

    def __post_init__(self):
        _require(type(self.clicks) is tuple and len(self.clicks) == 2 and
                 all(type(bit) is int and bit in (0, 1) for bit in self.clicks),
                 "two accepted-fragment bit addresses required")

    def with_click(self, side):
        _require(type(side) is int and side in (0, 1), "original A/B side address required")
        return Mark(tuple(1 if index == side else bit for index, bit in enumerate(self.clicks)))


INITIAL = Mark((0, 0))
MARKS = tuple(Mark(bits) for bits in REGISTRATION_ORDER)


def mark_index(mark):
    _require(type(mark) is Mark, "original window-CEM Mark required")
    return 2*mark.clicks[0]+mark.clicks[1]


def index_mark(index):
    _require(type(index) is int and 0 <= index < 4, "four-level CEM bit address required")
    return MARKS[index]


def _window(values):
    _require(type(values) is tuple and len(values) == 2, "raw half-open acceptance window required")
    start, end = map(full.exact, values)
    _require(start < end, "positive raw acceptance-window width required")
    return start, end


@dataclass(frozen=True)
class FragmentRegistration:
    probabilities: tuple
    electron_flight: Q
    ion_flight: Q
    electron_window: tuple
    ion_window: tuple

    def __post_init__(self):
        _require(type(self.probabilities) is tuple and len(self.probabilities) == 4,
                 "raw p00,p01,p10,p11 joint fragment probabilities required")
        probabilities = tuple(map(full.nonnegative, self.probabilities))
        _require(sum(probabilities, Q(0)) == 1, "raw joint registration probabilities must sum to one")
        object.__setattr__(self, "probabilities", probabilities)
        for name in ("electron_flight", "ion_flight"):
            object.__setattr__(self, name, full.nonnegative(getattr(self, name)))
        for name in ("electron_window", "ion_window"):
            object.__setattr__(self, name, _window(getattr(self, name)))

    def gates(self, birth_time):
        time = full.exact(birth_time)
        return tuple(int(start <= time+flight < end) for flight, (start, end) in (
            (self.electron_flight, self.electron_window), (self.ion_flight, self.ion_window)))

    def kappa(self, birth_time):
        electron, ion = self.gates(birth_time)
        p00, p01, p10, p11 = self.probabilities
        return p10*electron+p01*ion+p11*int(bool(electron or ion))

    def shifted_edges(self):
        return tuple(edge-flight for flight, window in (
            (self.electron_flight, self.electron_window), (self.ion_flight, self.ion_window)) for edge in window)

    def branches(self, birth_time):
        time = full.exact(birth_time)
        gates = self.gates(time)
        return tuple({"registered": bits, "probability": probability,
                      "arrival_times": (time+self.electron_flight, time+self.ion_flight),
                      "in_window": gates,
                      "accepted": tuple(bit*gate for bit, gate in zip(bits, gates)),
                      "click": int(any(bit*gate for bit, gate in zip(bits, gates)))}
                     for bits, probability in zip(REGISTRATION_ORDER, self.probabilities))

    def record(self):
        return {"schema": "rb87-raw-joint-fragment-registration/v1",
                "probabilities_p00_p01_p10_p11": list(map(str, self.probabilities)),
                "electron_flight": str(self.electron_flight), "ion_flight": str(self.ion_flight),
                "electron_window": list(map(str, self.electron_window)),
                "ion_window": list(map(str, self.ion_window)),
                "window_convention": "half-open [start,end)", "electron_ion_independence_assumed": False}

    @classmethod
    def from_record(cls, record):
        _require(type(record) is dict and record.get("schema") == "rb87-raw-joint-fragment-registration/v1",
                 "closed raw joint fragment-registration record required")
        result = cls(tuple(record["probabilities_p00_p01_p10_p11"]), record["electron_flight"],
                     record["ion_flight"], tuple(record["electron_window"]), tuple(record["ion_window"]))
        _require(result.record() == record, "raw fragment registration identity or scope changed")
        return result


def _waveform(segments):
    _require(type(segments) in (tuple, list) and segments, "complete raw full33 waveform required")
    _require(all(type(segment) is full.Segment for segment in segments), "original raw Segment inventory required")
    result = tuple(full.Segment.from_record(segment.record()) for segment in segments)
    _require(all(segment.duration > 0 for segment in result), "positive waveform segment widths required")
    return result


class WindowCEMSource:
    physical_dimension = joint.DIMENSION

    def __init__(self, first, second, *, registrations, backgrounds, logic_deadlines,
                 seconds_per_unit, interval_start=0):
        self.waveforms = _waveform(first), _waveform(second)
        self.duration = sum((segment.duration for segment in self.waveforms[0]), Q(0))
        _require(self.duration == sum((segment.duration for segment in self.waveforms[1]), Q(0)),
                 "both original waveforms must cover the same physical interval")
        self.interval_start = full.nonnegative(interval_start)
        self.seconds_per_unit = full.exact(seconds_per_unit)
        _require(self.seconds_per_unit > 0, "positive common physical time unit required")
        _require(type(registrations) is tuple and len(registrations) == 2 and
                 all(type(item) is FragmentRegistration for item in registrations),
                 "two side-owned raw FragmentRegistration sources required")
        self.registrations = tuple(FragmentRegistration.from_record(item.record()) for item in registrations)
        _require(type(backgrounds) is tuple and len(backgrounds) == 2 and
                 type(logic_deadlines) is tuple and len(logic_deadlines) == 2,
                 "two side-owned backgrounds and CEM logic deadlines required")
        self.backgrounds = tuple(map(full.nonnegative, backgrounds))
        self.logic_deadlines = tuple(map(full.exact, logic_deadlines))
        _require(all(value <= 1 for value in self.backgrounds), "raw background probability exceeds one")
        end = self.interval_start+self.duration
        for registration, deadline in zip(self.registrations, self.logic_deadlines):
            _require(self.interval_start <= deadline <= end and
                     max(registration.electron_window[1], registration.ion_window[1]) <= deadline,
                     "waveforms must cover each logic cutoff after its acceptance windows")
        edges, boundaries = {self.interval_start, end}, []
        for waveform in self.waveforms:
            time, side = self.interval_start, []
            for segment in waveform:
                side.append((time, time+segment.duration))
                edges.add(time+segment.duration)
                time += segment.duration
            boundaries.append(tuple(side))
        for registration in self.registrations:
            edges.update(edge for edge in registration.shifted_edges() if self.interval_start < edge < end)
        self.edges, self.waveform_intervals = tuple(sorted(edges)), tuple(boundaries)
        self.partition = tuple(self._phase_record(index) for index in range(len(self.edges)-1))

    def _phase_record(self, index):
        start, end = self.edges[index:index+2]
        positions = tuple(next(i for i, (left, right) in enumerate(side) if left <= start < right)
                          for side in self.waveform_intervals)
        return {"index": index, "interval_start": str(start), "duration": str(end-start),
                "waveform_indices": list(positions),
                "gates": [list(item.gates(start)) for item in self.registrations],
                "kappas": [str(item.kappa(start)) for item in self.registrations]}

    def phases(self):
        return tuple(WindowCEMPhase(self, index) for index in range(len(self.partition)))

    def phase(self, index):
        return WindowCEMPhase(self, index)

    def lift(self, initial, *, trap_histories):
        matrix = cem._poststate(initial, trap_histories)
        for (row, column) in matrix:
            for side, history in enumerate(trap_histories):
                _require(not history.occupied or dipole.ION not in (divmod(row, 33)[side], divmod(column, 33)[side]),
                         "occupied initial ION needs a source-owned departure time; neutral input required")
        return {(INITIAL, i, j): value for (i, j), value in matrix.items()}

    def background_action(self, state):
        """截止处的单次 CP OR；不重用 terminal ION 判据再注册一次。"""
        result = {}
        for mark, matrix in _blocks(state).items():
            for noise in REGISTRATION_ORDER:
                weight = Q(1)
                for bit, probability in zip(noise, self.backgrounds):
                    weight *= probability if bit else 1-probability
                target = Mark(tuple(int(bool(click or bit)) for click, bit in zip(mark.clicks, noise)))
                for (i, j), value in matrix.items():
                    local._add(result, (target, i, j), weight*value)
        return result

    def _image(self, image):
        _require(type(image) is cem.Image and image.source_record == self.record(), "same-source window-CEM image required")
        cem._histories(image.parent_trap_histories)
        full.nonnegative(image.trace_norm_error)
        return image

    def forget_poststate(self, report):
        verify_certificate(report, self)
        return cem.PairCEMInstrument.forget_marks(self, _image_from_report(report))

    def poststate(self, report, clicks):
        verify_certificate(report, self)
        return cem.PairCEMInstrument.poststate(self, _image_from_report(report), clicks)

    def observations(self, report):
        verify_certificate(report, self)
        generated = _image_from_report(report)
        result = []
        for clicks in REGISTRATION_ORDER:
            state = cem.PairCEMInstrument.poststate(self, generated, clicks)
            trace = joint._trace(state)
            _require(not trace.imag, "window-CEM source trace must be real")
            center, rounding = full.radical_midpoint(trace.real, 160)
            error = generated.trace_norm_error+rounding
            result.append({"clicks": clicks, "poststate": state, "trace_bounds": (center-error, center+error),
                           "trace_norm_error": generated.trace_norm_error})
        return result

    def coarsen(self, report, *, clicks, photon_counter=0):
        """独立核完整 report 后消费；同 record 的可变 Image 不承担来源。"""
        verify_certificate(report, self)
        image = self._image(_image_from_report(report))
        cem.PairCEMInstrument.poststate(self, image, clicks)
        _require(type(photon_counter) is int and photon_counter >= 0, "nonnegative retained photon counter required")
        result = {}
        for (mark, row, column), value in image.state.items():
            if mark.clicks != clicks:
                continue
            histories = []
            for side, previous in enumerate(image.parent_trap_histories):
                if not previous.occupied or not mark.fragments[side]:
                    histories.append(previous)
                    continue
                receipt = {"pair_event": image.receipt, "side": side, "clicks": list(mark.clicks),
                           "fragment_generated": True}
                fragment = trap.DepartedFragment(previous.current_atom_epoch, "programme-CEM-ion", cem._canonical(receipt))
                histories.append(trap.TrapHistory(previous.old_atom_epoch, previous.original_cem_receipt_json,
                                 previous.birth_modes, previous.departed_fragments+(fragment,), False))
            local._add(result, (tuple(histories), photon_counter, row, column), value)
        return result

    def record(self):
        return {"schema": SOURCE_SCHEMA, "waveforms": [[item.record() for item in side] for side in self.waveforms],
                "registrations": [item.record() for item in self.registrations],
                "backgrounds": list(map(str, self.backgrounds)), "logic_deadlines": list(map(str, self.logic_deadlines)),
                "seconds_per_unit": str(self.seconds_per_unit), "interval_start": str(self.interval_start),
                "duration": str(self.duration), "phase_inventory": list(self.partition),
                "physical_dimension": joint.DIMENSION, "atom_dimension": full.DIMENSION,
                "mark_levels": 4, "mark_index": "2*A_seen+B_seen; bit address, not threshold",
                "mark_time_semantics": "accepted-by-cutoff allocation at birth; not arrival-time click history",
                "background_time_semantics": "one independent Bernoulli per side at its logic cutoff; deferred commuting OR",
                "ionization_changed_by_window": False, "full_pair_poststate_retained": True,
                "initial_occupied_ION_with_unknown_birth_time_allowed": False,
                "actual_hardware_uniquely_identified": False, "controller_advance": False}

    @classmethod
    def from_record(cls, record):
        _require(type(record) is dict and record.get("schema") == SOURCE_SCHEMA, "closed raw window-CEM source record required")
        _require(len(record["waveforms"]) == len(record["registrations"]) == 2, "both original atom sources required")
        source = cls(*(tuple(full.Segment.from_record(item) for item in side) for side in record["waveforms"]),
                     registrations=tuple(FragmentRegistration.from_record(item) for item in record["registrations"]),
                     backgrounds=tuple(record["backgrounds"]), logic_deadlines=tuple(record["logic_deadlines"]),
                     seconds_per_unit=record["seconds_per_unit"], interval_start=record["interval_start"])
        _require(source.record() == record, "raw window-CEM source identity or derived partition changed")
        return source


def _blocks(state):
    _require(type(state) is dict, "source full marked pair matrix required")
    result = {}
    for key, value in state.items():
        _require(type(key) is tuple and len(key) == 3 and type(key[0]) is Mark,
                 "original CEM Mark and full pair addresses required")
        matrix = joint._matrix({key[1:]: value})
        if matrix:
            result.setdefault(key[0], {}).update(matrix)
    return result


def forget_marks(state):
    result = {}
    for matrix in _blocks(state).values():
        result = local._sum(result, matrix)
    return result


class WindowCEMPhase:
    """闭合的原 GKSL phase；κ 只能从其 raw parent waveform/windows 生成。"""
    physical_dimension = joint.DIMENSION

    def __init__(self, source, index):
        _require(type(source) is WindowCEMSource and type(index) is int and 0 <= index < len(source.partition),
                 "closed WindowCEMSource and its generated phase address required")
        self.parent, self.index = source, index
        item = source.partition[index]
        self.interval_start, self.duration = full.exact(item["interval_start"]), full.exact(item["duration"])
        self.kappas = tuple(registration.kappa(self.interval_start) for registration in source.registrations)
        raw = tuple(replace(side[position], duration=self.duration)
                    for side, position in zip(source.waveforms, item["waveform_indices"]))
        self.sources = tuple(local.CounterGenerator(program, threshold=1, background_rate=0,
                             efficiencies={jump.label: 0 for jump in local.natural_channels(program)}) for program in raw)
        self.ion_rates = tuple({dipole.INDEX[state]: rate for state, rate in program.ion_rates.items() if rate}
                               for program in raw)

    independent_atomic_action = joint.JointCounterGenerator.independent_atomic_action

    def ion_birth_action(self, matrix, side):
        _require(type(side) is int and side in (0, 1), "original A/B side address required")
        result = {}
        for (row, column), value in joint._matrix(matrix).items():
            first, second = divmod(row, 33), divmod(column, 33)
            if first[side] != second[side]:
                continue
            rate = self.ion_rates[side].get(first[side], Q(0))
            if rate:
                targets = tuple(33*dipole.ION+indices[1] if side == 0 else 33*indices[0]+dipole.ION
                                for indices in (first, second))
                local._add(result, targets, rate*value)
        return result

    def action(self, state):
        result = {}
        for mark, matrix in _blocks(state).items():
            stay = self.independent_atomic_action(matrix)
            for side, kappa in enumerate(self.kappas):
                for (i, j), value in self.ion_birth_action(matrix, side).items():
                    local._add(stay, (i, j), -kappa*value)
                    local._add(result, (mark.with_click(side), i, j), kappa*value)
            for (i, j), value in stay.items():
                local._add(result, (mark, i, j), value)
        return result

    def birth_flux(self, state, *, at_time=None):
        time = self.interval_start if at_time is None else full.exact(at_time)
        _require(self.interval_start <= time < self.interval_start+self.duration, "birth time outside generated phase")
        result = []
        for mark, matrix in _blocks(state).items():
            for side in (0, 1):
                birth = self.ion_birth_action(matrix, side)
                for branch in self.parent.registrations[side].branches(time):
                    result.append({"side": side, "birth_time": time, "source_mark": mark, **branch,
                                   "target_mark": mark.with_click(side) if branch["click"] else mark,
                                   "poststate_rate": {key: branch["probability"]*value for key, value in birth.items()
                                                      if branch["probability"]*value}})
        return tuple(result)

    def record(self):
        return {"schema": PHASE_SCHEMA, "raw_source": self.parent.record(), "phase_index": self.index,
                "generated_phase": self.parent.partition[self.index]}

    @classmethod
    def from_record(cls, record):
        _require(type(record) is dict and record.get("schema") == PHASE_SCHEMA, "closed raw window-CEM phase record required")
        phase = cls(WindowCEMSource.from_record(record["raw_source"]), record["phase_index"])
        _require(phase.record() == record, "raw phase or generated marking changed")
        return phase


class _MarkProjection:
    def __init__(self, record):
        self.phase = WindowCEMPhase.from_record(record)
        self.duration, self.threshold = self.phase.duration, 3

    def record(self):
        return self.phase.record()

    def action(self, matrix):
        raw = {(index_mark(c), i, j): value for (c, i, j), value in matrix.items()}
        return {(mark_index(mark), i, j): value for (mark, i, j), value in self.phase.action(raw).items()}


class SourceKernel(channel.SourceKernel):
    def __init__(self, phase, coefficient_bits=160):
        _require(type(phase) is WindowCEMPhase, "closed raw WindowCEMPhase required; arbitrary G is not input")
        _require(type(coefficient_bits) is int and 64 <= coefficient_bits <= 512, "registered coefficient precision required")
        self.source = _MarkProjection(phase.record())
        self.dimension, self.threshold, self.bits = joint.DIMENSION, 3, coefficient_bits
        self.columns, self.exact_columns, self.errors = {}, {}, {}


def _initial_marked(matrix):
    result = {}
    for mark, block in _blocks(matrix).items():
        for (i, j), value in block.items():
            _require(block.get((j, i), ZERO) == value.conjugate(), "Hermitian full marked source input required")
            result[mark_index(mark), i, j] = value
    return result


def _marked_record(matrix):
    return [[c, i, j, value.serialize()] for (c, i, j), value in sorted(matrix.items())]


def _read_marked(record):
    _require(type(record) is list, "complete initial marked source record required")
    result = {}
    for item in record:
        _require(type(item) is list and len(item) == 4, "marked source record entry required")
        c, i, j, value = item
        key = index_mark(c), i, j
        _require(key not in result, "duplicate source marked address")
        result[key] = channel._complex_record(value)
    _initial_marked(result)
    return result


def _read_histories(records):
    _require(type(records) is list and len(records) == 2, "two original trap cohort records required")
    histories = tuple(trap.TrapHistory(item["old_atom_epoch"], cem._canonical(item["cem_receipt"]),
                      tuple(dipole.State(*mode) for mode in item["birth_modes"]),
                      tuple(trap.DepartedFragment(fragment["atom_epoch"], fragment["stage"],
                            None if fragment["cem_receipt"] is None else cem._canonical(fragment["cem_receipt"]))
                            for fragment in item["departed_fragments"]), item["occupied"]) for item in records)
    _require(list(cem._histories(histories)) == records, "source cohort identity or departure record changed")
    return histories


def _precisions(mode_bits, coefficient_bits, exponential_bits):
    _require(type(mode_bits) is int and 32 <= mode_bits <= 256, "registered trial-mode precision required")
    _require(type(coefficient_bits) is int and 64 <= coefficient_bits <= 512, "registered coefficient precision required")
    _require(type(exponential_bits) is int and 64 <= exponential_bits <= 1024, "registered scalar precision required")


def _center(matrix, bits):
    center, error = {}, Q(0)
    for key, value in matrix.items():
        a, da = full.radical_midpoint(value.real, bits)
        b, db = full.radical_midpoint(value.imag, bits)
        full._add(center, key, a, b)
        error += da+db
    return center, error


def _observations(center, error):
    total, blocks = {}, []
    for index, mark in enumerate(MARKS):
        matrix = {(i, j): value for (c, i, j), value in center.items() if c == index}
        for key, (a, b) in matrix.items():
            full._add(total, key, a, b)
        blocks.append({"mark_index": index, "clicks": list(mark.clicks), **channel._observation(matrix, error)})
    return {"mark_blocks": blocks, "unconditional": channel._observation(total, error)}


def _bindings():
    paths = {Path(module.__file__).resolve() for module in (dipole, full, local, joint, channel, cem, trap)}
    paths.update((Path(__file__).resolve(), Path(channel.modes.__file__).resolve(), Path(channel.photons.__file__).resolve()))
    return [{"path": str(path.relative_to(full.ROOT)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
            for path in sorted(paths)]


def _checked_step(phase, center, error, pieces, mode_bits, coefficient_bits, exponential_bits):
    _require(type(pieces) is list, "complete raw phase trial pieces required")
    kernel, elapsed, records = SourceKernel(phase, coefficient_bits), Q(0), []
    for piece in pieces:
        width, begin, end, errors, diagnostics = channel._piece(kernel, piece, mode_bits, exponential_bits)
        gap = channel._difference(begin, center)
        error += gap+sum(errors.values(), Q(0))
        elapsed += width
        _require(elapsed <= phase.duration, "trial piece crosses a generated waveform/window edge")
        records.append({"duration": str(width), "initial_join_error": str(gap),
                        **{key: str(value) for key, value in errors.items()}, "modes": diagnostics})
        center = end
    _require(elapsed == phase.duration, "trial pieces must cover the whole generated phase")
    return center, error, {"generated_phase": phase.parent.partition[phase.index],
                           "source_columns_checked": len(kernel.columns), "piece_error_records": records}


def certify_step(phase, initial, pieces, *, upstream_error=0, mode_bits=60,
                 coefficient_bits=160, exponential_bits=160):
    _precisions(mode_bits, coefficient_bits, exponential_bits)
    _require(type(phase) is WindowCEMPhase, "closed raw WindowCEMPhase required; arbitrary G is not input")
    phase = WindowCEMPhase.from_record(phase.record())
    matrix, inherited = _initial_marked(initial), full.nonnegative(upstream_error)
    center, rounding = _center(matrix, coefficient_bits)
    center, error, checked = _checked_step(phase, center, inherited+rounding, pieces,
                                          mode_bits, coefficient_bits, exponential_bits)
    raw_phase, raw_initial = phase.record(), _marked_record(matrix)
    return {"schema": STEP_SCHEMA, "certified": True, "raw_phase": raw_phase,
            "raw_phase_sha256": channel._digest(raw_phase), "initial_marked_state": raw_initial,
            "initial_state_sha256": channel._digest(raw_initial), "upstream_trace_norm_error": str(inherited),
            "initial_radical_error": str(rounding), "trial_pieces": json.loads(channel._canonical(pieces)),
            "mode_bits": mode_bits, "coefficient_bits": coefficient_bits, "exponential_bits": exponential_bits,
            **checked, "trace_norm_error_bound": str(error),
            "marked_poststate_center": [[c, i, j, str(a), str(b)] for (c, i, j), (a, b) in sorted(center.items())],
            **_observations(center, error), "source_bindings": _bindings(),
            "whole_phase_covered": True, "complete_poststate_enclosure": True,
            "omitted_entries_covered_by_global_error": True, "solver_reexecuted_by_checker": False,
            "mark_address_is_threshold": False, "mark_is_arrival_time_receipt": False,
            "input_positivity_certified_here": False, "physical_probability_interpretation_requires_positive_input": True,
            "error_transport": "Hermitian full-mark CPTP contraction; one global budget",
            "actual_hardware_uniquely_identified": False, "controller_advance": False}


def verify_step_certificate(report, phase=None, initial=None, *, upstream_error=None):
    _require(type(report) is dict and report.get("schema") == STEP_SCHEMA, "window-CEM step certificate required")
    phase = WindowCEMPhase.from_record(report["raw_phase"]) if phase is None else WindowCEMPhase.from_record(phase.record())
    _require(phase.record() == report["raw_phase"], "raw phase or window source mismatch")
    initial = _read_marked(report["initial_marked_state"]) if initial is None else initial
    _require(_marked_record(_initial_marked(initial)) == report["initial_marked_state"], "initial marked source state mismatch")
    inherited = report["upstream_trace_norm_error"] if upstream_error is None else upstream_error
    _require(full.nonnegative(inherited) == full.nonnegative(report["upstream_trace_norm_error"]), "upstream error binding mismatch")
    expected = certify_step(phase, initial, report["trial_pieces"], upstream_error=inherited,
                            mode_bits=report["mode_bits"], coefficient_bits=report["coefficient_bits"],
                            exponential_bits=report["exponential_bits"])
    _require(expected == report, "window-CEM source residual certificate mismatch")
    return True


def certify(source, initial, trial_families, *, trap_histories, upstream_error=0,
            mode_bits=60, coefficient_bits=160, exponential_bits=160):
    _precisions(mode_bits, coefficient_bits, exponential_bits)
    _require(type(source) is WindowCEMSource, "closed raw WindowCEMSource required; arbitrary G is not input")
    source = WindowCEMSource.from_record(source.record())
    marked = source.lift(initial, trap_histories=trap_histories)
    _require(type(trial_families) is list and len(trial_families) == len(source.partition),
             "complete waveform/shifted-window phase trial family required")
    inherited = full.nonnegative(upstream_error)
    center, rounding = _center(_initial_marked(marked), coefficient_bits)
    error, records = inherited+rounding, []
    for index, pieces in enumerate(trial_families):
        center, error, checked = _checked_step(source.phase(index), center, error, pieces,
                                              mode_bits, coefficient_bits, exponential_bits)
        records.append(checked)
    final = source.background_action({(index_mark(c), i, j): dipole.ComplexRadical(a, b)
                                      for (c, i, j), (a, b) in center.items()})
    final_center = _initial_marked(final)
    final_center = {key: (value.real.as_rational(), value.imag.as_rational()) for key, value in final_center.items()}
    raw_source = source.record()
    raw_initial = channel._input_record(cem._poststate(initial, trap_histories))
    return {"schema": SCHEMA, "certified": True, "raw_source": raw_source,
            "raw_source_sha256": channel._digest(raw_source), "initial_state": raw_initial,
            "initial_state_sha256": channel._digest(raw_initial), "parent_trap_histories": list(cem._histories(trap_histories)),
            "upstream_trace_norm_error": str(inherited), "initial_radical_error": str(rounding),
            "trial_families": json.loads(channel._canonical(trial_families)), "phase_error_records": records,
            "mode_bits": mode_bits, "coefficient_bits": coefficient_bits, "exponential_bits": exponential_bits,
            "trace_norm_error_bound": str(error), "source_bindings": _bindings(),
            "accepted_fragment_poststate_center": [[c, i, j, str(a), str(b)] for (c, i, j), (a, b) in sorted(center.items())],
            "marked_poststate_center": [[c, i, j, str(a), str(b)] for (c, i, j), (a, b) in sorted(final_center.items())],
            **_observations(final_center, error), "physical_dimension": joint.DIMENSION, "mark_levels": 4,
            "duration": str(source.duration), "evaluation_time": str(source.interval_start+source.duration),
            "complete_poststate_enclosure": True, "omitted_entries_covered_by_global_error": True,
            "source_time_coverage_complete": True, "background_applied_once_at_cutoff": True,
            "legacy_fragment_efficiency_reapplied": False, "solver_reexecuted_by_checker": False,
            "mark_address_is_threshold": False, "upstream_error_counted_once": True,
            "input_positivity_certified_here": False, "physical_probability_interpretation_requires_positive_input": True,
            "error_transport": "Hermitian full-mark CPTP contraction; one global budget",
            "actual_hardware_uniquely_identified": False, "controller_advance": False}


def verify_certificate(report, source=None, initial=None, *, trap_histories=None, upstream_error=None):
    _require(type(report) is dict and report.get("schema") == SCHEMA, "window-CEM programme certificate required")
    source = WindowCEMSource.from_record(report["raw_source"]) if source is None else WindowCEMSource.from_record(source.record())
    _require(source.record() == report["raw_source"], "raw programme or window source mismatch")
    initial = channel._read_input(report["initial_state"], joint.DIMENSION) if initial is None else initial
    _require(channel._input_record(cem._poststate(initial, _read_histories(report["parent_trap_histories"]))) == report["initial_state"],
             "initial source matrix mismatch")
    histories = _read_histories(report["parent_trap_histories"]) if trap_histories is None else trap_histories
    _require(list(cem._histories(histories)) == report["parent_trap_histories"], "source cohort binding mismatch")
    inherited = report["upstream_trace_norm_error"] if upstream_error is None else upstream_error
    _require(full.nonnegative(inherited) == full.nonnegative(report["upstream_trace_norm_error"]), "upstream error binding mismatch")
    expected = certify(source, initial, report["trial_families"], trap_histories=histories, upstream_error=inherited,
                       mode_bits=report["mode_bits"], coefficient_bits=report["coefficient_bits"],
                       exponential_bits=report["exponential_bits"])
    _require(expected == report, "window-CEM programme residual certificate mismatch")
    return True


def marked_poststate(report):
    _require(type(report) is dict and report.get("schema") in (SCHEMA, STEP_SCHEMA), "window-CEM poststate certificate required")
    return {(index_mark(c), i, j): dipole.ComplexRadical(full.exact(a), full.exact(b))
            for c, i, j, a, b in report["marked_poststate_center"]}, full.nonnegative(report["trace_norm_error_bound"])


def _image_from_report(report):
    source, histories = WindowCEMSource.from_record(report["raw_source"]), _read_histories(report["parent_trap_histories"])
    marked, error = marked_poststate(report)
    state = {}
    for mark, matrix in _blocks(marked).items():
        matrix = cem._poststate(matrix, histories)
        for (row, column), value in matrix.items():
            fragments = tuple(history.occupied and divmod(row, 33)[side] == dipole.ION for side, history in enumerate(histories))
            local._add(state, (cem.Mark(mark.clicks, fragments), row, column), value)
    receipt = {"schema": "rb87-window-pair-CEM-source-receipt/v1", "detector_source": source.record(),
               "input_density_sha256": report["initial_state_sha256"], "parent_trap_histories": report["parent_trap_histories"],
               "cohort_at_measurement_start": [item.current_atom_epoch for item in histories],
               "accepted_fragment_center_sha256": channel._digest(report["accepted_fragment_poststate_center"]),
               "complete_residual_certificate_sha256": channel._digest(report), "fragment_registration_reapplied": False}
    return cem.Image(source.record(), histories, receipt, state, error)


def image(report):
    """原 cohort 及窗口 receipt 到既有 trap/reload carrier；不再生成注册噪声。"""
    verify_certificate(report)
    return _image_from_report(report)


def _terminal_local_marking(matrix, eta):
    result = {}
    for (i, j), value in local._matrix(matrix).items():
        _require((i == dipole.ION) == (j == dipole.ION), "generated neutral/ION block algebra required")
        if i == dipole.ION:
            local._add(result, (0, i, j), (1-eta)*value)
            local._add(result, (1, i, j), eta*value)
        else:
            local._add(result, (0, i, j), value)
    return result


def _local_marked_action(atom, kappa, state):
    result = {}
    rates = {dipole.INDEX[excited]: rate for excited, rate in atom.program.ion_rates.items() if rate}
    for seen in (0, 1):
        matrix = {(i, j): value for (mark, i, j), value in state.items() if mark == seen}
        stay = atom.atomic_action(matrix)
        for excited, rate in rates.items():
            value = kappa*rate*matrix.get((excited, excited), ZERO)
            local._add(stay, (dipole.ION, dipole.ION), -value)
            local._add(result, (1, dipole.ION, dipole.ION), value)
        for (i, j), value in stay.items():
            local._add(result, (seen, i, j), value)
    return result


def constant_gate_reduction(source):
    """全原子 block-basis 交换证书；两侧 tensor 因子支付完整 pair 算子。

η 从 raw joint 的 1-p00 生成。逐个 active-ion phase 检查 κ=η，再在每个
不同原 full33 action 的全部 1025 neutral/ION matrix units 上核
G_mark Dη = Dη G。初始 occupied-neutral 下 Dη 是 INITIAL lift；原吸收
sink 使此交换对完整传播成立。background OR 与 Dη 复合一次。
"""
    _require(type(source) is WindowCEMSource, "closed raw WindowCEMSource required; arbitrary G is not input")
    source = WindowCEMSource.from_record(source.record())
    etas = tuple(1-item.probabilities[0] for item in source.registrations)
    inventory, checked, cache = [], 0, {}
    units = tuple((i, j) for i in range(33) for j in range(33) if (i == dipole.ION) == (j == dipole.ION))
    for phase in source.phases():
        side_records = []
        for side, (atom, kappa, eta) in enumerate(zip(phase.sources, phase.kappas, etas)):
            active = bool(phase.ion_rates[side])
            _require(not active or kappa == eta, "active ion birth support is not covered by constant full-registration gate")
            raw_action = atom.program.record()
            raw_action.pop("duration")
            key = channel._digest([raw_action, str(eta), str(kappa)])
            if key not in cache:
                for i, j in units:
                    matrix = {(i, j): dipole.ComplexRadical(1)}
                    first = _local_marked_action(atom, kappa, _terminal_local_marking(matrix, eta))
                    second = _terminal_local_marking(atom.atomic_action(matrix), eta)
                    _require(first == second, "raw ion-birth/terminal-disposition intertwiner failed")
                    checked += 1
                cache[key] = len(units)
            side_records.append({"side": side, "active_ion_birth": active, "effective_eta": str(eta),
                                 "kappa": str(kappa), "raw_action_sha256": key, "local_basis_units": cache[key]})
        inventory.append({"generated_phase": source.partition[phase.index], "sides": side_records})
    return {"schema": "stage10-window-CEM-constant-gate-reduction/v1", "certified": True,
            "raw_source": source.record(), "raw_source_sha256": channel._digest(source.record()),
            "effective_fragment_efficiencies": list(map(str, etas)), "phase_commutation_inventory": inventory,
            "distinct_local_actions_checked": len(cache), "local_basis_columns_checked": checked,
            "local_block_algebra_dimension": len(units), "pair_block_algebra_dimension": len(units)**2,
            "tensor_factorization": "G_A tensor I + I tensor G_B; D_A tensor D_B",
            "all_active_ion_phases_constant": True, "full_pair_block_operator_intertwining_checked": True,
            "initial_occupied_neutral_required": True, "Empty_restriction_has_no_ion_birth": True,
            "background_composed_once": True, "endpoint_or_effect_supplied": False,
            "arrival_boundary": "exact half-open windows; every generated phase uses its left boundary",
            "source_bindings": _bindings(), "solver_reexecuted_by_checker": False,
            "actual_flight_times_identified": False, "actual_hardware_uniquely_identified": False,
            "controller_advance": False}


def verify_constant_gate_reduction(report, source=None):
    _require(type(report) is dict and report.get("schema") == "stage10-window-CEM-constant-gate-reduction/v1",
             "constant-gate source reduction certificate required")
    source = WindowCEMSource.from_record(report["raw_source"]) if source is None else WindowCEMSource.from_record(source.record())
    _require(source.record() == report["raw_source"], "constant-gate raw source mismatch")
    _require(constant_gate_reduction(source) == report, "constant-gate source reduction certificate mismatch")
    return True
