"""Two source-owned trap cohorts, sequential cooling masks and one shared APD.

Raw joint windows retain the public integrated-count/sequential-mask family.
Each window uses both original atom baths.  The initial post-CEM both-lit
diagnostic has capture off; subsequent per-side low counts activate raw capture.
Capture continues at saturated counts until the boundary decision.  A low
both-lit check restarts A/B diagnosis, so observed loss can regenerate loading.
Every branch preserves the full poststate and both source histories; counters
reset at pending boundaries.  There is no pair of independent waiting kernels.

The raw two-side n_s/g_s remain a finite Markov capture hypothesis.  The public
40 ms integration is an anchor, not identification of the raw time coordinate,
PC polling/reset policy, capture reservoir or actual hardware parameters.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import atomic_dipole as dipole
import atomic_full_forward as full
import fluorescence_channel as channel
import fluorescence_presence as local
import joint_fluorescence_presence as joint
import recognized_reload_source as recognized
import trap_reload_source as reload


SCHEMA = "rb87-joint-window-reload-source/v1"
CERTIFICATE_SCHEMA = "stage10-joint-window-reload-enclosure/v1"
EMPTY, GROUND, DIMENSION = reload.EMPTY, reload.GROUND, joint.DIMENSION
ZERO = dipole.ComplexRadical()
CONTROL_NAMES = ("post-CEM-both-diagnostic", "A-diagnostic", "A-reload", "B-diagnostic", "B-reload", "both-verification", "ready")
WINDOW_AT = (2, 0, 0, 1, 1, 2, 2)
LOADED_AT = ((False, False), (False, False), (False, False), (True, False), (True, False), (True, True), (True, True))
CAPTURE_AT = ((False, False), (False, False), (True, False), (False, False), (False, True), (False, False), (False, False))
NEXT_AT = ((1, 6), (2, 3), (2, 3), (4, 5), (4, 5), (1, 6))
READY = len(CONTROL_NAMES) - 1


@dataclass(frozen=True)
class JointReloadHistory:
    traps: tuple
    decisions: tuple


class JointReloadSource:
    physical_dimension = DIMENSION

    def __init__(self, captures, *, windows, cooling_masks):
        if type(captures) is not tuple or len(captures) != 2 or any(type(item) is not reload.ReloadSource for item in captures):
            raise TypeError("two original raw ReloadSource capture records required")
        if type(windows) is not tuple or len(windows) != 3 or any(type(item) is not joint.JointCounterGenerator for item in windows):
            raise TypeError("ordered raw shared-counter window programme required")
        if (type(cooling_masks) is not tuple or len(cooling_masks) != len(windows) or
                any(type(mask) is not tuple or len(mask) != 2 or not any(mask) or
                    any(type(bit) is not bool for bit in mask) for mask in cooling_masks)):
            raise ValueError("explicit two-side cooling mask for every raw window required")
        if cooling_masks != ((True, False), (False, True), (True, True)):
            raise ValueError("raw A-only/B-only/both cooling window inventory required")
        self.captures = tuple(reload.ReloadSource.from_record(item.record()) for item in captures)
        self.windows = tuple(joint.JointCounterGenerator.from_record(item.record()) for item in windows)
        self.cooling_masks = cooling_masks
        for window, mask in zip(self.windows, self.cooling_masks):
            if window.duration <= 0:
                raise ValueError("positive raw integrated-count window duration required")
            for side, enabled in enumerate(mask):
                program, capture = window.sources[side].program, self.captures[side].original.program
                if not enabled and (any(program.fields_r.values()) or any(program.fields_c.values())):
                    raise ValueError("off-side cooling mask must have both original raw fields off")
                if (program.gammas != capture.gammas or program.ion_rates != capture.ion_rates or
                        program.radiation_regime != capture.radiation_regime):
                    raise ValueError("cooling masks must preserve the original atom radiation and ion baths")

    def _flags(self, stage):
        if type(stage) is not int or not 0 <= stage <= READY:
            raise ValueError("source-generated joint programme stage required")
        return LOADED_AT[stage]

    def _window(self, stage):
        self._flags(stage)
        return self.windows[WINDOW_AT[stage]]

    def _next(self, stage, success):
        self._flags(stage)
        if stage == READY or type(success) is not bool:
            raise ValueError("pending source count decision required")
        return NEXT_AT[stage][int(success)]

    def _control(self, decisions):
        if type(decisions) is not tuple:
            raise ValueError("source window decision history required")
        stage = 0
        for item in decisions:
            if (type(item) is not tuple or len(item) != 2 or type(item[0]) is not int or type(item[1]) is not int or
                    stage == READY or item[0] != stage or not 0 <= item[1] <= self._window(stage).threshold):
                raise ValueError("joint window decision does not follow its source programme")
            stage = self._next(stage, item[1] == self._window(stage).threshold)
        return stage, self._flags(stage)

    def control(self, history):
        """Read the generated programme control; loaded confirmation is not occupancy."""
        if type(history) is not JointReloadHistory:
            raise ValueError("source joint window history required")
        stage, flags = self._control(history.decisions)
        return {"stage": stage, "name": CONTROL_NAMES[stage], "raw_window": WINDOW_AT[stage],
                "loaded_flags": flags, "capture_enabled": CAPTURE_AT[stage], "ready": stage == READY}

    @staticmethod
    def _receipt(receipt):
        if type(receipt) is not str:
            raise ValueError("canonical source CEM receipt required")
        try:
            canonical = reload._receipt(json.loads(receipt))
        except (TypeError, ValueError) as error:
            raise ValueError("canonical source CEM receipt required") from error
        if canonical != receipt:
            raise ValueError("canonical source CEM receipt required")

    def _trap(self, history, i, j, value):
        if (type(history) is not reload.TrapHistory or type(history.old_atom_epoch) is not int or history.old_atom_epoch < 0 or
                type(history.occupied) is not bool or type(history.birth_modes) is not tuple or
                any(type(mode) is not dipole.State or mode not in GROUND for mode in history.birth_modes) or
                type(history.departed_fragments) is not tuple or
                len(history.departed_fragments) != history.birth_counter + int(not history.occupied)):
            raise ValueError("complete original trap cohort/departure history required")
        self._receipt(history.original_cem_receipt_json)
        for index, fragment in enumerate(history.departed_fragments):
            if (type(fragment) is not reload.DepartedFragment or type(fragment.atom_epoch) is not int or
                    fragment.atom_epoch != history.old_atom_epoch + index or
                    fragment.stage not in ("old-CEM-ion", "reload-ionization", "programme-CEM-ion")):
                raise ValueError("source departure stage and literal cohort epoch required")
            if fragment.stage == "old-CEM-ion":
                if index != 0 or fragment.cem_receipt_json != history.original_cem_receipt_json:
                    raise ValueError("original departed CEM receipt changed")
            elif fragment.stage == "reload-ionization":
                if fragment.cem_receipt_json is not None:
                    raise ValueError("natural reload departure cannot invent a CEM receipt")
            else:
                self._receipt(fragment.cem_receipt_json)
        local._matrix({(i, j): value})
        if (history.occupied and EMPTY in (i, j)) or (not history.occupied and (i, j) != (EMPTY, EMPTY)):
            raise ValueError("source trap occupancy and original matrix addresses differ")

    def _blocks(self, state):
        if type(state) is not dict:
            raise TypeError("source joint cohort/window sparse state required")
        blocks = {}
        for key, value in state.items():
            if (type(key) is not tuple or len(key) != 4 or type(key[0]) is not JointReloadHistory or
                    type(key[0].traps) is not tuple or len(key[0].traps) != 2):
                raise ValueError("both source TrapHistories and joint window history required")
            history, counter, row, column = key
            stage, flags = self._control(history.decisions)
            window = self._window(stage)
            window._blocks({(counter, row, column): value})
            if stage == READY and counter != window.threshold:
                raise ValueError("ready source retains its last recognized saturated count")
            for side in range(2):
                i, j = divmod(row, 33)[side], divmod(column, 33)[side]
                self._trap(history.traps[side], i, j, value)
            value = dipole.complex_exact(value)
            if value:
                blocks.setdefault(history, {})[counter, row, column] = value
        return blocks

    def intake(self, coarsened):
        """Consume PairCEMInstrument.coarsen's two histories without reifying ions.

        Index32 may already mean Empty.  This interface preserves the supplied
        source histories; it never infers a departed ion from that matrix index.
        """
        if type(coarsened) is not dict:
            raise TypeError("full coarsened pair CEM source state required")
        result = {}
        for key, value in coarsened.items():
            if (type(key) is not tuple or len(key) != 4 or type(key[0]) is not tuple or len(key[0]) != 2 or
                    type(key[1]) is not int or key[1] != 0):
                raise ValueError("two CEM TrapHistories and a reset shared counter required")
            histories, counter, row, column = key
            result[JointReloadHistory(histories, ()), counter, row, column] = value
        self._blocks(result)
        return result

    @staticmethod
    def _replace_side(history, side, trap):
        traps = tuple(trap if index == side else old for index, old in enumerate(history.traps))
        return JointReloadHistory(traps, history.decisions)

    @staticmethod
    def _replace_index(index, side, target):
        pair = list(divmod(index, 33))
        pair[side] = target
        return joint.atom_pair_index(*pair)

    def action(self, state):
        result = {}
        for history, block in self._blocks(state).items():
            stage, flags = self._control(history.decisions)
            window = self._window(stage)
            change = window.action(block)
            for (counter, row, column), value in block.items():
                for side, trap in enumerate(history.traps):
                    i, j = divmod(row, 33)[side], divmod(column, 33)[side]
                    rate = window.sources[side].program.ion_rates.get(dipole.STATES[i], Q(0)) if i == j else Q(0)
                    if trap.occupied and rate:
                        key = counter, self._replace_index(row, side, EMPTY), self._replace_index(column, side, EMPTY)
                        flux = value * rate
                        local._add(change, key, -flux)
                        following = self._replace_side(history, side, trap.depart())
                        local._add(result, (following, *key), flux)
                    if not trap.occupied and CAPTURE_AT[stage][side]:
                        capture = self.captures[side]
                        local._add(result, (history, counter, row, column), -value * capture.first_birth_rate)
                        for ground, birth_rate in capture.rates.items():
                            if birth_rate:
                                target = dipole.INDEX[ground]
                                key = counter, self._replace_index(row, side, target), self._replace_index(column, side, target)
                                following = self._replace_side(history, side, trap.capture(ground))
                                local._add(result, (following, *key), value * birth_rate)
            for key, value in change.items():
                local._add(result, (history, *key), value)
        return result

    def forget_history(self, state):
        """Project histories to generated stage plus the complete joint matrix."""
        result = {}
        for history, block in self._blocks(state).items():
            stage, _ = self._control(history.decisions)
            for key, value in block.items():
                local._add(result, (stage, *key), value)
        return result

    def _projected_blocks(self, state):
        if type(state) is not dict:
            raise TypeError("source stage/shared-counter/full-joint sparse state required")
        blocks = {}
        for key, value in state.items():
            if type(key) is not tuple or len(key) != 4:
                raise ValueError("source stage and shared-counter/full-joint addresses required")
            stage, counter, row, column = key
            window = self._window(stage)
            window._blocks({(counter, row, column): value})
            if stage == READY and counter != window.threshold:
                raise ValueError("ready source retains its last recognized saturated count")
            blocks.setdefault(stage, {})[counter, row, column] = dipole.complex_exact(value)
        return blocks

    def _capture_action(self, matrix, side):
        result = {}
        for operator in self.captures[side].birth_operators.values():
            adjoint = dipole.matrix_adjoint(operator)
            loss = dipole.matrix_product(adjoint, operator)
            recycling = joint._operator_right(joint._operator_left(matrix, side, operator), side, adjoint)
            result = local._sum(result, recycling)
            for product in (joint._operator_left(matrix, side, loss), joint._operator_right(matrix, side, loss)):
                for key, value in product.items():
                    local._add(result, key, -value * Q(1, 2))
        return result

    def window_action(self, state, stage=0):
        """Complete shared-counter action at a closed programme stage face."""
        window = self._window(stage)
        result = window.action(state)
        for counter, matrix in window._blocks(state).items():
            for side, enabled in enumerate(CAPTURE_AT[stage]):
                if enabled:
                    for key, value in self._capture_action(matrix, side).items():
                        local._add(result, (counter, *key), value)
        return result

    def projected_action(self, state):
        result = {}
        for stage, block in self._projected_blocks(state).items():
            for key, value in self.window_action(block, stage).items():
                local._add(result, (stage, *key), value)
        return result

    def window_end(self, state):
        self._blocks(state)
        failed, recognized = {}, {}
        for (history, counter, row, column), value in state.items():
            stage, _ = self._control(history.decisions)
            if stage == READY:
                raise ValueError("window decision requires pending source programme")
            success = counter == self._window(stage).threshold
            following = JointReloadHistory(history.traps, history.decisions + ((stage, counter),))
            next_stage, _ = self._control(following.decisions)
            next_counter = counter if next_stage == READY else 0
            local._add(recognized if success else failed, (following, next_counter, row, column), dipole.complex_exact(value))
        return {"failed": failed, "recognized": recognized}

    def projected_window_end(self, state):
        self._projected_blocks(state)
        failed, recognized = {}, {}
        for (stage, counter, row, column), value in state.items():
            if stage == READY:
                raise ValueError("window decision requires pending source programme")
            success = counter == self._window(stage).threshold
            next_stage = self._next(stage, success)
            next_counter = counter if next_stage == READY else 0
            local._add(recognized if success else failed, (next_stage, next_counter, row, column), dipole.complex_exact(value))
        return {"failed": failed, "recognized": recognized}

    def record(self):
        return {"schema": SCHEMA, "raw_capture_sources": [capture.record() for capture in self.captures],
                "raw_shared_windows": [window.record() for window in self.windows],
                "cooling_masks": [list(mask) for mask in self.cooling_masks],
                "physical_dimension": DIMENSION, "atom_dimension": 33, "tensor_index": "33*A+B",
                "capture_control": "post-CEM/side diagnostics capture-off; side low count activates its raw capture; recognized side capture-off",
                "window_decision": "shared-count event alone generates flags/capture/next mask; preserve full state and reset pending counter",
                "feedback_policy": "both-low clears confirmation and returns to A diagnosis; A/B-low activates corresponding raw capture; A/B-high proceeds; both-high ready",
                "control_inventory": [{"stage": index, "name": name, "raw_window": WINDOW_AT[index],
                                       "loaded_flags": list(LOADED_AT[index]), "capture_enabled": list(CAPTURE_AT[index]),
                                       "low_next": NEXT_AT[index][0] if index != READY else None,
                                       "high_next": NEXT_AT[index][1] if index != READY else None}
                                      for index, name in enumerate(CONTROL_NAMES)],
                "failure_retains_full_joint_poststate_and_both_trap_histories": True,
                "source_decisions_retain_shared_count_and_stage": True,
                "initial_post_CEM_diagnostic_has_capture_off": True,
                "capture_start_generated_only_by_source_side_failure": True,
                "both_failure_generates_recurrent_presence_to_reload": True,
                "trap_fragment_stages": ["old-CEM-ion", "reload-ionization", "programme-CEM-ion"],
                "local_capture_counters_and_backgrounds_used": False,
                "background_channels_per_window": 1, "independent_waiting_kernels_used": False,
                "shared_APD_cross_terms_retained": True,
                "forget_shared_count_restores_two_original_baths_and_enabled_captures": True,
                "public_programme_source": "programme-sources-hp0001.json", "public_presence_integration_ms": 40,
                "raw_window_durations": [str(window.duration) for window in self.windows],
                "raw_single_and_both_thresholds": [window.threshold for window in self.windows],
                "actual_PC_window_overlap_polling_and_latency_identified": False,
                "capture_model": "two finite Markov reservoir capture hypotheses; actual MOT realization not identified",
                "physical_cohort_identity_recovered_from_projection": False,
                "actual_hardware_identity_asserted": False, "actual_clock_encoder_identified": False,
                "controller_advance": False, "propagation_performed": False}

    @classmethod
    def from_record(cls, record):
        if type(record) is not dict or record.get("schema") != SCHEMA:
            raise ValueError("registered joint window reload source record required")
        source = cls(tuple(reload.ReloadSource.from_record(item) for item in record["raw_capture_sources"]),
                     windows=tuple(joint.JointCounterGenerator.from_record(item) for item in record["raw_shared_windows"]),
                     cooling_masks=tuple(tuple(mask) for mask in record["cooling_masks"]))
        if source.record() != record:
            raise ValueError("joint reload source identity or control scope changed")
        return source


class _WindowProjection:
    def __init__(self, source, stage):
        channel._require(type(source) is JointReloadSource, "registered raw joint reload source constructor required")
        self.programme = JointReloadSource.from_record(source.record())
        channel._require(type(stage) is int and 0 <= stage < READY,
                         "pending joint window source stage required")
        self.stage, self.window = stage, self.programme._window(stage)
        self.threshold, self.duration = self.window.threshold, self.window.duration

    def action(self, matrix):
        return self.programme.window_action(matrix, self.stage)

    def record(self):
        return {"schema": "rb87-joint-reload-window-face/v1", "source_programme": self.programme.record(),
                "stage": self.stage, "physical_dimension": DIMENSION,
                "loaded_flags": list(self.programme._flags(self.stage)), "capture_enabled": list(CAPTURE_AT[self.stage])}


class SourceKernel(channel.SourceKernel):
    """Frozen exact columns/residual helpers, closed to one raw joint programme."""
    def __init__(self, generator, coefficient_bits=160, *, stage=0):
        channel._require(type(coefficient_bits) is int and 64 <= coefficient_bits <= 512,
                         "registered coefficient precision required")
        self.source = _WindowProjection(generator, stage)
        self.dimension, self.threshold = DIMENSION, self.source.threshold
        self.bits, self.columns, self.exact_columns, self.errors = coefficient_bits, {}, {}, {}


def _bindings(source):
    records = {item["path"]: item for item in channel._bindings(source)}
    for path in (Path(__file__).resolve(), Path(joint.__file__).resolve(), Path(reload.__file__).resolve(), Path(recognized.__file__).resolve()):
        relative = str(path.relative_to(full.ROOT))
        records[relative] = {"path": relative, "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
    return [records[path] for path in sorted(records)]


def certify_window(generator, initial, pieces, *, stage=0, upstream_error=0,
                   mode_bits=60, coefficient_bits=160, exponential_bits=160):
    channel._require(type(mode_bits) is int and 32 <= mode_bits <= 256, "registered trial-mode precision required")
    channel._require(type(exponential_bits) is int and 64 <= exponential_bits <= 1024, "registered scalar precision required")
    channel._require(type(pieces) is list, "complete joint window trial pieces required")
    kernel = SourceKernel(generator, coefficient_bits, stage=stage)
    initial = channel._initial(initial, DIMENSION)
    upstream_error = full.nonnegative(upstream_error)
    center, radical_error = {}, Q(0)
    for (i, j), value in initial.items():
        a, da = full.radical_midpoint(value.real, coefficient_bits)
        b, db = full.radical_midpoint(value.imag, coefficient_bits)
        channel._add(center, (0, i, j), a, b)
        radical_error += da + db
    error, elapsed, records = upstream_error + radical_error, Q(0), []
    for item in pieces:
        width, begin, end, errors, diagnostics = channel._piece(kernel, item, mode_bits, exponential_bits)
        gap = channel._difference(begin, center)
        error += gap + sum(errors.values(), Q(0))
        elapsed += width
        channel._require(elapsed <= kernel.source.duration, "trial extends beyond raw shared window")
        records.append({"duration": str(width), "initial_join_error": str(gap),
                        **{name: str(value) for name, value in errors.items()}, "modes": diagnostics})
        center = end
    channel._require(elapsed == kernel.source.duration, "trial must cover the whole raw shared window")
    observations = channel._observations(center, error, kernel.threshold)
    raw_source, raw_initial = kernel.source.record(), channel._input_record(initial)
    return {"schema": CERTIFICATE_SCHEMA, "certified": True, "raw_source": raw_source,
            "raw_source_sha256": channel._digest(raw_source), "initial_state": raw_initial,
            "initial_state_sha256": channel._digest(raw_initial), "initial_counter": 0,
            "upstream_trace_norm_error": str(upstream_error), "initial_radical_error": str(radical_error),
            "physical_dimension": DIMENSION, "stage": stage, "duration": str(kernel.source.duration),
            "counter_levels": kernel.threshold + 1, "counter_complex_coordinates": (kernel.threshold + 1) * DIMENSION ** 2,
            "trial_pieces": json.loads(channel._canonical(pieces)), "piece_error_records": records,
            "mode_bits": mode_bits, "coefficient_bits": coefficient_bits, "exponential_bits": exponential_bits,
            "trace_norm_error_bound": str(error), "source_columns_checked": len(kernel.columns),
            "counter_poststate_center": [[c, i, j, str(a), str(b)] for (c, i, j), (a, b) in sorted(center.items())],
            **observations, "source_bindings": _bindings(kernel.source),
            "failure_reset_counter": 0, "failure_next_stage": kernel.source.programme._next(stage, False),
            "recognized_next_stage": kernel.source.programme._next(stage, True),
            "failure_next_loaded_flags": list(kernel.source.programme._flags(kernel.source.programme._next(stage, False))),
            "recognized_next_loaded_flags": list(kernel.source.programme._flags(kernel.source.programme._next(stage, True))),
            "failure_next_capture_enabled": list(CAPTURE_AT[kernel.source.programme._next(stage, False)]),
            "recognized_next_capture_enabled": list(CAPTURE_AT[kernel.source.programme._next(stage, True)]),
            "source_time_coverage_complete": True, "complete_joint_poststate_enclosure": True,
            "omitted_entries_covered_by_global_error": True, "source_counter_trace_preservation_checked": True,
            "error_transport": "CPTP trace-norm contraction on Hermitian shared-window trial curves",
            "physical_probability_interpretation_requires_positive_input": True, "input_positivity_certified_here": False,
            "physical_cohort_identity_recovered_from_projection": False, "solver_reexecuted_by_checker": False,
            "independent_waiting_kernels_used": False, "actual_hardware_identity_asserted": False,
            "controller_advance": False, "propagation_performed": True}


def verify_window_certificate(report, generator=None, initial=None, *, upstream_error=None):
    channel._require(type(report) is dict and report.get("schema") == CERTIFICATE_SCHEMA,
                     "joint reload window certificate required")
    raw = report["raw_source"]
    source = JointReloadSource.from_record(raw["source_programme"]) if generator is None else generator
    channel._require(type(source) is JointReloadSource and source.record() == raw["source_programme"],
                     "raw joint reload programme mismatch")
    matrix = channel._read_input(report["initial_state"], DIMENSION) if initial is None else channel._initial(initial, DIMENSION)
    channel._require(channel._input_record(matrix) == report["initial_state"], "full original joint source input matrix mismatch")
    inherited = report["upstream_trace_norm_error"] if upstream_error is None else upstream_error
    channel._require(full.nonnegative(inherited) == full.nonnegative(report["upstream_trace_norm_error"]),
                     "upstream error binding mismatch")
    expected = certify_window(source, matrix, report["trial_pieces"], stage=report["stage"], upstream_error=inherited,
                              mode_bits=report["mode_bits"], coefficient_bits=report["coefficient_bits"],
                              exponential_bits=report["exponential_bits"])
    channel._require(expected == report, "source joint reload window residual certificate mismatch")
    return True


def poststate(report, branch="unconditional"):
    return channel.poststate(report, branch)
