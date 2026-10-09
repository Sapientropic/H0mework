"""Raw trap capture stopped by its own retained APD threshold.

The source is the frozen finite Markov capture hypothesis, with one additional
control rule: capture from Empty is enabled precisely on counter levels c<N.
The counter saturates at N, so capture remains off after first recognition.
Original laser, radiation, ionization and APD channels continue at that level.
This does not identify the hypothesis with the actual MOT programme.

Tagged history retains departed atoms, the original CEM receipt and generated
cohort epochs.  Its counter/atom projection is the same controlled source;
recognition includes Empty false positives and never prescribes a prepared atom.
"""
from dataclasses import dataclass
from fractions import Fraction as Q

import atomic_dipole as dipole
import atomic_full_forward as full
import fluorescence_presence as presence
import trap_reload_source as reload


SCHEMA = "rb87-count-recognized-reload-source/v1"
WINDOW_SCHEMA = "rb87-window-recognized-reload-source/v1"
EMPTY, NEUTRAL, GROUND = reload.EMPTY, reload.NEUTRAL, reload.GROUND


class RecognizedReloadSource:
    physical_dimension = full.DIMENSION

    def __init__(self, raw_capture):
        if type(raw_capture) is not reload.ReloadSource:
            raise TypeError("registered raw ReloadSource required; completed waiting kernels are not inputs")
        self.raw_capture = reload.ReloadSource.from_record(raw_capture.record())
        self.threshold, self.duration = self.raw_capture.threshold, self.raw_capture.duration

    def action(self, state):
        """Controlled full history action; departure and receipt rules stay source owned."""
        blocks = self.raw_capture._blocks(state)
        result = self.raw_capture.action(state)
        # Exact cancellation of only the frozen source's top-level birth terms
        # keeps its optical/departure implementation and all history identities.
        for history, block in blocks.items():
            if history.occupied:
                continue
            value = block.get((self.threshold, EMPTY, EMPTY), reload.ZERO)
            if value:
                presence._add(result, (history, self.threshold, EMPTY, EMPTY),
                              value * self.raw_capture.first_birth_rate)
                for ground, rate in self.raw_capture.rates.items():
                    if rate:
                        target = dipole.INDEX[ground]
                        presence._add(result, (history.capture(ground), self.threshold, target, target),
                                      -value * rate)
        return result

    def forget_history(self, state):
        return self.raw_capture.forget_history(state)

    def projected_action(self, state):
        """GKSL products from the same raw n_s/g_s, only on c<N blocks."""
        blocks = self.raw_capture.original._blocks(state)
        result = self.raw_capture.original.action(state)
        for counter, atom in blocks.items():
            if counter == self.threshold:
                continue
            for operator in self.raw_capture.birth_operators.values():
                adjoint = dipole.matrix_adjoint(operator)
                loss = dipole.matrix_product(adjoint, operator)
                recycling = dipole.matrix_product(dipole.matrix_product(operator, atom), adjoint)
                for key, value in recycling.items():
                    presence._add(result, (counter, *key), value)
                for product in (dipole.matrix_product(loss, atom), dipole.matrix_product(atom, loss)):
                    for key, value in product.items():
                        presence._add(result, (counter, *key), -value * Q(1, 2))
        return result

    def record(self):
        return {"schema": SCHEMA, "raw_capture_source": self.raw_capture.record(),
                "physical_dimension": self.physical_dimension, "empty_index": EMPTY,
                "threshold": self.threshold, "counter_levels": self.threshold + 1,
                "capture_control": "capture iff retained APD counter c<N; saturated N is permanent capture-off",
                "capture_control_generated_from_source_counter": True,
                "top_counter_continues_original_laser_radiation_ion_and_APD": True,
                "recognition_event": "first retained APD count reaches N; includes Empty false positives",
                "recognition_effect": "trace of every full33 state at saturated counter N",
                "first_birth_exponential_is_recognition_law": False,
                "full_history_retains_departed_fragments_CEM_receipt_and_atom_epochs": True,
                "projection": "forget tagged histories; retain all counter/full33 matrix coordinates",
                "capture_model": "finite Markov reservoir capture hypothesis; not actual MOT identity",
                "field_MOT_capture_realization_identified": False,
                "actual_hardware_identity_asserted": False, "actual_clock_encoder_identified": False,
                "controller_advance": False, "propagation_performed": False}

    @classmethod
    def from_record(cls, record):
        if type(record) is not dict or record.get("schema") != SCHEMA:
            raise ValueError("registered count-recognized raw reload source record required")
        source = cls(reload.ReloadSource.from_record(record["raw_capture_source"]))
        if source.record() != record:
            raise ValueError("raw recognized reload source identity or control rule changed")
        return source


@dataclass(frozen=True)
class WindowHistory:
    trap: reload.TrapHistory
    window_counts: tuple
    loaded: bool

    @property
    def completed_windows(self):
        return len(self.window_counts)


class WindowedReloadSource:
    """Integrated-count windows with a source-generated boundary decision.

    Within each window capture is ungated, including at saturated count N.
    At the boundary the low-count CP branch resets only the photon counter;
    the high-count branch generates loaded=True and disables capture afterward.
    This family matches integrated-count recognition but its nonoverlapping
    window/reset policy remains raw, rather than an identified public PC policy.
    """
    physical_dimension = full.DIMENSION

    def __init__(self, raw_capture):
        if type(raw_capture) is not reload.ReloadSource:
            raise TypeError("registered raw ReloadSource required; completed window maps are not inputs")
        self.raw_capture = reload.ReloadSource.from_record(raw_capture.record())
        self.threshold, self.duration = self.raw_capture.threshold, self.raw_capture.duration
        self._loaded = RecognizedReloadSource(self.raw_capture)

    def intake(self, state):
        """Canonical pending control from the paid old-CEM coarsening/history."""
        self.raw_capture._blocks(state)
        if any(counter != 0 for _, counter, _, _ in state):
            raise ValueError("a new integrated-count window starts at counter zero")
        return {(WindowHistory(history, (), False), counter, i, j): value
                for (history, counter, i, j), value in state.items()}

    def _groups(self, state):
        if type(state) is not dict:
            raise TypeError("source window/trap history sparse state required")
        groups = {}
        for key, value in state.items():
            if (type(key) is not tuple or len(key) != 4 or type(key[0]) is not WindowHistory or
                    type(key[0].window_counts) is not tuple or type(key[0].loaded) is not bool or
                    any(type(count) is not int or not 0 <= count <= self.threshold for count in key[0].window_counts)):
                raise ValueError("source-generated window control history required")
            history, counter, i, j = key
            if (history.loaded != bool(history.window_counts and history.window_counts[-1] == self.threshold) or
                    any(count == self.threshold for count in history.window_counts[:-1])):
                raise ValueError("loaded control must be generated by its last window decision")
            if history.loaded and counter != self.threshold:
                raise ValueError("loaded control retains its recognized saturated counter")
            raw = {(history.trap, counter, i, j): value}
            self.raw_capture._blocks(raw)
            groups.setdefault((history.window_counts, history.loaded), {}).update(raw)
        return groups

    def action(self, state):
        result = {}
        for (counts, loaded), raw in self._groups(state).items():
            change = self._loaded.action(raw) if loaded else self.raw_capture.action(raw)
            for (history, counter, i, j), value in change.items():
                presence._add(result, (WindowHistory(history, counts, loaded), counter, i, j), value)
        return result

    def forget_history(self, state):
        """Keep the generated loaded flag while forgetting cohort/history tags."""
        result = {}
        for (_, loaded), raw in self._groups(state).items():
            for (counter, i, j), value in self.raw_capture.forget_history(raw).items():
                presence._add(result, (loaded, counter, i, j), value)
        return result

    def _projected_blocks(self, state):
        if type(state) is not dict:
            raise TypeError("source loaded/counter/full33 sparse state required")
        blocks = {}
        for key, value in state.items():
            if type(key) is not tuple or len(key) != 4 or type(key[0]) is not bool:
                raise ValueError("generated loaded flag and original counter/atom address required")
            loaded, counter, i, j = key
            if loaded and counter != self.threshold:
                raise ValueError("loaded control retains its recognized saturated counter")
            raw = {(counter, i, j): value}
            self.raw_capture.original._blocks(raw)
            blocks.setdefault(loaded, {}).update(raw)
        return blocks

    def pending_action(self, state):
        """Ungated raw capture throughout the integrated-count window."""
        return self.raw_capture.projected_action(state)

    def projected_action(self, state):
        result = {}
        for loaded, raw in self._projected_blocks(state).items():
            change = self.raw_capture.original.action(raw) if loaded else self.pending_action(raw)
            for (counter, i, j), value in change.items():
                presence._add(result, (loaded, counter, i, j), value)
        return result

    def window_end(self, state):
        """CP branch/reset instrument; every failure keeps its full source history."""
        self._groups(state)
        failed, recognized = {}, {}
        for (history, counter, i, j), value in state.items():
            if history.loaded:
                raise ValueError("window decisions consume only a pending integrated-count window")
            loaded = counter == self.threshold
            following = WindowHistory(history.trap, history.window_counts + (counter,), loaded)
            target = recognized if loaded else failed
            presence._add(target, (following, counter if loaded else 0, i, j), dipole.complex_exact(value))
        return {"failed": failed, "recognized": recognized}

    def projected_window_end(self, state):
        self._projected_blocks(state)
        failed, recognized = {}, {}
        for (loaded, counter, i, j), value in state.items():
            if loaded:
                raise ValueError("window decisions consume only a pending integrated-count window")
            success = counter == self.threshold
            presence._add(recognized if success else failed,
                          (success, counter if success else 0, i, j), dipole.complex_exact(value))
        return {"failed": failed, "recognized": recognized}

    def record(self):
        return {"schema": WINDOW_SCHEMA, "raw_capture_source": self.raw_capture.record(),
                "physical_dimension": self.physical_dimension, "empty_index": EMPTY,
                "threshold": self.threshold, "counter_levels": self.threshold + 1,
                "window_duration": str(self.duration),
                "window_policy": "nonoverlapping raw integrated-count windows; boundary decision; failure counter reset to zero",
                "within_window_capture": "ungated raw capture at every counter, including saturated N",
                "recognized_control": "window-end saturated branch generates loaded flag and capture-off",
                "loaded_continues_original_laser_radiation_ion_and_APD": True,
                "failure_branch_retains_complete_atom_state_and_source_history": True,
                "recognition_effect": "window-end trace of every full33 state at saturated counter N",
                "full_history_retains_departed_fragments_CEM_receipt_and_atom_epochs": True,
                "public_integrated_count_family": True,
                "actual_PC_window_overlap_polling_and_latency_identified": False,
                "capture_model": "finite Markov reservoir capture hypothesis; not actual MOT identity",
                "field_MOT_capture_realization_identified": False,
                "actual_hardware_identity_asserted": False, "actual_clock_encoder_identified": False,
                "controller_advance": False, "propagation_performed": False}

    @classmethod
    def from_record(cls, record):
        if type(record) is not dict or record.get("schema") != WINDOW_SCHEMA:
            raise ValueError("registered integrated-window raw reload source record required")
        source = cls(reload.ReloadSource.from_record(record["raw_capture_source"]))
        if source.record() != record:
            raise ValueError("raw window reload source identity or control rule changed")
        return source
