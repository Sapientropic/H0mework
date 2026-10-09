"""Full pair CEM instrument, with atom/Empty identity paid by source history.

The detector is the existing fragment/background model d+(1-d)*eta*ion.
Raw phases generate the input; this instrument never replaces a full BSM
image with an ideal Bell state.  Index32 is a fragment only for a cohort
that entered the measurement occupied.  A previously Empty trap has no
fragment, including when it produced a background-only BSM herald.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from itertools import product
import hashlib
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import fluorescence_presence as local
import joint_fluorescence_presence as joint
import trap_reload_source as trap


ZERO = dipole.ComplexRadical()


def _canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _digest(value):
    return hashlib.sha256(_canonical(value).encode()).hexdigest()


def history_record(history):
    if type(history) is not trap.TrapHistory:
        raise ValueError("source-owned trap cohort history required")
    if (type(history.old_atom_epoch) is not int or history.old_atom_epoch < 0 or
            type(history.occupied) is not bool or type(history.birth_modes) is not tuple or
            any(mode not in trap.GROUND for mode in history.birth_modes) or
            type(history.departed_fragments) is not tuple or
            len(history.departed_fragments) != history.birth_counter + int(not history.occupied)):
        raise ValueError("incomplete source cohort history")
    for index, fragment in enumerate(history.departed_fragments):
        if (type(fragment) is not trap.DepartedFragment or
                fragment.atom_epoch != history.old_atom_epoch + index or
                fragment.stage not in ("old-CEM-ion", "reload-ionization", "programme-CEM-ion") or
                (fragment.stage == "old-CEM-ion" and
                 (index != 0 or fragment.cem_receipt_json != history.original_cem_receipt_json)) or
                (fragment.stage == "reload-ionization" and fragment.cem_receipt_json is not None) or
                (fragment.stage == "programme-CEM-ion" and fragment.cem_receipt_json is None)):
            raise ValueError("source departure identity or receipt changed")
        if fragment.cem_receipt_json is not None and _canonical(json.loads(fragment.cem_receipt_json)) != fragment.cem_receipt_json:
            raise ValueError("canonical source departure receipt required")
    receipt = json.loads(history.original_cem_receipt_json)
    if _canonical(receipt) != history.original_cem_receipt_json:
        raise ValueError("canonical original CEM source receipt required")
    return {"old_atom_epoch": history.old_atom_epoch, "cem_receipt": receipt,
            "birth_modes": [[mode.family, mode.f, mode.m] for mode in history.birth_modes],
            "departed_fragments": [{"atom_epoch": item.atom_epoch, "stage": item.stage,
                                    "cem_receipt": None if item.cem_receipt_json is None else
                                    json.loads(item.cem_receipt_json)}
                                   for item in history.departed_fragments],
            "occupied": history.occupied}


def _histories(histories):
    if type(histories) is not tuple or len(histories) != 2:
        raise ValueError("two ordered source trap histories required")
    return tuple(history_record(item) for item in histories)


def _poststate(matrix, histories):
    matrix = joint._matrix(matrix)
    _histories(histories)
    for (row, column), value in matrix.items():
        if matrix.get((column, row), ZERO) != value.conjugate():
            raise ValueError("Hermitian full pair source input required")
        for side, history in enumerate(histories):
            i, j = divmod(row, 33)[side], divmod(column, 33)[side]
            if (i == dipole.ION) != (j == dipole.ION):
                raise ValueError("CEM source requires the generated neutral/ion blocks")
            if not history.occupied and (i, j) != (trap.EMPTY, trap.EMPTY):
                raise ValueError("a vacant source cohort cannot acquire an atom without capture")
    return matrix


@dataclass(frozen=True)
class Mark:
    clicks: tuple
    fragments: tuple


@dataclass(frozen=True)
class Image:
    source_record: dict
    parent_trap_histories: tuple
    receipt: dict
    state: dict
    trace_norm_error: Q


class PairCEMInstrument:
    def __init__(self, *, backgrounds, fragment_efficiencies):
        if (type(backgrounds) not in (tuple, list) or len(backgrounds) != 2 or
                type(fragment_efficiencies) not in (tuple, list) or len(fragment_efficiencies) != 2):
            raise ValueError("two side-owned raw detector backgrounds and efficiencies required")
        self.backgrounds = tuple(full.exact(value) for value in backgrounds)
        self.efficiencies = tuple(full.exact(value) for value in fragment_efficiencies)
        if any(not 0 <= value <= 1 for value in self.backgrounds+self.efficiencies):
            raise ValueError("raw detector probabilities outside physical domain")

    def apply(self, poststate, *, trap_histories, input_error=0):
        """Generate the full fragment/outcome CP instrument on a source image."""
        matrix = _poststate(poststate, trap_histories)
        error = full.nonnegative(input_error)
        parent = _histories(trap_histories)
        source = self.record()
        receipt = {"schema": "rb87-pair-CEM-source-receipt/v1", "detector_source": source,
                   "input_density_sha256": _digest([[i, j, value.serialize()]
                                                     for (i, j), value in sorted(matrix.items())]),
                   "parent_trap_histories": list(parent),
                   "cohort_at_measurement_start": [item.current_atom_epoch for item in trap_histories]}
        state = {}
        for (row, column), value in matrix.items():
            indices = divmod(row, 33)
            fragments = tuple(history.occupied and index == dipole.ION
                              for history, index in zip(trap_histories, indices))
            rates = tuple(d+(1-d)*eta*int(fragment)
                          for d, eta, fragment in zip(self.backgrounds, self.efficiencies, fragments))
            for clicks in product((0, 1), repeat=2):
                weight = (rates[0] if clicks[0] else 1-rates[0]) * (rates[1] if clicks[1] else 1-rates[1])
                local._add(state, (Mark(clicks, fragments), row, column), value*weight)
        return Image(source, trap_histories, receipt, state, error)

    def _image(self, image):
        if type(image) is not Image or image.source_record != self.record():
            raise ValueError("same-source generated CEM image required")
        _histories(image.parent_trap_histories)
        full.nonnegative(image.trace_norm_error)
        return image

    def forget_marks(self, image):
        matrix = {}
        for (_, i, j), value in self._image(image).state.items():
            local._add(matrix, (i, j), value)
        return matrix

    def poststate(self, image, clicks):
        if (type(clicks) is not tuple or len(clicks) != 2 or
                any(type(bit) is not int or bit not in (0, 1) for bit in clicks)):
            raise ValueError("two generated CEM click bits required")
        matrix = {}
        for (mark, i, j), value in self._image(image).state.items():
            if mark.clicks == clicks:
                local._add(matrix, (i, j), value)
        return matrix

    def observations(self, image):
        image = self._image(image)
        result = []
        for clicks in product((0, 1), repeat=2):
            state = self.poststate(image, clicks)
            trace = joint._trace(state)
            if trace.imag:
                raise ValueError("source CEM trace must be real")
            # The complete flagged CP instrument transports upstream error once.
            center, rounding = full.radical_midpoint(trace.real, 160)
            error = image.trace_norm_error+rounding
            result.append({"clicks": clicks, "poststate": state,
                           "trace_bounds": (center-error, center+error),
                           "trace_norm_error": image.trace_norm_error})
        return result

    def coarsen(self, image, *, clicks, photon_counter=0):
        """Same event -> trap carrier; the Image retains the complete CEM journal."""
        image = self._image(image)
        # Also validates the requested classical restriction.
        self.poststate(image, clicks)
        if type(photon_counter) is not int or photon_counter < 0:
            raise ValueError("nonnegative retained shared counter required")
        result, histories = {}, image.parent_trap_histories
        for (mark, row, column), value in image.state.items():
            if mark.clicks != clicks:
                continue
            targets = []
            for side, previous in enumerate(histories):
                if not previous.occupied or not mark.fragments[side]:
                    # No new departure occurs; the event journal still records the background click.
                    targets.append(previous)
                    continue
                receipt = {"pair_event": image.receipt, "side": side, "clicks": list(mark.clicks),
                           "fragment_generated": mark.fragments[side]}
                fragment = trap.DepartedFragment(previous.current_atom_epoch, "programme-CEM-ion", _canonical(receipt))
                targets.append(trap.TrapHistory(previous.old_atom_epoch, previous.original_cem_receipt_json,
                                               previous.birth_modes, previous.departed_fragments+(fragment,), False))
            local._add(result, (tuple(targets), photon_counter, row, column), value)
        return result

    def record(self):
        return {"schema": "rb87-full-pair-CEM-instrument/v1", "physical_dimension": joint.DIMENSION,
                "backgrounds": list(map(str, self.backgrounds)),
                "fragment_efficiencies": list(map(str, self.efficiencies)),
                "fragment_click_rule": "d+(1-d)*eta for a source-generated departed atom; d otherwise",
                "empty_is_ionized_atom": False, "full_pair_input_retained": True,
                "neutral_ion_block_source_required": True, "fresh_noise_source_supplied": False,
                "actual_detector_realization_identified": False, "actual_hardware_uniquely_identified": False,
                "controller_advance": False}

    @classmethod
    def from_record(cls, record):
        if type(record) is not dict or record.get("schema") != "rb87-full-pair-CEM-instrument/v1":
            raise ValueError("raw full pair CEM source record required")
        source = cls(backgrounds=record["backgrounds"], fragment_efficiencies=record["fragment_efficiencies"])
        if source.record() != record:
            raise ValueError("raw CEM source identity or scope changed")
        return source
