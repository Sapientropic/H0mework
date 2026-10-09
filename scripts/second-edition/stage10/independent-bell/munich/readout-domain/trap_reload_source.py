"""Source-generated capture into a vacant trap, with atom cohort history retained.

Garthoff 2021 Secs. 2.2.2/2.2.4 describe MOT cooling/repumping, capture into the
dipole trap after additional cooling scattering, collision blockade, and count-
controlled MOT switching (https://xqp.physik.uni-muenchen.de/publications/files/
theses_phd/phd_garthoff.pdf).  The finite model here is an explicit Markov capture
hypothesis: an unresolved reservoir supplies ground modes with mean occupations
n_s and complex transfer couplings g_s.  It does not derive these couplings from
the MOT fields or assert the hypothesis as an identified apparatus programme.

Trap index32 means Empty, while legacy index32 means an ionized old atom.
Their source coarsening records the departed ion and CEM receipt.  A subsequent
capture represents a reservoir atom entering the trap and generates a fresh
cohort; it never removes the old departure record.  The constant capture-bath
moments neglect reservoir depletion.  No prepared density or waiting kernel is
an input.  First capture and count-recognized loading are separate events.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import atomic_modes as modes
import fluorescence_presence as presence


EMPTY = dipole.ION
NEUTRAL = tuple(index for index in range(full.DIMENSION) if index != dipole.ION)
GROUND = tuple(state for state in dipole.STATES if state.family == "ground")
ZERO = dipole.ComplexRadical()


@dataclass(frozen=True)
class DepartedFragment:
    atom_epoch: int
    stage: str
    cem_receipt_json: str | None


@dataclass(frozen=True)
class TrapHistory:
    old_atom_epoch: int
    original_cem_receipt_json: str
    birth_modes: tuple
    departed_fragments: tuple
    occupied: bool

    @property
    def birth_counter(self):
        return len(self.birth_modes)

    @property
    def current_atom_epoch(self):
        return self.old_atom_epoch + self.birth_counter if self.occupied else None

    def capture(self, ground):
        if self.occupied or ground not in GROUND:
            raise ValueError("capture requires Empty and an original ground reservoir mode")
        return TrapHistory(self.old_atom_epoch, self.original_cem_receipt_json,
                           self.birth_modes + (ground,), self.departed_fragments, True)

    def depart(self):
        if not self.occupied:
            raise ValueError("departure requires an occupied original cohort")
        fragment = DepartedFragment(self.current_atom_epoch, "reload-ionization", None)
        return TrapHistory(self.old_atom_epoch, self.original_cem_receipt_json,
                           self.birth_modes, self.departed_fragments + (fragment,), False)


def _receipt(value):
    try:
        return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)
    except (TypeError, ValueError) as error:
        raise ValueError("immutable JSON CEM source receipt required") from error


def coarsen_old_cem(poststate, *, old_atom_epoch, cem_receipt, photon_counter=0):
    """Explicit legacy33 -> trap33 plus departure/history source instrument.

    The paid CEM instrument produces neutral-plus-ion blocks.  Ion-neutral
    coherences cannot be silently erased at this source interface.
    """
    if type(old_atom_epoch) is not int or old_atom_epoch < 0 or type(photon_counter) is not int or photon_counter < 0:
        raise ValueError("original atom epoch and nonnegative photon counter required")
    matrix = presence._matrix(poststate)
    if any((i == dipole.ION) != (j == dipole.ION) for i, j in matrix):
        raise ValueError("old CEM source must have neutral/ion block structure")
    if any(matrix.get((j, i), ZERO) != value.conjugate() for (i, j), value in matrix.items()):
        raise ValueError("Hermitian old CEM poststate required")
    receipt = _receipt(cem_receipt)
    neutral_history = TrapHistory(old_atom_epoch, receipt, (), (), True)
    ion_history = TrapHistory(old_atom_epoch, receipt, (),
                              (DepartedFragment(old_atom_epoch, "old-CEM-ion", receipt),), False)
    return {(ion_history if i == dipole.ION else neutral_history, photon_counter, i, j): value
            for (i, j), value in matrix.items()}


class ReloadSource:
    physical_dimension = full.DIMENSION

    def __init__(self, original, *, reservoir_occupations, capture_couplings):
        if type(original) is not presence.CounterGenerator:
            raise TypeError("original registered fluorescence CounterGenerator required")
        # Reconstruct the source from its primitive record rather than consume
        # a caller's cached action.  The coarsening is a separate entry operation.
        from fluorescence_channel import source_from_record
        self.original = source_from_record(original.record())
        if (type(reservoir_occupations) is not dict or set(reservoir_occupations) != set(GROUND) or
                type(capture_couplings) is not dict or set(capture_couplings) != set(GROUND)):
            raise ValueError("all eight original ground reservoir modes required")
        self.occupations = {state: full.nonnegative(reservoir_occupations[state]) for state in GROUND}
        self.couplings = {state: dipole.complex_exact(capture_couplings[state]) for state in GROUND}
        self.birth_operators, self.rates = {}, {}
        for state in GROUND:
            amplitude = self.couplings[state] * dipole.sqrt_rational(self.occupations[state])
            self.birth_operators[state] = {(dipole.INDEX[state], EMPTY): amplitude} if amplitude else {}
            self.rates[state] = self.occupations[state] * (
                self.couplings[state].real * self.couplings[state].real +
                self.couplings[state].imag * self.couplings[state].imag)
        self.first_birth_rate = sum(self.rates.values(), dipole.Radical())
        self.threshold, self.duration = self.original.threshold, self.original.program.duration

    def _blocks(self, state):
        if type(state) is not dict:
            raise TypeError("source trap/history sparse state required")
        blocks = {}
        for key, value in state.items():
            if (type(key) is not tuple or len(key) != 4 or type(key[0]) is not TrapHistory or
                    type(key[1]) is not int or not 0 <= key[1] <= self.threshold):
                raise ValueError("source trap history and retained photon-counter address required")
            history, counter, i, j = key
            if (type(history.old_atom_epoch) is not int or history.old_atom_epoch < 0 or
                    type(history.occupied) is not bool or type(history.birth_modes) is not tuple or
                    any(type(mode) is not dipole.State or mode not in GROUND for mode in history.birth_modes) or
                    type(history.departed_fragments) is not tuple or
                    len(history.departed_fragments) != history.birth_counter + int(not history.occupied)):
                raise ValueError("source cohort/departure history is incomplete")
            for index, fragment in enumerate(history.departed_fragments):
                if (type(fragment) is not DepartedFragment or fragment.atom_epoch != history.old_atom_epoch + index or
                        fragment.stage not in ("old-CEM-ion", "reload-ionization") or
                        (fragment.stage == "old-CEM-ion" and (index != 0 or fragment.cem_receipt_json != history.original_cem_receipt_json)) or
                        (fragment.stage == "reload-ionization" and fragment.cem_receipt_json is not None)):
                    raise ValueError("original departure identity or CEM receipt changed")
            matrix = presence._matrix({(i, j): value})
            if (history.occupied and EMPTY in (i, j)) or (not history.occupied and (i, j) != (EMPTY, EMPTY)):
                raise ValueError("cohort occupancy and original trap matrix addresses differ")
            if matrix:
                blocks.setdefault(history, {}).update({(counter, i, j): matrix[i, j]})
        return blocks

    def action(self, state):
        result = {}
        for history, block in self._blocks(state).items():
            change = self.original.action(block)
            # Resolved ionization leaves a source departure, rather than leave
            # an ion in the current trap cohort or relabel it as a new atom.
            if history.occupied:
                for counter in range(self.threshold + 1):
                    flux = sum((block.get((counter, dipole.INDEX[excited], dipole.INDEX[excited]), ZERO) * rate
                                for excited, rate in self.original.program.ion_rates.items()), ZERO)
                    if flux:
                        presence._add(change, (counter, EMPTY, EMPTY), -flux)
                        presence._add(result, (history.depart(), counter, EMPTY, EMPTY), flux)
            for (counter, i, j), value in change.items():
                presence._add(result, (history, counter, i, j), value)
            if not history.occupied:
                for (counter, i, j), value in block.items():
                    presence._add(result, (history, counter, i, j), -value * self.first_birth_rate)
                    for ground, rate in self.rates.items():
                        if rate:
                            target = dipole.INDEX[ground]
                            presence._add(result, (history.capture(ground), counter, target, target), value * rate)
        return result

    def forget_history(self, state):
        result = {}
        for block in self._blocks(state).values():
            result = presence._sum(result, block)
        return result

    def projected_action(self, matrix):
        """Full old atomic/photon source plus self-generated capture dissipators."""
        result = self.original.action(matrix)
        for counter in range(self.threshold + 1):
            atom = {(i, j): dipole.complex_exact(value) for (c, i, j), value in matrix.items() if c == counter}
            for operator in self.birth_operators.values():
                adjoint = dipole.matrix_adjoint(operator)
                loss = dipole.matrix_product(adjoint, operator)
                recycling = dipole.matrix_product(dipole.matrix_product(operator, atom), adjoint)
                for key, value in recycling.items():
                    presence._add(result, (counter, *key), value)
                for product in (dipole.matrix_product(loss, atom), dipole.matrix_product(atom, loss)):
                    for key, value in product.items():
                        presence._add(result, (counter, *key), -value * Q(1, 2))
        return result

    def first_birth_survival_interval(self, time, *, bits=160):
        """Source-derived exp(-Lambda*t) from an initial Empty trap.

        An occupied or mixed post-CEM input requires the full source evolution;
        this conditional first-capture law is not the recognized-loading law.
        """
        time = full.nonnegative(time)
        if type(bits) is not int or not 64 <= bits <= 512:
            raise ValueError("registered scalar bound precision required")
        if not time or not self.first_birth_rate:
            return Q(1), Q(1)
        center, error = full.radical_midpoint(self.first_birth_rate, bits)
        low, high = max(Q(0), center - error), center + error
        a, ea = modes.complex_exponential(-high * time, 0, bits=bits)
        b, eb = modes.complex_exponential(-low * time, 0, bits=bits)
        return max(Q(0), a[0] - ea), min(Q(1), b[0] + eb)

    def record(self):
        return {"schema": "rb87-trap-reload-source/v1", "original_counter_source": self.original.record(),
                "physical_dimension": full.DIMENSION, "empty_index": EMPTY,
                "neutral_indices": list(NEUTRAL), "ground_reservoir_modes": [
                    {"state": [state.family, state.f, state.m], "occupation": str(self.occupations[state]),
                     "capture_coupling": self.couplings[state].serialize(), "birth_rate": self.rates[state].serialize()}
                    for state in GROUND], "total_first_birth_rate": self.first_birth_rate.serialize(),
                "capture_model": "finite 0/1 boson occupation; incoherent Markov reservoir ground modes",
                "reservoir_model": "fixed occupation moments; transfer into trap; depletion unresolved",
                "capture_bath_monitored_by_APD": False,
                "birth_counter_generated_from_capture_history": True,
                "new_atom_epoch_rule": "old_atom_epoch+number_of_source_capture_events",
                "first_birth_waiting_initial_condition": "trap initially Empty",
                "coarsening_requires_departed_fragment_and_original_CEM_receipt": True,
                "recognized_reload_waiting_law_generated": False,
                "field_MOT_capture_realization_identified": False,
                "actual_hardware_identity_asserted": False, "actual_clock_encoder_identified": False,
                "controller_advance": False, "propagation_performed": False}

    @classmethod
    def from_record(cls, record):
        from fluorescence_channel import source_from_record, _complex_record
        if type(record) is not dict or record.get("schema") != "rb87-trap-reload-source/v1":
            raise ValueError("registered raw trap capture source record required")
        original = source_from_record(record["original_counter_source"])
        occupations, couplings = {}, {}
        for item in record["ground_reservoir_modes"]:
            state = item["state"]
            if (type(state) is not list or len(state) != 3 or state[0] != "ground" or
                    type(state[1]) is not int or type(state[2]) is not int):
                raise ValueError("original ground reservoir mode identity required")
            state = dipole.State(*state)
            if state not in GROUND or state in occupations:
                raise ValueError("unknown or duplicate source capture mode")
            occupations[state], couplings[state] = full.nonnegative(item["occupation"]), _complex_record(item["capture_coupling"])
        source = cls(original, reservoir_occupations=occupations, capture_couplings=couplings)
        if source.record() != record:
            raise ValueError("raw capture source identity or claim scope changed")
        return source
