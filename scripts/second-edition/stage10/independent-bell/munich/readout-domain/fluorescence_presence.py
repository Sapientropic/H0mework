"""Exact full-atom fluorescence counting and threshold observation source.

SI I.A/B records APD photon counts and chooses trap loading from counts integrated
within 40 ms: https://arxiv.org/pdf/1611.04604v2#page=10 .  The probe programme,
collection, APD background rate, threshold and time coordinate remain raw inverse
variables.  This module generates their counter action; it assigns no values to
the actual comparator, programme or local record clock.

The retained counter is classical, with N meaning at least N photons.  Each
source counter has its own increment channel, including N -> N.  Saturation
does not stop the atom.  Coherent collection mixes only the q modes of an original
resolved line/F'/F bath; secular transition labels remain resolved in its diagonal
efficiency slice.  No photon-count likelihood or completed clock kernel is input.
"""
from fractions import Fraction as Q

import atomic_dipole as dipole
import atomic_full_forward as full
from atom_photon_source import collection_matrix


ZERO = dipole.ComplexRadical()


def _add(matrix, key, value):
    value = matrix.get(key, ZERO) + value
    if value:
        matrix[key] = value
    else:
        matrix.pop(key, None)


def _sum(first, second):
    result = dict(first)
    for key, value in second.items():
        _add(result, key, value)
    return result


def _matrix(matrix):
    if type(matrix) is not dict:
        raise TypeError("source full-atom sparse matrix required")
    result = {}
    for key, value in matrix.items():
        if (type(key) is not tuple or len(key) != 2 or
                any(type(index) is not int or not 0 <= index < full.DIMENSION for index in key)):
            raise ValueError("original 33-state matrix address required")
        value = dipole.complex_exact(value)
        if value:
            result[key] = value
    return result


def _recycling_add(target, operator, rate):
    for (a, i), first in operator.items():
        for (b, j), second in operator.items():
            _add(target, (a, b, i, j), rate * first * second.conjugate())


def _apply_recycling(terms, matrix):
    result = {}
    for (a, b, i, j), coefficient in terms.items():
        value = matrix.get((i, j), ZERO)
        if value:
            _add(result, (a, b), coefficient * value)
    return result


def _trace(matrix, *, neutral=False):
    return sum((value for (i, j), value in matrix.items()
                if i == j and (not neutral or i != dipole.ION)), ZERO)


def natural_channels(program):
    if type(program) is not full.Segment:
        raise TypeError("raw full33 probe Segment required")
    return dipole.natural_jumps(program.radiation_regime, dict.fromkeys(full.WIDTHS, 1))


class CounterGenerator:
    """Generated GKSL action restricted to classical counter-diagonal blocks.

    collection is one passive 2x3 matrix or a complete line/F'/F matrix dictionary.
    efficiencies is an alternative complete original-jump probability dictionary.
    All gamma and ion rates, diagonal detunings and raw fields come from Segment.
    """

    def __init__(self, program, *, threshold, background_rate, collection=None, efficiencies=None):
        if type(threshold) is not int or threshold < 1:
            raise ValueError("positive integer photon threshold required")
        self.jumps = natural_channels(program)
        self.program, self.threshold = program, threshold
        self.background_rate = full.nonnegative(background_rate)
        if (collection is None) == (efficiencies is None):
            raise ValueError("exactly one raw collection or efficiency specification required")
        self.hamiltonian = dipole.hamiltonian(program.fields_r, program.fields_c, program.r, program.c,
                                              program.detunings, convention=program.field_convention)
        self.recycling, self.detected_recycling = {}, {}
        self.outgoing = [Q(0) for _ in dipole.STATES]
        for jump in self.jumps:
            rate = program.gammas[jump.label[:2]]
            operator = {key: dipole.complex_exact(value) for key, value in jump.matrix.items()}
            loss = dipole.matrix_product(dipole.matrix_adjoint(operator), operator)
            if any(i != j or value.imag for (i, j), value in loss.items()):
                raise ValueError("original angular-channel loss is not diagonal")
            for (i, _), value in loss.items():
                self.outgoing[i] += rate * value.real.as_rational()
            _recycling_add(self.recycling, operator, rate)
        for state, rate in program.ion_rates.items():
            source = dipole.INDEX[state]
            self.outgoing[source] += rate
            _add(self.recycling, (dipole.ION, dipole.ION, source, source), dipole.ComplexRadical(rate))
        self.detected_channels, self.undetected_grams = [], {}
        if collection is not None:
            self._coherent_collection(collection)
        else:
            self._diagonal_efficiencies(efficiencies)
        self.unobserved_recycling = dict(self.recycling)
        for key, coefficient in self.detected_recycling.items():
            _add(self.unobserved_recycling, key, -coefficient)
        self._check_trace()

    def _coherent_collection(self, collection):
        if self.program.radiation_regime != "coherent_q_F":
            raise ValueError("q-coherent collection requires the original coherent_q_F bath")
        groups = {}
        for jump in self.jumps:
            groups.setdefault(jump.label[:3], {})[jump.label[3]] = jump.matrix
        if type(collection) is dict:
            if set(collection) != set(groups):
                raise ValueError("complete resolved line/F'/F collection dictionary required")
            matrices = {group: collection_matrix(collection[group]) for group in groups}
        else:
            matrix = collection_matrix(collection)
            matrices = dict.fromkeys(groups, matrix)
        for group, operators in groups.items():
            matrix = matrices[group]
            self.undetected_grams[group] = tuple(tuple(
                dipole.ComplexRadical(int(q == r)) -
                sum((matrix[p][q].conjugate() * matrix[p][r] for p in range(2)), ZERO)
                for r in range(3)) for q in range(3))
            for p in range(2):
                operator = {}
                for q, atomic in operators.items():
                    for key, value in atomic.items():
                        _add(operator, key, matrix[p][dipole.Q_COMPONENTS.index(q)] * value)
                rate = self.program.gammas[group[:2]]
                _recycling_add(self.detected_recycling, operator, rate)
                self.detected_channels.append((group + (p,), operator, rate))
        self.collection_record = {"mode": "coherent_2x3", "groups": [
            {"label": list(group), "matrix": [[value.serialize() for value in row] for row in matrices[group]]}
            for group in sorted(groups)]}

    def _diagonal_efficiencies(self, efficiencies):
        labels = {jump.label for jump in self.jumps}
        if type(efficiencies) is not dict or set(efficiencies) != labels:
            raise ValueError("complete original-jump efficiency dictionary required")
        values = {label: full.nonnegative(value) for label, value in efficiencies.items()}
        if any(value > 1 for value in values.values()):
            raise ValueError("collected photon efficiency exceeds one")
        for jump in self.jumps:
            operator = {key: dipole.complex_exact(value) for key, value in jump.matrix.items()}
            rate = values[jump.label] * self.program.gammas[jump.label[:2]]
            _recycling_add(self.detected_recycling, operator, rate)
            self.detected_channels.append((jump.label, operator, rate))
        self.collection_record = {"mode": "diagonal_original_channels", "channels": [
            {"label": list(label), "efficiency": str(values[label])} for label in sorted(labels)]}

    def _check_trace(self):
        feedback = {}
        for (a, b, i, j), coefficient in self.recycling.items():
            if a == b:
                _add(feedback, (i, j), coefficient)
        expected = {(i, i): dipole.ComplexRadical(rate) for i, rate in enumerate(self.outgoing) if rate}
        if feedback != expected:
            raise ValueError("original full33 recycling/loss trace identity failed")
        for key in set(self.recycling) | set(self.detected_recycling):
            if self.unobserved_recycling.get(key, ZERO) + self.detected_recycling.get(key, ZERO) != self.recycling.get(key, ZERO):
                raise ValueError("source monitored/unmonitored recycling sum failed")
        if self.outgoing[dipole.ION]:
            raise ValueError("original ion sink is not absorbing")

    def lift(self, poststate, *, counter=0):
        """Linear intake of the same 33-state source postmeasurement matrix."""
        if type(counter) is not int or not 0 <= counter <= self.threshold:
            raise ValueError("retained photon-counter address required")
        return {(counter, i, j): value for (i, j), value in _matrix(poststate).items()}

    def _blocks(self, state):
        if type(state) is not dict:
            raise TypeError("sparse counter/atom state required")
        blocks = {}
        for key, value in state.items():
            if (type(key) is not tuple or len(key) != 3 or type(key[0]) is not int or
                    not 0 <= key[0] <= self.threshold):
                raise ValueError("retained photon-counter address required")
            matrix = _matrix({key[1:]: value})
            if matrix:
                blocks.setdefault(key[0], {}).update(matrix)
        return blocks

    def _drift(self, matrix):
        result = {}
        for (i, j), value in matrix.items():
            _add(result, (i, j), -(self.outgoing[i] + self.outgoing[j]) * value * Q(1, 2))
        left = dipole.matrix_product(self.hamiltonian, matrix)
        right = dipole.matrix_product(matrix, self.hamiltonian)
        for key in set(left) | set(right):
            _add(result, key, dipole.ComplexRadical(0, -1) * (left.get(key, ZERO) - right.get(key, ZERO)))
        return result

    def atomic_action(self, matrix):
        matrix = _matrix(matrix)
        return _sum(self._drift(matrix), _apply_recycling(self.recycling, matrix))

    def action(self, state):
        result = {}
        for counter, matrix in self._blocks(state).items():
            target = min(counter + 1, self.threshold)
            stay = _sum(self._drift(matrix), _apply_recycling(self.unobserved_recycling, matrix))
            move = _apply_recycling(self.detected_recycling, matrix)
            for key, value in matrix.items():
                _add(stay, key, -self.background_rate * value)
                _add(move, key, self.background_rate * value)
            for (i, j), value in stay.items():
                _add(result, (counter, i, j), value)
            for (i, j), value in move.items():
                _add(result, (target, i, j), value)
        return result

    def forget_counter(self, state):
        result = {}
        for matrix in self._blocks(state).values():
            result = _sum(result, matrix)
        return result

    def observations(self, state):
        """Read both complete threshold outcomes and their subnormalised continuations."""
        below, above = {}, {}
        for counter, matrix in self._blocks(state).items():
            if counter == self.threshold:
                above = _sum(above, matrix)
            else:
                below = _sum(below, matrix)
        total = _sum(below, above)
        return {"below_N": {"weight": _trace(below), "poststate": below},
                "at_least_N": {"weight": _trace(above), "poststate": above},
                "neutral_survival": _trace(total, neutral=True),
                "total_weight": _trace(total), "unconditional_poststate": total}

    def record(self):
        return {"schema": "rb87-fluorescence-counter-source/v1", "probe_programme": self.program.record(),
                "physical_dimension": full.DIMENSION, "threshold": self.threshold,
                "counter_levels": self.threshold + 1, "top_counter": "at least N; atomic dynamics continues",
                "background_rate": str(self.background_rate), "collection": self.collection_record,
                "counter_representation": "classical diagonal blocks; each original count has its own jump",
                "original_angular_channels": len(self.jumps), "resolved_ion_channels": len(full.EXCITED),
                "source_trace_identity_checked": True, "monitored_recycling_completeness_checked": True,
                "public_protocol_source": "https://arxiv.org/pdf/1611.04604v2#page=10; SI I.A/B",
                "actual_presence_programme_identified": False, "actual_clock_encoder_identified": False,
                "actual": False, "controller_advance": False, "propagation_performed": False}
