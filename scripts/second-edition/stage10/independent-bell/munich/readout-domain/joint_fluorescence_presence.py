"""Two original atom baths, one collected-photon counter and full joint memory.

Garthoff 2021 Sec. 2.6.3 (pp32--34) uses the common BSM/APDs to monitor both
traps, alternately switching their cooling light for source discrimination:
https://xqp.physik.uni-muenchen.de/publications/files/theses_phd/phd_garthoff.pdf .
The raw fields in each Segment encode those masks.  Switching a laser off does
not remove an atom.  Original resolved line/F'/F bath groups remain distinct.

A passive optical matrix acts on six modes (Aq=-1,0,+1; Bq=-1,0,+1).  Detected
jumps may coherently mix sides, but their unobserved complement cancels every
cross term when the counter is forgotten.  The unconditional source is the two
original independent atomic GKSL generators, rather than a collective bath.
"""
from fractions import Fraction as Q

import atomic_dipole as dipole
import atomic_full_forward as full
import fluorescence_presence as local
from atom_photon_source import radical_inverse, radical_sign


ATOM_DIMENSION = full.DIMENSION
DIMENSION = ATOM_DIMENSION ** 2
ZERO = dipole.ComplexRadical()
MODE_ORDER = tuple((side, q) for side in ("A", "B") for q in dipole.Q_COMPONENTS)


def atom_pair_index(a, b):
    if any(type(index) is not int or not 0 <= index < ATOM_DIMENSION for index in (a, b)):
        raise ValueError("original two-atom basis addresses required")
    return ATOM_DIMENSION * a + b


def _matrix(matrix):
    if type(matrix) is not dict:
        raise TypeError("source sparse joint matrix required")
    result = {}
    for key, value in matrix.items():
        if (type(key) is not tuple or len(key) != 2 or
                any(type(index) is not int or not 0 <= index < DIMENSION for index in key)):
            raise ValueError("original 33x33 tensor matrix address required")
        value = dipole.complex_exact(value)
        if value:
            result[key] = value
    return result


def passive_transfer(matrix):
    """Exact Schur-complement PSD check for I6-T* T, including zero pivots."""
    if (type(matrix) not in (tuple, list) or not 1 <= len(matrix) <= 4 or
            any(type(row) not in (tuple, list) or len(row) != 6 for row in matrix)):
        raise ValueError("one to four detector rows by six raw source modes required")
    matrix = tuple(tuple(dipole.complex_exact(value) for value in row) for row in matrix)
    gram = tuple(tuple(sum((row[i].conjugate() * row[j] for row in matrix), ZERO)
                       for j in range(6)) for i in range(6))
    remainder = tuple(tuple(dipole.ComplexRadical(int(i == j)) - gram[i][j]
                            for j in range(6)) for i in range(6))
    schur = [list(row) for row in remainder]
    for pivot in range(6):
        value = schur[pivot][pivot]
        sign = radical_sign(value.real)
        if value.imag or sign < 0:
            raise ValueError("nonphysical shared collection: T* T exceeds identity")
        if sign == 0:
            if any(schur[pivot][j] for j in range(pivot + 1, 6)):
                raise ValueError("nonphysical shared collection: zero PSD pivot has nonzero row")
            continue
        inverse = radical_inverse(value.real)
        for i in range(pivot + 1, 6):
            for j in range(pivot + 1, 6):
                schur[i][j] -= schur[i][pivot] * schur[pivot][j] * inverse
    return matrix, gram, remainder


def _source(source):
    if type(source) is local.CounterGenerator:
        source = source.program
    if type(source) is not full.Segment:
        raise TypeError("original CounterGenerator or raw full33 Segment required")
    programme = full.Segment.from_record(source.record())
    if programme.radiation_regime != "coherent_q_F":
        raise ValueError("shared q-coherent collection requires coherent_q_F source baths")
    efficiencies = {jump.label: 0 for jump in local.natural_channels(programme)}
    # Only the original atomic source is imported; local counters/backgrounds
    # do not define the common detector's counter or background process.
    return local.CounterGenerator(programme, threshold=1, background_rate=0, efficiencies=efficiencies)


def _operator_left(matrix, side, operator):
    columns = {}
    for (target, source), value in operator.items():
        columns.setdefault(source, []).append((target, value))
    result = {}
    for (row, column), value in matrix.items():
        a, b = divmod(row, ATOM_DIMENSION)
        for target, coefficient in columns.get(a if side == 0 else b, ()):
            index = atom_pair_index(target, b) if side == 0 else atom_pair_index(a, target)
            local._add(result, (index, column), coefficient * value)
    return result


def _operator_right(matrix, side, operator):
    rows = {}
    for (source, target), value in operator.items():
        rows.setdefault(source, []).append((target, value))
    result = {}
    for (row, column), value in matrix.items():
        a, b = divmod(column, ATOM_DIMENSION)
        for target, coefficient in rows.get(a if side == 0 else b, ()):
            index = atom_pair_index(target, b) if side == 0 else atom_pair_index(a, target)
            local._add(result, (row, index), value * coefficient)
    return result


def _trace(matrix, neutral_sides=()):
    return sum((value for (i, j), value in matrix.items() if i == j and
                all(divmod(i, ATOM_DIMENSION)[side] != dipole.ION for side in neutral_sides)), ZERO)


class JointCounterGenerator:
    physical_dimension = DIMENSION

    def __init__(self, first, second, *, threshold, background_rate, collection):
        if type(threshold) is not int or threshold < 1:
            raise ValueError("positive integer shared photon threshold required")
        self.sources = _source(first), _source(second)
        if self.sources[0].program.duration != self.sources[1].program.duration:
            raise ValueError("both original programmes require the same raw duration")
        self.duration = self.sources[0].program.duration
        self.threshold, self.background_rate = threshold, full.nonnegative(background_rate)
        groups = {}
        for side, source in enumerate(self.sources):
            for jump in source.jumps:
                groups.setdefault(jump.label[:3], {})[side, jump.label[3]] = jump.matrix
        if type(collection) is dict:
            if set(collection) != set(groups):
                raise ValueError("complete original line/F'/F collection dictionary required")
            checked = {group: passive_transfer(collection[group]) for group in groups}
        else:
            value = passive_transfer(collection)
            checked = dict.fromkeys(groups, value)
        rows = {len(item[0]) for item in checked.values()}
        if len(rows) != 1:
            raise ValueError("shared APD port inventory differs between source environment groups")
        self.detector_ports = rows.pop()
        self.detected_operators, self.undetected_grams = [], {}
        for group, operators in sorted(groups.items()):
            matrix, gram, remainder = checked[group]
            self.undetected_grams[group] = remainder
            for i in range(6):
                for j in range(6):
                    if gram[i][j] + remainder[i][j] != dipole.ComplexRadical(int(i == j)):
                        raise ValueError("independent-bath observed/unobserved Gram sum failed")
            for port in range(self.detector_ports):
                output = ({}, {})
                for (side, q), atomic in operators.items():
                    factor = matrix[port][3 * side + dipole.Q_COMPONENTS.index(q)] * dipole.sqrt_rational(
                        self.sources[side].program.gammas[group[:2]])
                    for key, value in atomic.items():
                        local._add(output[side], key, factor * value)
                self.detected_operators.append((group + (port,), output))
        self.collection_record = [{"label": list(group),
                                   "matrix": [[value.serialize() for value in row] for row in checked[group][0]]}
                                  for group in sorted(groups)]

    def independent_atomic_action(self, matrix):
        matrix = _matrix(matrix)
        result = {}
        for side, source in enumerate(self.sources):
            fibres = {}
            for (row, column), value in matrix.items():
                a, b = divmod(row, ATOM_DIMENSION)
                c, d = divmod(column, ATOM_DIMENSION)
                fixed, key = ((b, d), (a, c)) if side == 0 else ((a, c), (b, d))
                fibres.setdefault(fixed, {})[key] = value
            for (fixed_row, fixed_column), fibre in fibres.items():
                for (i, j), value in source.atomic_action(fibre).items():
                    key = ((atom_pair_index(i, fixed_row), atom_pair_index(j, fixed_column)) if side == 0 else
                           (atom_pair_index(fixed_row, i), atom_pair_index(fixed_column, j)))
                    local._add(result, key, value)
        return result

    def detected_action(self, matrix):
        matrix = _matrix(matrix)
        result = {}
        for _, operators in self.detected_operators:
            left = local._sum(_operator_left(matrix, 0, operators[0]), _operator_left(matrix, 1, operators[1]))
            right = local._sum(_operator_right(left, 0, dipole.matrix_adjoint(operators[0])),
                               _operator_right(left, 1, dipole.matrix_adjoint(operators[1])))
            result = local._sum(result, right)
        return result

    def unobserved_action(self, matrix):
        result = self.independent_atomic_action(matrix)
        for key, value in self.detected_action(matrix).items():
            local._add(result, key, -value)
        return result

    def lift(self, poststate, *, counter=0):
        if type(counter) is not int or not 0 <= counter <= self.threshold:
            raise ValueError("retained shared photon-counter address required")
        return {(counter, i, j): value for (i, j), value in _matrix(poststate).items()}

    def _blocks(self, state):
        if type(state) is not dict:
            raise TypeError("source sparse counter/joint-atom matrix required")
        result = {}
        for key, value in state.items():
            if (type(key) is not tuple or len(key) != 3 or type(key[0]) is not int or
                    not 0 <= key[0] <= self.threshold):
                raise ValueError("retained shared photon-counter address required")
            matrix = _matrix({key[1:]: value})
            if matrix:
                result.setdefault(key[0], {}).update(matrix)
        return result

    def action(self, state):
        result = {}
        for counter, matrix in self._blocks(state).items():
            move = self.detected_action(matrix)
            stay = self.independent_atomic_action(matrix)
            for key, value in move.items():
                local._add(stay, key, -value)
            for key, value in matrix.items():
                local._add(stay, key, -self.background_rate * value)
                local._add(move, key, self.background_rate * value)
            target = min(counter + 1, self.threshold)
            for (i, j), value in stay.items():
                local._add(result, (counter, i, j), value)
            for (i, j), value in move.items():
                local._add(result, (target, i, j), value)
        return result

    def forget_counter(self, state):
        result = {}
        for matrix in self._blocks(state).values():
            result = local._sum(result, matrix)
        return result

    def observations(self, state, *, threshold=None):
        threshold = self.threshold if threshold is None else threshold
        if type(threshold) is not int or not 1 <= threshold <= self.threshold:
            raise ValueError("observation threshold exceeds the retained shared count")
        below, above = {}, {}
        for counter, matrix in self._blocks(state).items():
            if counter >= threshold:
                above = local._sum(above, matrix)
            else:
                below = local._sum(below, matrix)
        total = local._sum(below, above)
        return {"below_N": {"weight": _trace(below), "poststate": below},
                "at_least_N": {"weight": _trace(above), "poststate": above},
                "neutral_A": _trace(total, (0,)), "neutral_B": _trace(total, (1,)),
                "both_neutral": _trace(total, (0, 1)), "total_weight": _trace(total),
                "unconditional_poststate": total}

    def record(self):
        return {"schema": "rb87-joint-fluorescence-counter-source/v1",
                "programmes": [source.program.record() for source in self.sources],
                "duration": str(self.duration), "physical_dimension": DIMENSION,
                "atom_dimension": ATOM_DIMENSION, "tensor_index": "33*A+B",
                "threshold": self.threshold, "counter_levels": self.threshold + 1,
                "top_counter": "at least N; both original atomic dynamics continue",
                "background_rate": str(self.background_rate), "background_channels": 1,
                "detector_ports": self.detector_ports, "mode_order": [list(mode) for mode in MODE_ORDER],
                "collection": self.collection_record, "bath_environment": "original resolved line/F'/F groups",
                "unconditional_bath": "two original independent atomic baths",
                "observed_unobserved_gram_identity_checked": True,
                "source_trace_identity_checked": True, "dense_tensor_enumeration_used": False,
                "actual_presence_programme_identified": False, "actual_clock_encoder_identified": False,
                "actual": False, "controller_advance": False, "propagation_performed": False}

    @classmethod
    def from_record(cls, record):
        if type(record) is not dict or record.get("schema") != "rb87-joint-fluorescence-counter-source/v1":
            raise ValueError("registered raw joint fluorescence source record required")

        def exact_complex(value):
            def radical(part):
                return dipole.Radical({int(root): full.exact(coefficient) for root, coefficient in part.items()})
            return dipole.ComplexRadical(radical(value["real"]), radical(value["imag"]))

        if len(record["programmes"]) != 2:
            raise ValueError("both original atom programmes required")
        collection = {}
        for item in record["collection"]:
            label = tuple(item["label"])
            if label in collection:
                raise ValueError("duplicate source collection environment group")
            collection[label] = tuple(tuple(exact_complex(value) for value in row) for row in item["matrix"])
        source = cls(*(full.Segment.from_record(item) for item in record["programmes"]),
                     threshold=record["threshold"], background_rate=record["background_rate"], collection=collection)
        if source.record() != record:
            raise ValueError("joint source record identity or claim scope changed")
        return source
