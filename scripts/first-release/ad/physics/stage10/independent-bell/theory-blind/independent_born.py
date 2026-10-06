"""Full eight-dimensional Born contraction over Q(sqrt(2)), without data input.

The basis is (Dirac component, color), in lexicographic order.  Source
coefficients, the doubled spin action, and color-Z preparation follow the
original source declarations.  All probabilities are obtained by multiplying
spectral projection matrices into that vector; no closed Bell probability
formula is used here.  Evidence storage belongs to the caller.
"""

from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class Q2:
    r: Fraction = Fraction(0)
    s: Fraction = Fraction(0)

    def __post_init__(self):
        for name in ("r", "s"):
            value = getattr(self, name)
            if type(value) not in (int, Fraction):
                raise TypeError("exact rational coefficients required")
            object.__setattr__(self, name, Fraction(value))

    @staticmethod
    def coerce(value):
        if isinstance(value, Q2):
            return value
        return Q2(value)

    def __add__(self, other):
        other = self.coerce(other)
        return Q2(self.r + other.r, self.s + other.s)

    __radd__ = __add__

    def __neg__(self):
        return Q2(-self.r, -self.s)

    def __sub__(self, other):
        return self + -self.coerce(other)

    def __rsub__(self, other):
        return self.coerce(other) - self

    def __mul__(self, other):
        other = self.coerce(other)
        return Q2(self.r * other.r + 2 * self.s * other.s,
                  self.r * other.s + self.s * other.r)

    __rmul__ = __mul__

    def inverse(self):
        norm = self.r * self.r - 2 * self.s * self.s
        if norm == 0:
            raise ZeroDivisionError("zero field element")
        return Q2(self.r / norm, -self.s / norm)

    def __truediv__(self, other):
        return self * self.coerce(other).inverse()

    def __rtruediv__(self, other):
        return self.coerce(other) / self

    def sign(self):
        if self.s == 0:
            return (self.r > 0) - (self.r < 0)
        if self.r == 0:
            return (self.s > 0) - (self.s < 0)
        if self.r > 0 and self.s > 0:
            return 1
        if self.r < 0 and self.s < 0:
            return -1
        difference = self.r * self.r - 2 * self.s * self.s
        return ((difference > 0) - (difference < 0)) * ((self.r > 0) - (self.r < 0))

    def record(self):
        return {"r": str(self.r), "s": str(self.s)}


ZERO = Q2()
ONE = Q2(1)
SQRT2 = Q2(0, 1)


@dataclass(frozen=True)
class C2:
    real: Q2 = ZERO
    imag: Q2 = ZERO

    def __post_init__(self):
        object.__setattr__(self, "real", Q2.coerce(self.real))
        object.__setattr__(self, "imag", Q2.coerce(self.imag))

    @staticmethod
    def coerce(value):
        return value if isinstance(value, C2) else C2(Q2.coerce(value))

    def __add__(self, other):
        other = self.coerce(other)
        return C2(self.real + other.real, self.imag + other.imag)

    __radd__ = __add__

    def __neg__(self):
        return C2(-self.real, -self.imag)

    def __mul__(self, other):
        other = self.coerce(other)
        return C2(self.real * other.real - self.imag * other.imag,
                  self.real * other.imag + self.imag * other.real)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Q2.coerce(other)
        return C2(self.real / other, self.imag / other)

    def conjugate(self):
        return C2(self.real, -self.imag)

    def norm_sq(self):
        return self.real * self.real + self.imag * self.imag

    def record(self):
        return {"real": self.real.record(), "imag": self.imag.record()}


def identity(dimension):
    return tuple(tuple(ONE if row == column else ZERO
                       for column in range(dimension)) for row in range(dimension))


def transpose(matrix):
    return tuple(tuple(matrix[column][row] for column in range(len(matrix)))
                 for row in range(len(matrix[0])))


def matmul(first, second):
    if len(first[0]) != len(second):
        raise ValueError("matrix dimensions disagree")
    return tuple(tuple(sum((first[row][index] * second[index][column]
                            for index in range(len(second))), ZERO)
                       for column in range(len(second[0]))) for row in range(len(first)))


def add(first, second):
    return tuple(tuple(first[row][column] + second[row][column]
                       for column in range(len(first[0]))) for row in range(len(first)))


def scale(coefficient, matrix):
    coefficient = Q2.coerce(coefficient)
    return tuple(tuple(value * coefficient for value in row) for row in matrix)


def tensor(first, second):
    return tuple(tuple(first[row_a][column_a] * second[row_b][column_b]
                       for column_a in range(len(first[0]))
                       for column_b in range(len(second[0])))
                 for row_a in range(len(first)) for row_b in range(len(second)))


def act(matrix, vector):
    if len(matrix[0]) != len(vector):
        raise ValueError("vector dimension disagrees")
    return tuple(sum((vector[column] * matrix[row][column]
                      for column in range(len(vector))), C2()) for row in range(len(matrix)))


def inner(first, second):
    return sum((left.conjugate() * right for left, right in zip(first, second)), C2())


def axis(x, z):
    x, z = Q2.coerce(x), Q2.coerce(z)
    if x * x + z * z != ONE:
        raise ValueError("nonunit XZ axis")
    return ((z, x), (x, -z))


def spin_axis(x, z):
    return tensor(identity(2), axis(x, z))


def outcome_sign(outcome):
    if type(outcome) is not bool:
        raise TypeError("finite outcome label must be bool")
    return -ONE if outcome else ONE


def spectral_projection(observable, outcome):
    dimension = len(observable)
    unit = identity(dimension)
    if transpose(observable) != observable or matmul(observable, observable) != unit:
        raise ValueError("observable is not a self-adjoint involution")
    return scale(Fraction(1, 2), add(unit, scale(outcome_sign(outcome), observable)))


def joint_projection(a, b, outcome_a, outcome_b):
    return tensor(spectral_projection(spin_axis(*a), outcome_a),
                  spectral_projection(axis(*b), outcome_b))


def certify_projection(projection):
    unit = identity(len(projection))
    complement = add(unit, scale(-1, projection))
    if transpose(projection) != projection or matmul(projection, projection) != projection:
        raise ValueError("joint spectral effect failed")
    if matmul(transpose(projection), projection) != projection:
        raise ValueError("positive Gram factor failed")
    if transpose(complement) != complement or matmul(transpose(complement), complement) != complement:
        raise ValueError("complement positive Gram factor failed")
    return complement


def spin_pair_coefficients(upper, lower):
    upper, lower = C2.coerce(upper), C2.coerce(lower)
    return (C2(), upper, -upper, C2(), C2(), lower, -lower, C2())


def source_vector(upper=C2(ONE), lower=C2(ONE)):
    if upper.norm_sq() != ONE or lower.norm_sq() != ONE:
        raise ValueError("original source amplitudes must be unit phases")
    return tuple(coefficient / 2 for coefficient in spin_pair_coefficients(upper, lower))


def prepared_vector(herald, upper=C2(ONE), lower=C2(ONE)):
    if type(herald) is not bool:
        raise TypeError("finite herald label must be bool")
    vector = source_vector(upper, lower)
    if herald:
        vector = act(tensor(identity(4), axis(0, 1)), vector)
    if inner(vector, vector) != C2(ONE):
        raise ValueError("full source vector is not normalized")
    return vector


def born(vector, projection):
    complement = certify_projection(projection)
    projected = act(projection, vector)
    rejected = act(complement, vector)
    contraction = inner(vector, projected)
    norm = inner(projected, projected)
    residual = inner(rejected, rejected)
    if contraction != norm or contraction.imag != ZERO or residual.imag != ZERO:
        raise ValueError("Born contraction does not equal projected squared norm")
    if norm.real.sign() < 0 or residual.real.sign() < 0:
        raise ValueError("projected squared norm is negative")
    if norm + residual != C2(ONE):
        raise ValueError("full projection/complement decomposition is not normalized")
    return contraction.real


def fixed_axes():
    q = SQRT2 / 2
    return ((ZERO, ONE), (ONE, ZERO)), ((q, q), (-q, q))


def table(upper=C2(ONE), lower=C2(ONE)):
    alice, bob = fixed_axes()
    result = {}
    for herald in (False, True):
        vector = prepared_vector(herald, upper, lower)
        for a in (0, 1):
            for b in (0, 1):
                for outcome_a in (False, True):
                    for outcome_b in (False, True):
                        key = (herald, a, b, outcome_a, outcome_b)
                        result[key] = born(vector, joint_projection(alice[a], bob[b], outcome_a, outcome_b))
    return result


def aligned_table(raw):
    return {(herald, a, b, outcome_a ^ (herald and a == 1), outcome_b): value
            for (herald, a, b, outcome_a, outcome_b), value in raw.items()}


def check_distribution(probabilities):
    if len(probabilities) != 32:
        raise ValueError("incomplete herald/setting/outcome carrier")
    for herald in (False, True):
        for a in (0, 1):
            for b in (0, 1):
                if sum((probabilities[(herald, a, b, x, y)]
                        for x in (False, True) for y in (False, True)), ZERO) != ONE:
                    raise ValueError("four-outcome distribution is not normalized")
                for outcome in (False, True):
                    left = sum((probabilities[(herald, a, b, outcome, y)]
                                for y in (False, True)), ZERO)
                    right = sum((probabilities[(herald, a, b, x, outcome)]
                                 for x in (False, True)), ZERO)
                    if left != ONE / 2 or right != ONE / 2:
                        raise ValueError("nonuniform local marginal")


def correlations(probabilities, herald):
    return {(a, b): sum((outcome_sign(x) * outcome_sign(y) *
                         probabilities[(herald, a, b, x, y)]
                         for x in (False, True) for y in (False, True)), ZERO)
            for a in (0, 1) for b in (0, 1)}


def corrected_chsh(raw_correlations, herald):
    sign = outcome_sign(herald)
    return (-raw_correlations[(0, 0)] - raw_correlations[(0, 1)]
            - sign * raw_correlations[(1, 0)] + sign * raw_correlations[(1, 1)])


def records(probabilities):
    return [{"herald": herald, "setting_a": a, "setting_b": b,
             "outcome_a": x, "outcome_b": y, "probability": value.record()}
            for (herald, a, b, x, y), value in probabilities.items()]


def phase_controls():
    q = SQRT2 / 2
    phases = (C2(ONE), C2(ZERO, ONE), C2(q, q),
              C2(Q2(Fraction(-3, 5)), Q2(Fraction(4, 5))))
    baseline = table()
    controls = []
    for index, upper in enumerate(phases):
        lower = upper.conjugate()
        same = table(upper, lower) == baseline
        if not same:
            raise ValueError("finite source phase control changed Born probabilities")
        controls.append({"label": index, "upper": upper.record(), "lower": lower.record(),
                         "full_32_probabilities_equal_point_zero": same})
    return controls


def generate():
    raw = table()
    aligned = aligned_table(raw)
    check_distribution(raw)
    check_distribution(aligned)
    raw_records = records(raw)
    for record in raw_records:
        record["aligned_outcome_a"] = record["outcome_a"] ^ (
            record["herald"] and record["setting_a"] == 1)
    summaries = []
    for herald in (False, True):
        raw_e = correlations(raw, herald)
        aligned_e = correlations(aligned, herald)
        aligned_s = corrected_chsh(aligned_e, False)
        corrected_s = corrected_chsh(raw_e, herald)
        if corrected_s != aligned_s:
            raise ValueError("herald readout does not commute with CHSH")
        summaries.append({
            "herald": herald,
            "raw_correlations": [{"setting_a": a, "setting_b": b, "value": value.record()}
                                 for (a, b), value in raw_e.items()],
            "aligned_correlations": [{"setting_a": a, "setting_b": b, "value": value.record()}
                                     for (a, b), value in aligned_e.items()],
            "herald_corrected_chsh": corrected_s.record(),
            "aligned_chsh": aligned_s.record(),
        })
    return {
        "schema": "stage10-theory-blind-independent-born/v1",
        "status": "verified_full_source_spectral_contraction",
        "coefficient_field": "Q(sqrt(2))",
        "dimension": 8,
        "source_vector_point_zero": [value.record() for value in source_vector()],
        "setting_axes": {side: [{"x": x.record(), "z": z.record()} for x, z in axes]
                         for side, axes in zip(("alice", "bob"), fixed_axes())},
        "raw_records": raw_records,
        "aligned_records": records(aligned),
        "herald_summaries": summaries,
        "finite_unit_phase_controls": phase_controls(),
        "checks": {"spectral_projection_count": len(raw),
                   "positive_gram_and_complement_checked": True,
                   "born_equals_projected_norm_sq_checked": True,
                   "normalized_distribution_count": 8,
                   "local_half_marginals_checked": True,
                   "raw_aligned_reindexing_checked": True},
        "scope": {"mathematical_matrix_cross": True,
                  "source_phase_uniform_proof_supplied_by_finite_controls": False,
                  "fixed_setting_theoretical_prediction": True,
                  "empirical_parameters_used": False,
                  "public_statistical_tables_read": 0,
                  "trial_event_files_read": 0,
                  "real_instrument_empirical_verdict_executed": False,
                  "controller_advance": False},
    }
