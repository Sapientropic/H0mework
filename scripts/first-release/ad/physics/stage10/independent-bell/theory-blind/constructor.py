"""Pure exact readout of the source XZ law; no empirical inputs or I/O."""
from dataclasses import dataclass
from fractions import Fraction


@dataclass(frozen=True)
class Q2:
    r: Fraction = Fraction(0)
    s: Fraction = Fraction(0)

    def __add__(self, other):
        other = lift(other)
        return Q2(self.r + other.r, self.s + other.s)

    def __radd__(self, other):
        return self + other

    def __neg__(self):
        return Q2(-self.r, -self.s)

    def __sub__(self, other):
        return self + -lift(other)

    def __mul__(self, other):
        other = lift(other)
        return Q2(self.r * other.r + 2 * self.s * other.s,
                  self.r * other.s + self.s * other.r)

    def __rmul__(self, other):
        return self * other

    def __truediv__(self, other):
        other = lift(other)
        norm = other.r * other.r - 2 * other.s * other.s
        if norm == 0:
            raise ZeroDivisionError('zero quadratic-field denominator')
        return self * Q2(other.r / norm, -other.s / norm)

    def sign(self):
        if self.r == 0:
            return rational_sign(self.s)
        if self.s == 0 or rational_sign(self.r) == rational_sign(self.s):
            return rational_sign(self.r)
        return rational_sign(self.r) * rational_sign(self.r * self.r - 2 * self.s * self.s)

    def encode(self):
        return {'r': str(self.r), 's': str(self.s)}


def lift(value):
    if isinstance(value, Q2):
        return value
    if isinstance(value, (int, Fraction)):
        return Q2(Fraction(value))
    raise TypeError('exact rational or quadratic-field value required')


def rational_sign(value):
    return (value > 0) - (value < 0)


def sign(bit):
    return -1 if bit else 1


def theoretical_axes():
    zero, one = Q2(), Q2(Fraction(1))
    diagonal = Q2(Fraction(0), Fraction(1, 2))
    return ((zero, one), (one, zero)), ((diagonal, diagonal), (-diagonal, diagonal))


def source_probability(herald, axis_a, axis_b, outcome_a, outcome_b):
    bx = -axis_b[0] if herald else axis_b[0]
    dot = axis_a[0] * bx + axis_a[1] * axis_b[1]
    return (Q2(Fraction(1)) - sign(outcome_a) * sign(outcome_b) * dot) / 4


def build_prediction():
    alice, bob = theoretical_axes()
    records = []
    aligned = []
    correlations = []
    scores = []
    for herald in (False, True):
        expectations = []
        for setting_a in (0, 1):
            for setting_b in (0, 1):
                expectation = Q2()
                for outcome_a in (False, True):
                    for outcome_b in (False, True):
                        probability = source_probability(
                            herald, alice[setting_a], bob[setting_b], outcome_a, outcome_b)
                        corrected_a = outcome_a ^ (herald and setting_a == 1)
                        records.append({
                            'herald': herald, 'setting_a': setting_a, 'setting_b': setting_b,
                            'outcome_a': outcome_a, 'outcome_b': outcome_b,
                            'aligned_outcome_a': corrected_a, 'probability': probability.encode()})
                        expectation += sign(outcome_a) * sign(outcome_b) * probability
                        source_a = outcome_a ^ (herald and setting_a == 1)
                        corrected_probability = source_probability(
                            herald, alice[setting_a], bob[setting_b], source_a, outcome_b)
                        aligned.append({
                            'herald': herald, 'setting_a': setting_a, 'setting_b': setting_b,
                            'outcome_a': outcome_a, 'outcome_b': outcome_b,
                            'source_outcome_a': source_a, 'probability': corrected_probability.encode()})
                expectations.append(expectation)
                correlations.append({'herald': herald, 'setting_a': setting_a,
                                     'setting_b': setting_b, 'value': expectation.encode()})
        score = (-expectations[0] - expectations[1] - sign(herald) * expectations[2]
                 + sign(herald) * expectations[3])
        scores.append({'herald': herald, 'value': score.encode()})
    return {
        'schema': 'stage10-theory-blind-prediction/v1',
        'axes': {'alice': [[v.encode() for v in axis] for axis in alice],
                 'bob': [[v.encode() for v in axis] for axis in bob]},
        'records': records, 'aligned_records': aligned,
        'correlations': correlations, 'chsh': scores}
