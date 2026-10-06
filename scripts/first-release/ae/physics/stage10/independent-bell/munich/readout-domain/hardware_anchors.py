"""Recover signed local effects from a source law and two independent probe responses.

The law fixes biases and X/Z products.  Probe vectors and measured signed means
are separate inputs: these functions neither manufacture experimental anchors
nor choose a representative of an uncalibrated fibre.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import product

from model import Effect, Instrument, bit, rational


@dataclass(frozen=True)
class Probe:
    setting: int
    x: Fraction
    z: Fraction

    def __post_init__(self):
        bit(self.setting)
        for name in ("x", "z"):
            object.__setattr__(self, name, rational(getattr(self, name)))
        if self.x ** 2 + self.z ** 2 > 1:
            raise ValueError("Known normalized XZ qubit probe required")


def response(effect, probe):
    return effect.mu + effect.u * probe.x + effect.z * probe.z


def quotient(point):
    return {"alice_bias": [str(e.mu) for e in point.alice], "bob_bias": [str(e.mu) for e in point.bob],
            "X": [[str(a.u * b.u) for b in point.bob] for a in point.alice],
            "Z": [[str(a.z * b.z) for b in point.bob] for a in point.alice]}


def decode_quotient(record):
    if type(record) is not dict or set(record) != {"alice_bias", "bob_bias", "X", "Z"}:
        raise ValueError("Only the original observable quotient admitted")
    biases = []
    for side in ("alice", "bob"):
        row = record[side + "_bias"]
        if type(row) is not list or len(row) != 2:
            raise ValueError("Two own-setting source biases required")
        values = tuple(map(rational, row))
        if any(not -1 <= v <= 1 for v in values):
            raise ValueError("Legal source biases required")
        biases.append(values)
    matrices = []
    for name in ("X", "Z"):
        rows = record[name]
        if type(rows) is not list or len(rows) != 2 or any(type(r) is not list or len(r) != 2 for r in rows):
            raise ValueError("Two complete source product matrices required")
        matrix = tuple(tuple(map(rational, row)) for row in rows)
        if matrix[0][0] * matrix[1][1] != matrix[0][1] * matrix[1][0]:
            raise ValueError("Source product matrix is not rank one")
        matrices.append(matrix)
    return (*biases, *matrices)


class AnchorChart:
    def __init__(self, law, probes):
        self.alice_bias, self.bob_bias, self.X, self.Z = decode_quotient(law)
        self.law = {"alice_bias": list(map(str, self.alice_bias)), "bob_bias": list(map(str, self.bob_bias)),
                    "X": [list(map(str, row)) for row in self.X], "Z": [list(map(str, row)) for row in self.Z]}
        if type(probes) not in (list, tuple) or len(probes) != 2 or any(type(p) is not Probe for p in probes):
            raise ValueError("Two known local probe inputs required")
        self.probes = tuple(probes)
        self.pivots = []
        ratios = []
        for matrix in (self.X, self.Z):
            pivot = next(((a, b) for a, b in product((0, 1), repeat=2) if matrix[a][b] != 0), None)
            if pivot is None:
                raise ValueError("Each source product needs a nonzero anchor")
            a, b = pivot
            self.pivots.append(pivot)
            ratios.append(tuple(matrix[i][b] / matrix[a][b] for i in (0, 1)))
        self.relative_x, self.relative_z = ratios
        self.coefficients = tuple((p.x * self.relative_x[p.setting], p.z * self.relative_z[p.setting]) for p in probes)
        (a, b), (c, d) = self.coefficients
        self.determinant = a * d - b * c
        if self.determinant == 0:
            raise ValueError("Probe responses do not independently fix both source scales")
        self.inverse = ((d / self.determinant, -b / self.determinant),
                        (-c / self.determinant, a / self.determinant))

    def anchor_coordinates(self, means):
        if type(means) not in (list, tuple) or len(means) != 2:
            raise ValueError("Two independent signed probe responses required")
        values = tuple(map(rational, means))
        if any(not -1 <= v <= 1 for v in values):
            raise ValueError("Signed probe means must be physical")
        centered = tuple(v - self.alice_bias[p.setting] for p, v in zip(self.probes, values))
        return tuple(sum(coefficient * y for coefficient, y in zip(row, centered)) for row in self.inverse)

    def recover(self, means):
        u, z = self.anchor_coordinates(means)
        if not u or not z:
            raise ValueError("Recovered anchor contradicts nonzero source product")
        alice = tuple(Effect(self.alice_bias[a], self.relative_x[a] * u, self.relative_z[a] * z) for a in (0, 1))
        ax, _ = self.pivots[0]
        az, _ = self.pivots[1]
        bob = tuple(Effect(self.bob_bias[b], self.X[ax][b] / u, self.Z[az][b] / z) for b in (0, 1))
        result = Instrument(alice, bob)
        if quotient(result) != self.law or any(response(result.alice[p.setting], p) != rational(v)
                                               for p, v in zip(self.probes, means)):
            raise ValueError("Recovered instrument does not realize the source law and probes")
        return result

    def sensitivity(self):
        return tuple(sum(map(abs, row)) for row in self.inverse)

    def interval_coordinates(self, intervals):
        if type(intervals) not in (list, tuple) or len(intervals) != 2:
            raise ValueError("Two signed-response uncertainty intervals required")
        centered = []
        for row, probe in zip(intervals, self.probes):
            if type(row) not in (list, tuple) or len(row) != 2:
                raise ValueError("Two ordered interval endpoints required")
            low, high = map(rational, row)
            if not -1 <= low <= high <= 1:
                raise ValueError("Ordered physical response interval required")
            centered.append((low - self.alice_bias[probe.setting], high - self.alice_bias[probe.setting]))
        bounds = []
        for row in self.inverse:
            terms = [(min(c * low, c * high), max(c * low, c * high)) for c, (low, high) in zip(row, centered)]
            bounds.append((sum(low for low, _ in terms), sum(high for _, high in terms)))
        return tuple(bounds)


def self_calibrate_atom_response(biases, atom_effects):
    """Known atomic ionization responses plus two joint-law biases fix the detector factor.

    atom_effects carry Tr(J), Tr(JX), Tr(JZ) from an independent forward model.
    The same detector background and efficiency act on both local settings.
    """
    if type(atom_effects) not in (list, tuple) or len(atom_effects) != 2:
        raise ValueError("Two independently generated atomic effects required")
    if any(type(row) is not dict or set(row) != {"trace", "x", "z"} for row in atom_effects):
        raise ValueError("Atomic effect moments, not assignment targets, required")
    atoms = [tuple(rational(row[key]) for key in ("trace", "x", "z")) for row in atom_effects]
    for trace, x, z in atoms:
        if not 0 <= trace <= 2 or x * x + z * z > min(trace, 2 - trace) ** 2:
            raise ValueError("Lawful atomic ionization effect required")
    if type(biases) not in (list, tuple) or len(biases) != 2:
        raise ValueError("Two source-identified local biases required")
    mu0, mu1 = map(rational, biases)
    if not -1 <= mu0 <= 1 or not -1 <= mu1 <= 1:
        raise ValueError("Legal source-identified local biases required")
    t0, t1 = atoms[0][0], atoms[1][0]
    if t0 == t1:
        raise ValueError("Equal atomic traces leave the absolute detector factor unidentified")
    detection = (mu1 - mu0) / (t0 - t1)
    background = (1 - mu0 - detection * t0) / 2
    if not 0 <= background < 1 or not 0 <= detection <= 1 - background:
        raise ValueError("Recovered detector violates the physical model")
    efficiency = detection / (1 - background)
    effects = tuple(Effect(mu, -detection * x, -detection * z) for mu, (_, x, z) in zip((mu0, mu1), atoms))
    return {"background": background, "fragment_efficiency": efficiency,
            "common_detected_ionization_factor": detection, "effects": effects}
