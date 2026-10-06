"""Independent Gauss elimination checks source-law anchored hardware recovery."""
from fractions import Fraction
from itertools import product

from model import Effect, Instrument, bit, rational


def recover(law, probes, responses):
    if type(law) is not dict or set(law) != {'alice_bias', 'bob_bias', 'X', 'Z'}:
        raise ValueError("Only the complete source quotient admitted")
    for key in ('alice_bias', 'bob_bias'):
        if type(law[key]) is not list or len(law[key]) != 2 or any(not -1 <= rational(v) <= 1 for v in law[key]):
            raise ValueError("Two legal own-setting biases required")
    for key in ('X', 'Z'):
        if type(law[key]) is not list or len(law[key]) != 2 or any(type(row) is not list or len(row) != 2 for row in law[key]):
            raise ValueError("Complete two-by-two source products required")
    if len(probes) != 2 or len(responses) != 2:
        raise ValueError("Two independent local response equations required")
    matrices = {name: [[rational(v) for v in row] for row in law[name]] for name in ("X", "Z")}
    pivots = {}
    for name, values in matrices.items():
        if len(values) != 2 or any(len(row) != 2 for row in values) or values[0][0] * values[1][1] != values[0][1] * values[1][0]:
            raise ValueError("Complete rank-one products required")
        pivots[name] = next(((a, b) for a, b in product((0, 1), repeat=2) if values[a][b]), None)
        if pivots[name] is None:
            raise ValueError("Nonzero products required for each source direction")
    biases = {side: tuple(map(rational, law[side + "_bias"])) for side in ("alice", "bob")}
    row_ratios = {}
    for name, (a, b) in pivots.items():
        row_ratios[name] = [matrices[name][i][b] / matrices[name][a][b] for i in (0, 1)]
    equations = []
    for probe, response in zip(probes, responses):
        if type(probe) is not dict or set(probe) != {"setting", "x", "z"}:
            raise ValueError("Known Bloch probe coordinates required")
        setting = bit(probe["setting"])
        x, z, mean = map(rational, (probe["x"], probe["z"], response))
        if x * x + z * z > 1 or not -1 <= mean <= 1:
            raise ValueError("Physical probe and response required")
        equations.append([x * row_ratios['X'][setting], z * row_ratios['Z'][setting], mean - biases['alice'][setting]])
    # Exact row reduction supplies an independent construction of both unknown anchor coordinates.
    for column in (0, 1):
        row = next((index for index in range(column, 2) if equations[index][column]), None)
        if row is None:
            raise ValueError("Dependent probe equations cannot identify both source scales")
        equations[column], equations[row] = equations[row], equations[column]
        coefficient = equations[column][column]
        equations[column] = [v / coefficient for v in equations[column]]
        for index in range(2):
            if index == column:
                continue
            factor = equations[index][column]
            equations[index] = [v - factor * w for v, w in zip(equations[index], equations[column])]
    u, z = equations[0][2], equations[1][2]
    if not u or not z:
        raise ValueError("Recovered zero contradicts nonzero source product")
    alice = tuple(Effect(biases['alice'][a], row_ratios['X'][a] * u, row_ratios['Z'][a] * z) for a in (0, 1))
    bob = tuple(Effect(biases['bob'][b], matrices['X'][pivots['X'][0]][b] / u,
                       matrices['Z'][pivots['Z'][0]][b] / z) for b in (0, 1))
    point = Instrument(alice, bob)
    for name, coordinate in (('X', 'u'), ('Z', 'z')):
        if any(getattr(point.alice[a], coordinate) * getattr(point.bob[b], coordinate) != matrices[name][a][b]
               for a, b in product((0, 1), repeat=2)):
            raise ValueError("Recovered point changed the complete observable products")
    return point
