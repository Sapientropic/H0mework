#!/usr/bin/env python3
"""Independently check the Stage9DEF occupied-source current on fermion Fock space.

Run from any directory with Python 3.10+ (standard library only):
    python3 Verification/physics/quantization-current/check.py
    python3 Verification/physics/quantization-current/check.py --output /tmp/current.json

The matrices below translate the named Lean source definitions directly.  No
current expectation is used to construct an observable.  Assertions compare
the independently evaluated source dual, occupied Hilbert-space response and
256-dimensional Fock response.  This is numerical verification of eight
occupied modes, subordinate to the Lean source and its exact theorems.

Conventions: k = 2*spin + color; matrix entries are [output, input].  Fock basis
|mask> = (a_0^dagger)^n0 ... (a_7^dagger)^n7 |vac>, with bit k equal to nk.
Creation and annihilation have sign (-1)^(number of occupied modes below k).
The source independent-dual exchange F swaps spin 0<->2 and 1<->3; it is NOT
the source gamma^0 matrix.  Omitting F changes the source dual/observable.
"""

from __future__ import annotations

import argparse
import cmath
import json
import math
from pathlib import Path
import random
import sys
from typing import Sequence


MODES = 8
DIMENSION = 1 << MODES
TOLERANCE = 2e-12
RANDOM_SEED = 20260907

# Sparse columns represent the FULL matrix; omitted entries are exactly zero.
Matrix = list[dict[int, complex]]
Vector = list[complex]

SOURCE_PROVENANCE = {
    "parameters": (
        "SaturationMonoid/PhysicsCore/Stage9C/Material/SpinPair/Parameters.lean",
        ["spinScale", "gaugeScale", "lapse", "frequency"],
    ),
    "phases": (
        "SaturationMonoid/PhysicsCore/Stage9C/Material/SpinPair/Phase.lean",
        ["phase", "upperPhase", "lowerPhase", "upperDualPhase", "lowerDualPhase"],
    ),
    "matter_and_independent_dual": (
        "SaturationMonoid/PhysicsCore/Stage9C/Material/SpinPair/Spinor.lean",
        ["spinPairCoefficients", "sourceColorDiracDual", "spinPairMatter", "spinPairDual"],
    ),
    "actual": (
        "SaturationMonoid/PhysicsCore/Stage9C/Material/SpinPair/Actual.lean",
        ["gaugePotential", "actual_matter", "actual_conjugateMatter", "actual_gaugeConnection"],
    ),
    "preparation": (
        "SaturationMonoid/PhysicsCore/Stage9DEF/Source/Coefficients.lean",
        ["Index", "amplitude", "vector", "vector_inner_self"],
    ),
    "restriction": (
        "SaturationMonoid/PhysicsCore/Stage9DEF/Source/Restriction.lean",
        ["restrict", "restrict_actual"],
    ),
    "color_seed": (
        "SaturationMonoid/PhysicsCore/SU7MotherGaugeConnection.lean",
        ["colorCartanRaw", "colorMixingRaw", "p286LieBracket", "suLieBracket"],
    ),
    "color_generators": (
        "SaturationMonoid/PhysicsCore/Stage9C/Material/SpinPair/ColorDoublet.lean",
        ["sourceColorP286Generator", "sourceColorPauli", "sourceColorP286Generator_topLeft"],
    ),
    "occupied_invariance": (
        "SaturationMonoid/PhysicsCore/Stage9C/Material/SpinPair/ColorInvariant.lean",
        ["sourceColorDoublet_generatorAction"],
    ),
    "gamma": (
        "SaturationMonoid/PhysicsCore/DiracCliffordRepresentation.lean",
        ["diracGammaZero", "diracGammaOne", "diracGammaTwo", "diracGammaThree"],
    ),
    "full_current_compression": (
        "SaturationMonoid/PhysicsCore/Stage9C/Material/SpinPair/Current.lean",
        ["sourceColorDoubletDual_matrixMotherAction", "spinPairCurrentComplex_full"],
    ),
    "dual_response": (
        "SaturationMonoid/PhysicsCore/Stage9DEF/Compatibility/DualResponse.lean",
        ["spinFlip", "flip", "dualCoefficient_source_star", "responseMatrix", "actual_action_quantumResponse"],
    ),
    "current": (
        "SaturationMonoid/PhysicsCore/Stage9DEF/Compatibility/Current.lean",
        ["currentAction", "currentObservable", "current_source_prediction", "current_time_zero", "actualConnectionObservable"],
    ),
    "physical_readout": (
        "SaturationMonoid/PhysicsCore/Stage9DEF/Compatibility/Hermitian.lean",
        ["hermitianPart", "physicalCurrent", "physicalCurrent_readout"],
    ),
}


def matrix(rows: Sequence[Sequence[complex]]) -> Matrix:
    size = len(rows)
    return [{r: complex(rows[r][c]) for r in range(size) if rows[r][c] != 0}
            for c in range(size)]


def identity(size: int) -> Matrix:
    return [{column: 1.0 + 0j} for column in range(size)]


def scale(value: complex, operator: Matrix) -> Matrix:
    return [{row: value * entry for row, entry in column.items() if value * entry != 0}
            for column in operator]


def add(*operators: Matrix) -> Matrix:
    result: Matrix = [{} for _ in operators[0]]
    for operator in operators:
        for column, entries in enumerate(operator):
            for row, value in entries.items():
                result[column][row] = result[column].get(row, 0j) + value
    return [{row: value for row, value in entries.items() if value != 0}
            for entries in result]


def compose(left: Matrix, right: Matrix) -> Matrix:
    result: Matrix = [{} for _ in right]
    for column, entries in enumerate(right):
        for middle, right_value in entries.items():
            for row, left_value in left[middle].items():
                result[column][row] = result[column].get(row, 0j) + left_value * right_value
    return [{row: value for row, value in entries.items() if value != 0}
            for entries in result]


def adjoint(operator: Matrix) -> Matrix:
    result: Matrix = [{} for _ in operator]
    for column, entries in enumerate(operator):
        for row, value in entries.items():
            result[row][column] = value.conjugate()
    return result


def act(operator: Matrix, vector: Sequence[complex]) -> Vector:
    result = [0j] * len(operator)
    for column, entries in enumerate(operator):
        if vector[column] != 0:
            for row, value in entries.items():
                result[row] += value * vector[column]
    return result


def inner(left: Sequence[complex], right: Sequence[complex]) -> complex:
    return sum((complex(x).conjugate() * y for x, y in zip(left, right)), 0j)


def expectation(state: Sequence[complex], operator: Matrix) -> complex:
    return inner(state, act(operator, state))


def hermitian_part(operator: Matrix) -> Matrix:
    return scale(0.5, add(operator, adjoint(operator)))


def matrix_error(left: Matrix, right: Matrix) -> float:
    return max((abs(left[c].get(r, 0j) - right[c].get(r, 0j))
                for c in range(len(left)) for r in left[c].keys() | right[c].keys()), default=0.0)


def vector_error(left: Sequence[complex], right: Sequence[complex]) -> float:
    return max((abs(x - y) for x, y in zip(left, right)), default=0.0)


def tensor(left: Matrix, right: Matrix) -> Matrix:
    width = len(right)
    return [{r * width + s: a * b for r, a in left[c].items() for s, b in right[d].items()}
            for c in range(len(left)) for d in range(width)]


def block_entry(operator: Matrix, row: int, column: int) -> complex:
    return operator[column].get(row, 0j)


def source_parameters() -> dict[str, float]:
    spin = math.sqrt(2)
    gauge = 3 * spin / 5
    lapse = math.sqrt(54 / 125)
    return {"spinScale": spin, "gaugeScale": gauge, "lapse": lapse,
            "frequency": 3 * lapse / 2 * (spin - gauge)}


def spin_pair(upper: complex, lower: complex) -> Vector:
    # Spinor.spinPairCoefficients; color is the fastest varying index.
    return [0j, upper, -upper, 0j, 0j, lower, -lower, 0j]


def source_state(point: Sequence[float], parameters: dict[str, float]) -> tuple[Vector, Vector, Vector]:
    upper = cmath.exp(1j * parameters["frequency"] * point[0])
    lower = cmath.exp(-1j * parameters["frequency"] * point[0])
    amplitude = spin_pair(upper, lower)
    vector = [value / 2 for value in amplitude]
    # The source dual is linear: coefficients multiply WITHOUT conjugation.
    dual = spin_pair(parameters["spinScale"] * upper, parameters["spinScale"] * lower)
    return amplitude, vector, dual


def source_operators() -> tuple[list[Matrix], list[Matrix], Matrix]:
    gamma = [
        matrix([[0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, -1, 0, 0]]),
        matrix([[0, 0, 0, 1], [0, 0, 1, 0], [0, 1, 0, 0], [1, 0, 0, 0]]),
        matrix([[0, 0, 0, -1j], [0, 0, 1j, 0], [0, -1j, 0, 0], [1j, 0, 0, 0]]),
        matrix([[0, 0, 1, 0], [0, 0, 0, -1], [1, 0, 0, 0], [0, -1, 0, 0]]),
    ]
    cartan = matrix([[1j, 0, 0], [0, -1j, 0], [0, 0, 0]])
    mixing = matrix([[0, 1, 0], [-1, 0, 0], [0, 0, 0]])
    # ColorDoublet.sourceColorP286Generator derives T0 by a commutator.
    color3 = [scale(0.25, add(compose(cartan, mixing), scale(-1, compose(mixing, cartan)))),
              scale(0.5, mixing), scale(0.5, cartan)]
    color2 = [matrix([[block_entry(operator, r, c) for c in range(2)] for r in range(2)])
              for operator in color3]
    spin_exchange = matrix([[0, 0, 1, 0], [0, 0, 0, 1], [1, 0, 0, 0], [0, 1, 0, 0]])
    return gamma, color2, tensor(spin_exchange, identity(2))


def source_dual_current(amplitude: Vector, dual: Vector, gamma: Matrix, color: Matrix) -> complex:
    # Independent component calculation of sourceColorDoubletDual_matrixMotherAction.
    # It does not use the compressed observable or the quantum expectation.
    return sum((dual[2 * spin + state] * 1j * block_entry(gamma, spin, other_spin)
                * block_entry(color, state, other_state) * amplitude[2 * other_spin + other_state]
                for spin in range(4) for state in range(2)
                for other_spin in range(4) for other_state in range(2)), 0j)


def source_current_closed_form(amplitude: Vector, dual: Vector, color: Matrix) -> Vector:
    # SpinPair.Current.spinPairCurrentComplex_full, before any normalized prediction.
    upper, lower, p, q = amplitude[1], amplitude[5], dual[1], dual[5]
    diagonal_sum = block_entry(color, 0, 0) + block_entry(color, 1, 1)
    off_sum = block_entry(color, 0, 1) + block_entry(color, 1, 0)
    off_difference = block_entry(color, 0, 1) - block_entry(color, 1, 0)
    diagonal_difference = block_entry(color, 0, 0) - block_entry(color, 1, 1)
    cross_sum = p * lower + q * upper
    return [1j * (p * lower - q * upper) * diagonal_sum,
            -1j * cross_sum * off_sum, cross_sum * off_difference,
            -1j * cross_sum * diagonal_difference]


def jordan_wigner() -> tuple[list[Matrix], list[Matrix]]:
    annihilation: list[Matrix] = []
    creation: list[Matrix] = []
    for mode in range(MODES):
        bit = 1 << mode
        lower_mask = bit - 1
        # Compute both directions separately so the adjoint test is independent.
        annihilation.append([
            {mask ^ bit: complex((-1) ** (mask & lower_mask).bit_count())} if mask & bit else {}
            for mask in range(DIMENSION)])
        creation.append([
            {mask | bit: complex((-1) ** (mask & lower_mask).bit_count())} if not mask & bit else {}
            for mask in range(DIMENSION)])
    return annihilation, creation


def one_particle(vector: Sequence[complex], creation: list[Matrix]) -> Vector:
    vacuum = [1.0 + 0j] + [0j] * (DIMENSION - 1)
    result = [0j] * DIMENSION
    for mode, coefficient in enumerate(vector):
        created = act(creation[mode], vacuum)
        for index, value in enumerate(created):
            result[index] += coefficient * value
    return result


def lift_one_particle_image(vector: Sequence[complex]) -> Vector:
    result = [0j] * DIMENSION
    for mode, value in enumerate(vector):
        result[1 << mode] = value
    return result


def second_quantize(operator: Matrix, products: list[list[Matrix]]) -> Matrix:
    # This is an actual full-Fock matrix sum, not an inserted one-particle block.
    terms = [scale(value, products[row][column])
             for column, entries in enumerate(operator) for row, value in entries.items()]
    return add(*terms) if terms else [{} for _ in range(DIMENSION)]


class Checks:
    def __init__(self) -> None:
        self.errors: dict[str, float] = {}
        self.counts: dict[str, int] = {}

    def record(self, name: str, error: float) -> None:
        if not math.isfinite(error) or error > TOLERANCE:
            raise AssertionError(f"{name}: residual {error:.17g} exceeds {TOLERANCE:.1e}")
        self.errors[name] = max(self.errors.get(name, 0.0), error)
        self.counts[name] = self.counts.get(name, 0) + 1


def complex_json(value: complex) -> dict[str, float]:
    return {"real": float(value.real), "imaginary": float(value.imag)}


def normalized_random(size: int, rng: random.Random) -> Vector:
    vector = [complex(rng.uniform(-1, 1), rng.uniform(-1, 1)) for _ in range(size)]
    norm = math.sqrt(inner(vector, vector).real)
    return [value / norm for value in vector]


def run() -> dict[str, object]:
    checks = Checks()
    parameters = source_parameters()
    gamma, color, exchange = source_operators()
    annihilation, creation = jordan_wigner()
    zero: Matrix = [{} for _ in range(DIMENSION)]
    full_identity = identity(DIMENSION)
    products = [[compose(creation[row], annihilation[column]) for column in range(MODES)]
                for row in range(MODES)]

    for first in range(MODES):
        checks.record("creation_annihilation_adjoint", matrix_error(creation[first], adjoint(annihilation[first])))
        for second in range(MODES):
            checks.record("CAR_aa", matrix_error(add(compose(annihilation[first], annihilation[second]),
                                                      compose(annihilation[second], annihilation[first])), zero))
            checks.record("CAR_creation_creation", matrix_error(add(compose(creation[first], creation[second]),
                                                                    compose(creation[second], creation[first])), zero))
            checks.record("CAR_a_creation", matrix_error(add(compose(annihilation[first], creation[second]),
                                                            compose(creation[second], annihilation[first])),
                                                            full_identity if first == second else zero))
    number = [{mask: complex(mask.bit_count())} if mask else {} for mask in range(DIMENSION)]
    checks.record("second_quantized_identity_is_number", matrix_error(second_quantize(identity(MODES), products), number))
    checks.record("exchange_involution", matrix_error(compose(exchange, exchange), identity(MODES)))
    checks.record("exchange_self_adjoint", matrix_error(exchange, adjoint(exchange)))
    explicit_pauli = [matrix([[0, 1j / 2], [1j / 2, 0]]),
                      matrix([[0, 1 / 2], [-1 / 2, 0]]),
                      matrix([[1j / 2, 0], [0, -1j / 2]])]
    for generated, explicit in zip(color, explicit_pauli):
        checks.record("source_color_commutator_vs_explicit_Pauli", matrix_error(generated, explicit))
    for mu in range(4):
        for nu in range(4):
            target = scale((-2 if mu == 0 else 2), identity(4)) if mu == nu else [{} for _ in range(4)]
            checks.record("source_Clifford_minus_plus_plus_plus", matrix_error(
                add(compose(gamma[mu], gamma[nu]), compose(gamma[nu], gamma[mu])), target))

    compressed = [[scale(1j, tensor(gamma[mu], color[g])) for g in range(3)] for mu in range(4)]
    response = [[compose(exchange, compressed[mu][g]) for g in range(3)] for mu in range(4)]
    checks.record("reported_changed_observable_sparse_matrix", matrix_error(
        compressed[1][0], [{7 - column: -0.5 + 0j} for column in range(MODES)]))
    checks.record("reported_source_observable_sparse_matrix", matrix_error(
        response[1][0], [{column ^ 3: -0.5 + 0j} for column in range(MODES)]))
    physical = [[hermitian_part(response[mu][g]) for g in range(3)] for mu in range(4)]
    quantized = [[second_quantize(response[mu][g], products) for g in range(3)] for mu in range(4)]
    quantized_physical = [[second_quantize(physical[mu][g], products) for g in range(3)] for mu in range(4)]
    for mu in range(4):
        for generator in range(3):
            checks.record("physicalCurrent_self_adjoint", matrix_error(physical[mu][generator], adjoint(physical[mu][generator])))
            checks.record("physicalCurrent_Fock_self_adjoint", matrix_error(quantized_physical[mu][generator], adjoint(quantized_physical[mu][generator])))

    frequency = parameters["frequency"]
    points = [
        ("theta=0", (0.0, 0.0, 0.0, 0.0)),
        ("theta=pi/4", (math.pi / (4 * frequency), 1.0, -2.0, 3.0)),
        ("theta=pi/2", (math.pi / (2 * frequency), -3.0, 4.0, 5.0)),
        ("theta=pi", (math.pi / frequency, 2.0, 0.0, -1.0)),
        ("time=1.25", (1.25, -1.0, 0.5, 2.0)),
        ("time=-2.3", (-2.3, 7.0, -4.0, 1.0)),
    ]
    source_rows = []
    negative_rows = []
    for label, point in points:
        amplitude, vector, dual = source_state(point, parameters)
        fock_state = one_particle(vector, creation)
        checks.record("source_amplitude_norm_squared_is_four", abs(inner(amplitude, amplitude) - 4))
        checks.record("source_vector_normalized", abs(inner(vector, vector) - 1))
        checks.record("source_Fock_state_normalized", abs(inner(fock_state, fock_state) - 1))
        checks.record("creation_on_vacuum_embedding", vector_error(fock_state, lift_one_particle_image(vector)))
        checks.record("source_independent_dual_exchange", vector_error(
            dual, [2 * parameters["spinScale"] * value.conjugate() for value in act(exchange, vector)]))
        occupied_values = [[0j] * 3 for _ in range(4)]
        fock_values = [[0j] * 3 for _ in range(4)]
        raw_values = [[0j] * 3 for _ in range(4)]
        for mu in range(4):
            for generator in range(3):
                occupied_value = expectation(vector, response[mu][generator])
                fock_value = expectation(fock_state, quantized[mu][generator])
                physical_value = expectation(fock_state, quantized_physical[mu][generator])
                raw = source_dual_current(amplitude, dual, gamma[mu], color[generator])
                closed = source_current_closed_form(amplitude, dual, color[generator])[mu]
                expected = 0.5 if mu == generator + 1 else 0.0
                checks.record("source_dual_direct_vs_closed_form", abs(raw - closed))
                checks.record("raw_source_dual_vs_normalized_response", abs(raw - 4 * parameters["spinScale"] * occupied_value))
                checks.record("source_current_one_particle_intertwining", vector_error(
                    act(quantized[mu][generator], fock_state), lift_one_particle_image(act(response[mu][generator], vector))))
                checks.record("source_current_occupied_vs_Fock", abs(occupied_value - fock_value))
                checks.record("source_current_all_directions_generators", abs(fock_value - expected))
                checks.record("source_physicalCurrent_readout", abs(physical_value - occupied_value.real))
                occupied_values[mu][generator] = occupied_value
                fock_values[mu][generator] = fock_value
                raw_values[mu][generator] = raw

        connection_values = []
        for mu in range(4):
            # Actual.gaugePotential = [0, gaugeScale*T0, gaugeScale*T1, gaugeScale*T2].
            connection_color = scale(parameters["gaugeScale"], color[mu - 1]) if mu else matrix([[0, 0], [0, 0]])
            connection_observable = compose(exchange, scale(1j, tensor(gamma[mu], connection_color)))
            connection_fock = second_quantize(connection_observable, products)
            raw = source_dual_current(amplitude, dual, gamma[mu], connection_color)
            observed = expectation(fock_state, connection_fock)
            expected = parameters["gaugeScale"] / 2 if mu else 0.0
            checks.record("actual_connection_quantum_response", abs(raw - 4 * parameters["spinScale"] * observed))
            checks.record("actual_connection_prediction", abs(observed - expected))
            connection_values.append({"direction": mu, "normalized_Fock": complex_json(observed),
                                      "direct_source_dual": complex_json(raw)})

        wrong = compressed[1][0]
        wrong_fock = second_quantize(wrong, products)
        wrong_value = expectation(fock_state, wrong_fock)
        correct_value = fock_values[1][0]
        theta = frequency * point[0]
        # A changed observable still obeys the same valid quantization identity.
        checks.record("changed_observable_still_quantizes", abs(wrong_value - expectation(vector, wrong)))
        checks.record("changed_observable_cosine_formula", abs(wrong_value - math.cos(2 * theta) / 2))
        negative_rows.append({"label": label, "theta": theta,
                              "source_F_included": complex_json(correct_value),
                              "F_omitted_changed_observable": complex_json(wrong_value),
                              "absolute_difference": abs(correct_value - wrong_value)})
        source_rows.append({"label": label, "point": list(point), "theta": theta,
                            "source_vector": [complex_json(value) for value in vector],
                            "normalized_occupied_current": [[complex_json(value) for value in row] for row in occupied_values],
                            "normalized_Fock_current": [[complex_json(value) for value in row] for row in fock_values],
                            "direct_source_dual_current": [[complex_json(value) for value in row] for row in raw_values],
                            "actual_connection": connection_values})

    # At theta=pi/2 the exact source phases are i,-i.  All numbers in this
    # additional calculation are Gaussian dyadics, exactly representable here.
    exact_dark_vector = [value / 2 for value in spin_pair(1j, -1j)]
    exact_correct = expectation(exact_dark_vector, response[1][0])
    exact_changed = expectation(exact_dark_vector, compressed[1][0])
    if exact_correct != 0.5 or exact_changed != -0.5:
        raise AssertionError("The source-derived changed-observable witness failed")
    checks.record("dark_source_phases_match_exact_witness", vector_error(
        source_state(points[2][1], parameters)[1], exact_dark_vector))
    checks.record("dark_changed_observable_discrepancy_is_one", abs(negative_rows[2]["absolute_difference"] - 1))

    rng = random.Random(RANDOM_SEED)
    random_rows = []
    for trial in range(4):
        arbitrary = matrix([[complex(rng.uniform(-1, 1), rng.uniform(-1, 1))
                             for _ in range(MODES)] for _ in range(MODES)])
        vector = normalized_random(MODES, rng)
        state = one_particle(vector, creation)
        quantized_arbitrary = second_quantize(arbitrary, products)
        quantized_h = second_quantize(hermitian_part(arbitrary), products)
        checks.record("arbitrary_vector_normalized", abs(inner(vector, vector) - 1))
        checks.record("arbitrary_Fock_state_normalized", abs(inner(state, state) - 1))
        checks.record("arbitrary_matrix_one_particle_intertwining", vector_error(
            act(quantized_arbitrary, state), lift_one_particle_image(act(arbitrary, vector))))
        checks.record("arbitrary_matrix_complex_expectation", abs(expectation(state, quantized_arbitrary) - expectation(vector, arbitrary)))
        checks.record("arbitrary_matrix_dGamma_adjoint", matrix_error(
            second_quantize(adjoint(arbitrary), products), adjoint(quantized_arbitrary)))
        checks.record("arbitrary_matrix_dGamma_hermitian_part", matrix_error(
            quantized_h, hermitian_part(quantized_arbitrary)))
        one_particle_block = matrix([[block_entry(quantized_arbitrary, 1 << row, 1 << column)
                                     for column in range(MODES)] for row in range(MODES)])
        checks.record("arbitrary_matrix_complete_one_particle_block", matrix_error(arbitrary, one_particle_block))
        checks.record("arbitrary_matrix_preserves_all_particle_sectors", max(
            (abs(value) for column, entries in enumerate(quantized_arbitrary)
             for row, value in entries.items() if row.bit_count() != column.bit_count()), default=0.0))
        many_particle_state = normalized_random(DIMENSION, rng)
        checks.record("arbitrary_full_Fock_state_normalized", abs(inner(many_particle_state, many_particle_state) - 1))
        checks.record("arbitrary_full_Fock_hermitian_readout", abs(
            expectation(many_particle_state, quantized_h) - expectation(many_particle_state, quantized_arbitrary).real))
        random_rows.append({"trial": trial, "occupied_expectation": complex_json(expectation(vector, arbitrary)),
                            "Fock_expectation": complex_json(expectation(state, quantized_arbitrary))})

    return {
        "status": "PASS", "verification_kind": "independent_numerical_source_current_consumer",
        "python": sys.version.split()[0], "dependencies": "Python standard library only",
        "modes": MODES, "Fock_dimension": DIMENSION, "particle_sector_dimensions": [math.comb(MODES, n) for n in range(MODES + 1)],
        "tolerance": TOLERANCE, "random_seed": RANDOM_SEED, "source_parameters": parameters,
        "conventions": {"mode_order": "mode = 2*spin + color, spin=0..3, color=0..1",
                        "occupation_basis": "mask bit k = nk; |mask> = (a0^dagger)^n0 ... (a7^dagger)^n7 |vac>",
                        "operator_entries": "[output row, input column]",
                        "Jordan_Wigner_sign": "(-1)^popcount(mask & ((1<<mode)-1))",
                        "independent_dual": "linear, no conjugation on its coefficients",
                        "source_exchange_F": "spin 0<->2, 1<->3; distinct from source gamma^0",
                        "current_action_compression": "C_mu,g = i gamma_mu tensor T_g",
                        "source_current_observable": "R_mu,g = F C_mu,g",
                        "physicalCurrent": "(R + R^dagger)/2",
                        "normalization": "amplitude = 2 psi; raw dual current = 4 spinScale <psi,R psi>",
                        "second_quantization": "dGamma(A) = sum_(i,j) A_ij a_i^dagger a_j",
                        "source_tables": "rows direction 0,1,2,3; columns generator 0,1,2"},
        "source_provenance": {name: {"path_relative_to_Lean": path, "declarations": names}
                              for name, (path, names) in SOURCE_PROVENANCE.items()},
        "maximum_absolute_residual": max(checks.errors.values()),
        "checks": {name: {"evaluations": checks.counts[name], "maximum_absolute_residual": error}
                   for name, error in sorted(checks.errors.items())},
        "source_points": source_rows,
        "changed_observable_negative_control": {
            "meaning": "Omitting the source independent-dual exchange F changes the observable; both observables obey the same quantization identity.",
            "direction": 1, "generator": 0,
            "source_derived_sparse_matrices": {"C": "C[row,7-row]=-1/2; other entries zero",
                                               "R": "R[row,row xor 3]=-1/2; other entries zero"},
            "changed_expectation_formula": "cos(2 theta)/2",
            "exact_dark_phase_witness": {"upper": "i", "lower": "-i", "source_expectation": complex_json(exact_correct),
                                         "changed_observable_expectation": complex_json(exact_changed), "absolute_difference": abs(exact_correct - exact_changed)},
            "phase_table": negative_rows,
        },
        "arbitrary_complex_matrix_trials": random_rows,
        "scope": "Eight occupied source modes and their complete finite fermionic Fock space; current source compression, preparation normalization, actual connection response, CAR and one-particle second quantization.",
        "limitations": ["Floating-point numerical verification is distinct from the accompanying Lean proofs.",
                        "The occupied source compression is the one proved by the cited source declarations; this script does not reconstruct the entire SU7 exterior carrier.",
                        "No continuum field quantization, interacting spacetime dynamics or full quantum-gravity claim is tested."],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--output", type=Path, help="Optional JSON results path; stdout always receives the same JSON")
    args = parser.parse_args()
    result = run()
    rendered = json.dumps(result, indent=2, ensure_ascii=False, allow_nan=False) + "\n"
    if args.output is not None:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(rendered, encoding="utf-8")
    sys.stdout.write(rendered)


if __name__ == "__main__":
    main()
