"""Conditional Rb87 preparation, collected emission and photonic herald source.

The public programme prepares ground F=1,m=0 and excites D2 F'=0,m'=0.
SI I.B fixes the four detector patterns: opposite ports/orthogonal polarizations
give Psi-, and same port/orthogonal polarizations give Psi+ (arXiv:1611.04604v2,
https://arxiv.org/pdf/1611.04604v2).  Their amplitudes below come from a linear
beam splitter, rather than an input Bell state or target density matrix.

The branch conditions on successful preparation/excitation and one photon per
atom in a common coherent wavepacket.  Raw passive optical matrices act on all
three emitted spherical components; pi collection retains ground m=0.  Detector
patterns are distinct classical records and their density contributions add.
Collection losses and beam-splitter imbalance remain raw optical variables.
"""
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations, permutations
from math import isqrt

from atomic_dipole import (ComplexRadical, INDEX, Q_COMPONENTS, Radical, State,
                           complex_exact, dipole_coefficient, sqrt_rational)


PREPARATION = State("ground", 1, 0)
EXCITATION = State("D2", 0, 0)
ATOM_BASIS = tuple(INDEX[State("ground", 1, m)] for m in (-1, 0, 1))
PAIR_BASIS = tuple((a, b) for a in ATOM_BASIS for b in ATOM_BASIS)
PAIR_INDEX = {pair: index for index, pair in enumerate(PAIR_BASIS)}
POLARIZATIONS = ("perp", "parallel")
HERALD_PATTERNS = (("Psi-", ((1, "perp"), (2, "parallel"))),
                   ("Psi-", ((1, "parallel"), (2, "perp"))),
                   ("Psi+", ((1, "perp"), (1, "parallel"))),
                   ("Psi+", ((2, "perp"), (2, "parallel"))))


def radical_sign(value):
    """Resolve a canonical nonzero radical with exact outward dyadic bounds."""
    value = Radical(value)
    if not value:
        return 0
    bits = 32
    while True:
        scale = 1 << bits
        lower = upper = Fraction(0)
        for root, coefficient in value.terms:
            integer = isqrt(root * scale * scale)
            lo = Fraction(integer, scale)
            hi = lo if integer * integer == root * scale * scale else Fraction(integer + 1, scale)
            lower += coefficient * (lo if coefficient > 0 else hi)
            upper += coefficient * (hi if coefficient > 0 else lo)
        if lower > 0:
            return 1
        if upper < 0:
            return -1
        bits *= 2


def radical_inverse(value):
    """Exact inversion in the finite multiquadratic field of a nonzero sum."""
    value = Radical(value)
    if not value:
        raise ZeroDivisionError("zero herald probability")
    numerator, denominator = Radical(1), value
    while any(root != 1 for root, _ in denominator.terms):
        number = next(root for root, _ in denominator.terms if root != 1)
        prime = 2
        while number % prime:
            prime = 3 if prime == 2 else prime + 2
        conjugate = Radical({root: (-coefficient if root % prime == 0 else coefficient)
                             for root, coefficient in denominator.terms})
        numerator *= conjugate
        denominator *= conjugate
    return numerator / denominator.as_rational()


def _matrix(matrix, rows, columns):
    if (type(matrix) not in (tuple, list) or len(matrix) != rows or
            any(type(row) not in (tuple, list) or len(row) != columns for row in matrix)):
        raise ValueError(f"{rows} by {columns} raw optical matrix required")
    return tuple(tuple(complex_exact(value) for value in row) for row in matrix)


def _norm_squared(value):
    value = complex_exact(value)
    return value.real * value.real + value.imag * value.imag


def _determinant(matrix):
    result = ComplexRadical()
    for order in permutations(range(len(matrix))):
        sign = (-1) ** sum(order[i] > order[j] for i in range(len(order)) for j in range(i + 1, len(order)))
        term = ComplexRadical(sign)
        for i, j in enumerate(order):
            term *= matrix[i][j]
        result += term
    return result


def collection_matrix(matrix):
    """Check passivity M* M <= I through every Hermitian principal minor."""
    matrix = _matrix(matrix, 2, 3)
    remainder = tuple(tuple(ComplexRadical(int(i == j)) -
                            sum((matrix[p][i].conjugate() * matrix[p][j] for p in range(2)),
                                ComplexRadical()) for j in range(3)) for i in range(3))
    for size in (1, 2, 3):
        for indices in combinations(range(3), size):
            minor = _determinant(tuple(tuple(remainder[i][j] for j in indices) for i in indices))
            if minor.imag or radical_sign(minor.real) < 0:
                raise ValueError("nonphysical optical collection: M* M exceeds identity")
    return matrix


def ideal_collection():
    """Pi-suppressed circular-to-linear convention compatible with the source x basis.

    Rows are perpendicular/parallel; columns are photon q=-1,0,+1.  Together
    with generated emission this gives ux*parallel + dx*perp, using the public
    ux=(uz+dz)/sqrt(2), dx=i(uz-dz)/sqrt(2) phase convention.
    """
    half = sqrt_rational(Fraction(1, 2))
    return ((ComplexRadical(0, half), ComplexRadical(), ComplexRadical(0, -half)),
            (ComplexRadical(half), ComplexRadical(), ComplexRadical(half)))


def balanced_beam_splitter():
    """a_p -> (c_p+i d_p)/sqrt(2), b_p -> (i c_p+d_p)/sqrt(2)."""
    half = sqrt_rational(Fraction(1, 2))
    return ((ComplexRadical(half), ComplexRadical(0, half)),
            (ComplexRadical(0, half), ComplexRadical(half)))


def beam_splitter_matrix(matrix):
    matrix = _matrix(matrix, 2, 2)
    for i in range(2):
        for j in range(2):
            inner = sum((matrix[p][i].conjugate() * matrix[p][j] for p in range(2)), ComplexRadical())
            if inner != ComplexRadical(int(i == j)):
                raise ValueError("lossless unitary two-port beam splitter required")
    return matrix


def emission_amplitudes():
    """Keep the photon carrier while normalizing the generated D2F0 dipoles."""
    amplitudes = {}
    norm = Fraction(0)
    for f in (1, 2):
        for m in range(-f, f + 1):
            for q in Q_COMPONENTS:
                value = dipole_coefficient("D2", f, m, 0, 0, q)
                if value:
                    amplitudes[INDEX[State("ground", f, m)], q] = value
                    norm += (value * value).as_rational()
    factor = sqrt_rational(1 / norm)
    return {key: ComplexRadical(value * factor) for key, value in amplitudes.items()}


def collected_amplitudes(matrix):
    matrix = collection_matrix(matrix)
    result = {}
    for (atom, q), value in emission_amplitudes().items():
        for p, polarization in enumerate(POLARIZATIONS):
            key = (atom, polarization)
            result[key] = result.get(key, ComplexRadical()) + matrix[p][Q_COMPONENTS.index(q)] * value
    return {key: value for key, value in result.items() if value}


@dataclass(frozen=True)
class DetectionBra:
    herald: str
    detectors: tuple
    coefficients: dict


def bsm_bras(beam_splitter=None):
    splitter = beam_splitter_matrix(balanced_beam_splitter() if beam_splitter is None else beam_splitter)
    result = []
    for herald, detectors in HERALD_PATTERNS:
        (first_port, first_pol), (second_port, second_pol) = detectors
        coefficients = {}
        for a in POLARIZATIONS:
            for b in POLARIZATIONS:
                value = ComplexRadical()
                if a == first_pol and b == second_pol:
                    value += splitter[first_port - 1][0] * splitter[second_port - 1][1]
                if a == second_pol and b == first_pol:
                    value += splitter[second_port - 1][0] * splitter[first_port - 1][1]
                if value:
                    coefficients[a, b] = value
        result.append(DetectionBra(herald, detectors, coefficients))
    return tuple(result)


def _outer(vector):
    return {(i, j): a * b.conjugate() for i, a in vector.items() for j, b in vector.items() if a and b}


def density_trace(density):
    result = sum((value for (i, j), value in density.items() if i == j), ComplexRadical())
    if result.imag:
        raise ValueError("non-real density trace")
    return result.real


@dataclass(frozen=True)
class HeraldBranch:
    detectors: tuple
    amplitudes: dict
    probability: Radical


@dataclass(frozen=True)
class HeraldDensity:
    herald: str
    branches: tuple
    subnormalized: dict
    probability: Radical
    conditional: dict | None


def prepare_heralds(collection_a, collection_b, *, beam_splitter=None):
    """Generate rho(theta) and its rate; a zero-rate conditional is undefined.

    Sparse density indices refer to PAIR_BASIS, whose entries retain the
    original 33-state addresses on each side.  No qubit projection is applied.
    """
    first, second = collected_amplitudes(collection_a), collected_amplitudes(collection_b)
    branches = {"Psi-": [], "Psi+": []}
    for bra in bsm_bras(beam_splitter):
        vector = {}
        for (a, pa), x in first.items():
            for (b, pb), y in second.items():
                value = x * y * bra.coefficients.get((pa, pb), ComplexRadical())
                if value:
                    index = PAIR_INDEX[a, b]
                    vector[index] = vector.get(index, ComplexRadical()) + value
        vector = {index: value for index, value in vector.items() if value}
        rate = sum((_norm_squared(value) for value in vector.values()), Radical())
        branches[bra.herald].append(HeraldBranch(bra.detectors, vector, rate))
    result = {}
    for herald, patterns in branches.items():
        density = {}
        for pattern in patterns:
            for key, value in _outer(pattern.amplitudes).items():
                density[key] = density.get(key, ComplexRadical()) + value
        density = {key: value for key, value in density.items() if value}
        rate = density_trace(density)
        inverse = radical_inverse(rate) if rate else None
        conditional = {key: value * inverse for key, value in density.items()} if rate else None
        result[herald] = HeraldDensity(herald, tuple(patterns), density, rate, conditional)
    return result


def model_metadata():
    return {"schema": "rb87-atom-photon-herald-source/v1",
            "public_programme_source": "https://arxiv.org/pdf/1611.04604v2#page=10; SI I.B",
            "preparation": "ground F=1,m=0 followed by D2 F'=0,m'=0 excitation",
            "preparation_scope": "conditional successful preparation/excitation",
            "dipoles": "atomic_dipole standard-3j Racah factory; photon q retained",
            "atom_basis": tuple(("ground", 1, m) for m in (-1, 0, 1)),
            "atom_indices": ATOM_BASIS, "pair_basis": PAIR_BASIS,
            "photon_basis": Q_COMPONENTS, "polarizations": POLARIZATIONS,
            "collection": "raw passive 2x3 transfer per side",
            "beam_splitter": "raw unitary 2x2; balanced convention is explicit default",
            "optical_regime": "one photon per atom; coherent common wavepacket; ideal photon counters",
            "herald_patterns": HERALD_PATTERNS,
            "herald_token_mapping_asserted": False,
            "actual_preparation_identified": False, "actual": False,
            "controller_advance": False, "propagation_performed": False}
