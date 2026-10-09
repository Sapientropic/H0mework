"""Exact Rb87 D1/D2 hyperfine dipoles from angular momenta.

The basis is |(J I) F m> with Condon--Shortley phases.  A dipole entry is
<J' I F' m'|d_q|J I F m>/<J'||d||J>, with the standard 3j-normalised
electronic reduced matrix element.  This differs from a stretched-transition
Rabi amplitude.  R and C below use this electronic reduced convention.

The recoupling follows the Wigner--Eckart/6j reduction, with the explicit
normalisation convention above (Steck, Rubidium 87 D Line Data, Sec. 3.3,
https://steck.us/alkalidata).  Racah sums, not a target Hamiltonian table,
generate every coefficient.  No floating-point or SymPy dependency is used.

The 33-state carrier retains all stated D1/D2 hyperfine sublevels and one
effective ion sink.  It does not identify an actual apparatus configuration,
select a waveform, or model the ion continuum by a bound-state dipole.
"""
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from math import factorial, gcd


def rational(value):
    if type(value) not in (int, str, Fraction):
        raise TypeError("exact rational required")
    return Fraction(value)


def _square_part(number):
    if type(number) is not int or number <= 0:
        raise ValueError("positive integer radicand required")
    square, free, factor = 1, 1, 2
    while factor * factor <= number:
        exponent = 0
        while number % factor == 0:
            exponent += 1
            number //= factor
        square *= factor ** (exponent // 2)
        if exponent % 2:
            free *= factor
        factor = 3 if factor == 2 else factor + 2
    return square, free * number


@dataclass(frozen=True, init=False)
class Radical:
    """Canonical finite sum of rational multiples of square-free roots."""
    terms: tuple

    def __init__(self, value=0):
        if isinstance(value, Radical):
            object.__setattr__(self, "terms", value.terms)
            return
        source = value if isinstance(value, dict) else {1: rational(value)}
        reduced = {}
        for root, coefficient in source.items():
            square, free = _square_part(root)
            reduced[free] = reduced.get(free, Fraction(0)) + rational(coefficient) * square
        object.__setattr__(self, "terms", tuple(sorted((root, coefficient) for root, coefficient
                                                     in reduced.items() if coefficient)))

    def __bool__(self):
        return bool(self.terms)

    def __add__(self, other):
        other = Radical(other)
        values = dict(self.terms)
        for root, coefficient in other.terms:
            values[root] = values.get(root, Fraction(0)) + coefficient
        return Radical(values)

    __radd__ = __add__

    def __neg__(self):
        return Radical({root: -coefficient for root, coefficient in self.terms})

    def __sub__(self, other):
        return self + -Radical(other)

    def __rsub__(self, other):
        return Radical(other) - self

    def __mul__(self, other):
        other = Radical(other)
        values = {}
        for a, x in self.terms:
            for b, y in other.terms:
                common = gcd(a, b)
                root = (a // common) * (b // common)
                values[root] = values.get(root, Fraction(0)) + common * x * y
        return Radical(values)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = Radical(other)
        if len(other.terms) != 1:
            raise ValueError("nonzero monomial divisor required")
        root, coefficient = other.terms[0]
        return self * Radical({root: 1 / (coefficient * root)})

    def as_rational(self):
        if not self.terms:
            return Fraction(0)
        if len(self.terms) == 1 and self.terms[0][0] == 1:
            return self.terms[0][1]
        raise ValueError("value is not rational")

    def serialize(self):
        return {str(root): str(coefficient) for root, coefficient in self.terms}


def sqrt_rational(value):
    value = rational(value)
    if value < 0:
        raise ValueError("nonnegative rational radicand required")
    if not value:
        return Radical()
    return Radical({value.numerator * value.denominator: Fraction(1, value.denominator)})


@dataclass(frozen=True)
class ComplexRadical:
    real: Radical = Radical()
    imag: Radical = Radical()

    def __post_init__(self):
        object.__setattr__(self, "real", Radical(self.real))
        object.__setattr__(self, "imag", Radical(self.imag))

    def __bool__(self):
        return bool(self.real) or bool(self.imag)

    def __add__(self, other):
        other = complex_exact(other)
        return ComplexRadical(self.real + other.real, self.imag + other.imag)

    __radd__ = __add__

    def __neg__(self):
        return ComplexRadical(-self.real, -self.imag)

    def __sub__(self, other):
        return self + -complex_exact(other)

    def __rsub__(self, other):
        return complex_exact(other) - self

    def __mul__(self, other):
        other = complex_exact(other)
        return ComplexRadical(self.real * other.real - self.imag * other.imag,
                              self.real * other.imag + self.imag * other.real)

    __rmul__ = __mul__

    def conjugate(self):
        return ComplexRadical(self.real, -self.imag)

    def serialize(self):
        return {"real": self.real.serialize(), "imag": self.imag.serialize()}


def complex_exact(value):
    if isinstance(value, ComplexRadical):
        return value
    if type(value) is tuple and len(value) == 2:
        return ComplexRadical(*value)
    return ComplexRadical(Radical(value))


def _integer(value):
    value = rational(value)
    if value.denominator != 1:
        raise ValueError("integer factorial or phase required")
    return value.numerator


def _phase(value):
    return -1 if _integer(value) % 2 else 1


def _angular(value):
    value = rational(value)
    if value < 0 or (2 * value).denominator != 1:
        raise ValueError("nonnegative integer or half-integer angular momentum required")
    return value


def _triangle(a, b, c):
    values = (a + b - c, a - b + c, -a + b + c, a + b + c)
    if any(value < 0 or value.denominator != 1 for value in values):
        return Fraction(0)
    x, y, z, total = map(_integer, values)
    return Fraction(factorial(x) * factorial(y) * factorial(z), factorial(total + 1))


def wigner_3j_witness(j1, j2, j3, m1, m2, m3):
    j1, j2, j3 = map(_angular, (j1, j2, j3))
    m1, m2, m3 = map(rational, (m1, m2, m3))
    args = (j1, j2, j3, m1, m2, m3)
    triangle = _triangle(j1, j2, j3)
    valid = (bool(triangle) and m1 + m2 + m3 == 0 and
             all(abs(m) <= j and (j + m).denominator == 1 for j, m in zip(args[:3], args[3:])))
    if not valid:
        return {"arguments": tuple(map(str, args)), "allowed": False, "radicand": "0",
                "phase": 1, "terms": (), "sum": "0", "value": Radical().serialize()}
    root = triangle
    for j, m in zip(args[:3], args[3:]):
        root *= factorial(_integer(j + m)) * factorial(_integer(j - m))
    lower = max(0, _integer(j2 - j3 - m1), _integer(j1 - j3 + m2))
    upper = min(_integer(j1 + j2 - j3), _integer(j1 - m1), _integer(j2 + m2))
    terms = []
    for z in range(lower, upper + 1):
        factors = (z, _integer(j1 + j2 - j3) - z, _integer(j1 - m1) - z,
                   _integer(j2 + m2) - z, _integer(j3 - j2 + m1) + z,
                   _integer(j3 - j1 - m2) + z)
        denominator = 1
        for number in factors:
            denominator *= factorial(number)
        terms.append((z, Fraction(_phase(z), denominator)))
    total = sum((value for _, value in terms), Fraction(0))
    phase = _phase(j1 - j2 - m3)
    value = phase * total * sqrt_rational(root)
    return {"arguments": tuple(map(str, args)), "allowed": True, "radicand": str(root),
            "phase": phase, "terms": tuple((z, str(value)) for z, value in terms),
            "sum": str(total), "value": value.serialize()}


@lru_cache(maxsize=None, typed=True)
def wigner_3j(j1, j2, j3, m1, m2, m3):
    return Radical({int(root): Fraction(value) for root, value in
                    wigner_3j_witness(j1, j2, j3, m1, m2, m3)["value"].items()})


def wigner_6j_witness(a, b, c, d, e, f):
    a, b, c, d, e, f = map(_angular, (a, b, c, d, e, f))
    args = (a, b, c, d, e, f)
    triangles = (_triangle(a, b, c), _triangle(a, e, f), _triangle(d, b, f), _triangle(d, e, c))
    if not all(triangles):
        return {"arguments": tuple(map(str, args)), "allowed": False, "radicand": "0",
                "terms": (), "sum": "0", "value": Radical().serialize()}
    root = Fraction(1)
    for triangle in triangles:
        root *= triangle
    low = tuple(map(_integer, (a + b + c, a + e + f, d + b + f, d + e + c)))
    high = tuple(map(_integer, (a + b + d + e, a + c + d + f, b + c + e + f)))
    terms = []
    for z in range(max(low), min(high) + 1):
        denominator = 1
        for number in tuple(z - value for value in low) + tuple(value - z for value in high):
            denominator *= factorial(number)
        terms.append((z, Fraction(_phase(z) * factorial(z + 1), denominator)))
    total = sum((value for _, value in terms), Fraction(0))
    value = total * sqrt_rational(root)
    return {"arguments": tuple(map(str, args)), "allowed": True, "radicand": str(root),
            "terms": tuple((z, str(value)) for z, value in terms), "sum": str(total),
            "value": value.serialize()}


@lru_cache(maxsize=None, typed=True)
def wigner_6j(a, b, c, d, e, f):
    return Radical({int(root): Fraction(value) for root, value in
                    wigner_6j_witness(a, b, c, d, e, f)["value"].items()})


def clebsch_gordan(j1, m1, j2, m2, total, magnetic):
    j1, j2, total = map(_angular, (j1, j2, total))
    m1, m2, magnetic = map(rational, (m1, m2, magnetic))
    if m1 + m2 != magnetic or not _triangle(j1, j2, total):
        return Radical()
    return _phase(j1 - j2 + magnetic) * sqrt_rational(2 * total + 1) * \
        wigner_3j(j1, j2, total, m1, m2, -magnetic)


NUCLEAR_SPIN = Fraction(3, 2)
GROUND_J = Fraction(1, 2)
EXCITED_J = {"D1": Fraction(1, 2), "D2": Fraction(3, 2)}
EXCITED_F = {"D1": (1, 2), "D2": (0, 1, 2, 3)}
Q_COMPONENTS = (-1, 0, 1)
MANIFOLDS = (("ground", 1), ("ground", 2), ("D1", 1), ("D1", 2),
             ("D2", 0), ("D2", 1), ("D2", 2), ("D2", 3), ("ion", None))


@dataclass(frozen=True)
class State:
    family: str
    f: int | None
    m: int | None


STATES = tuple(State(family, f, m) for family, f in MANIFOLDS
               for m in ((None,) if f is None else range(-f, f + 1)))
INDEX = {state: index for index, state in enumerate(STATES)}
ION = INDEX[State("ion", None, None)]


def dipole_witness(line, ground_f, ground_m, excited_f, excited_m, q):
    if line not in EXCITED_J or type(q) is not int or q not in Q_COMPONENTS:
        raise ValueError("named D line and spherical component required")
    if (type(ground_f) is not int or ground_f not in (1, 2) or
            type(excited_f) is not int or excited_f not in EXCITED_F[line] or
            type(ground_m) is not int or abs(ground_m) > ground_f or
            type(excited_m) is not int or abs(excited_m) > excited_f):
        raise ValueError("retained hyperfine sublevel required")
    jp = EXCITED_J[line]
    three = wigner_3j_witness(excited_f, 1, ground_f, -excited_m, q, ground_m)
    six = wigner_6j_witness(jp, excited_f, NUCLEAR_SPIN, ground_f, GROUND_J, 1)
    phase = _phase(excited_f - excited_m + jp + NUCLEAR_SPIN + ground_f + 1)
    dimension = (2 * excited_f + 1) * (2 * ground_f + 1)
    value = (phase * sqrt_rational(dimension) *
             wigner_3j(excited_f, 1, ground_f, -excited_m, q, ground_m) *
             wigner_6j(jp, excited_f, NUCLEAR_SPIN, ground_f, GROUND_J, 1))
    return {"line": line, "ground": (ground_f, ground_m), "excited": (excited_f, excited_m),
            "q": q, "phase": phase, "dimension_radicand": dimension,
            "three_j": three, "six_j": six, "coefficient": value.serialize()}


@lru_cache(maxsize=None, typed=True)
def dipole_coefficient(line, ground_f, ground_m, excited_f, excited_m, q):
    return Radical({int(root): Fraction(value) for root, value in
                    dipole_witness(line, ground_f, ground_m, excited_f, excited_m, q)["coefficient"].items()})


def dipole_matrix(line, q):
    if line not in EXCITED_J or type(q) is not int or q not in Q_COMPONENTS:
        raise ValueError("named D line and spherical component required")
    matrix = {}
    for e, excited in enumerate(STATES):
        if excited.family != line:
            continue
        for g, ground in enumerate(STATES):
            if ground.family != "ground":
                continue
            value = dipole_coefficient(line, ground.f, ground.m, excited.f, excited.m, q)
            if value:
                matrix[e, g] = value
    return matrix


def _field(field):
    if type(field) is not dict or set(field) != set(Q_COMPONENTS) or any(type(q) is not int for q in field):
        raise ValueError("all three explicit spherical field components required")
    return {q: complex_exact(value) for q, value in field.items()}


def hamiltonian_terms(convention="spherical_components"):
    """Excitation matrices multiplying reduced R/C and one raw field component.

    spherical_components uses H=-d.E/2+h.c., d.E=sum_q(-1)^q d_q E_-q.
    absorption_amplitudes uses H=sum_q amplitude_q*d_q/2+h.c.
    The latter coefficients are the explicitly dualised former field.
    """
    if convention not in ("spherical_components", "absorption_amplitudes"):
        raise ValueError("explicit field convention required")
    terms = []
    for line in EXCITED_J:
        for q in Q_COMPONENTS:
            field_q = -q if convention == "spherical_components" else q
            sign = -_phase(q) if convention == "spherical_components" else 1
            terms.append((line, field_q, {key: sign * value / 2
                                         for key, value in dipole_matrix(line, q).items()}))
    return tuple(terms)


def hamiltonian(fields_r, fields_c, r, c, detunings, *, convention="spherical_components"):
    """Evaluate the electric-dipole rotating-wave Hamiltonian at a stated time/frame.

    Fields may contain the frequency/time phases; no resonant, real-Jones or
    rectangular-pulse assumption is made.  Detunings must explicitly cover
    all States or all MANIFOLDS.  H_diag=-detuning; manifold input states an
    equal-m detuning regime, while State input retains Zeeman shifts.
    """
    fields = {"D1": _field(fields_r), "D2": _field(fields_c)}
    amplitudes = {"D1": complex_exact(r), "D2": complex_exact(c)}
    if type(detunings) is not dict:
        raise ValueError("explicit diagonal rotating-frame controls required")
    if set(detunings) == set(STATES):
        energies = [Radical(detunings[state]) for state in STATES]
    elif set(detunings) == set(MANIFOLDS):
        energies = [Radical(detunings[state.family, state.f]) for state in STATES]
    else:
        raise ValueError("all State or manifold detunings required")
    matrix = {(index, index): ComplexRadical(-energy) for index, energy in enumerate(energies) if energy}
    for line, q, coefficients in hamiltonian_terms(convention):
        factor = amplitudes[line] * fields[line][q]
        for (e, g), coefficient in coefficients.items():
            value = factor * coefficient
            if value:
                matrix[e, g] = matrix.get((e, g), ComplexRadical()) + value
                matrix[g, e] = matrix.get((g, e), ComplexRadical()) + value.conjugate()
    return {key: value for key, value in matrix.items() if value}


@dataclass(frozen=True)
class Jump:
    label: tuple
    matrix: dict


def natural_jumps(regime, gammas):
    """Normalise the generated dipoles to each explicit excited-manifold width.

    gammas keys are (line,F') for all six excited manifolds.  Coherent q/F
    retains magnetic-sublevel coherence within each resolved line/F'/F/q;
    secular rank1 resolves each magnetic transition as a separate bath mode.
    Neither bath-resolution regime is asserted to be the actual apparatus.
    """
    if regime not in ("coherent_q_F", "secular_rank1"):
        raise ValueError("explicit radiation resolution regime required")
    expected = {(line, f) for line in EXCITED_J for f in EXCITED_F[line]}
    if type(gammas) is not dict or set(gammas) != expected:
        raise ValueError("all excited-manifold natural widths required")
    rates = {key: rational(value) for key, value in gammas.items()}
    if any(value < 0 for value in rates.values()):
        raise ValueError("nonnegative natural widths required")
    norms = {}
    for line in EXCITED_J:
        for q in Q_COMPONENTS:
            for (e, _), value in dipole_matrix(line, q).items():
                norms[e] = norms.get(e, Fraction(0)) + (value * value).as_rational()
    operators = {}
    for line in EXCITED_J:
        for q in Q_COMPONENTS:
            for (e, g), value in dipole_matrix(line, q).items():
                excited, ground = STATES[e], STATES[g]
                coefficient = value * sqrt_rational(rates[line, excited.f] / norms[e])
                if not coefficient:
                    continue
                label = (line, excited.f, ground.f, q)
                if regime == "secular_rank1":
                    label += (excited.m, ground.m)
                operators.setdefault(label, {})[g, e] = ComplexRadical(coefficient)
    return tuple(Jump(label, matrix) for label, matrix in sorted(operators.items()))


def matrix_adjoint(matrix):
    return {(column, row): complex_exact(value).conjugate() for (row, column), value in matrix.items()}


def matrix_product(left, right):
    values = {}
    by_row = {}
    for (row, column), value in right.items():
        by_row.setdefault(row, []).append((column, complex_exact(value)))
    for (row, middle), a in left.items():
        for column, b in by_row.get(middle, ()):
            key = (row, column)
            values[key] = values.get(key, ComplexRadical()) + complex_exact(a) * b
    return {key: value for key, value in values.items() if value}


def source_qubit_bridge():
    """The named source phase bridge, with no optical-frame or CSV label claim."""
    u = INDEX[State("ground", 1, 1)]
    d = INDEX[State("ground", 1, -1)]
    half_root = sqrt_rational(Fraction(1, 2))
    return {"u_z": {u: ComplexRadical(1)}, "d_z": {d: ComplexRadical(1)},
            "u_x": {u: ComplexRadical(half_root), d: ComplexRadical(half_root)},
            "d_x": {u: ComplexRadical(0, half_root), d: ComplexRadical(0, -half_root)}}


def qubit_restriction(matrix):
    basis = source_qubit_bridge()
    vectors = (basis["u_x"], basis["d_x"])
    result = {}
    for a, left in enumerate(vectors):
        for b, right in enumerate(vectors):
            value = sum((x.conjugate() * complex_exact(matrix.get((i, j), 0)) * y
                         for i, x in left.items() for j, y in right.items()), ComplexRadical())
            if value:
                result[a, b] = value
    return result


def model_metadata():
    return {"schema": "rb87-angular-dipole/v1", "dimension": len(STATES), "nuclear_spin": "3/2",
            "ground_j": "1/2", "excited_j": {line: str(j) for line, j in EXCITED_J.items()},
            "basis": "Condon-Shortley |(J I)F m>",
            "dipole_normalization": "standard 3j electronic reduced matrix element",
            "field_convention": "explicit spherical components or dual absorption amplitudes",
            "hamiltonian_regime": "electric-dipole rotating-wave; explicit frequency/time phases and diagonal frame",
            "units": "Hamiltonian/hbar angular frequency; natural widths inverse time in the same time unit",
            "radiation_regimes": {"coherent_q_F": "resolved line/F'/F/q, unresolved magnetic sublevels",
                                  "secular_rank1": "each magnetic transition resolved"},
            "source_qubit": "u_x=(u_z+d_z)/sqrt(2); d_x=-i(d_z-u_z)/sqrt(2)",
            "ion": "effective sink; no bound-state electric-dipole couplings",
            "actual_hardware_configuration": False, "actual": False, "controller_advance": False,
            "propagation_performed": False}
