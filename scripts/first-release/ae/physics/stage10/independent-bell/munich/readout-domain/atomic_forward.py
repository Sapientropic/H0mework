"""Enclose the nominal twelve-state atomic response from primitive pulse controls.

Garthoff (2015), Eq. 3.6--3.13, defines the Hamiltonian and rank-one jumps.
The five Hamiltonian components form an invariant block-diagonal Hermitian
space of dimension 32.  Directed Taylor action supplies a local residual;
Hermitian trace-norm contraction of the exact Lindblad channel transports
each residual additively.  No measured assignment probability is an input.
"""
from dataclasses import dataclass
from decimal import Context, Decimal, ROUND_CEILING, ROUND_FLOOR, ROUND_HALF_EVEN
from fractions import Fraction as Q
from math import factorial


DETUNING = Q(3258, 23)
GAMMA2 = Q(30333, 28750)
BLOCKS = ((1, 2, 9), (4, 7, 12), (11, 8, 10), (5, 6), (3,))
EXCITED = (2, 6, 7, 8, 9, 10, 12)
NATURAL_JUMPS = (
    (1, 2, Q(1, 12)), (4, 2, Q(1, 12)), (5, 2, Q(5, 6)),
    (1, 7, Q(1, 12)), (4, 7, Q(1, 12)), (11, 7, Q(1, 3)), (5, 7, Q(1, 2)),
    (1, 9, Q(1, 2)), (5, 9, Q(1, 2)),
    (4, 8, Q(1, 4)), (11, 8, Q(1, 4)), (5, 8, Q(1, 2)),
    (4, 10, Q(1, 12)), (11, 10, Q(1, 12)), (5, 10, Q(5, 6)),
    (4, 12, Q(1, 2)), (5, 12, Q(1, 2)), (5, 6, GAMMA2),
)
# Each real/imaginary coordinate is the upper entry in the displayed block order.
COORDINATES = tuple(item for block in BLOCKS for item in
                    ([(i, i, "real") for i in block] +
                     [(i, j, part) for position, i in enumerate(block)
                      for j in block[position + 1:] for part in ("real", "imag")]))
DIAGONALS = tuple(i for i, (a, b, _) in enumerate(COORDINATES) if a == b)
ION_COORDINATE = COORDINATES.index((3, 3, "real"))
ZERO = (Q(0), Q(0), Q(0))


def rational(value):
    if isinstance(value, bool) or type(value) not in (int, str, Q):
        raise TypeError("Exact integer, rational string, or Fraction required")
    return Q(value)


@dataclass(frozen=True)
class Pulse:
    duration: Q
    omega_r: Q
    omega_c: Q
    ion_rate: Q

    def __post_init__(self):
        for name in ("duration", "omega_r", "omega_c", "ion_rate"):
            value = rational(getattr(self, name))
            if value < 0:
                raise ValueError("Nonnegative dimensionless pulse controls required")
            object.__setattr__(self, name, value)

    @classmethod
    def from_angular_rates(cls, duration_ns, omega_r_rad_per_second,
                           omega_c_rad_per_second, ion_rad_per_second,
                           gamma_d1_rad_per_second):
        """The explicit angular-rate unit contract retains the common 2 pi factor."""
        duration, readout, cycling, ion, gamma = map(rational, (
            duration_ns, omega_r_rad_per_second, omega_c_rad_per_second,
            ion_rad_per_second, gamma_d1_rad_per_second))
        if gamma <= 0:
            raise ValueError("Positive D1 angular decay rate required")
        return cls(duration * gamma / 10 ** 9, readout / gamma, cycling / gamma, ion / gamma)


def add_coefficient(left, right):
    return tuple(a + b for a, b in zip(left, right))


def multiply_coefficient(value, factor):
    return tuple(a * factor for a in value)


def generator_coefficients(pulse):
    """Return the exact sparse generator, with each entry a + b sqrt(3) + c sqrt(6)."""
    if type(pulse) is not Pulse:
        raise TypeError("Primitive Pulse required")
    h = {}
    for i, j, root in ((1, 2, 0), (1, 9, 2), (4, 7, 0), (4, 12, 2),
                       (8, 11, 1), (10, 11, 0)):
        values = [Q(0)] * 3
        values[root] = pulse.omega_r / 2
        h[i, j] = h[j, i] = tuple(values)
    h[5, 6] = h[6, 5] = (pulse.omega_c / 2, Q(0), Q(0))
    for state in (7, 8, 9, 12):
        h[state, state] = (-DETUNING, Q(0), Q(0))
    matrix = [[ZERO for _ in COORDINATES] for _ in COORDINATES]
    for column, (i, j, part) in enumerate(COORDINATES):
        entries = [(i, j, 1, 0)] if i == j else (
            [(i, j, 1, 0), (j, i, 1, 0)] if part == "real" else
            [(i, j, 0, 1), (j, i, 0, -1)])
        commutator = {}
        for a, b, real, imag in entries:
            for (c, d), coefficient in h.items():
                if d == a:
                    old = commutator.get((c, b), (ZERO, ZERO))
                    commutator[c, b] = (add_coefficient(old[0], multiply_coefficient(coefficient, real)),
                                        add_coefficient(old[1], multiply_coefficient(coefficient, imag)))
                if b == c:
                    old = commutator.get((a, d), (ZERO, ZERO))
                    commutator[a, d] = (add_coefficient(old[0], multiply_coefficient(coefficient, -real)),
                                        add_coefficient(old[1], multiply_coefficient(coefficient, -imag)))
        for row, (a, b, output_part) in enumerate(COORDINATES):
            real, imag = commutator.get((a, b), (ZERO, ZERO))
            matrix[row][column] = imag if output_part == "real" else multiply_coefficient(real, -1)
    jumps = NATURAL_JUMPS + tuple((3, state, pulse.ion_rate) for state in EXCITED)
    outgoing = {state: sum(rate for _, source, rate in jumps if source == state)
                for state in range(1, 13)}
    for row, (a, b, _) in enumerate(COORDINATES):
        decay = -(outgoing[a] + outgoing[b]) / 2
        matrix[row][row] = add_coefficient(matrix[row][row], (decay, Q(0), Q(0)))
    for target, source, rate in jumps:
        row = COORDINATES.index((target, target, "real"))
        column = COORDINATES.index((source, source, "real"))
        matrix[row][column] = add_coefficient(matrix[row][column], (rate, Q(0), Q(0)))
    return tuple(tuple((column, entry) for column, entry in enumerate(row) if entry != ZERO)
                 for row in matrix)


class Arithmetic:
    def __init__(self, precision):
        if type(precision) is not int or precision < 40 or precision > 500:
            raise ValueError("Decimal precision between 40 and 500 required")
        self.down = Context(prec=precision, rounding=ROUND_FLOOR)
        self.up = Context(prec=precision, rounding=ROUND_CEILING)
        self.near = Context(prec=precision, rounding=ROUND_HALF_EVEN)
        self.zero, self.one = Decimal(0), Decimal(1)
        self.roots = [self.sqrt(Q(3)), self.sqrt(Q(6))]

    def fraction(self, value):
        value = rational(value)
        numerator, denominator = Decimal(value.numerator), Decimal(value.denominator)
        return (self.down.divide(numerator, denominator), self.up.divide(numerator, denominator))

    def sqrt(self, value):
        low, high = self.fraction(value)
        # Decimal sqrt is correctly rounded to nearest, regardless of Context.rounding.
        return (self.down.next_minus(self.near.sqrt(low)), self.up.next_plus(self.near.sqrt(high)))

    def add(self, left, right):
        return (self.down.add(left[0], right[0]), self.up.add(left[1], right[1]))

    def multiply(self, left, right):
        lows = [self.down.multiply(a, b) for a in left for b in right]
        highs = [self.up.multiply(a, b) for a in left for b in right]
        return min(lows), max(highs)

    def coefficient(self, value):
        result = self.fraction(value[0])
        for scalar, root in zip(value[1:], self.roots):
            if scalar:
                result = self.add(result, self.multiply(self.fraction(scalar), root))
        return result

    def midpoint(self, interval):
        return self.near.divide(self.near.add(*interval), Decimal(2))

    def radius(self, interval, midpoint):
        return max(self.up.subtract(midpoint, interval[0]), self.up.subtract(interval[1], midpoint))


@dataclass(frozen=True)
class Generator:
    pulse: Pulse
    exact: tuple
    rows: tuple
    norm_infinity_upper: Decimal


def build_generator(pulse, precision=80):
    arithmetic = Arithmetic(precision)
    exact = generator_coefficients(pulse)
    rows = tuple(tuple((column, arithmetic.coefficient(value)) for column, value in row) for row in exact)
    norm = max(sum_upper(arithmetic, [max(endpoint.copy_abs() for endpoint in value)
                                     for _, value in row]) for row in rows)
    return Generator(pulse, exact, rows, norm)


def sum_upper(arithmetic, values):
    result = Decimal(0)
    for value in values:
        result = arithmetic.up.add(result, value)
    return result


def trace_preserving(exact):
    diagonal_rows = [dict(exact[row]) for row in DIAGONALS]
    return all(sum((row.get(column, ZERO)[part] for row in diagonal_rows), Q(0)) == 0
               for column in range(32) for part in range(3))


def apply_generator(arithmetic, rows, vector):
    result = []
    for row in rows:
        interval = (Decimal(0), Decimal(0))
        for column, coefficient in row:
            interval = arithmetic.add(interval, arithmetic.multiply(coefficient, vector[column]))
        result.append(interval)
    return result


def local_taylor(arithmetic, generator, vector, duration, order, norm_cap=Q(4)):
    """Enclose exp(duration L) acting on one Hermitian center and its local error."""
    h = arithmetic.fraction(duration)
    r = arithmetic.up.multiply(h[1], generator.norm_infinity_upper)
    if r > norm_cap or r >= order + 2:
        raise ValueError("Taylor step exceeds its declared norm cap")
    term = [(value, value) for value in vector]
    total = term.copy()
    for k in range(1, order + 1):
        factor = arithmetic.multiply(h, arithmetic.fraction(Q(1, k)))
        term = [arithmetic.multiply(value, factor)
                for value in apply_generator(arithmetic, generator.rows, term)]
        total = [arithmetic.add(left, right) for left, right in zip(total, term)]
    power = Decimal(1)
    for _ in range(order + 1):
        power = arithmetic.up.multiply(power, r)
    denominator = arithmetic.down.multiply(Decimal(factorial(order + 1)),
                    arithmetic.down.subtract(Decimal(1), arithmetic.up.divide(r, Decimal(order + 2))))
    tail = arithmetic.up.divide(arithmetic.up.multiply(max(value.copy_abs() for value in vector), power), denominator)
    centers = [arithmetic.midpoint(value) for value in total]
    radius = max(arithmetic.up.add(arithmetic.radius(value, center), tail)
                 for value, center in zip(total, centers))
    # ||E||_1 <= sqrt(12)||E||_F; 12 diagonal and 20 off-diagonal
    # real coordinates give ||E||_F^2 <= (12 + 2*20) radius^2 < 64 radius^2.
    # Thus 32 radius strictly bounds the trace norm without rounded square roots.
    return centers, arithmetic.up.multiply(Decimal(32), radius), tail


def propagate(pulses, precision=80, order=80, norm_cap=Q(4), max_steps=100000):
    if type(pulses) not in (list, tuple) or not pulses or any(type(pulse) is not Pulse for pulse in pulses):
        raise ValueError("Nonempty primitive rectangular pulse sequence required")
    if type(order) is not int or not 16 <= order <= 256:
        raise ValueError("Taylor order between 16 and 256 required")
    if type(max_steps) is not int or max_steps < 1:
        raise ValueError("Positive maximum step budget required")
    norm_cap = rational(norm_cap)
    if not 0 < norm_cap <= 4:
        raise ValueError("Taylor norm cap in (0,4] required")
    arithmetic = Arithmetic(precision)
    states = [[Decimal(0) for _ in COORDINATES] for _ in range(2)]
    states[0][COORDINATES.index((1, 1, "real"))] = Decimal(1)
    states[1][COORDINATES.index((4, 4, "real"))] = Decimal(1)
    errors = [Decimal(0), Decimal(0)]
    segments, used, all_trace_preserving = [], 0, True
    for pulse in pulses:
        generator = build_generator(pulse, precision)
        all_trace_preserving = all_trace_preserving and trace_preserving(generator.exact)
        needed = (Q(generator.norm_infinity_upper) * pulse.duration / norm_cap).__ceil__()
        steps = max(1, needed + 1)
        if used + steps > max_steps:
            raise ValueError("Declared Taylor step budget exceeded")
        used += steps
        h = pulse.duration / steps
        tails = [Decimal(0), Decimal(0)]
        for _ in range(steps):
            for branch in (0, 1):
                states[branch], residual, tail = local_taylor(arithmetic, generator, states[branch], h, order, norm_cap)
                errors[branch] = arithmetic.up.add(errors[branch], residual)
                tails[branch] = arithmetic.up.add(tails[branch], tail)
        segments.append({"pulse": {name: str(getattr(pulse, name)) for name in
                                  ("duration", "omega_r", "omega_c", "ion_rate")},
                         "steps": steps, "step_duration": str(h),
                         "generator_norm_infinity_upper": str(Q(generator.norm_infinity_upper)),
                         "summed_coordinate_taylor_tails": [str(Q(tail)) for tail in tails]})
    output = {"dimension": 32, "physical_dimension": 12, "precision": precision, "taylor_order": order,
              "total_steps": used, "norm_cap": str(norm_cap), "segments": segments,
              "error_transport": "Hermitian trace-norm contraction of the exact Lindblad channel",
              "initial_states": {"bright": 1, "dark": 4}, "ion_state": 3,
              "natural_jump_count": len(NATURAL_JUMPS), "ion_jump_count": len(EXCITED),
              "basis": [list(coordinate) for coordinate in COORDINATES]}
    for name, state, error in zip(("bright", "dark"), states, errors):
        midpoint = state[ION_COORDINATE]
        bounds = (arithmetic.down.subtract(midpoint, error), arithmetic.up.add(midpoint, error))
        trace = (Decimal(0), Decimal(0))
        for index in DIAGONALS:
            trace = arithmetic.add(trace, (state[index], state[index]))
        trace_bounds = (arithmetic.down.subtract(trace[0], error), arithmetic.up.add(trace[1], error))
        output[name] = {"ionization_interval": [str(Q(value)) for value in bounds],
                        "ionization_center": str(Q(midpoint)), "trace_norm_error_upper": str(Q(error)),
                        "trace_interval": [str(Q(value)) for value in trace_bounds],
                        "density_center": [str(Q(value)) for value in state],
                        "population_intervals": [[str(Q(arithmetic.down.subtract(state[index], error))),
                                                  str(Q(arithmetic.up.add(state[index], error)))]
                                                 for index in DIAGONALS]}
    output["p_bright"] = output["bright"]["ionization_interval"]
    output["p_dark"] = output["dark"]["ionization_interval"]
    output["trace_j"] = [str(rational(a) + rational(b))
                         for a, b in zip(output["p_bright"], output["p_dark"])]
    output["ion_offdiagonal_zero"] = True
    output["generator_trace_preserving"] = all_trace_preserving
    return output
