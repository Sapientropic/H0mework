"""Independent full-12-state rational/dyadic atomic response enclosures.

The action retains all 144 complex matrix coordinates. It does not import the
Hermitian block producer or use numerical outputs as primitive inputs.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from math import factorial, isqrt, lcm


DIMENSION = 12
ION, BRIGHT, DARK = 2, 0, 3
DETUNING = Fraction(3258, 23)
D2_RATE = Fraction(30333, 28750)
BITS, ORDER, NORM_CAP = 240, 80, Fraction(4)
RAW_KEYS = frozenset(("duration", "omega_r", "omega_c", "ion_rate"))
# (destination, origin, rate), using the source's 1-based labels.
NATURAL_JUMPS = (
    (1, 2, Fraction(1, 12)), (1, 7, Fraction(1, 12)), (1, 9, Fraction(1, 2)),
    (4, 2, Fraction(1, 12)), (4, 7, Fraction(1, 12)), (4, 8, Fraction(1, 4)),
    (4, 10, Fraction(1, 12)), (4, 12, Fraction(1, 2)),
    (11, 7, Fraction(1, 3)), (11, 8, Fraction(1, 4)), (11, 10, Fraction(1, 12)),
    (5, 2, Fraction(5, 6)), (5, 6, D2_RATE), (5, 7, Fraction(1, 2)),
    (5, 8, Fraction(1, 2)), (5, 9, Fraction(1, 2)),
    (5, 10, Fraction(5, 6)), (5, 12, Fraction(1, 2)),
)
EXCITED = (2, 6, 7, 8, 9, 10, 12)
COHERENT_EDGES = ((1, 2, 1), (1, 9, 6), (4, 7, 1), (4, 12, 6),
                  (8, 11, 3), (10, 11, 1), (5, 6, 0))
COMPONENTS = ((1, 2, 9), (4, 7, 12), (5, 6), (8, 10, 11), (3,))


def exact(value):
    if type(value) not in (str, int, Fraction):
        raise ValueError("exact_raw_atomic_parameter_required")
    result = Fraction(value)
    if type(value) is str and str(result) != value:
        raise ValueError("canonical_raw_atomic_fraction_required")
    return result


@dataclass(frozen=True)
class Pulse:
    duration: Fraction
    omega_r: Fraction
    omega_c: Fraction
    ion_rate: Fraction

    def __post_init__(self):
        for name in RAW_KEYS:
            object.__setattr__(self, name, exact(getattr(self, name)))
        if any(getattr(self, name) < 0 for name in RAW_KEYS):
            raise ValueError("nonnegative_atomic_pulse_controls_required")

    @classmethod
    def parse(cls, value):
        if type(value) is dict:
            if set(value) != RAW_KEYS:
                raise ValueError("atomic_pulse_raw_shape")
            return cls(**value)
        if isinstance(value, cls):
            return value
        # A different implementation's raw Pulse is read through its fields.
        return cls(**{name: getattr(value, name) for name in RAW_KEYS})


def sqrt_enclosure(integer, bits=BITS):
    if type(integer) is not int or integer < 0 or type(bits) is not int or bits < 32:
        raise ValueError("dyadic_sqrt_parameters")
    denominator = 1 << bits
    numerator = isqrt(integer * denominator * denominator)
    lo = Fraction(numerator, denominator)
    hi = lo if numerator * numerator == integer * denominator * denominator else Fraction(numerator + 1, denominator)
    return lo, hi


def round_nearest(numerator, denominator):
    if denominator <= 0:
        raise ValueError("positive_rounding_denominator_required")
    sign = -1 if numerator < 0 else 1
    quotient, remainder = divmod(abs(numerator), denominator)
    return sign * (quotient + (2 * remainder >= denominator))


def _add(target, key, real=0, imag=0):
    old_real, old_imag = target.get(key, (0, 0))
    value = old_real + real, old_imag + imag
    if value == (0, 0):
        target.pop(key, None)
    else:
        target[key] = value


class Generator:
    """An independently transcribed real Hamiltonian and rank-one jumps."""

    def __init__(self, pulse, bits=BITS):
        self.pulse, self.bits = Pulse.parse(pulse), bits
        p = self.pulse
        self.hamiltonian = {(index - 1, index - 1): -DETUNING for index in (7, 8, 9, 12)}
        uncertainty = [Fraction(0) for _ in range(DIMENSION)]
        self.sqrt_intervals = {}
        for left, right, root in COHERENT_EDGES:
            if root == 0:
                coefficient = p.omega_c / 2
            else:
                lo, hi = sqrt_enclosure(root, bits)
                self.sqrt_intervals[root] = (lo, hi)
                coefficient = p.omega_r * (lo + hi) / 4
                error = abs(p.omega_r) * (hi - lo) / 4
                uncertainty[left - 1] += error
                uncertainty[right - 1] += error
            if coefficient:
                self.hamiltonian[left - 1, right - 1] = coefficient
                self.hamiltonian[right - 1, left - 1] = coefficient
        self.hamiltonian_uncertainty = max(uncertainty)
        self.jumps = tuple((left - 1, right - 1, rate) for left, right, rate in NATURAL_JUMPS) + tuple(
            (ION, index - 1, p.ion_rate) for index in EXCITED if p.ion_rate
        )
        self.outgoing = [Fraction(0) for _ in range(DIMENSION)]
        for _, source, rate in self.jumps:
            self.outgoing[source] += rate
        row_sums = [Fraction(0) for _ in range(DIMENSION)]
        for (row, _), coefficient in self.hamiltonian.items():
            row_sums[row] += abs(coefficient)
        self.norm_bound = 2 * max(row_sums) + 2 * max(self.outgoing)
        values = list(self.hamiltonian.values()) + [rate for _, _, rate in self.jumps] + [v / 2 for v in self.outgoing]
        self.denominator = lcm(*(v.denominator for v in values))
        self.h_integer = tuple((row, column, int(value * self.denominator))
                               for (row, column), value in self.hamiltonian.items())
        self.j_integer = tuple((destination, source, int(rate * self.denominator))
                               for destination, source, rate in self.jumps)
        self.half_exit_integer = tuple(int(value * self.denominator / 2) for value in self.outgoing)
        self._check_structure()

    def _check_structure(self):
        if any(self.hamiltonian.get((column, row), Fraction(0)) != value
               for (row, column), value in self.hamiltonian.items()):
            raise ValueError("independent_hamiltonian_not_hermitian")
        if any(rate < 0 for _, _, rate in self.jumps) or self.outgoing[ION] != 0:
            raise ValueError("invalid_jump_or_ion_absorption")
        if any(ION in key for key in self.hamiltonian):
            raise ValueError("ion_not_absorbing")
        component = {label - 1: index for index, block in enumerate(COMPONENTS) for label in block}
        if any(component[row] != component[column] for row, column in self.hamiltonian):
            raise ValueError("bright_dark_coherent_sector_mixing")
        for root, (lo, hi) in self.sqrt_intervals.items():
            if not 0 <= lo * lo <= root <= hi * hi:
                raise ValueError("clebsch_gordan_sqrt_not_enclosed")

    def integer_action(self, matrix):
        """Return denominator times L(matrix), for any full complex matrix."""
        result = {}
        by_row, by_column = {}, {}
        for (row, column), (real, imag) in matrix.items():
            by_row.setdefault(row, []).append((column, real, imag))
            by_column.setdefault(column, []).append((row, real, imag))
            loss = self.half_exit_integer[row] + self.half_exit_integer[column]
            _add(result, (row, column), -loss * real, -loss * imag)
        for row, column, coefficient in self.h_integer:
            for other, real, imag in by_row.get(column, ()):
                _add(result, (row, other), coefficient * imag, -coefficient * real)
            for other, real, imag in by_column.get(row, ()):
                _add(result, (other, column), -coefficient * imag, coefficient * real)
        for destination, source, rate in self.j_integer:
            real, imag = matrix.get((source, source), (0, 0))
            _add(result, (destination, destination), rate * real, rate * imag)
        return result

    def action(self, matrix):
        """Exact Fraction action on arbitrary (real, imaginary) entries."""
        denominator = lcm(*(exact(value).denominator for pair in matrix.values() for value in pair)) if matrix else 1
        integer_matrix = {key: tuple(int(exact(v) * denominator) for v in pair) for key, pair in matrix.items()}
        return {key: tuple(Fraction(v, denominator * self.denominator) for v in pair)
                for key, pair in self.integer_action(integer_matrix).items()}

    def check_all_matrix_units(self):
        """Check all 144 complex coordinates; no density-sector reduction."""
        checked = 0
        for row in range(DIMENSION):
            for column in range(DIMENSION):
                for seed in ((1, 0), (0, 1)):
                    result = self.integer_action({(row, column): seed})
                    trace = tuple(sum(result.get((index, index), (0, 0))[part] for index in range(DIMENSION))
                                  for part in (0, 1))
                    if trace != (0, 0):
                        raise ValueError("full_liouvillian_trace_failure")
                    checked += 1
        return checked


def _hermitian(matrix):
    for (row, column), (real, imag) in matrix.items():
        if matrix.get((column, row), (0, 0)) != (real, -imag):
            return False
    return True


def _entry_norm(matrix, quantum):
    return Fraction(sum(abs(real) + abs(imag) for real, imag in matrix.values()), quantum)


def _advance(generator, matrix, dt, quantum, order):
    term, total = matrix, dict(matrix)
    for index in range(1, order + 1):
        action = generator.integer_action(term)
        divisor = generator.denominator * dt.denominator * index
        term = {key: tuple(round_nearest(value * dt.numerator, divisor) for value in pair)
                for key, pair in action.items()}
        term = {key: pair for key, pair in term.items() if pair != (0, 0)}
        for key, (real, imag) in term.items():
            _add(total, key, real, imag)
        if not term:
            break
    if not _hermitian(total):
        raise ValueError("full_matrix_hermitian_rounding_failure")
    return total


def _rounding_error(radius, quantum, order):
    # Each of 144 real and 144 imaginary entries incurs <= 1/2 quantum.
    # The bound remains valid when exact sparsity eliminates most operations.
    previous, accumulated = Fraction(0), Fraction(0)
    for index in range(1, order + 1):
        previous = radius * previous / index + Fraction(144, quantum)
        accumulated += previous
    return accumulated


def _dyadic_upper(value, bits=16):
    denominator = 1 << bits
    numerator = -(-(value.numerator * denominator) // value.denominator)
    return Fraction(numerator, denominator)


def _formal_action(pulse, root3, root6, matrix):
    """Full exact action after a formal linear substitution for the two roots."""
    h = {(index - 1, index - 1): -DETUNING for index in (7, 8, 9, 12)}
    for left, right, root in COHERENT_EDGES:
        coefficient = pulse.omega_c / 2 if root == 0 else pulse.omega_r * {1: 1, 3: root3, 6: root6}[root] / 2
        h[left - 1, right - 1] = h[right - 1, left - 1] = coefficient
    jumps = [(left - 1, right - 1, rate) for left, right, rate in NATURAL_JUMPS]
    jumps.extend((ION, state - 1, pulse.ion_rate) for state in EXCITED)
    outgoing = [sum((rate for _, source, rate in jumps if source == state), Fraction(0)) for state in range(DIMENSION)]
    result = {}
    for (a, b), (real, imag) in matrix.items():
        loss = (outgoing[a] + outgoing[b]) / 2
        _add(result, (a, b), -loss * real, -loss * imag)
        for (row, column), coefficient in h.items():
            if column == a:
                _add(result, (row, b), coefficient * imag, -coefficient * real)
            if row == b:
                _add(result, (a, column), -coefficient * imag, coefficient * real)
    for target, source, rate in jumps:
        real, imag = matrix.get((source, source), (0, 0))
        _add(result, (target, target), rate * real, rate * imag)
    return result


def verify_restriction(pulse, coordinates, rows):
    """Verify a supplied 32-coordinate restriction against all 144 coordinates.

    The three formal substitutions recover every coefficient of
    a+b sqrt(3)+c sqrt(6) exactly. They are algebra checks, not approximations
    of the physical Clebsch--Gordan factors.
    """
    pulse = Pulse.parse(pulse)
    coordinates = tuple(tuple(value) for value in coordinates)
    if len(coordinates) != 32 or len(set(coordinates)) != 32 or len(rows) != 32:
        raise ValueError("complete_32_coordinate_restriction_required")
    coordinate_keys, basis_keys = set(), set()
    for a, b, part in coordinates:
        if not (1 <= a <= DIMENSION and 1 <= b <= DIMENSION and part in ("real", "imag")) or (a == b and part != "real"):
            raise ValueError("invalid_hermitian_coordinate")
        coordinate_keys.add((a - 1, b - 1))
        coordinate_keys.add((b - 1, a - 1))
        basis_keys.add((min(a, b), max(a, b), part))
    expected_support = {(a - 1, b - 1) for block in COMPONENTS for a in block for b in block}
    expected_basis = {(a, a, "real") for a in range(1, DIMENSION + 1)} | {
        (min(a, b), max(a, b), part) for block in COMPONENTS for a in block for b in block if a != b for part in ("real", "imag")}
    if coordinate_keys != expected_support or basis_keys != expected_basis:
        raise ValueError("hermitian_restriction_omits_source_block")
    parsed_rows = []
    for row in rows:
        parsed = {}
        for column, coefficients in row:
            if type(column) is not int or not 0 <= column < 32 or column in parsed or len(coefficients) != 3:
                raise ValueError("invalid_sparse_restriction_entry")
            parsed[column] = tuple(map(exact, coefficients))
        parsed_rows.append(parsed)
    substitutions = ((0, 0), (1, 0), (0, 1))
    for column, (a, b, part) in enumerate(coordinates):
        a, b = a - 1, b - 1
        if a == b:
            matrix = {(a, b): (1, 0)}
        elif part == "real":
            matrix = {(a, b): (1, 0), (b, a): (1, 0)}
        else:
            matrix = {(a, b): (0, 1), (b, a): (0, -1)}
        for root3, root6 in substitutions:
            result = _formal_action(pulse, root3, root6, matrix)
            if any(key not in expected_support for key in result):
                raise ValueError("full_action_escapes_32_coordinate_restriction")
            for row, (left, right, output_part) in enumerate(coordinates):
                actual = result.get((left - 1, right - 1), (0, 0))[output_part == "imag"]
                a0, b0, c0 = parsed_rows[row].get(column, (Fraction(0),) * 3)
                if actual != a0 + b0 * root3 + c0 * root6:
                    raise ValueError("full_liouvillian_restriction_coefficient_mismatch")
    return {"full_complex_coordinates": 144, "hermitian_coordinates": 32,
            "exact_formal_coefficient_checks": 3 * 32 * 32, "restriction_verified": True}


def propagate(pulses, bits=BITS, order=ORDER, norm_cap=NORM_CAP, max_steps=100000):
    if type(bits) is not int or not 64 <= bits <= 1024 or type(order) is not int or not 16 <= order <= 256:
        raise ValueError("atomic_independent_precision_or_order")
    if type(pulses) not in (list, tuple) or not pulses:
        raise ValueError("nonempty_rectangular_pulse_sequence_required")
    if type(max_steps) is not int or max_steps < 1:
        raise ValueError("positive_atomic_step_budget_required")
    cap = exact(norm_cap)
    if not 0 < cap <= 4 or cap >= order + 2:
        raise ValueError("atomic_taylor_tail_ratio_not_below_one")
    parsed = tuple(Pulse.parse(pulse) for pulse in pulses)
    quantum = 1 << bits
    states = [{(BRIGHT, BRIGHT): (quantum, 0)}, {(DARK, DARK): (quantum, 0)}]
    errors, sqrt_error, steps = [Fraction(0), Fraction(0)], Fraction(0), 0
    pulse_certificates = []
    for pulse in parsed:
        generator = Generator(pulse, bits)
        if pulse.duration == 0:
            count, dt = 0, Fraction(0)
        else:
            ratio = pulse.duration * generator.norm_bound / cap
            count = max(1, -(-ratio.numerator // ratio.denominator))
            dt = pulse.duration / count
        if steps + count > max_steps:
            raise ValueError("atomic_independent_step_budget_exceeded")
        radius = dt * generator.norm_bound
        # This outward dyadic radius keeps certificates compact without losing
        # the true action-norm bound or enlarging the integration step.
        radius_upper = _dyadic_upper(radius)
        if radius_upper >= order + 2:
            raise ValueError("rounded_atomic_tail_ratio_not_below_one")
        rounding = _rounding_error(radius_upper, quantum, order)
        tail = radius_upper ** (order + 1) / factorial(order + 1) / (1 - radius_upper / (order + 2))
        # Two Hamiltonians are Hermitian; their Lindblad semigroups are CPTP.
        # Duhamel on a density matrix bounds the Hamiltonian substitution by
        # 2 T ||H_exact-H_mid||op; trace norm contraction prevents stiff growth.
        coefficient_error = 2 * pulse.duration * generator.hamiltonian_uncertainty
        sqrt_error += coefficient_error
        max_local = [Fraction(0), Fraction(0)]
        for _ in range(count):
            for index in (0, 1):
                local = _entry_norm(states[index], quantum) * tail + rounding
                errors[index] += local
                max_local[index] = max(max_local[index], local)
                states[index] = _advance(generator, states[index], dt, quantum, order)
            steps += 1
        pulse_certificates.append({"steps": count, "dt": str(dt), "liouvillian_entry_norm_bound": str(generator.norm_bound),
                                   "step_radius": str(radius), "step_radius_upper": str(radius_upper), "taylor_tail_factor": str(tail),
                                   "rounding_error_per_step": str(rounding), "sqrt_coefficient_error": str(coefficient_error),
                                   "maximum_local_error": list(map(str, max_local)),
                                   "natural_jumps": 18, "ionization_jumps": 7 if pulse.ion_rate else 0,
                                   "full_matrix_unit_trace_checks": generator.check_all_matrix_units()})
    errors = [error + sqrt_error for error in errors]
    centers = [Fraction(state.get((ION, ION), (0, 0))[0], quantum) for state in states]
    intervals = [(max(Fraction(0), center - error), min(Fraction(1), center + error))
                 for center, error in zip(centers, errors)]
    if any(lo > hi for lo, hi in intervals):
        raise ValueError("atomic_density_probability_enclosure_empty")
    return {"p_bright": list(map(str, intervals[0])), "p_dark": list(map(str, intervals[1])),
            "trace_j": [str(intervals[0][0] + intervals[1][0]), str(intervals[0][1] + intervals[1][1])],
            "probability_centers": list(map(str, centers)), "error_bounds": list(map(str, errors)),
            "steps": steps, "bits": bits, "order": order, "norm_cap": str(cap),
            "generator_trace_preserving": True, "full_144_complex_liouvillian": True,
            "ion_offdiagonal_zero": True, "hermitian_states_checked": True,
            "pulse_certificates": pulse_certificates}


def verify_intersection(primary, checked):
    for name in ("p_bright", "p_dark", "trace_j"):
        left, right = tuple(map(exact, primary[name])), tuple(map(exact, checked[name]))
        maximum = 2 if name == "trace_j" else 1
        if (len(left) != 2 or len(right) != 2
                or max(Fraction(0), left[0], right[0]) > min(Fraction(maximum), left[1], right[1])):
            raise ValueError("independent_atomic_interval_disagreement_" + name)
    return True
