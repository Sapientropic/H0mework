"""Full 33-state Rb87 pulse response with phase and radiation memory retained.

All frequencies and durations use one common reciprocal time unit.  The sink
is the explicitly named effective resolved-absorption model.  No apparatus
waveform, detector efficiency, target Hamiltonian, or target effect is input.
The numerical centers and their scalar error certificates are separate.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
import hashlib
import json
from math import factorial, isqrt, lcm
from pathlib import Path

import atomic_dipole as dipole

DIMENSION = len(dipole.STATES)
COMPLEX_COORDINATES = DIMENSION ** 2
EXCITED = tuple(state for state in dipole.STATES if state.family in dipole.EXCITED_J)
WIDTHS = tuple((line, f) for line in dipole.EXCITED_J for f in dipole.EXCITED_F[line])
SINK_REGIME = "effective_resolved_absorption_sink"
TOMOGRAPHY = ("u_x", "d_x", "plus", "plus_i")
BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[5]
_dipole_path = Path(dipole.__file__).resolve()
_dipole_source = _dipole_path.read_bytes()


def exact(value):
    if type(value) not in (int, str, Q):
        raise TypeError("exact rational primitive required")
    return Q(value)


def nonnegative(value):
    value = exact(value)
    if value < 0:
        raise ValueError("nonnegative primitive required")
    return value


def _fields(value):
    if type(value) is not dict or set(value) != set(dipole.Q_COMPONENTS) or any(type(q) is not int for q in value):
        raise ValueError("all three explicit spherical components required")
    return {q: dipole.complex_exact(component) for q, component in value.items()}


@dataclass(frozen=True)
class Segment:
    duration: Q
    fields_r: dict
    fields_c: dict
    r: object
    c: object
    detunings: dict
    gammas: dict
    ion_rates: dict
    radiation_regime: str = "coherent_q_F"
    field_convention: str = "spherical_components"
    ion_regime: str = SINK_REGIME

    def __post_init__(self):
        object.__setattr__(self, "duration", nonnegative(self.duration))
        for name in ("fields_r", "fields_c"):
            object.__setattr__(self, name, _fields(getattr(self, name)))
        for name in ("r", "c"):
            object.__setattr__(self, name, dipole.complex_exact(getattr(self, name)))
        if type(self.detunings) is not dict or set(self.detunings) not in (set(dipole.STATES), set(dipole.MANIFOLDS)):
            raise ValueError("complete State or manifold detunings required")
        object.__setattr__(self, "detunings", {key: dipole.Radical(value) for key, value in self.detunings.items()})
        if type(self.gammas) is not dict or set(self.gammas) != set(WIDTHS):
            raise ValueError("all six natural widths required")
        object.__setattr__(self, "gammas", {key: nonnegative(value) for key, value in self.gammas.items()})
        if type(self.ion_rates) is not dict or set(self.ion_rates) != set(EXCITED):
            raise ValueError("all 24 resolved excited-state ion rates required")
        object.__setattr__(self, "ion_rates", {key: nonnegative(value) for key, value in self.ion_rates.items()})
        if self.radiation_regime not in ("coherent_q_F", "secular_rank1"):
            raise ValueError("explicit radiation-resolution regime required")
        if self.field_convention not in ("spherical_components", "absorption_amplitudes"):
            raise ValueError("explicit electric-field convention required")
        if self.ion_regime != SINK_REGIME:
            raise ValueError("registered resolved ion-sink regime required")

    def record(self):
        state_mode = set(self.detunings) == set(dipole.STATES)
        keys = dipole.STATES if state_mode else dipole.MANIFOLDS
        return {"duration": str(self.duration),
                "fields_r": {str(q): self.fields_r[q].serialize() for q in dipole.Q_COMPONENTS},
                "fields_c": {str(q): self.fields_c[q].serialize() for q in dipole.Q_COMPONENTS},
                "r": self.r.serialize(), "c": self.c.serialize(),
                "detuning_mode": "State" if state_mode else "manifold",
                "detunings": [self.detunings[key].serialize() for key in keys],
                "gammas": [str(self.gammas[key]) for key in WIDTHS],
                "ion_rates": [str(self.ion_rates[key]) for key in EXCITED],
                "radiation_regime": self.radiation_regime, "field_convention": self.field_convention,
                "ion_regime": self.ion_regime}

    @classmethod
    def from_record(cls, item):
        def radical(value):
            return dipole.Radical({int(root): exact(coefficient) for root, coefficient in value.items()})

        def complex_value(value):
            return dipole.ComplexRadical(radical(value["real"]), radical(value["imag"]))

        keys = {"State": dipole.STATES, "manifold": dipole.MANIFOLDS}[item["detuning_mode"]]
        if (len(item["detunings"]) != len(keys) or len(item["gammas"]) != len(WIDTHS)
                or len(item["ion_rates"]) != len(EXCITED)):
            raise ValueError("complete serialized primitive inventory required")
        return cls(item["duration"], {int(q): complex_value(v) for q, v in item["fields_r"].items()},
                   {int(q): complex_value(v) for q, v in item["fields_c"].items()},
                   complex_value(item["r"]), complex_value(item["c"]),
                   dict(zip(keys, map(radical, item["detunings"]))),
                   dict(zip(WIDTHS, item["gammas"])), dict(zip(EXCITED, item["ion_rates"])),
                   item["radiation_regime"], item["field_convention"], item["ion_regime"])


def _sqrt(integer, bits):
    scale = 1 << bits
    floor = isqrt(integer * scale * scale)
    low = Q(floor, scale)
    return low, low if floor * floor == integer * scale * scale else Q(floor + 1, scale)


def radical_midpoint(value, bits):
    low = high = Q(0)
    for root, coefficient in value.terms:
        a, b = _sqrt(root, bits)
        low += coefficient * (a if coefficient >= 0 else b)
        high += coefficient * (b if coefficient >= 0 else a)
    return (low + high) / 2, (high - low) / 2


def _midpoint_matrix(matrix, bits):
    center, error = {}, {}
    for key, value in matrix.items():
        real, er = radical_midpoint(value.real, bits)
        imag, ei = radical_midpoint(value.imag, bits)
        if real or imag:
            center[key] = real, imag
        if er or ei:
            error[key] = er + ei
    return center, error


def _operator_bound(entry_bounds):
    rows, columns = {}, {}
    for (row, column), value in entry_bounds.items():
        rows[row] = rows.get(row, Q(0)) + value
        columns[column] = columns.get(column, Q(0)) + value
    return max((*rows.values(), *columns.values()), default=Q(0))


def _norm(matrix):
    return _operator_bound({key: abs(real) + abs(imag) for key, (real, imag) in matrix.items()})


def _add(matrix, key, real=0, imag=0):
    previous = matrix.get(key, (0, 0))
    value = previous[0] + real, previous[1] + imag
    if value == (0, 0):
        matrix.pop(key, None)
    else:
        matrix[key] = value


def _hermitian(matrix):
    return all(matrix.get((j, i), (0, 0)) == (real, -imag) for (i, j), (real, imag) in matrix.items())


class Generator:
    """Full complex action from generated H and bath-resolved angular jumps."""

    def __init__(self, segment, bits=240):
        if type(segment) is not Segment or type(bits) is not int or not 64 <= bits <= 1024:
            raise ValueError("primitive Segment and dyadic bits in [64,1024] required")
        self.segment, self.bits = segment, bits
        self.h_exact = dipole.hamiltonian(segment.fields_r, segment.fields_c, segment.r, segment.c,
                                         segment.detunings, convention=segment.field_convention)
        self.hamiltonian, uncertainty = _midpoint_matrix(self.h_exact, bits)
        if not _hermitian(self.hamiltonian):
            raise ValueError("generated Hamiltonian is not Hermitian")
        self.h_error = _operator_bound(uncertainty)
        self.generator_difference_bound = 2 * self.h_error
        self.outgoing = [Q(0) for _ in dipole.STATES]
        recycling, unit_records = {}, []
        units = dipole.natural_jumps(segment.radiation_regime, dict.fromkeys(WIDTHS, 1))
        for jump in units:
            rate = segment.gammas[jump.label[:2]]
            if not rate:
                continue
            center, error = _midpoint_matrix(jump.matrix, bits)
            # The generated resolved F'/F/q angular channel has one distinct
            # row and column per magnetic transition.  K=L†L is diagonal;
            # L rho L† still retains all coherent magnetic cross entries.
            if (len({i for i, _ in center}) != len(center) or
                    len({j for _, j in center}) != len(center)):
                raise ValueError("generated resolved angular jump is not a partial weighted permutation")
            delta, midpoint_norm = _operator_bound(error), _norm(center)
            defect = 2 * rate * (2 * midpoint_norm + delta) * delta
            self.generator_difference_bound += defect
            for (target, source), (real, imag) in center.items():
                self.outgoing[source] += rate * (real * real + imag * imag)
                for (other_target, other_source), (other_real, other_imag) in center.items():
                    coefficient = rate * (real * other_real + imag * other_imag)
                    imaginary = rate * (imag * other_real - real * other_imag)
                    key = target, other_target, source, other_source
                    old = recycling.get(key, (Q(0), Q(0)))
                    recycling[key] = old[0] + coefficient, old[1] + imaginary
            unit_records.append({"label": list(jump.label), "rate": str(rate),
                                 "midpoint_operator_bound": str(midpoint_norm), "operator_error_bound": str(delta),
                                 "generator_difference_bound": str(defect)})
        for state, rate in segment.ion_rates.items():
            source = dipole.INDEX[state]
            self.outgoing[source] += rate
            if rate:
                key = dipole.ION, dipole.ION, source, source
                previous = recycling.get(key, (Q(0), Q(0)))
                recycling[key] = previous[0] + rate, previous[1]
        self.recycling = {key: value for key, value in recycling.items() if value != (0, 0)}
        recycled_columns = {}
        for (_, _, i, j), (real, imag) in self.recycling.items():
            recycled_columns[i, j] = recycled_columns.get((i, j), Q(0)) + abs(real) + abs(imag)
        self.norm_bound = 2 * _norm(self.hamiltonian) + max(self.outgoing) + max(recycled_columns.values(), default=Q(0))
        values = [component for pair in self.hamiltonian.values() for component in pair]
        values += [component for pair in self.recycling.values() for component in pair]
        values += [value / 2 for value in self.outgoing]
        self.denominator = lcm(*(value.denominator for value in values))
        self.h_integer = tuple((i, j, int(real * self.denominator), int(imag * self.denominator))
                               for (i, j), (real, imag) in self.hamiltonian.items())
        self.recycle_integer = tuple((*key, int(real * self.denominator), int(imag * self.denominator))
                                     for key, (real, imag) in self.recycling.items())
        self.half_exit_integer = tuple(int(value * self.denominator / 2) for value in self.outgoing)
        self.angular_jump_certificates = unit_records
        self.natural_jump_count = len(unit_records)
        self.ion_jump_count = sum(rate > 0 for rate in segment.ion_rates.values())
        if self.outgoing[dipole.ION] != 0 or any(dipole.ION in key and key != (dipole.ION, dipole.ION)
                                               for key in self.hamiltonian):
            raise ValueError("registered ion sink is not absorbing")
        self._check_trace()

    def _check_trace(self):
        feed = {}
        for (row, column, i, j), coefficient in self.recycling.items():
            if row == column:
                previous = feed.get((i, j), (Q(0), Q(0)))
                feed[i, j] = previous[0] + coefficient[0], previous[1] + coefficient[1]
        for i in range(DIMENSION):
            for j in range(DIMENSION):
                if feed.get((i, j), (0, 0)) != (self.outgoing[i] if i == j else 0, 0):
                    raise ValueError("generated recycling/loss trace identity failed")

    def integer_action(self, matrix):
        result, by_row, by_column = {}, {}, {}
        for (i, j), (real, imag) in matrix.items():
            by_row.setdefault(i, []).append((j, real, imag))
            by_column.setdefault(j, []).append((i, real, imag))
            loss = self.half_exit_integer[i] + self.half_exit_integer[j]
            _add(result, (i, j), -loss * real, -loss * imag)
        for i, j, a, b in self.h_integer:
            for other, real, imag in by_row.get(j, ()):
                _add(result, (i, other), a * imag + b * real, -a * real + b * imag)
            for other, real, imag in by_column.get(i, ()):
                _add(result, (other, j), -a * imag - b * real, a * real - b * imag)
        for i, j, source_i, source_j, a, b in self.recycle_integer:
            real, imag = matrix.get((source_i, source_j), (0, 0))
            _add(result, (i, j), a * real - b * imag, a * imag + b * real)
        return result

    def action(self, matrix):
        denominator = lcm(*(exact(value).denominator for pair in matrix.values() for value in pair)) if matrix else 1
        encoded = {key: tuple(int(exact(value) * denominator) for value in pair) for key, pair in matrix.items()}
        return {key: tuple(Q(value, denominator * self.denominator) for value in pair)
                for key, pair in self.integer_action(encoded).items()}

    def check_all_matrix_units(self):
        for i in range(DIMENSION):
            for j in range(DIMENSION):
                for value in ((1, 0), (0, 1)):
                    action = self.integer_action({(i, j): value})
                    if any(sum(action.get((k, k), (0, 0))[part] for k in range(DIMENSION)) for part in (0, 1)):
                        raise ValueError("full complex matrix-unit trace failure")
        return 2 * COMPLEX_COORDINATES


build_generator = Generator


def initial_densities():
    bridge = dipole.source_qubit_bridge()
    u, d = bridge["u_x"], bridge["d_x"]
    half_root = dipole.sqrt_rational(Q(1, 2))
    positions = set(u) | set(d)
    zero, imaginary = dipole.ComplexRadical(), dipole.ComplexRadical(0, 1)
    vectors = (u, d,
               {i: (u.get(i, zero) + d.get(i, zero)) * half_root for i in positions},
               {i: (u.get(i, zero) + imaginary * d.get(i, zero)) * half_root for i in positions})
    result = []
    for vector in vectors:
        density = {}
        for i, left in vector.items():
            for j, right in vector.items():
                value = left * right.conjugate()
                if value:
                    density[i, j] = value.real.as_rational(), value.imag.as_rational()
        if sum(value[0] for (i, j), value in density.items() if i == j) != 1 or not _hermitian(density):
            raise ValueError("source-produced tomography density is not normalized Hermitian")
        result.append(density)
    return tuple(result)


def _round_nearest(numerator, denominator):
    sign = -1 if numerator < 0 else 1
    quotient, remainder = divmod(abs(numerator), denominator)
    return sign * (quotient + (2 * remainder >= denominator))


def _advance(generator, matrix, dt, quantum, order):
    term, total = matrix, dict(matrix)
    for index in range(1, order + 1):
        divisor = generator.denominator * dt.denominator * index
        term = {key: tuple(_round_nearest(value * dt.numerator, divisor) for value in pair)
                for key, pair in generator.integer_action(term).items()}
        term = {key: pair for key, pair in term.items() if pair != (0, 0)}
        for key, (real, imag) in term.items():
            _add(total, key, real, imag)
        if not term:
            break
    if not _hermitian(total):
        raise ValueError("full Hermitian dyadic rounding failed")
    return total


def _entry_norm(matrix, quantum):
    return Q(sum(abs(real) + abs(imag) for real, imag in matrix.values()), quantum)


def _dyadic_upper(value, bits=16):
    scale = 1 << bits
    return Q(-(-(value.numerator * scale) // value.denominator), scale)


def rounding_error(radius, quantum, order):
    previous = accumulated = Q(0)
    for index in range(1, order + 1):
        # 1089 complex coordinates, each with two <=1/(2Q) component errors.
        previous = radius * previous / index + Q(COMPLEX_COORDINATES, quantum)
        accumulated += previous
    return accumulated


def step_certificate(generator, dt, quantum, order):
    radius = dt * generator.norm_bound
    upper = _dyadic_upper(radius)
    if upper >= order + 2:
        raise ValueError("Taylor tail ratio must be below one")
    return {"step_radius": str(radius), "step_radius_upper": str(upper),
            "tail_factor": str(upper ** (order + 1) / factorial(order + 1) / (1 - upper / (order + 2))),
            "rounding_error": str(rounding_error(upper, quantum, order)),
            "coefficient_error": str(dt * generator.generator_difference_bound)}


def _encode_density(matrix, quantum):
    return [[i, j, str(Q(real, quantum)), str(Q(imag, quantum))]
            for (i, j), (real, imag) in sorted(matrix.items())]


def _source_bindings():
    if _dipole_path.read_bytes() != _dipole_source:
        raise ValueError("loaded angular producer differs from bound source")
    return [{"path": str(path.relative_to(ROOT)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()}
            for path in (Path(__file__).resolve(), _dipole_path)]


def _program_digest(records):
    return hashlib.sha256(json.dumps(records, sort_keys=True, separators=(",", ":")).encode("utf-8")).hexdigest()


def _effect_enclosure(intervals):
    p0, p1, plus, plus_i = intervals
    mean = ((p0[0] + p1[0]) / 2, (p0[1] + p1[1]) / 2)
    real = plus[0] - mean[1], plus[1] - mean[0]
    imag = mean[0] - plus_i[1], mean[1] - plus_i[0]
    encode = lambda values: list(map(str, values))
    return {"00": encode(p0), "11": encode(p1),
            "01": {"real": encode(real), "imag": encode(imag)},
            "10": {"real": encode(real), "imag": encode((-imag[1], -imag[0]))}}


def propagate(segments, bits=240, order=80, norm_cap=4, max_steps=100000):
    if type(segments) not in (list, tuple) or not segments or any(type(item) is not Segment for item in segments):
        raise ValueError("nonempty primitive Segment sequence required")
    if type(bits) is not int or not 64 <= bits <= 1024 or type(order) is not int or not 16 <= order <= 256:
        raise ValueError("dyadic precision/order outside declared range")
    cap = exact(norm_cap)
    if not 0 < cap <= 4 or type(max_steps) is not int or max_steps < 1:
        raise ValueError("positive bounded Taylor controller required")
    quantum = 1 << bits
    states = [{key: tuple(int(value * quantum) for value in pair) for key, pair in matrix.items()}
              for matrix in initial_densities()]
    errors, coefficients, certificates, steps = [Q(0)] * 4, Q(0), [], 0
    for segment in segments:
        generator = Generator(segment, bits)
        ratio = segment.duration * generator.norm_bound / cap
        count = 0 if segment.duration == 0 else max(1, -(-ratio.numerator // ratio.denominator))
        if steps + count > max_steps:
            raise ValueError("declared full-atom step budget exceeded")
        dt = segment.duration / count if count else Q(0)
        certificate = step_certificate(generator, dt, quantum, order)
        tail, rounding = exact(certificate["tail_factor"]), exact(certificate["rounding_error"])
        for _ in range(count):
            for index in range(4):
                errors[index] += _entry_norm(states[index], quantum) * tail + rounding
                states[index] = _advance(generator, states[index], dt, quantum, order)
            steps += 1
        coefficients += segment.duration * generator.generator_difference_bound
        certificates.append({"raw_segment": segment.record(), "steps": count, "dt": str(dt),
                             "liouvillian_entry_norm_bound": str(generator.norm_bound), **certificate,
                             "generator_difference_bound": str(generator.generator_difference_bound),
                             "hamiltonian_operator_error": str(generator.h_error),
                             "angular_jump_certificates": generator.angular_jump_certificates,
                             "natural_jump_count": generator.natural_jump_count, "ion_jump_count": generator.ion_jump_count,
                             "density_centers_after_segment": [_encode_density(state, quantum) for state in states],
                             "numerical_error_bounds_after_segment": list(map(str, errors))})
    tomography, intervals = {}, []
    for name, state, numerical in zip(TOMOGRAPHY, states, errors):
        error = numerical + coefficients
        center = Q(state.get((dipole.ION, dipole.ION), (0, 0))[0], quantum)
        raw = center - error, center + error
        physical = max(Q(0), raw[0]), min(Q(1), raw[1])
        if physical[0] > physical[1]:
            raise ValueError("ion response enclosure has empty CPTP probability intersection")
        trace = Q(sum(state.get((index, index), (0, 0))[0] for index in range(DIMENSION)), quantum)
        tomography[name] = {"density_center": _encode_density(state, quantum),
                            "all_unlisted_density_entries_exact_center_zero": True,
                            "ionization_center": str(center), "ionization_raw_interval": list(map(str, raw)),
                            "ionization_interval": list(map(str, physical)), "trace_center": str(trace),
                            "trace_interval": [str(trace - error), str(trace + error)],
                            "numerical_trace_norm_error": str(numerical), "coefficient_trace_norm_error": str(coefficients),
                            "trace_norm_error_bound": str(error)}
        intervals.append(physical)
    return {"schema": "stage10-full-atomic-forward/v1", "physical_dimension": DIMENSION,
            "complex_density_coordinates": COMPLEX_COORDINATES, "bits": bits, "order": order,
            "norm_cap": str(cap), "steps": steps, "ion_regime": SINK_REGIME,
            "radiation_regimes": [item.radiation_regime for item in segments],
            "initial_state_names": list(TOMOGRAPHY), "tomography": tomography, "J": _effect_enclosure(intervals),
            "hermitian_states_checked": True, "generator_trace_preserving": True,
            "full_phase_and_density_memory_retained": True, "diagonal_ion_effect_assumed": False,
            "error_transport": "Hermitian trace-norm contraction of generated finite Lindblad CPTP channels",
            "rounding_complex_coordinates": COMPLEX_COORDINATES,
            "pulse_certificates": certificates, "source_bindings": _source_bindings(),
            "raw_program_sha256": _program_digest([segment.record() for segment in segments]),
            "actual_hardware_identity_asserted": False}


def verify_certificate(report, segments=None):
    """Check the raw-source Taylor recurrence and error witnesses, without calling propagate."""
    if (report.get("schema") != "stage10-full-atomic-forward/v1" or report.get("physical_dimension") != DIMENSION
            or report.get("complex_density_coordinates") != COMPLEX_COORDINATES
            or report.get("rounding_complex_coordinates") != COMPLEX_COORDINATES
            or report.get("source_bindings") != _source_bindings()):
        raise ValueError("full-atomic certificate identity/source mismatch")
    if (report.get("ion_regime") != SINK_REGIME or report.get("initial_state_names") != list(TOMOGRAPHY)
            or report.get("actual_hardware_identity_asserted") is not False
            or report.get("diagonal_ion_effect_assumed") is not False
            or any(report.get(key) is not True for key in
                   ("hermitian_states_checked", "generator_trace_preserving", "full_phase_and_density_memory_retained"))):
        raise ValueError("full-atomic certificate scope mismatch")
    records = [item["raw_segment"] for item in report["pulse_certificates"]]
    if not records or report.get("raw_program_sha256") != _program_digest(records):
        raise ValueError("full-atomic raw program binding mismatch")
    if segments is not None and records != [segment.record() for segment in segments]:
        raise ValueError("full-atomic certificate belongs to a different raw program")
    bits, order, cap = report["bits"], report["order"], exact(report["norm_cap"])
    if type(bits) is not int or not 64 <= bits <= 1024 or type(order) is not int or not 16 <= order <= 256 or not 0 < cap <= 4:
        raise ValueError("full-atomic certificate controller")
    quantum = 1 << bits
    states = [{key: tuple(int(value * quantum) for value in pair) for key, pair in matrix.items()}
              for matrix in initial_densities()]
    errors, coefficients, steps = [Q(0)] * 4, Q(0), 0
    for certificate in report["pulse_certificates"]:
        segment = Segment.from_record(certificate["raw_segment"])
        generator = Generator(segment, bits)
        ratio = segment.duration * generator.norm_bound / cap
        count = 0 if segment.duration == 0 else max(1, -(-ratio.numerator // ratio.denominator))
        dt = segment.duration / count if count else Q(0)
        expected = step_certificate(generator, dt, quantum, order)
        if (certificate["steps"] != count or exact(certificate["dt"]) != dt or
                exact(certificate["liouvillian_entry_norm_bound"]) != generator.norm_bound or
                any(certificate[key] != value for key, value in expected.items()) or
                certificate["angular_jump_certificates"] != generator.angular_jump_certificates or
                certificate["generator_difference_bound"] != str(generator.generator_difference_bound) or
                certificate["hamiltonian_operator_error"] != str(generator.h_error) or
                certificate["natural_jump_count"] != generator.natural_jump_count or
                certificate["ion_jump_count"] != generator.ion_jump_count):
            raise ValueError("full-atomic source/error certificate mismatch")
        tail, rounding = exact(expected["tail_factor"]), exact(expected["rounding_error"])
        for _ in range(count):
            for index in range(4):
                errors[index] += _entry_norm(states[index], quantum) * tail + rounding
                states[index] = _advance(generator, states[index], dt, quantum, order)
            steps += 1
        coefficients += segment.duration * generator.generator_difference_bound
        if (certificate["density_centers_after_segment"] != [_encode_density(state, quantum) for state in states] or
                certificate["numerical_error_bounds_after_segment"] != list(map(str, errors))):
            raise ValueError("full-atomic center recurrence certificate mismatch")
    intervals = []
    for name, state, numerical in zip(TOMOGRAPHY, states, errors):
        item, error = report["tomography"][name], numerical + coefficients
        center = Q(state.get((dipole.ION, dipole.ION), (0, 0))[0], quantum)
        raw, trace = (center - error, center + error), Q(sum(state.get((i, i), (0, 0))[0] for i in range(DIMENSION)), quantum)
        physical = max(Q(0), raw[0]), min(Q(1), raw[1])
        if (item["density_center"] != _encode_density(state, quantum) or item["trace_norm_error_bound"] != str(error)
                or item["ionization_center"] != str(center) or item["ionization_raw_interval"] != list(map(str, raw))
                or item["ionization_interval"] != list(map(str, physical))
                or item["trace_center"] != str(trace) or item["numerical_trace_norm_error"] != str(numerical)
                or item["coefficient_trace_norm_error"] != str(coefficients)
                or item["all_unlisted_density_entries_exact_center_zero"] is not True
                or item["trace_interval"] != [str(trace - error), str(trace + error)]):
            raise ValueError("full-atomic tomography certificate mismatch")
        intervals.append(physical)
    if (report["steps"] != steps or report["J"] != _effect_enclosure(intervals) or
            report["radiation_regimes"] != [item["radiation_regime"] for item in records]):
        raise ValueError("full-atomic phase readout certificate mismatch")
    return True
