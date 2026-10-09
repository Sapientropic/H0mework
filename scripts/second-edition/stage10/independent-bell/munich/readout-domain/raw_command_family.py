"""Shared atom-location electric transfer, nominal commands, and full CEM instrument.

T is the unknown 3x2 spherical electric-field transfer at the atom.  It is not
a bright-qubit projector or a calibrated laboratory-to-atom bridge.  The two
settings share T, pulse templates, and the stated constant detector regime.
Bob's nested radicals are retained exactly as expressions; rational command
substitution has an explicit source-Hamiltonian Duhamel error.
"""
from dataclasses import dataclass, replace
from fractions import Fraction as Q
import hashlib
from itertools import product
from math import isqrt
from pathlib import Path

import atomic_dipole as dipole
import atomic_full_forward as full

SIDE_ANGLES = {"alice": ("0", "pi/4"), "bob": ("-pi/8", "pi/8")}


def probability(value):
    value = full.exact(value)
    if not 0 <= value <= 1:
        raise ValueError("detector probability outside [0,1]")
    return value


def transfer_matrix(value):
    if type(value) is dict:
        if set(value) != set(dipole.Q_COMPONENTS) or any(type(q) is not int for q in value):
            raise ValueError("all three explicit spherical transfer rows required")
        rows = [value[q] for q in dipole.Q_COMPONENTS]
    elif type(value) in (tuple, list) and len(value) == 3:
        rows = value
    else:
        raise ValueError("raw 3x2 atom-location electric transfer required")
    if any(type(row) not in (tuple, list) or len(row) != 2 for row in rows):
        raise ValueError("two nominal command ports per spherical transfer row required")
    return tuple(tuple(dipole.complex_exact(entry) for entry in row) for row in rows)


def _sqrt_bounds(value, bits):
    value = full.exact(value)
    if value < 0:
        raise ValueError("nonnegative nested radicand required")
    scale = 1 << bits
    floor = isqrt((value.numerator * scale * scale) // value.denominator)
    low = Q(floor, scale)
    high = low if floor * floor * value.denominator == value.numerator * scale * scale else Q(floor + 1, scale)
    return low, high


@dataclass(frozen=True)
class Command:
    angle: str
    exact_expressions: tuple
    coefficients: tuple | None
    bounds: tuple

    @property
    def midpoints(self):
        return tuple((low + high) / 2 for low, high in self.bounds)

    @property
    def radii(self):
        return tuple((high - low) / 2 for low, high in self.bounds)

    def record(self):
        return {"angle": self.angle, "port_convention": "(cos(alpha),-sin(alpha))",
                "exact_expressions": list(self.exact_expressions),
                "exact_radical_coefficients": None if self.coefficients is None else [v.serialize() for v in self.coefficients],
                "outward_bounds": [list(map(str, interval)) for interval in self.bounds],
                "rational_midpoints": list(map(str, self.midpoints))}


def nominal_command(angle, bits=240):
    if type(bits) is not int or not 64 <= bits <= 1024:
        raise ValueError("command dyadic bits in [64,1024] required")
    if angle == "0":
        return Command(angle, ("1", "0"), (dipole.Radical(1), dipole.Radical()), ((Q(1), Q(1)), (Q(0), Q(0))))
    if angle == "pi/4":
        root = dipole.sqrt_rational(Q(1, 2))
        lo, hi = _sqrt_bounds(Q(1, 2), bits)
        return Command(angle, ("sqrt(2)/2", "-sqrt(2)/2"), (root, -root), ((lo, hi), (-hi, -lo)))
    if angle not in ("-pi/8", "pi/8", "+pi/8"):
        raise ValueError("registered nominal command angle required")
    inner_lo, inner_hi = _sqrt_bounds(2, bits)
    cos_lo = _sqrt_bounds((2 + inner_lo) / 4, bits)[0]
    cos_hi = _sqrt_bounds((2 + inner_hi) / 4, bits)[1]
    sin_lo = _sqrt_bounds((2 - inner_hi) / 4, bits)[0]
    sin_hi = _sqrt_bounds((2 - inner_lo) / 4, bits)[1]
    positive = angle == "-pi/8"
    sine = (sin_lo, sin_hi) if positive else (-sin_hi, -sin_lo)
    return Command(angle, ("sqrt(2+sqrt(2))/2", ("" if positive else "-") + "sqrt(2-sqrt(2))/2"),
                   None, ((cos_lo, cos_hi), sine))


def _field(transfer, coefficients):
    return {q: sum((entry * coefficient for entry, coefficient in zip(row, coefficients)), dipole.ComplexRadical())
            for q, row in zip(dipole.Q_COMPONENTS, transfer)}


def _hamiltonian_column_bound(transfer, column, template, bits):
    field = {q: row[column] for q, row in zip(dipole.Q_COMPONENTS, transfer)}
    matrix = dipole.hamiltonian(field, dict.fromkeys(dipole.Q_COMPONENTS, 0), template.r, 0,
                               dict.fromkeys(dipole.MANIFOLDS, 0), convention=template.field_convention)
    midpoint, errors = full._midpoint_matrix(matrix, bits)
    return full._norm(midpoint) + full._operator_bound(errors)


@dataclass(frozen=True)
class CommandProgram:
    transfer: tuple
    command: Command
    segments: tuple
    command_trace_norm_error: Q
    hamiltonian_certificates: tuple

    def record(self):
        return {"transfer": {str(q): [entry.serialize() for entry in row]
                             for q, row in zip(dipole.Q_COMPONENTS, self.transfer)},
                "command": self.command.record(), "segments": [segment.record() for segment in self.segments],
                "command_trace_norm_error": str(self.command_trace_norm_error),
                "hamiltonian_certificates": list(self.hamiltonian_certificates),
                "electronic_reduced_normalization": "atomic_dipole standard 3j-normalised electronic reduced convention"}


def compile_commands(transfer, templates, angle, command_bits=240):
    transfer = transfer_matrix(transfer)
    if type(templates) not in (tuple, list) or not templates or any(type(item) is not full.Segment for item in templates):
        raise ValueError("nonempty primitive Segment templates required")
    if any(any(item.fields_r.values()) for item in templates):
        raise ValueError("template readout field must be an explicit zero placeholder")
    command = nominal_command(angle, command_bits)
    coefficients = command.coefficients if command.coefficients is not None else command.midpoints
    field = _field(transfer, coefficients)
    segments, certificates, error = [], [], Q(0)
    for template in templates:
        segments.append(replace(template, fields_r=field))
        if command.coefficients is None:
            column_bounds = tuple(_hamiltonian_column_bound(transfer, index, template, command_bits) for index in (0, 1))
            delta = sum((radius * norm for radius, norm in zip(command.radii, column_bounds)), Q(0))
        else:
            column_bounds, delta = (Q(0), Q(0)), Q(0)
        payment = 2 * template.duration * delta
        error += payment
        certificates.append({"duration": str(template.duration), "source_column_operator_bounds": list(map(str, column_bounds)),
                             "command_radii": list(map(str, command.radii)), "hamiltonian_substitution_bound": str(delta),
                             "cptp_duhamel_trace_norm_error": str(payment),
                             "exact_command_passed_to_segment": command.coefficients is not None})
    return CommandProgram(transfer, command, tuple(segments), error, tuple(certificates))


@dataclass(frozen=True)
class Interval:
    lo: Q
    hi: Q

    def __post_init__(self):
        object.__setattr__(self, "lo", full.exact(self.lo))
        object.__setattr__(self, "hi", full.exact(self.hi))
        if self.lo > self.hi:
            raise ValueError("ordered exact interval required")

    @classmethod
    def read(cls, values):
        return cls(*values)

    @staticmethod
    def lift(value):
        return value if type(value) is Interval else Interval(value, value)

    def __add__(self, other):
        other = self.lift(other)
        return Interval(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Interval(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -self.lift(other)

    def __rsub__(self, other):
        return self.lift(other) - self

    def __mul__(self, other):
        other = self.lift(other)
        values = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Interval(min(values), max(values))

    __rmul__ = __mul__

    def record(self):
        return [str(self.lo), str(self.hi)]

    def probability_domain(self):
        return Interval(max(Q(0), self.lo), min(Q(1), self.hi))


@dataclass(frozen=True)
class ComplexInterval:
    real: Interval
    imag: Interval

    @staticmethod
    def lift(value):
        return value if type(value) is ComplexInterval else ComplexInterval(Interval.lift(value), Interval(0, 0))

    def __add__(self, other):
        other = self.lift(other)
        return ComplexInterval(self.real + other.real, self.imag + other.imag)

    __radd__ = __add__

    def __neg__(self):
        return ComplexInterval(-self.real, -self.imag)

    def __mul__(self, other):
        other = self.lift(other)
        return ComplexInterval(self.real * other.real - self.imag * other.imag,
                               self.real * other.imag + self.imag * other.real)

    __rmul__ = __mul__

    def conjugate(self):
        return ComplexInterval(self.real, -self.imag)

    def record(self):
        return {"real": self.real.record(), "imag": self.imag.record()}


def expanded_tomography(report, extra_error):
    if (set(report["tomography"]) != set(full.TOMOGRAPHY) or report["initial_state_names"] != list(full.TOMOGRAPHY)
            or report["physical_dimension"] != full.DIMENSION):
        raise ValueError("fixed source-qubit tomography required; qutrit inputs are not projected")
    extra_error = full.nonnegative(extra_error)
    result = {}
    for name in full.TOMOGRAPHY:
        original = report["tomography"][name]
        error = full.exact(original["trace_norm_error_bound"]) + extra_error
        center = full.exact(original["ionization_center"])
        result[name] = {**original, "trace_norm_error_bound": str(error),
                        "command_trace_norm_error": str(extra_error),
                        "trace_interval": [str(full.exact(original["trace_center"]) - error),
                                           str(full.exact(original["trace_center"]) + error)],
                        "ionization_raw_interval": [str(center - error), str(center + error)],
                        "ionization_interval": Interval(center - error, center + error).probability_domain().record()}
    return result


@dataclass(frozen=True)
class DetectorEffect:
    operator: tuple
    coordinates: dict
    ion_effect: dict

    def record(self):
        return {"operator": [[entry.record() for entry in row] for row in self.operator],
                "coordinates": {name: value.record() for name, value in self.coordinates.items()},
                "ion_effect": self.ion_effect,
                "outcome_convention": "0=noclick/dark, 1=click"}


def detector_effect(report, extra_error, d, eta):
    d, eta = probability(d), probability(eta)
    tomography = expanded_tomography(report, extra_error)
    ion = full._effect_enclosure([tuple(map(full.exact, tomography[name]["ionization_interval"])) for name in full.TOMOGRAPHY])
    j00, j11 = Interval.read(ion["00"]), Interval.read(ion["11"])
    real, imag = Interval.read(ion["01"]["real"]), Interval.read(ion["01"]["imag"])
    k = (1 - d) * eta
    diagonal0, diagonal1 = (1 - 2 * d) - 2 * k * j00, (1 - 2 * d) - 2 * k * j11
    off = ComplexInterval(-2 * k * real, -2 * k * imag)
    operator = ((ComplexInterval(diagonal0, Interval(0, 0)), off),
                (off.conjugate(), ComplexInterval(diagonal1, Interval(0, 0))))
    coordinates = {"mu": (1 - 2 * d) - k * (j00 + j11), "u": -2 * k * real,
                   "v": 2 * k * imag, "z": -k * (j00 - j11)}
    return DetectorEffect(operator, coordinates, ion)


def _outcome(effect, outcome):
    if type(outcome) is not int or outcome not in (0, 1):
        raise ValueError("binary source outcome required")
    sign = 1 - 2 * outcome
    return tuple(tuple((ComplexInterval.lift(1 if i == j else 0) + sign * effect.operator[i][j]) * Q(1, 2)
                       for j in range(2)) for i in range(2))


def tensor_born(first, second, h, x, y):
    if type(h) is not int or h not in (0, 1):
        raise ValueError("binary source herald required")
    left, right = _outcome(first, x), _outcome(second, y)
    tensor = tuple(tuple(left[i // 2][j // 2] * right[i % 2][j % 2] for j in range(4)) for i in range(4))
    # The original two Dirac sectors are spectators.  Each retained sector
    # contributes the same singlet/psi+ contraction with weight 1/2.
    cross = Q(2 * h - 1, 2)
    contraction = (tensor[1][1] + tensor[2][2]) * Q(1, 2) + (tensor[1][2] + tensor[2][1]) * cross
    if not contraction.imag.lo <= 0 <= contraction.imag.hi:
        raise ValueError("source tensor Born enclosure lost Hermitian reality")
    return {"raw_interval": contraction.real.record(),
            "probability_interval": contraction.real.probability_domain().record()}


def _density(item):
    return {(i, j): (full.exact(real), full.exact(imag)) for i, j, real, imag in item["density_center"]}


def _scale(matrix, coefficient):
    return {key: tuple(coefficient * value for value in pair) for key, pair in matrix.items() if coefficient and pair != (0, 0)}


def _sum(first, second):
    result = dict(first)
    for key, pair in second.items():
        full._add(result, key, *pair)
    return result


def _encode(matrix):
    return [[i, j, str(real), str(imag)] for (i, j), (real, imag) in sorted(matrix.items())]


def _trace(matrix, *, bound=False):
    return sum((pair[0] for (i, j), pair in matrix.items() if i == j and (not bound or i != dipole.ION)), Q(0))


def post_instrument(report, extra_error, d, eta):
    """Subnormalised click/noclick outputs retain neutral-state memory for next presence."""
    d, eta = probability(d), probability(eta)
    k, result = (1 - d) * eta, {}
    for name, item in expanded_tomography(report, extra_error).items():
        total = _density(item)
        if any((i == dipole.ION) != (j == dipole.ION) for i, j in total):
            raise ValueError("resolved absorbing sink output has forbidden ion-bound coherence")
        ion = {key: pair for key, pair in total.items() if key == (dipole.ION, dipole.ION)}
        bound = {key: pair for key, pair in total.items() if dipole.ION not in key}
        click = _sum(_scale(total, d), _scale(ion, k))
        noclick = _scale(_sum(bound, _scale(ion, 1 - eta)), 1 - d)
        if _sum(ion, bound) != total or _sum(click, noclick) != total:
            raise ValueError("source CEM instrument sum differs from Phi")
        error = full.exact(item["trace_norm_error_bound"])
        branches = {}
        for label, matrix, radius in (("Phi", total, error), ("Phi_ion", ion, error),
                                      ("Phi_bound", bound, error), ("click", click, (d + k) * error),
                                      ("noclick", noclick, (1 - d) * error)):
            trace, presence = _trace(matrix), _trace(matrix, bound=True)
            branches[label] = {"density_center": _encode(matrix), "trace_norm_error_bound": str(radius),
                               "trace_interval": Interval(trace - radius, trace + radius).probability_domain().record(),
                               "bound_presence_trace_interval": Interval(presence - radius, presence + radius).probability_domain().record()}
        result[name] = {"branches": branches, "center_sum_equals_Phi": True,
                        "source_model_sum_equals_Phi": True,
                        "source_rule": "ground-qubit inputs; generated H and resolved jumps preserve bound-plus-ion blocks"}
    return result


def instrument_maps(instrument):
    """The four generated tomography outputs determine each complete qubit-to-atom map."""
    maps = {}
    for branch in ("Phi", "Phi_ion", "Phi_bound", "click", "noclick"):
        items = [instrument[name]["branches"][branch] for name in full.TOMOGRAPHY]
        a, b, plus, plus_i = map(_density, items)
        mean = _scale(_sum(a, b), Q(1, 2))
        real = _sum(plus, _scale(mean, -1))
        imag = _sum(plus_i, _scale(mean, -1))
        # rho_(0+i1) has input 01=-i/2.  Thus Phi(E01)=A+iB
        # with A=Phi(plus)-mean and B=Phi(plus_i)-mean.
        times_i = {key: (-pair[1], pair[0]) for key, pair in imag.items()}
        upper = _sum(real, times_i)
        lower = _sum(real, _scale(times_i, -1))
        if {(j, i): (pair[0], -pair[1]) for (i, j), pair in upper.items()} != lower:
            raise ValueError("generated source matrix-unit images lost Hermitian adjoint relation")
        errors = [full.exact(item["trace_norm_error_bound"]) for item in items]
        maps[branch] = {"00": {"density_center": _encode(a), "trace_norm_error_bound": str(errors[0])},
                        "11": {"density_center": _encode(b), "trace_norm_error_bound": str(errors[1])},
                        "01": {"density_center": _encode(upper), "trace_norm_error_bound": str(sum(errors))},
                        "10": {"density_center": _encode(lower), "trace_norm_error_bound": str(sum(errors))}}
    for key in ("00", "11", "01", "10"):
        if _sum(_density(maps["click"][key]), _density(maps["noclick"][key])) != _density(maps["Phi"][key]):
            raise ValueError("full source instrument matrix-unit sum differs from Phi")
    return maps


def source_bindings():
    root = full.ROOT
    paths = (Path(__file__).resolve(), Path(full.__file__).resolve(), Path(dipole.__file__).resolve())
    return [{"path": str(path.relative_to(root)), "sha256": hashlib.sha256(path.read_bytes()).hexdigest()} for path in paths]


@dataclass(frozen=True)
class SidePrediction:
    side: str
    d: Q
    eta: Q
    programs: tuple
    reports: tuple
    effects: tuple
    instruments: tuple

    def record(self):
        return {"side": self.side, "d": str(self.d), "eta": str(self.eta),
                "input_dimension": 2, "input_basis": ["u_x", "d_x"], "output_atomic_dimension": full.DIMENSION,
                "unknown_transfer_variable_at_atom": True, "constant_detector_regime": True,
                "settings": [{"program": program.record(), "full_atomic_report": report,
                              "dark_effect": effect.record(), "post_instrument": instrument,
                              "qubit_to_atom_instrument_maps": instrument_maps(instrument)}
                             for program, report, effect, instrument in zip(self.programs, self.reports, self.effects, self.instruments)],
                "source_bindings": source_bindings(), "actual_hardware_identity_asserted": False}


def predict_side(side, transfer, templates, d, eta, *, command_bits=240, **propagation_options):
    if side not in SIDE_ANGLES:
        raise ValueError("named Alice or Bob side required")
    d, eta = probability(d), probability(eta)
    programs, reports, effects, instruments = [], [], [], []
    for angle in SIDE_ANGLES[side]:
        program = compile_commands(transfer, templates, angle, command_bits)
        report = full.propagate(program.segments, **propagation_options)
        programs.append(program)
        reports.append(report)
        effects.append(detector_effect(report, program.command_trace_norm_error, d, eta))
        instruments.append(post_instrument(report, program.command_trace_norm_error, d, eta))
    return SidePrediction(side, d, eta, tuple(programs), tuple(reports), tuple(effects), tuple(instruments))


def joint_table(alice, bob):
    if alice.side != "alice" or bob.side != "bob":
        raise ValueError("original ordered Alice/Bob source roles required")
    return [{"h": h, "a": a, "b": b, "x": x, "y": y,
             **tensor_born(alice.effects[a], bob.effects[b], h, x, y)}
            for h, a, b, x, y in product((0, 1), repeat=5)]
