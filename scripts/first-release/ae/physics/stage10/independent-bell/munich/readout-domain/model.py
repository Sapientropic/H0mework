"""Pure rational points of the full compact, shared-herald source/readout carrier."""
from dataclasses import dataclass
from fractions import Fraction
from itertools import product


def rational(value):
    if isinstance(value, Fraction):
        return value
    if type(value) is int or isinstance(value, str):
        return Fraction(value)
    raise TypeError("Exact rational primitive required")


def bit(value):
    if type(value) is not int or value not in (0, 1):
        raise ValueError("Binary integer required")
    return value


def sign(value):
    return 1 - 2 * bit(value)


@dataclass(frozen=True)
class Effect:
    mu: Fraction
    u: Fraction
    z: Fraction

    def __post_init__(self):
        for name in ("mu", "u", "z"):
            object.__setattr__(self, name, rational(getattr(self, name)))
        length_squared = self.u * self.u + self.z * self.z
        if not (-1 <= self.mu <= 1 and length_squared <= (1 + self.mu)**2 and
                length_squared <= (1 - self.mu)**2):
            raise ValueError("Primitive effect is outside the complete legal readout cone")


@dataclass(frozen=True)
class Instrument:
    alice: tuple
    bob: tuple

    def __post_init__(self):
        for side in (self.alice, self.bob):
            if type(side) is not tuple or len(side) != 2 or any(not isinstance(item, Effect) for item in side):
                raise ValueError("Each side requires its two own-setting effects")


@dataclass(frozen=True)
class Mapping:
    h: int
    a: int
    b: int
    x: int
    y: int

    def __post_init__(self):
        for value in (self.h, self.a, self.b, self.x, self.y):
            bit(value)


IDENTITY = Mapping(0, 0, 0, 0, 0)
MAPPINGS = tuple(Mapping(*values) for values in product(range(2), repeat=5))


def effect_from_axis_errors(axis_x, axis_z, e0, e1):
    ax, az, first_error, second_error = map(rational, (axis_x, axis_z, e0, e1))
    if ax * ax + az * az != 1 or not (0 <= first_error <= 1 and 0 <= second_error <= 1):
        raise ValueError("Legal unit XZ axis and full-square channel errors required")
    gain = 1 - first_error - second_error
    return Effect(second_error - first_error, gain * ax, gain * az)


def source_joint(instrument, h, a, b, x, y):
    h, a, b, x, y = map(bit, (h, a, b, x, y))
    first, second = instrument.alice[a], instrument.bob[b]
    correlation = first.mu * second.mu - sign(h) * first.u * second.u - first.z * second.z
    return (1 + sign(x) * first.mu + sign(y) * second.mu + sign(x) * sign(y) * correlation) / 4


def raw_joint(instrument, mapping, h, a, b, x, y):
    return source_joint(instrument, h ^ mapping.h, a ^ mapping.a, b ^ mapping.b,
                        x ^ mapping.x, y ^ mapping.y)


def full_joint(instrument, mapping=IDENTITY):
    return tuple({"h": h, "a": a, "b": b,
                  "probabilities": tuple(raw_joint(instrument, mapping, h, a, b, x, y)
                                         for x, y in product(range(2), repeat=2))}
                 for h, a, b in product(range(2), repeat=3))


def orbit_member(instrument, mapping):
    alice = tuple(Effect(sign(mapping.x) * instrument.alice[a ^ mapping.a].mu,
                         sign(mapping.x) * sign(mapping.h) * instrument.alice[a ^ mapping.a].u,
                         sign(mapping.x) * instrument.alice[a ^ mapping.a].z) for a in (0, 1))
    bob = tuple(Effect(sign(mapping.y) * instrument.bob[b ^ mapping.b].mu,
                       sign(mapping.y) * instrument.bob[b ^ mapping.b].u,
                       sign(mapping.y) * instrument.bob[b ^ mapping.b].z) for b in (0, 1))
    return Instrument(alice, bob)


def orbit(instrument):
    return tuple((mapping, orbit_member(instrument, mapping)) for mapping in MAPPINGS)


def encode(instrument):
    return {side: [{name: str(getattr(effect, name)) for name in ("mu", "u", "z")} for effect in getattr(instrument, side)]
            for side in ("alice", "bob")}


def decode(document):
    if set(document) != {"alice", "bob"}:
        raise ValueError("Only primitive local effects are admitted")
    sides = []
    for side in ("alice", "bob"):
        if len(document[side]) != 2:
            raise ValueError("Two local settings required")
        effects = []
        for entry in document[side]:
            if set(entry) != {"mu", "u", "z"}:
                raise ValueError("Target probability and extra source parameters are not primitive effects")
            effects.append(Effect(**entry))
        sides.append(tuple(effects))
    return Instrument(*sides)
