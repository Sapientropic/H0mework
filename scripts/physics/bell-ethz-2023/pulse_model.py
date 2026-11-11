"""Independent pulse/phase oracle. Pure matrices; no files, fitting or data access.

Basis: gg, ge, eg, ee. Pauli Y=[[0,-i],[i,0]]. Source convention is
(|eg> + exp(-i*gamma)|ge>)/sqrt(2), exactly the Eq.14 ordering.
"""

from dataclasses import dataclass
import cmath
import math

I = ((1, 0), (0, 1))
X = ((0, 1), (1, 0))
Y = ((0, -1j), (1j, 0))
Z = ((1, 0), (0, -1))
OUTCOMES = ((1, 1), (1, -1), (-1, 1), (-1, -1))
SETTINGS = ((0, 0), (0, 1), (1, 0), (1, 1))
OFFICIAL_CHSH_SIGNS = (1, -1, 1, 1)  # Supplement Eq.7, independently checked by custodian.


def multiply(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(len(b)))
                       for j in range(len(b[0]))) for i in range(len(a)))


def dagger(a):
    return tuple(tuple(complex(a[j][i]).conjugate() for j in range(len(a)))
                 for i in range(len(a[0])))


def tensor(a, b):
    return tuple(tuple(a[i // len(b)][j // len(b[0])] * b[i % len(b)][j % len(b[0])]
                       for j in range(len(a[0]) * len(b[0])))
                 for i in range(len(a) * len(b)))


def apply(a, state):
    return tuple(sum(z * v for z, v in zip(row, state)) for row in a)


def expectation(state, operator):
    return sum(complex(z).conjugate() * v for z, v in zip(state, apply(operator, state)))


def source_state(gamma):
    if not math.isfinite(gamma):
        raise ValueError("source phase must be finite")
    s = 1 / math.sqrt(2)
    return (0, s * cmath.exp(-1j * gamma), s, 0)


@dataclass(frozen=True)
class Pulse:
    phase: float  # Physical azimuth, distinct from an uncalibrated drive register.
    angle: float  # Signed Bloch angle in R=exp(-i*angle*n.sigma/2).

    def __post_init__(self):
        if not all(math.isfinite(v) for v in (self.phase, self.angle)):
            raise ValueError("pulse phase and angle must be finite")

    def matrix(self):
        c, s = math.cos(self.angle / 2), math.sin(self.angle / 2)
        return tuple(tuple(c * I[i][j] - 1j * s *
                           (math.cos(self.phase) * X[i][j] + math.sin(self.phase) * Y[i][j])
                           for j in range(2)) for i in range(2))


@dataclass(frozen=True)
class Station:
    fixed: Pulse
    optional: Pulse
    order: str = "fixed_then_optional"
    setting_xor: int = 0
    output_signs: tuple = (1, 1)  # reported = sign[raw bit] * physical Z outcome.

    def __post_init__(self):
        if self.order not in ("fixed_then_optional", "optional_then_fixed"):
            raise ValueError("unregistered pulse order")
        if self.setting_xor not in (0, 1):
            raise ValueError("setting convention must be a bit bijection")
        if len(self.output_signs) != 2 or any(s not in (-1, 1) for s in self.output_signs):
            raise ValueError("output conventions must specify both raw settings")

    def unitary(self, raw_bit):
        if raw_bit not in (0, 1):
            raise ValueError("setting outside binary domain")
        fixed = self.fixed.matrix()
        optional = self.optional.matrix() if raw_bit ^ self.setting_xor else I
        if self.order == "fixed_then_optional":
            return multiply(optional, fixed)
        return multiply(fixed, optional)

    def observable(self, raw_bit):
        unitary = self.unitary(raw_bit)
        return multiply(multiply(dagger(unitary), Z), unitary)


def quarter_station(physical_phase, *, fixed_sign=1, optional_sign=1,
                    optional_handedness=1, **conventions):
    if any(s not in (-1, 1) for s in (fixed_sign, optional_sign, optional_handedness)):
        raise ValueError("pulse signs/handedness must be +/-1")
    return Station(Pulse(physical_phase, fixed_sign * math.pi / 2),
                   Pulse(physical_phase + optional_handedness * math.pi / 2,
                         optional_sign * math.pi / 2), **conventions)


def drive_station(control_phase, *, zero_phase, phase_handedness=1, rotation_sign=1, **conventions):
    """Explicit drive-to-geometric chart; zero_phase must be supplied, not inferred."""
    return quarter_station(zero_phase + phase_handedness * control_phase,
                           fixed_sign=rotation_sign, optional_sign=rotation_sign,
                           optional_handedness=phase_handedness, **conventions)


def joint_probabilities(gamma, alice, bob, a, b):
    evolved = apply(tensor(alice.unitary(a), bob.unitary(b)), source_state(gamma))
    sa, sb = alice.output_signs[a], bob.output_signs[b]
    return tuple(abs(evolved[2 * (x * sa == -1) + (y * sb == -1)]) ** 2
                 for x, y in OUTCOMES)


def correlations(gamma, alice, bob):
    return tuple(sum(x * y * p for (x, y), p in
                     zip(OUTCOMES, joint_probabilities(gamma, alice, bob, a, b)))
                 for a, b in SETTINGS)


def equatorial_correlation(gamma, alpha, beta):
    return math.cos(beta - alpha + gamma)


def quarter_correlations(gamma, phase_a, phase_b, *, fa=1, oa=1, ha=1, fb=1, ob=1, hb=1):
    """Physical-setting formula, before any setting/readout remapping."""
    if any(s not in (-1, 1) for s in (fa, oa, ha, fb, ob, hb)):
        raise ValueError("pulse signs/handedness must be +/-1")
    c, s = math.cos(gamma + phase_b - phase_a), math.sin(gamma + phase_b - phase_a)
    return (fa * fb * c, -fa * ob * hb * s, oa * ha * fb * s, oa * ob * ha * hb * c)


def chsh(values, signs):
    """The sign functional is mandatory; this does not select one from outcomes."""
    if len(values) != 4 or len(signs) != 4 or any(s not in (-1, 1) for s in signs) or math.prod(signs) != -1:
        raise ValueError("a four-term CHSH sign functional is required")
    return sum(s * value for s, value in zip(signs, values))


def depolarize_and_assign(joint, visibility, fidelity_a, fidelity_b):
    """Specified v-depolarization followed by independent asymmetric channels."""
    parameters = (visibility, *fidelity_a, *fidelity_b)
    if len(fidelity_a) != 2 or len(fidelity_b) != 2:
        raise ValueError("each channel requires F0 and F1")
    if any(not math.isfinite(p) or not 0 <= p <= 1 for p in parameters):
        raise ValueError("channel parameters must be probabilities")
    if len(joint) != 4 or any(not math.isfinite(p) or p < 0 for p in joint) or abs(sum(joint) - 1) > 1e-12:
        raise ValueError("invalid joint probability vector")
    latent = tuple(visibility * p + (1 - visibility) / 4 for p in joint)
    def channel(fidelity, reported, actual):
        correct = fidelity[0 if actual == 1 else 1]
        return correct if reported == actual else 1 - correct
    return tuple(sum(p * channel(fidelity_a, x, u) * channel(fidelity_b, y, v)
                     for p, (u, v) in zip(latent, OUTCOMES)) for x, y in OUTCOMES)
