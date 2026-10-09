"""Raw simultaneous lasers in one full-atom rotating frame.

Garthoff 2021 sections 2.3.1 and 2.6.3 use two pump frequencies and shared
fluorescence with sequential cooling masks.  A tone drives every allowed
transition of its D line; a named resonance does not delete off-resonant edges.
The time-dependent source is compiled to existing full33 Segments with a
Hamiltonian Duhamel bound.  Neither a prepared state nor an effect is input.
"""
from dataclasses import dataclass, replace
from fractions import Fraction as Q
from math import comb

import atomic_dipole as dipole
import atomic_full_forward as full
from atomic_modes import complex_exponential
from fluorescence_presence import CounterGenerator, _matrix


ZERO = dipole.ComplexRadical()


def _sum(first, second):
    result = dict(first)
    for key, value in second.items():
        value = result.get(key, ZERO) + value
        if value:
            result[key] = value
        else:
            result.pop(key, None)
    return result


def _scale(matrix, scalar):
    return {key: scalar * value for key, value in matrix.items() if scalar * value}


def _commutator(hamiltonian, matrix):
    left = dipole.matrix_product(hamiltonian, matrix)
    right = dipole.matrix_product(matrix, hamiltonian)
    return _scale(_sum(left, _scale(right, -1)), dipole.ComplexRadical(0, -1))


@dataclass(frozen=True)
class Tone:
    name: str
    line: str
    angular_frequency: Q
    field: dict

    def __post_init__(self):
        if type(self.name) is not str or not self.name or self.line not in dipole.EXCITED_J:
            raise ValueError("named D1 or D2 raw optical tone required")
        object.__setattr__(self, "angular_frequency", full.exact(self.angular_frequency))
        object.__setattr__(self, "field", full._fields(self.field))

    def record(self):
        return {"name": self.name, "line": self.line,
                "angular_frequency_in_common_reciprocal_time_unit": str(self.angular_frequency),
                "field_at_local_time_zero": {str(q): value.serialize() for q, value in self.field.items()},
                "phase": "exp(-i angular_frequency local_time)"}


@dataclass(frozen=True)
class Cell:
    start: Q
    end: Q
    segment: full.Segment
    hamiltonian_error: Q
    trace_norm_error: Q
    tones: tuple

    def record(self):
        return {"start": str(self.start), "end": str(self.end), "midpoint": str((self.start + self.end) / 2),
                "raw_segment": self.segment.record(), "hamiltonian_error": str(self.hamiltonian_error),
                "cptp_duhamel_trace_norm_error": str(self.trace_norm_error),
                "error_scope": "induced trace norm; multiply by input trace norm",
                "tone_bounds": list(self.tones)}


class Programme:
    def __init__(self, base, tones):
        if type(base) is not full.Segment or type(tones) not in (list, tuple) or not tones:
            raise ValueError("one raw atomic base and nonempty raw tone inventory required")
        if any(base.fields_r.values()) or any(base.fields_c.values()):
            raise ValueError("base optical fields must be zero; all lasers enter the tone inventory")
        if any(type(tone) is not Tone for tone in tones) or len({tone.name for tone in tones}) != len(tones):
            raise ValueError("distinct named raw tones required")
        self.base, self.tones = base, tuple(tones)
        self.excitations = tuple(self._excitation(tone) for tone in tones)
        self.static = dipole.hamiltonian(base.fields_r, base.fields_c, base.r, base.c,
                                        base.detunings, convention=base.field_convention)
        self.bath = CounterGenerator(base, threshold=1, background_rate=0,
                                     efficiencies={jump.label: Q(0) for jump in
                                                   dipole.natural_jumps(base.radiation_regime,
                                                                       dict.fromkeys(full.WIDTHS, 1))})

    def _excitation(self, tone):
        result = {}
        reduced = self.base.r if tone.line == "D1" else self.base.c
        for line, q, coefficients in dipole.hamiltonian_terms(self.base.field_convention):
            if line == tone.line:
                result = _sum(result, _scale(coefficients, reduced * tone.field[q]))
        return result

    def hamiltonian_derivative_at_zero(self, order=0):
        if type(order) is not int or order < 0:
            raise ValueError("nonnegative source derivative order required")
        result = dict(self.static) if order == 0 else {}
        for tone, excitation in zip(self.tones, self.excitations):
            factor = dipole.ComplexRadical(1)
            for _ in range(order):
                factor *= dipole.ComplexRadical(0, -tone.angular_frequency)
            forward = _scale(excitation, factor)
            result = _sum(result, _sum(forward, dipole.matrix_adjoint(forward)))
        return result

    def action_derivative_at_zero(self, matrix, order=0):
        """Exact time derivative of the raw generator, retaining all 33 states."""
        if type(order) is not int or order < 0:
            raise ValueError("nonnegative source derivative order required")
        matrix = _matrix(matrix)
        if order == 0:
            static_action = self.bath.atomic_action(matrix)
            optical = _sum(self.hamiltonian_derivative_at_zero(), _scale(self.static, -1))
            return _sum(static_action, _commutator(optical, matrix))
        return _commutator(self.hamiltonian_derivative_at_zero(order), matrix)

    def density_jet_at_zero(self, initial, order):
        """Source recursion rho^(n+1)=sum_k binomial(n,k) G^(k) rho^(n-k)."""
        if type(order) is not int or not 0 <= order <= 64:
            raise ValueError("finite source jet order in [0,64] required")
        initial = _matrix(initial)
        derivatives = [initial]
        for n in range(order):
            value = {}
            for k in range(n + 1):
                value = _sum(value, _scale(self.action_derivative_at_zero(derivatives[n-k], k), comb(n, k)))
            derivatives.append(value)
        return tuple(derivatives)

    def compile_cell(self, start, end, *, bits=160):
        start, end = full.exact(start), full.exact(end)
        if type(bits) is not int or not 64 <= bits <= 1024:
            raise ValueError("dyadic precision in [64,1024] required")
        if not 0 <= start < end <= self.base.duration:
            raise ValueError("positive source interval inside the raw programme required")
        midpoint, halfwidth = (start + end) / 2, (end - start) / 2
        fields = {line: dict.fromkeys(dipole.Q_COMPONENTS, ZERO) for line in dipole.EXCITED_J}
        error, records = Q(0), []
        for tone, excitation in zip(self.tones, self.excitations):
            scalar, phase_error = (complex_exponential(0, -tone.angular_frequency * midpoint, bits=bits)
                                   if tone.angular_frequency else ((Q(1), Q(0)), Q(0)))
            phase = dipole.ComplexRadical(*scalar)
            for q in dipole.Q_COMPONENTS:
                fields[tone.line][q] += tone.field[q] * phase
            centre, remainder = full._midpoint_matrix(excitation, bits)
            norm = full._norm(centre) + full._operator_bound(remainder)
            variation = min(Q(2), abs(tone.angular_frequency) * halfwidth)
            # A exp(-iwt)+A† exp(iwt) changes by at most 2||A|| times the phase error.
            payment = 2 * norm * (variation + phase_error)
            error += payment
            records.append({"name": tone.name, "excitation_operator_norm_upper": str(norm),
                            "phase_variation_upper": str(variation), "scalar_phase_error": str(phase_error),
                            "hamiltonian_error_upper": str(payment)})
        segment = replace(self.base, duration=end-start, fields_r=fields["D1"], fields_c=fields["D2"])
        return Cell(start, end, segment, error, 2 * (end-start) * error, tuple(records))

    def compile_grid(self, cuts, *, bits=160):
        if type(cuts) not in (tuple, list) or len(cuts) < 2:
            raise ValueError("complete finite raw time partition required")
        cuts = tuple(full.exact(value) for value in cuts)
        if cuts[0] != 0 or cuts[-1] != self.base.duration or any(a >= b for a, b in zip(cuts, cuts[1:])):
            raise ValueError("strict partition must cover exactly the whole raw programme")
        return tuple(self.compile_cell(a, b, bits=bits) for a, b in zip(cuts, cuts[1:]))

    def record(self):
        return {"schema": "rb87-raw-multitone-programme/v1", "physical_dimension": full.DIMENSION,
                "base": self.base.record(), "tones": [tone.record() for tone in self.tones],
                "all_allowed_D_line_transitions_retained": True,
                "public_protocol_source": "Garthoff2021 sections 2.3.1 and 2.6.3",
                "raw_frame": "one rotating frame per D line; ground hyperfine and Zeeman energies retained",
                "target_prepared_state_supplied": False, "actual_programme_identified": False,
                "controller_advance": False}
