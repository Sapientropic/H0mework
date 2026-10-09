"""Integrate a source-certified analytic operator curve on its original clock.

Scalar moments keep their physical time scale outside the arithmetic.  The
whole-curve operator price is integrated separately from scalar evaluation;
an endpoint price is never used as a uniform curve certificate.
"""
from dataclasses import dataclass
from fractions import Fraction as Q
from functools import lru_cache

import atomic_dipole as dipole
import atomic_full_forward as full
import atomic_modes as scalar
import b_field_photon_source as photons
import fluorescence_channel as channel


ZERO = (Q(0), Q(0))
_ISSUED = set()


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _source_execution():
    _require(photons._check is photons._CHECK and photons._check.__code__ is photons._CHECK_CODE,
             'physical photon source execution changed')
    photons._CHECK()


def _complex(value):
    _require(type(value) in (tuple, list) and len(value) == 2, 'exact complex exponent required')
    return tuple(map(full.exact, value))


def _norm(value):
    return abs(value[0])+abs(value[1])


def _product(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]


def _inverse(value):
    denominator = value[0]**2+value[1]**2
    _require(denominator > 0, 'nonzero exact exponent required')
    return value[0]/denominator, -value[1]/denominator


def _ceil(value, bits):
    quantum = 1 << bits
    scaled = value*quantum
    return Q(-(-scaled.numerator//scaled.denominator), quantum)


@dataclass(frozen=True)
class Enclosure:
    centre: tuple
    error: Q

    def __post_init__(self):
        object.__setattr__(self, 'centre', _complex(self.centre))
        object.__setattr__(self, 'error', full.nonnegative(self.error))

    def add(self, other):
        return Enclosure(tuple(a+b for a, b in zip(self.centre, other.centre)), self.error+other.error)

    def scale(self, value):
        value = full.exact(value)
        return Enclosure(tuple(value*a for a in self.centre), abs(value)*self.error)

    def multiply(self, other):
        return Enclosure(_product(self.centre, other.centre),
            self.error*_norm(other.centre)+other.error*_norm(self.centre)+self.error*other.error)

    def rounded(self, bits):
        quantum = 1 << bits
        centre = tuple(Q(round(value*quantum), quantum) for value in self.centre)
        price = self.error+sum((abs(a-b) for a, b in zip(centre, self.centre)), Q(0))
        return Enclosure(centre, _ceil(price, bits))


def _exp(value, time, bits):
    a, b = value
    centre, error = scalar.complex_exponential(a*time, b*time, bits=bits, order=min(128, max(48, bits//2)))
    return Enclosure(centre, _ceil(error, bits))


@lru_cache(maxsize=2048)
def _unit_moment(value, degree, start, stop, bits):
    """Integral of x**degree exp(value*x) on a subinterval of [0,1]."""
    radius = _norm(value)
    if not radius:
        return Enclosure((Q(stop**(degree+1)-start**(degree+1), degree+1), Q(0)), Q(0))
    if radius <= Q(1, 2):
        precision = bits+32
        term = Enclosure((Q(1), Q(0)), Q(0))
        total = Enclosure(ZERO, Q(0))
        exponent = Enclosure(value, Q(0))
        power, tail = Q(1), Q(2)
        for k in range(4096):
            weight = (stop**(degree+k+1)-start**(degree+k+1))/(degree+k+1)
            total = total.add(term.scale(weight)).rounded(precision)
            power *= radius/(k+1)
            tail = 2*power
            if tail <= Q(1, 1 << (bits+16)):
                return Enclosure(total.centre, total.error+tail).rounded(bits)
            term = term.multiply(exponent).scale(Q(1, k+1)).rounded(precision)
        raise ValueError('source exponential moment tail did not close')
    # Work at enough guard precision to cover recurrence amplification near
    # the series boundary.  Scalar errors remain explicit at every step.
    growth = Q(1)
    amplification = _norm(_inverse(value))
    for n in range(degree+1):
        growth = max(Q(1), amplification*(2+n*growth))
    guard = max(0, growth.numerator.bit_length()-growth.denominator.bit_length()+2)
    precision = min(1024, bits+32+guard)
    a, b = _exp(value, start, precision), _exp(value, stop, precision)
    inverse = Enclosure(_inverse(value), Q(0))
    result = b.add(a.scale(-1)).multiply(inverse).rounded(precision)
    for n in range(1, degree+1):
        boundary = b.scale(stop**n).add(a.scale(-start**n))
        result = boundary.add(result.scale(-n)).multiply(inverse).rounded(precision)
    return result.rounded(bits)


def exponential_moment(value, degree, start, stop, *, bits=192):
    value = _complex(value)
    a, b = full.nonnegative(start), full.nonnegative(stop)
    _require(type(degree) is int and 0 <= degree <= 64 and a <= b and
             type(bits) is int and 64 <= bits <= 512, 'ordered physical moment and registered degree/precision required')
    _require(value[0]*b <= Q(1, 2), 'mode exceeds the registered growth on its physical clock')
    if a == b:
        return Enclosure(ZERO, Q(0))
    scaled = tuple(z*b for z in value)
    result = _unit_moment(scaled, degree, a/b, Q(1), bits)
    return result.scale(b**(degree+1))


def exponential_triangle(first, second, start, stop, *, inner_start=0, bits=192):
    """Integral exp(first*x+second*t) over start<t<=stop, inner_start<x<=t."""
    first, second = _complex(first), _complex(second)
    a, b, lower = map(full.nonnegative, (start, stop, inner_start))
    _require(lower <= a <= b and type(bits) is int and 64 <= bits <= 512,
             'ordered original first-arrival triangle required')
    if a == b:
        return Enclosure(ZERO, Q(0))
    z, w = tuple(v*b for v in first), tuple(v*b for v in second)
    a, lower = a/b, lower/b
    _require(max(w[0], w[0]+z[0], z[0]*lower) <= Q(1, 2),
             'source triangle exponent exceeds its registered growth')
    if not _norm(z):
        value = _unit_moment(w, 1, a, Q(1), bits).add(
            _unit_moment(w, 0, a, Q(1), bits).scale(-lower))
    elif _norm(z) <= Q(1, 2):
        # A frequency collision is integrated by its series, so division
        # by a nearly zero exponent cannot erase a useful enclosure.
        precision = bits+32
        term, value = Enclosure((Q(1), Q(0)), Q(0)), Enclosure(ZERO, Q(0))
        power, radius = Q(1), _norm(z)
        outer = _unit_moment(w, 0, a, Q(1), precision)
        for k in range(65):
            moment = _unit_moment(w, k+1, a, Q(1), precision).add(outer.scale(-lower**(k+1)))
            value = value.add(term.multiply(moment).scale(Q(1, k+1))).rounded(precision)
            power *= radius/(k+1)
            tail = 4*power*(1-a)
            if tail <= Q(1, 1 << (bits+16)):
                value = Enclosure(value.centre, value.error+tail)
                break
            term = term.multiply(Enclosure(z, Q(0))).scale(Q(1, k+1)).rounded(precision)
        else:
            raise ValueError('source triangle series requires a larger moment degree')
    else:
        precision = bits+32
        joint = tuple(x+y for x, y in zip(z, w))
        direct = _unit_moment(joint, 0, a, Q(1), precision)
        offset = _exp(z, lower, precision).multiply(_unit_moment(w, 0, a, Q(1), precision))
        value = direct.add(offset.scale(-1)).multiply(Enclosure(_inverse(z), Q(0)))
    return value.rounded(bits).scale(b*b)


class OperatorTimeMeasure:
    def __init__(self, leg, certificate):
        _source_execution()
        _require(type(leg) is photons.BFieldPhotonLeg, 'closed physical photon leg required; a curve table is not source input')
        self._leg = leg
        self._certificate = photons._copy(certificate)
        self._curve = photons.BFieldPhotonLeg.exponential_curve(leg, certificate)
        self._seal = photons._digest({'certificate': self._certificate, 'curve': self._curve})
        _ISSUED.add(self._seal)

    def record(self):
        _require(type(self) is OperatorTimeMeasure and set(vars(self)) == {'_leg', '_certificate', '_curve', '_seal'} and
                 self._seal in _ISSUED and
                 self._seal == photons._digest({'certificate': self._certificate, 'curve': self._curve}) and
                 photons.BFieldPhotonLeg.record(self._leg) == self._curve['source_record'],
                 'source operator curve or its physical time mother changed')
        return photons._copy(self._curve)

    def interval(self, start, stop, *, bits=192):
        curve = OperatorTimeMeasure.record(self)
        a, b = full.nonnegative(start), full.nonnegative(stop)
        _require(0 <= a <= b <= Q(curve['duration_seconds']), 'restriction must lie in the original source clock')
        matrix, scalar_price, source_price = {}, Q(0), Q(0)
        for piece in curve['pieces']:
            origin, end = map(Q, piece['source_interval_seconds'])
            left, right = max(a, origin), min(b, end)
            if left >= right:
                continue
            width = Q(piece['piece_duration_seconds'])
            source_price += (right-left)*Q(piece['physical_uniform_operator_error_upper_with_exact_block_phases'])
            for term in piece['complete_physical_operator_terms']:
                exponent = tuple(map(Q, term['lambda_per_second']))
                phase = _exp((Q(0), Q(term['constant_source_phase_angle_radians'])), Q(1), bits)
                quantum = 1 << term['mode_bits']
                for degree, rows in enumerate(term['normalized_polynomial_coefficients']):
                    weight = phase.multiply(exponential_moment(exponent, degree, left-origin, right-origin,
                                                              bits=bits)).scale(1/width**degree)
                    coefficient = {(i, j): dipole.ComplexRadical(Q(r, quantum), Q(s, quantum)) for i, j, r, s in rows}
                    norm = full._operator_bound({key: (abs(v.real.as_rational())+abs(v.imag.as_rational()))
                                                for key, v in coefficient.items()})
                    scalar_price += weight.error*norm
                    factor = dipole.ComplexRadical(*weight.centre)
                    for key, value in coefficient.items():
                        photons.local._add(matrix, key, value*factor)
        return {'schema': 'stage10-source-analytic-operator-time-measure/v1', 'source_curve': curve,
            'restriction_seconds': [str(a), str(b)], 'scalar_bits': bits,
            'complete_operator_integral': channel._input_record(matrix),
            'uniform_curve_integration_error': str(source_price), 'scalar_moment_error': str(scalar_price),
            'operator_norm_error_upper': str(source_price+scalar_price),
            'endpoint_error_used_as_uniform': False, 'probability_measure_asserted': False}


class PhotonTimeMeasure:
    """One original detected photon, integrated at a fixed matter clock."""
    def __init__(self, source, side, certificate):
        _source_execution()
        _require(type(source) is photons.BFieldPhotonSource and type(side) is int and side in (0, 1),
                 'closed two-arm physical photon source and original side required')
        raw = photons.BFieldPhotonSource.record(source)
        leg = source._legs[side]
        _require(certificate['source_record'] == raw['physical_legs'][side] and certificate['sector'] == 'all',
                 'the complete no-jump curve must belong to the same physical arm')
        curve = photons.BFieldPhotonLeg.exponential_curve(leg, certificate)
        _require(len(curve['pieces']) == 1 and curve['pieces'][0]['source_interval_seconds'][0] == '0' and
                 all(len(term['normalized_polynomial_coefficients']) == 1 for term in
                     curve['pieces'][0]['complete_physical_operator_terms']),
                 'this temporal consumer requires one complete constant-coefficient mode family')
        self._source, self._side, self._curve = source, side, curve
        self._certificate = photons._copy(certificate)
        self._seal = photons._digest({'source': raw, 'side': side, 'curve': curve, 'certificate': certificate})
        _ISSUED.add(self._seal)

    def record(self):
        raw = photons.BFieldPhotonSource.record(self._source)
        _require(type(self) is PhotonTimeMeasure and set(vars(self)) == {'_source', '_side', '_curve', '_certificate', '_seal'} and
                 self._seal in _ISSUED and self._seal == photons._digest({
                     'source': raw, 'side': self._side, 'curve': self._curve, 'certificate': self._certificate}) and
                 self._curve['source_record'] == raw['physical_legs'][self._side],
                 'detected photon source, analytic curve or arm changed')
        return photons._copy({'source_record': raw, 'side': self._side, 'source_curve': self._curve})

    def _jump(self, group, port, bits):
        raw = photons.BFieldPhotonSource.record(self._source)
        _require(type(group) in (tuple, list) and type(port) is int and 0 <= port < 4,
                 'original resolved group and physical detector port required')
        transfer = photons.optical._read_matrix(raw['common_optical_source']['generated_four_by_six_transfer'])
        angular, rate, found = {}, None, False
        for item in raw['physical_legs'][self._side]['original_physical_natural_jumps']:
            if tuple(item['group']) != tuple(group):
                continue
            found = True
            amplitude = transfer[port][3*self._side+dipole.Q_COMPONENTS.index(item['q'])]
            current_rate = Q(item['physical_amplitude_squared_per_second'])
            _require(rate is None or rate == current_rate, 'one resolved source environment must have one width')
            rate = current_rate
            photons._add(angular, photons._matrix(item['normalized_natural_jump_operator']), amplitude)
        _require(found, 'resolved radiation group is absent from this original arm')
        value, error = photons._sqrt_rate(rate, bits)
        matrix = {key: entry*value for key, entry in angular.items() if entry*value}
        return matrix, error*photons._operator_bound(angular, bits)

    def interval_column(self, row, column, group, port, start, stop, observation, *, bits=192):
        record = PhotonTimeMeasure.record(self)
        _require(type(row) is int and type(column) is int and 0 <= row < 33 and 0 <= column < 33 and
                 type(bits) is int and 64 <= bits <= 512, 'original full33 matrix-unit column and precision required')
        a, b, tau = map(full.nonnegative, (start, stop, observation))
        source = record['source_record']
        flight = Q(source['flight_seconds'][self._side])
        origin = Q(source['emission_origin_seconds'][self._side])
        _require(origin <= tau and origin+flight <= a <= b <= tau and
                 tau-origin <= Q(self._curve['duration_seconds']),
                 'arrival restriction must be causal and covered by the original matter clock')
        jump, jump_error = PhotonTimeMeasure._jump(self, group, port, bits)
        piece = self._curve['pieces'][0]
        uniform = Q(piece['physical_uniform_operator_error_upper_with_exact_block_phases'])
        modes = []
        for term in piece['complete_physical_operator_terms']:
            _require(term['constant_source_phase_angle_radians'] == '0', 'one source-origin phase chart required')
            quantum = 1 << term['mode_bits']
            matrix = {(i, j): dipole.ComplexRadical(Q(r, quantum), Q(s, quantum))
                      for i, j, r, s in term['normalized_polynomial_coefficients'][0]}
            modes.append((tuple(map(Q, term['lambda_per_second'])), matrix))
        ground, excited = [], []
        for exponent, matrix in modes:
            g = {key: value for key, value in matrix.items()
                 if all(dipole.STATES[i].family == 'ground' for i in key)}
            e = {key: value for key, value in matrix.items()
                 if all(dipole.STATES[i].family in ('D1', 'D2') for i in key)}
            if g:
                ground.append((exponent, g))
            if e:
                excited.append((exponent, e))
        amplitudes = []
        for ge, gm in ground:
            after = _exp(ge, tau-origin, bits)
            for ee, em in excited:
                matrix = dipole.matrix_product(dipole.matrix_product(gm, jump), em)
                if not matrix or not any(j in (row, column) for i, j in matrix):
                    continue
                exponent = tuple(x-y for x, y in zip(ee, ge))
                amplitudes.append((exponent, after, matrix))
        matrix, scalar_price = {}, Q(0)
        for ae, ac, am in amplitudes:
            for be, bc, bm in amplitudes:
                exponent = ae[0]+be[0], ae[1]-be[1]
                prefactor = ac.multiply(Enclosure((bc.centre[0], -bc.centre[1]), bc.error))
                weight = prefactor.multiply(exponential_moment(exponent, 0, a-flight-origin, b-flight-origin, bits=bits))
                left = {(i, 0): value for (i, j), value in am.items() if j == row}
                right = {(i, 0): value for (i, j), value in bm.items() if j == column}
                image = dipole.matrix_product(left, dipole.matrix_adjoint(right))
                scalar_price += weight.error*photons.bsm._entry_norm(image, bits=bits)
                factor = dipole.ComplexRadical(*weight.centre)
                photons._add(matrix, image, factor)
        # True no-jump operators are contractions; projected numerical
        # curves therefore have norm <=1+uniform.  The jump rounding is
        # paid before the physical density kernel is integrated.
        jump_norm = photons._operator_bound(jump, bits)
        norm = (1+uniform)**2*jump_norm
        amplitude_error = (1+uniform)**2*(jump_norm+jump_error)-jump_norm
        kernel_error = amplitude_error*(2*norm+amplitude_error)
        source_price = (b-a)*kernel_error
        zero = a == b or any(dipole.STATES[i].family not in ('D1', 'D2') for i in (row, column))
        if zero:
            matrix, source_price, scalar_price = {}, Q(0), Q(0)
        return {'schema': 'stage10-source-one-photon-arrival-CP-time-column/v1', **record,
            'source_matrix_unit': [row, column], 'resolved_group': list(group), 'physical_port': port,
            'arrival_restriction_seconds': list(map(str, (a, b))), 'physical_observation_seconds': str(tau),
            'complete_matter_poststate': channel._input_record(matrix),
            'uniform_amplitude_error_upper': str(amplitude_error),
            'source_curve_integration_error': str(source_price), 'scalar_integration_error': str(scalar_price),
            'trace_norm_error_upper': str(source_price+scalar_price),
            'same_matter_clock_used_for_all_arrivals': True, 'earlier_arrivals_not_discarded': True,
            'ground_or_ion_source_emits_zero': zero,
            'complete_two_arm_field_mother': source, 'whole_BSM_measure_asserted': False}
