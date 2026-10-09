"""Source-owned decreasing Gaussian tails supplement the original jet.

After an active leg's original pulse centre, the candidate may omit its
drive.  The physical drive and every original column remain in the law;
its residual is paid by the source's actual envelope tail integral.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib

import retarded_frequency_clustered_certificate as clustered

checked, trajectory, gaussian, full = clustered.checked, clustered.trajectory, clustered.gaussian, clustered.full
SCHEMA = 'stage10-original-retarded-decreasing-Gaussian-tail-descriptors/v1'
_CLUSTER_CHECK = clustered._CHECK
POLICIES = ('source_tail', 'original_jet')


def _require(value, message):
    if not value:
        raise ValueError(message)


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__), *(Path(m.__file__) for m in (clustered, checked, trajectory, gaussian)))}


def policy(value):
    _require(type(value) is str and value in POLICIES, 'named original Gaussian residual policy required')
    return {'name': value, 'tail_regime': 'active local start >= original pulse centre + 8 sigma upper',
        'tail_integral': 'original envelope from local cut to infinity',
        'original_drive_is_retained': True, 'actual_turnoff_command_inferred': False,
        'tail_integral_divided_by_width_is_uniform_bound': False,
        'polynomial_weight_bound': 'oppositely monotone Chebyshev: integral(a*u^n) <= integral(a)/(n+1)',
        'whole_mode_growth_factor_upper': '2'}


def weighted_tail_price(integral, image_norm, column_error, phase_error, degree):
    _require(type(degree) is int and degree >= 0, 'nonnegative complete polynomial degree required')
    values = tuple(map(full.nonnegative, (integral, image_norm, column_error, phase_error)))
    # On [0,1], a is decreasing and u^n increasing.  Their double-integral
    # covariance is nonpositive, so integral(a*u^n) <= integral(a)/(n+1).
    # Re(lambda)*width <= 1/2 supplies the independent growth bound < 2.
    return 2*values[0]*sum(values[1:], Q(0))/Q(degree+1)


def _clock(source, start, stop):
    trajectory.RetardedGaussianTrajectorySource.record(source)
    _, active = trajectory.RetardedGaussianTrajectorySource._clock(source, start)
    trajectory.RetardedGaussianTrajectorySource._clock(source, stop)
    raw = source._value['retarded_source']['complete_driven_field_source']
    births = tuple(Q(a)+Q(b) for a, b in zip(raw['emission_origins_seconds'], raw['flight_seconds']))
    _require(start < stop and not any(start < birth < stop for birth in births),
             'partition the original arm activation boundary')
    return raw, births, tuple(active)


def _tail_cut(leg, bits):
    sigma = Q(leg['sigma_squared_seconds'])
    _require(sigma > 0, 'positive original Gaussian variance required')
    _, upper = full._sqrt(sigma.numerator*sigma.denominator, bits)
    return Q(leg['centre_seconds'])+8*upper/sigma.denominator


def _tail(source, raw, births, active, start, side, bits):
    local = max(Q(0), start-births[side])
    pulse = source._law._field._pulses[side]
    leg = raw['Gaussian_source_legs'][side]
    _require(gaussian.GaussianAtomicPulseSource.record(pulse) == leg,
             'the tail must belong to the very original retarded pulse')
    cut = _tail_cut(leg, bits)
    if not active[side] or local < cut:
        return None
    receipt = gaussian.GaussianAtomicPulseSource.field_off_tail_price(pulse, local, bits=bits)
    _require(receipt['Gaussian_tail_set_to_zero'] is False and
             receipt['actual_field_off_command_identified'] is False, 'original nonzero Gaussian tail required')
    return {'source_side': side, 'source_local_cut_seconds': str(local),
        'source_pulse_centre_seconds': leg['centre_seconds'], 'original_tail_integral_receipt': receipt,
        'source_generated_eight_sigma_tail_cut_seconds': str(cut),
        'original_tail_integral_seconds_upper': receipt['field_envelope_tail_integral_seconds_upper'],
        'candidate_drive_polynomial_is_zero': True, 'physical_source_drive_set_to_zero': False,
        'drive_registered_as_source_zero': False, 'local_envelope_is_monotone_decreasing': True,
        'Gaussian_jet_generated_for_this_leg': False}


def descriptors(source, columns, start, stop, states, envelope_order, *, tail_policy='source_tail'):
    _CHECK(); policy(tail_policy)
    _require(type(columns) is clustered.integer.IntegerColumns and columns.source is source,
             'same original full integer columns required')
    columns._closed()
    if tail_policy == 'original_jet':
        active, original = checked._descriptors(source, columns, start, stop, states, envelope_order)
        return active, original, {}
    raw, births, active = _clock(source, start, stop); width = stop-start
    omega = tuple(Q(leg['carrier_angular_frequency_per_second']) for leg in raw['Gaussian_source_legs'])
    answer = []; tails = {}
    for component in trajectory.COMPONENTS:
        if component == 'quiet':
            answer.append((component, Q(0), [(Q(1), Q(0))], Q(0), False)); continue
        if component[0] == 'drive':
            tail = _tail(source, raw, births, active, start, component[1], columns.bits)
            if tail is not None:
                tails[component] = tail
                answer.append((component, Q(0), [(Q(0), Q(0))], Q(0), False)); continue
        zero = all(columns.action(component, matrix, active)[2] for matrix in states)
        if zero:
            answer.append((component, Q(0), [(Q(0), Q(0))], Q(1), True)); continue
        if component[0] == 'drive':
            side = component[1]; local = max(Q(0), start-births[side])
            coefficients, radius = gaussian._envelope_polynomial(raw['Gaussian_source_legs'][side],
                local, width, envelope_order, columns.bits)
            answer.append((component, Q(0), [(v, Q(0)) for v in coefficients], radius, False))
        else:
            side, other = component[1:]; frequency = omega[other]-omega[side]
            angle = -omega[side]*(start-births[side])+omega[other]*(start-births[other])
            centre, radius = gaussian._exponential(Q(0), angle, columns.bits)
            answer.append((component, frequency, [centre], radius, False))
    return active, answer, tails


def candidate_scalars(source, start, stop, order, envelope_order, *, tail_policy='source_tail'):
    _CHECK(); policy(tail_policy)
    raw, births, active = _clock(source, start, stop); width = stop-start
    omega = tuple(Q(leg['carrier_angular_frequency_per_second']) for leg in raw['Gaussian_source_legs'])
    answer = []
    for component in trajectory.COMPONENTS:
        if component == 'quiet':
            frequency = Q(0); polynomial = [complex(1)]
        elif component[0] == 'drive':
            side = component[1]; local = max(Q(0), start-births[side]); frequency = Q(0)
            if not active[side] or (tail_policy == 'source_tail' and
                    local >= _tail_cut(raw['Gaussian_source_legs'][side], source._value['scalar_bits'])):
                polynomial = [complex(0)]
            else:
                coefficients, _ = gaussian._envelope_polynomial(raw['Gaussian_source_legs'][side],
                    local, width, envelope_order, source._value['scalar_bits'])
                polynomial = [complex(float(value)) for value in coefficients]
        else:
            side, other = component[1:]; frequency = omega[other]-omega[side]
            angle = -omega[side]*(start-births[side])+omega[other]*(start-births[other])
            centre, _ = gaussian._exponential(Q(0), angle, source._value['scalar_bits'])
            polynomial = [complex(float(centre[0]), float(centre[1]))]
        exponential = [complex(1)]
        for n in range(1, order+1):
            exponential.append(exponential[-1]*complex(0, float(frequency*width))/n)
        scalars = [sum(polynomial[k]*exponential[n-k] for k in range(min(n+1, len(polynomial))))
                   for n in range(order+1)]
        answer.append((component, scalars))
    return active, answer


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    return tuple(map(_function, (_require, _bindings, policy, weighted_tail_price, _clock, _tail_cut, _tail,
        descriptors, candidate_scalars, _function, _signature, _check,
        gaussian.GaussianAtomicPulseSource.record, gaussian.GaussianAtomicPulseSource.field_off_tail_price,
        gaussian._envelope_polynomial, gaussian._exponential, checked._descriptors,
        full._sqrt,
        clustered.integer.IntegerColumns.action, clustered.integer.IntegerColumns._closed,
        trajectory.RetardedGaussianTrajectorySource.record, trajectory.RetardedGaussianTrajectorySource._clock))), SCHEMA, POLICIES


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
             clustered._CHECK is _CLUSTER_CHECK, 'source Gaussian tail descriptor execution changed')
    _CLUSTER_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
