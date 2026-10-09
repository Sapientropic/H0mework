"""The reference Ready clock and optical lambda generate photon time CP.

The centre curve is checked by the original full-Zeeman source.  Its finite
mathematical Gamma enclosure is then paid on the same physical arrival
interval; it is never represented as a second free hardware coordinate.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib

import atomic_dipole as dipole
import atomic_full_forward as full
import b_field_photon_source as photons
import common_optical_readout as optical
import fluorescence_channel as channel
import reference_atomic_clock_source as reference
import reference_local_phase_source as local
import source_mode_time_measure as temporal


SCHEMA = 'stage10-reference-clock-photon-arrival-source/v1'
_ISSUED = set()


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _bindings():
    paths = (Path(__file__), *(Path(module.__file__) for module in
        (dipole, full, photons, optical, channel, reference, local, temporal)))
    return {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def _sqrt_bounds(value, bits):
    centre, error = photons._sqrt_rate(full.nonnegative(value), bits)
    return max(Q(0), centre-error), centre+error


def _clock_payment(raw, source_record, side, group, port, start, stop, observation, bits):
    clock = raw['reference_clock']
    gamma = Q(clock['Gamma_numerical_centre'])
    delta = Q(clock['Gamma_numerical_error'])
    lo, hi = map(Q, clock['angular_Gamma_enclosure_per_second'])
    lo, hi = min(lo, gamma), max(hi, gamma)
    sqrt_lo, _ = _sqrt_bounds(lo, bits)
    sqrt_c_lo, sqrt_c_hi = _sqrt_bounds(gamma, bits)
    _, sqrt_hi = _sqrt_bounds(hi, bits)
    _require(sqrt_lo+sqrt_c_lo > 0, 'positive source Gamma required for its natural amplitude')
    leg = source_record['physical_legs'][side]
    transfer = photons.optical._read_matrix(source_record['common_optical_source']['generated_four_by_six_transfer'])
    angular, width = {}, None
    for item in leg['original_physical_natural_jumps']:
        if tuple(item['group']) != tuple(group):
            continue
        current = Q(item['physical_amplitude_squared_per_second'])/gamma
        _require(width is None or width == current, 'the same resolved source width must be retained')
        width = current
        coefficient = transfer[port][3*side+dipole.Q_COMPONENTS.index(item['q'])]
        photons._add(angular, photons._matrix(item['normalized_natural_jump_operator']), coefficient)
    _require(width is not None, 'resolved group is absent from the reference arm')
    _, width_upper = _sqrt_bounds(width, bits)
    jump_norm = width_upper*photons._operator_bound(angular, bits)
    normalized_k = {key: value*(1/gamma) for key, value in photons._matrix(leg['full_K_per_second']).items()}
    k_norm = photons._operator_bound(normalized_k, bits)
    origin = Q(source_record['emission_origin_seconds'][side])
    age = observation-origin
    operator_price = delta*age*k_norm
    jump_price = delta/(sqrt_lo+sqrt_c_lo)
    amplitude_price = jump_norm*(sqrt_hi*operator_price+jump_price)
    density_price = amplitude_price*jump_norm*(sqrt_hi+sqrt_c_hi)
    price = (stop-start)*density_price
    return {
        'reference_clock': clock, 'resolved_normalized_width': str(width),
        'normalized_jump_operator_norm_upper': str(jump_norm),
        'full_normalized_K_operator_norm_upper': str(k_norm),
        'physical_matter_age_seconds': str(age),
        'reference_no_jump_operator_payment': str(operator_price),
        'reference_sqrt_Gamma_payment': str(jump_price),
        'uniform_reference_amplitude_payment': str(amplitude_price),
        'uniform_reference_density_payment': str(density_price),
        'integrated_reference_clock_payment': str(price),
        'source_law': 'K_Gamma=Gamma*K_normalized; L_Gamma=sqrt(Gamma)*L_normalized',
        'bound': 'width*eA*(sqrtGamma_hi+sqrtGamma_c_hi)*norm(L_normalized)',
        'parameter_error_multiplies_numerical_curve_error': False,
        'mathematical_Gamma_enclosure_is_a_hardware_coordinate': False,
    }


class ReferencePhotonTimeSource:
    def __init__(self, parent, *, flight_seconds, gate_seconds=None):
        _check()
        _require(type(parent) is local.ReferenceLocalPhaseSource,
                 'closed reference Ready/local source required; a prepared density is not input')
        raw = local.ReferenceLocalPhaseSource.record(parent)
        common = optical.CommonOpticalReadout.from_record(raw['working_common_optical_source'])
        ready_time = Q(raw['source_ready_physical_clock_seconds'])
        origins = tuple(ready_time+sum((Q(item['raw_controls']['duration_seconds']) for item in plan), Q(0))
                        for plan in raw['source_generated_local_plans'])
        flights = tuple(map(full.nonnegative, flight_seconds))
        _require(len(flights) == 2, 'two original raw flight coordinates required')
        if gate_seconds is None:
            start = max(t+f for t, f in zip(origins, flights))
            gate_seconds = (start, start+photons.bsm.GATE_SECONDS)
        centre = photons.BFieldPhotonSource(common, flight_seconds=flights,
                                           emission_origin_seconds=origins, gate_seconds=gate_seconds)
        source_record = photons.BFieldPhotonSource.record(centre)
        _require(source_record['common_optical_source'] == raw['working_common_optical_source'] and
                 raw['working_aperture_source']['common_optical_source'] == source_record['common_optical_source'],
                 'reference field must retain the same atomic, optical and aperture lambda')
        self._parent, self._centre = parent, centre
        self._value = {
            'schema': SCHEMA, 'reference_local_parent': raw, 'reference_clock': raw['reference_clock'],
            'reference_centre_field_source': source_record,
            'same_lambda_aperture_source': raw['working_aperture_source'],
            'source_local_emission_origins_seconds': list(map(str, origins)),
            'reference_four_BG_rate_enclosures_per_second': [
                reference._clock_bounds(Q(value), raw['reference_clock'], rate=True)
                for value in source_record['common_optical_source']['background_rates']],
            'BG_used_in_one_photon_signal_CP': False,
            'complete_preparation_then_excitation_plan': raw['complete_preparation_then_excitation_plan'],
            'complete_reference_native_and_pending_mother': raw['whole_reference_native_time_and_PC_mother'],
            'source_bindings': _bindings(), 'controller_advance': False,
        }
        self._seal = photons._digest(self._value)
        _ISSUED.add(self._seal)

    def record(self):
        _check()
        _require(type(self) is ReferencePhotonTimeSource and
                 set(vars(self)) == {'_parent', '_centre', '_value', '_seal'} and
                 self._seal in _ISSUED and self._seal == photons._digest(self._value) and
                 self._value['source_bindings'] == _bindings() and
                 local.ReferenceLocalPhaseSource.record(self._parent) == self._value['reference_local_parent'] and
                 photons.BFieldPhotonSource.record(self._centre) == self._value['reference_centre_field_source'],
                 'same reference clock, physical field, aperture or source mother changed')
        return photons._copy(self._value)

    def interval_column(self, side, certificate, row, column, group, port, start, stop, observation, *, bits=192):
        raw = ReferencePhotonTimeSource.record(self)
        source = raw['reference_centre_field_source']
        measure = temporal.PhotonTimeMeasure(self._centre, side, certificate)
        report = temporal.PhotonTimeMeasure.interval_column(measure, row, column, group, port,
                                                          start, stop, observation, bits=bits)
        a, b, tau = map(full.nonnegative, (start, stop, observation))
        payment = _clock_payment(raw, source, side, group, port, a, b, tau, bits)
        price = Q(payment['integrated_reference_clock_payment'])
        if report['ground_or_ion_source_emits_zero']:
            price = Q(0)
        return {
            'schema': SCHEMA+'/one-photon-CP-column', 'source_record': raw,
            'reference_centre_CP_certificate': report, 'reference_clock_price': payment,
            'complete_matter_poststate': report['complete_matter_poststate'],
            'source_matrix_unit': list((row, column)), 'arrival_restriction_seconds': list(map(str, (a, b))),
            'physical_observation_seconds': str(tau), 'scalar_bits': bits,
            'centre_curve_and_scalar_error': report['trace_norm_error_upper'],
            'integrated_reference_clock_payment': str(price),
            'trace_norm_error_upper': str(Q(report['trace_norm_error_upper'])+price),
            'old_unit_or_old_Ready_relabelled': False, 'whole_BSM_measure_asserted': False,
            'actual_hardware_parameters_identified': False,
        }


def _fingerprint(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _execution():
    functions = (_require, _bindings, _sqrt_bounds, _clock_payment, _fingerprint, _execution, _check,
                 local.ReferenceLocalPhaseSource.record, optical.CommonOpticalReadout.from_record,
                 photons.BFieldPhotonSource.__init__, photons.BFieldPhotonSource.record,
                 photons._sqrt_rate, photons._operator_bound, photons._matrix, photons._add,
                 reference._clock_bounds, temporal.PhotonTimeMeasure.__init__,
                 temporal.PhotonTimeMeasure.record, temporal.PhotonTimeMeasure._jump,
                 temporal.PhotonTimeMeasure.interval_column)
    methods = tuple(_fingerprint(member) for member in vars(ReferencePhotonTimeSource).values() if callable(member))
    return tuple(map(_fingerprint, functions)), methods, SCHEMA


def _check():
    if _check is not _CHECK or _check.__code__ is not _CHECK_CODE or \
       _execution is not _EXECUTION or _execution.__code__ is not _EXECUTION_CODE or _execution() != _EXPECTED:
        raise ValueError('reference photon source execution changed')


_CHECK, _CHECK_CODE = _check, _check.__code__
_EXECUTION, _EXECUTION_CODE = _execution, _execution.__code__
_EXPECTED = _execution()
