"""The checked two-pump coimage enters its own Gaussian output field.

The final constant-excitation phase is never run.  All five Hermitian
tensor terms come from the programme's source-issued phase-index-two mouth.
The field readout is a time-density kernel; its inherited error is therefore
multiplied by the true amplitude operator bounds, not by a TNI coefficient.
Earlier emitted fields and rolling counts retain their source recipe.
"""
from fractions import Fraction as Q
from itertools import product
from math import factorial
from pathlib import Path
import hashlib
import json

import fourier_reference_local_programme_source as programme
import driven_gaussian_field_source as driven
import prepared_retarded_source as tensor

field = driven.field
dipole, full, channel, joint, bsm = driven.dipole, driven.full, driven.channel, driven.joint, driven.bsm
SCHEMA = 'stage10-source-issued-two-pump-Gaussian-field/v1'
_ISSUED = {}
_PROGRAMME_CHECK = programme._GUARD
_FIELD_CHECK = driven._CHECK


def _require(condition, message):
    if not condition:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
            (Path(__file__), *(Path(m.__file__) for m in
              (programme, driven, tensor, programme.factors, dipole, full, channel, joint, bsm)))}


def _price(value, bits):
    return str(field._price_upper(value, bits))


def _mass_upper(parent, bits):
    ready = parent['reference_first_poll_ready']
    state = channel._read_input(ready['generated_first_ready_poststate'], joint.DIMENSION)
    trace = joint._trace(state)
    _require(not trace.imag, 'the original Ready source mass is real')
    centre, rounding = full.radical_midpoint(trace.real, bits)
    return min(Q(1), max(Q(0), centre+rounding+Q(ready['first_poll_joint_error'])))


def _freeze_terms(terms):
    return tuple((tuple(sorted(a.items())), tuple(sorted(b.items()))) for a, b in terms)


def _matrices(terms):
    return tuple((dict(a), dict(b)) for a, b in terms)


def _prefix(source, certificates, templates, bits):
    issued = programme.FourierReferenceLocalProgrammeSource.record(source)
    parent = issued['reference_local_parent']
    _require(type(certificates) in (list, tuple) and len(certificates) == 2 and
             type(templates) in (list, tuple) and len(templates) == 2,
             'both original factor-prefix inventories and source-owned shared templates are required')
    endpoints = [{}, {}]; inventories = []; elapsed = []
    for side, original in enumerate(parent['local_factor_inventory']):
        plan = parent['source_generated_local_plans'][side]
        _require(len(plan) == 3 and all(item['raw_controls']['kind'] == 'preparation' for item in plan[:2]) and
                 plan[2]['raw_controls']['kind'] == 'excitation',
                 'the owned prefix must be two pumps followed by its original excitation role')
        rows = certificates[side]
        _require(type(rows) in (list, tuple) and [r.get('factor_id') for r in rows] == [r['factor_id'] for r in original] and
                 type(templates[side]) in (list, tuple) and len(templates[side]) == 2,
                 'every original factor keeps exactly the two original pump phases')
        generated = []
        for item in rows:
            _require(type(item) is dict and set(item) == {'factor_id', 'complete_phase_certificates'} and
                     type(item['complete_phase_certificates']) in (list, tuple) and len(item['complete_phase_certificates']) == 2,
                     'only the actual two checked pump certificates are consumed')
            face = programme.FourierReferenceLocalProgrammeSource.phase_source(source, side, item['factor_id'],
                       item['complete_phase_certificates'], templates[side])
            raw = programme._FactorPhaseSource.record(face)
            _require(raw['phase_index'] == 2 and raw['source_phase'] == plan[2]['source_phase'],
                     'the next source is the same index-two excitation inlet, not a final prepared target')
            matrix = channel._read_input(raw['complete_initial_local_factor'], full.DIMENSION)
            error = Q(raw['factor_upstream_error'])
            endpoints[side][item['factor_id']] = (matrix, error)
            generated.append({'factor_id': item['factor_id'], 'source_issued_next_phase': raw,
                'prefix_certificate_digests': [_digest(r) for r in item['complete_phase_certificates']]})
        clocks = {Q(row['source_issued_next_phase']['phase_local_elapsed_before_seconds']) for row in generated}
        _require(len(clocks) == 1, 'all signed factors must share the same source pump clock')
        elapsed.append(clocks.pop()); inventories.append(generated)
    old = Q(parent['upstream_trace_norm_error']); total = old; terms = []; prices = []
    for left, right in parent['source_tensor_factor_ids']:
        a, ea = endpoints[0][left]; b, eb = endpoints[1][right]
        payment, na, nb = programme.factors._tensor_price(a, b, ea, eb, bits)
        total += payment; terms.append((a, b))
        prices.append({'source_factor_ids': [left, right], 'local_errors': list(map(str, (ea, eb))),
            'local_norm_upper': list(map(str, (na, nb))), 'tensor_error': str(payment)})
    ready_time = Q(parent['source_ready_physical_clock_seconds'])
    return issued, parent, terms, total, old, inventories, prices, tuple(ready_time+t for t in elapsed)


def _branches(source, word, observation, bits):
    """Pull back the original field's local operators, not another CP model."""
    raw = source._field_record
    driven._word(source._field, word)
    entries = []
    for assignment in product((0, 1), repeat=len(word)):
        if any(Q(e['arrival_seconds'])-Q(raw['flight_seconds'][s]) < Q(raw['emission_origins_seconds'][s]) or
               Q(e['arrival_seconds'])-Q(raw['flight_seconds'][s]) > observation or
               (e['mode'][0] == 'loss' and e['mode'][1]//3 != s)
               for e, s in zip(word, assignment)):
            continue
        a, _ = driven.DrivenGaussianFieldSource._local_word(source._field, 0,
                  [e for e, s in zip(word, assignment) if s == 0], observation, bits)
        b, _ = driven.DrivenGaussianFieldSource._local_word(source._field, 1,
                  [e for e, s in zip(word, assignment) if s == 1], observation, bits)
        entries.append((a, b))
    lower, upper = driven._sqrt_interval(Q(1, factorial(len(word))), bits)
    return tuple(entries), (lower+upper)/2


def _pullback(a, b, terms):
    return tensor._tensor_sandwich(a[0], a[1], b[0], b[1], terms)


class PreparedGaussianFieldSource:
    def __init__(self, source, prefix_certificates, shared_phase_templates, photon_source, *, bits=160):
        _CHECK(); field._closed(source); field._closed(photon_source)
        _require(type(source) is programme.FourierReferenceLocalProgrammeSource and
                 type(photon_source) is driven.DrivenGaussianFieldSource,
                 'closed sequential programme and its same-parent Gaussian field required; rho is not input')
        driven.gaussian._precision(bits)
        field_record = driven.DrivenGaussianFieldSource.record(photon_source)
        original = programme.FourierReferenceLocalProgrammeSource.record(source)['reference_local_parent']
        _require(field_record['reference_local_parent'] == original, 'the real pumps and Gaussian field need the same exact parent')
        _require(all(len(plan) == 3 and all(item['raw_controls']['kind'] == 'preparation' for item in plan[:2]) and
                     plan[2]['raw_controls']['kind'] == 'excitation' for plan in original['source_generated_local_plans']),
                 'this inlet consumes exactly two pump phases then the original index-two excitation role')
        _require(all(leg['original_constant_excitation_controls'] == plan[2] for leg, plan in
                     zip(field_record['Gaussian_source_legs'], original['source_generated_local_plans'])),
                 'Gaussian controls must equal the original index-two excitation drive')
        expected_origins = tuple(Q(original['source_ready_physical_clock_seconds'])+
            sum((Q(p['raw_controls']['duration_seconds']) for p in plan[:2]), Q(0))
            for plan in original['source_generated_local_plans'])
        _require(list(map(str, expected_origins)) == field_record['emission_origins_seconds'],
                 'Gaussian source clocks are Ready plus the two pump durations; old excitation time is excluded')
        _require(all(origin+Q(flight) <= Q(field_record['gate_seconds'][0]) for origin, flight in
                     zip(expected_origins, field_record['flight_seconds'])),
                 'pump-emitted photons can still enter this gate; the short marginal inlet requires their driven field')
        issued, parent, terms, error, old, inventory, prices, origins = _prefix(source, prefix_certificates, shared_phase_templates, bits)
        _require(field_record['reference_local_parent'] == parent and
                 field_record['working_atomic_owner'] == parent['working_atomic_owner'] and
                 field_record['working_common_optical_source'] == parent['working_common_optical_source'] and
                 field_record['working_aperture_source'] == parent['working_aperture_source'],
                 'the real pump coimage, aperture and driven field must have one exact parent')
        _require(list(map(str, origins)) == field_record['emission_origins_seconds'],
                 'Gaussian source clocks are Ready plus the two pump durations; old excitation time is excluded')
        gate_start = Q(field_record['gate_seconds'][0]); flights = tuple(map(Q, field_record['flight_seconds']))
        latest = tuple(a+b for a, b in zip(origins, flights))
        _require(max(latest) <= gate_start,
                 'pump-emitted photons can still enter this gate; the short marginal inlet requires their driven field')
        self._source, self._field = source, photon_source
        self._field_record = _copy(field_record); self._terms = _freeze_terms(terms)
        self._witnesses = (channel._canonical(prefix_certificates), channel._canonical(shared_phase_templates))
        mass = _mass_upper(parent, bits)
        self._value = {'schema': SCHEMA, 'programme_source_record': issued, 'Gaussian_field_source': field_record,
            'reference_local_parent': parent, 'source_issued_two_pump_factor_inlets': inventory,
            'source_tensor_factor_ids': parent['source_tensor_factor_ids'], 'source_tensor_error_records': prices,
            'two_pump_trace_norm_error': _price(error, bits), 'original_Ready_error_once': str(old),
            'two_pump_local_and_tensor_error': _price(error-old, bits),
            'source_positive_mass_upper': _price(mass, bits), 'source_centre_trace_norm_upper': _price(mass+error, bits),
            'source_Gaussian_origins_seconds': list(map(str, origins)),
            'pump_gate_causal_disjointness': {'latest_pump_arrival_seconds': list(map(str, latest)),
                'fixed_gate_start_seconds': str(gate_start), 'continuous_natural_field_has_no_endpoint_atom': True},
            'retained_pump_field_and_queue_mother': {'whole_reference_native_time_and_PC_mother': parent['whole_reference_native_time_and_PC_mother'],
                'raw_pump_phase_sources': [plan[:2] for plan in parent['source_generated_local_plans']],
                'same_optical_source': parent['working_common_optical_source'], 'physical_flight_seconds': list(map(str, flights)),
                'representation': 'source action and photon-arrival recipe; no traced field or arrival trajectory is reconstructed',
                'old_pump_photons_forced_to_vacuum': False, 'persistent_queue_reset': False},
            'native_pending_poststate': parent['native_pending_poststate'],
            'prefix_certificate_inventory_sha256': _digest(prefix_certificates),
            'shared_phase_templates_sha256': _digest(shared_phase_templates),
            'legacy_constant_excitation_executed': False, 'signed_factors_assumed_positive': False,
            'free_prepared_density_or_Bell_target_supplied': False, 'source_scope': 'source-issued two-pump marginal and future Gaussian field after causally disjoint pump arrivals',
            'point_density_old_error_rule': 'Eprefix*(norm(Fbra_centre)+ebra)*(norm(Fket_centre)+eket)',
            'uncomputed_prior_pump_photon_and_queue_recipe_retained': True,
            'scalar_bits': bits, 'source_bindings': _bindings(), 'controller_advance': False}
        self._seal = _digest(self._value)
        _ISSUED[id(self)] = (self._seal, self._terms, self._witnesses)

    def record(self):
        _CHECK(); field._closed(self)
        owned = _ISSUED.get(id(self))
        _require(type(self) is PreparedGaussianFieldSource and set(vars(self)) ==
                 {'_source', '_field', '_field_record', '_terms', '_witnesses', '_value', '_seal'} and owned is not None and
                 self._seal == owned[0] and self._terms is owned[1] and self._witnesses is owned[2] and
                 _digest(self._value) == self._seal and self._value['source_bindings'] == _bindings() and
                 self._field_record == self._value['Gaussian_field_source'] and
                 programme.FourierReferenceLocalProgrammeSource.record(self._source) == self._value['programme_source_record'] and
                 driven.DrivenGaussianFieldSource.record(self._field) == self._field_record,
                 'prepared pump source, actual factor inlets, field clocks or executed source changed')
        return _copy(self._value)

    def source_tensors(self):
        raw = PreparedGaussianFieldSource.record(self)
        return {'source_record': raw, 'tensor_terms': _matrices(self._terms),
            'whole_upstream_trace_norm_error': Q(raw['two_pump_trace_norm_error']),
            'source_centre_trace_norm_upper': Q(raw['source_centre_trace_norm_upper']),
            'source_positive_mass_upper': Q(raw['source_positive_mass_upper']),
            'time_state_mother': raw['retained_pump_field_and_queue_mother'],
            'source_Gaussian_origins_seconds': tuple(map(Q, raw['source_Gaussian_origins_seconds']))}

    def field_state(self, bra_word, ket_word, observation, *, bits=160):
        raw = PreparedGaussianFieldSource.record(self); driven.gaussian._precision(bits)
        time = full.nonnegative(observation)
        bra = driven.DrivenGaussianFieldSource.field_amplitude(self._field, bra_word, time, bits=bits)
        ket = driven.DrivenGaussianFieldSource.field_amplitude(self._field, ket_word, time, bits=bits)
        a = driven.original._matrix(bra['full_pair_operator'], joint.DIMENSION)
        b = driven.original._matrix(ket['full_pair_operator'], joint.DIMENSION)
        na, nb = driven._norm(a, bits), driven._norm(b, bits)
        ea, eb = Q(bra['operator_error_upper']), Q(ket['operator_error_upper'])
        left, wleft = _branches(self, bra_word, time, bits); right, wright = _branches(self, ket_word, time, bits)
        # Independently reconstruct the issuer's complete central operators
        # before using local tensor pullback on the source-born input.
        for branches, weight, expected in ((left, wleft, a), (right, wright, b)):
            complete = {}
            for first, second in branches:
                field._add(complete, driven.original._tensor(first, second), weight)
            _require(complete == expected, 'source local branches disagree with the original complete Gaussian amplitude')
        state = {}; terms = _matrices(self._terms)
        for first in left:
            for second in right:
                field._add(state, _pullback(first, second, terms), wleft*wright)
        inherited = Q(raw['two_pump_trace_norm_error']); norm = Q(raw['source_centre_trace_norm_upper'])
        amplitude_product = (na+ea)*(nb+eb)
        old_payment = inherited*amplitude_product
        curve_payment = norm*(ea*nb+eb*na+ea*eb)
        error = old_payment+curve_payment
        return {'schema': SCHEMA+'/future-field-time-density', 'source_record': raw,
            'physical_observation_seconds': str(time), 'bra_photon_word': _copy(bra_word), 'ket_photon_word': _copy(ket_word),
            'complete_matter_field_kernel': channel._input_record(state), 'trace_norm_kernel_error': _price(error, bits),
            'whole_prefix_error_times_point_amplitude_product': _price(old_payment, bits),
            'finite_field_curve_price_on_source_coimage': _price(curve_payment, bits),
            'point_amplitude_operator_norm_product_upper': _price(amplitude_product, bits),
            'point_kernel_is_integrated_TNI_instrument': False,
            'time_density_degree': [len(bra_word), len(ket_word)],
            'number_and_time_coherence_retained': True, 'legacy_constant_excitation_executed': False,
            'raw_pump_field_and_queue_mother': raw['retained_pump_field_and_queue_mother'],
            'scalar_bits': bits, 'controller_advance': False}

    @classmethod
    def from_record(cls, record, *, prefix_certificates, shared_phase_templates, operator_certificates):
        _require(cls is PreparedGaussianFieldSource and type(record) is dict and record.get('schema') == SCHEMA,
                 'closed prepared Gaussian source and its complete original witnesses required')
        source = programme.FourierReferenceLocalProgrammeSource.from_record(record['programme_source_record'])
        photon = driven.DrivenGaussianFieldSource.from_record(record['Gaussian_field_source'], operator_certificates=operator_certificates)
        prepared = cls(source, prefix_certificates, shared_phase_templates, photon, bits=record['scalar_bits'])
        _require(PreparedGaussianFieldSource.record(prepared) == record, 'source-issued pump coimage or field mother changed')
        return prepared


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None)), repr(getattr(value, '__defaults__', None)), repr(getattr(value, '__kwdefaults__', None))


def _signature():
    functions = (_require, _copy, _digest, _bindings, _price, _mass_upper, _freeze_terms, _matrices, _prefix,
        _branches, _pullback, _function, _signature, _check,
        programme.FourierReferenceLocalProgrammeSource.record, programme.FourierReferenceLocalProgrammeSource.from_record,
        programme.FourierReferenceLocalProgrammeSource.phase_source, programme._FactorPhaseSource.record,
        programme._FactorPhaseSource.verify, programme.factors._tensor_price,
        driven.DrivenGaussianFieldSource.record, driven.DrivenGaussianFieldSource.from_record,
        driven.DrivenGaussianFieldSource._local_word, driven.DrivenGaussianFieldSource.field_amplitude,
        driven._word, driven._sqrt_interval, driven._norm, driven.original._tensor, driven.original._matrix,
        tensor._tensor_sandwich, channel._input_record, channel._read_input, full.radical_midpoint,
        joint._trace, field._closed, field._add, field._price_upper)
    methods = tuple(_function(v) for v in vars(PreparedGaussianFieldSource).values() if callable(v) or isinstance(v, classmethod))
    return tuple(map(_function, functions)), methods, tuple(dipole.STATES), joint.DIMENSION, SCHEMA


def _check():
    if _check is not _CHECK or _check.__code__ is not _CHECK_CODE or _signature is not _SIGNATURE or _signature() != _EXPECTED:
        raise ValueError('prepared Gaussian source execution closure changed')
    if programme._GUARD is not _PROGRAMME_CHECK or driven._CHECK is not _FIELD_CHECK:
        raise ValueError('source issuer checker changed')
    _PROGRAMME_CHECK(); _FIELD_CHECK()


_SIGNATURE = _signature
_CHECK, _CHECK_CODE = _check, _check.__code__
_EXPECTED = _signature()
