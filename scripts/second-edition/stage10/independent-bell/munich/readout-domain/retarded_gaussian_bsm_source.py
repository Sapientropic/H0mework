"""The open-loop detection law in the source's retarded two-arm chart.

One common detector clock indexes two local source times.  The returned
coimage belongs to those retarded times; the later physical atom and its
in-flight field are supplied by the same source dilation, never a reset.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import driven_gaussian_field_source as driven
import retarded_receipt_source as original

gaussian, field = driven.gaussian, driven.field
dipole, full, channel, joint, bsm, optical = (driven.dipole, driven.full, driven.channel,
                                            driven.joint, driven.bsm, driven.optical)
SCHEMA = 'stage10-source-retarded-Gaussian-BSM-GKSL/v1'
_ISSUED = {}
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
              (driven, original, gaussian, dipole, full, channel, joint, bsm, optical)))}


def _add(result, matrix, factor=1):
    field._add(result, matrix, factor)


def _recycle(matrix, first, second):
    side, a = first; other, b = second
    return joint._operator_right(joint._operator_left(matrix, side, a), other, dipole.matrix_adjoint(b))


def _closed_groups(raw):
    groups = {}
    for side, leg in enumerate(raw['physical_legs']):
        for item in leg['original_physical_natural_jumps']:
            group = tuple(item['group']); q = dipole.Q_COMPONENTS.index(item['q'])
            rate = Q(item['physical_amplitude_squared_per_second'])
            values = groups.setdefault(group, {'rate': rate, 'modes': {}})
            _require(values['rate'] == rate and 3*side+q not in values['modes'],
                     'both source arms need the same physical width in each resolved bath')
            values['modes'][3*side+q] = side, gaussian._matrix(item['normalized_natural_jump_operator'])
    return tuple((g, value['rate'], tuple(sorted(value['modes'].items()))) for g, value in sorted(groups.items()))


class RetardedGaussianBSMSource:
    def __init__(self, source):
        _CHECK(); field._closed(source)
        _require(type(source) is driven.DrivenGaussianFieldSource,
                 'closed same-owner Gaussian field and optical source required; K or effects are not input')
        raw = driven.DrivenGaussianFieldSource.record(source)
        common = optical.CommonOpticalReadout.from_record(raw['working_common_optical_source'])
        background = original.PortBackgroundLaw(common)
        bg = original.PortBackgroundLaw.record(background)
        gate = bsm.BSMSource.from_record(bg['raw_BSM_gate'])
        transfer = tuple(tuple(channel._complex_record(v) for v in row) for row in
                         raw['working_common_optical_source']['generated_four_by_six_transfer'])
        _, gram, loss = joint.passive_transfer(transfer)
        groups = _closed_groups(raw)
        self._field, self._gate, self._groups = source, gate, groups
        self._transfer, self._gram, self._loss = transfer, gram, loss
        self._value = {'schema': SCHEMA, 'complete_driven_field_source': raw, 'BG_source': bg,
            'gate_seconds': raw['gate_seconds'],
            'source_local_time_rule': 'u_s=tau-flight_s-emission_origin_s; du_s/dtau=1',
            'retarded_atom_physical_time_rule': 'tau-flight_s',
            'physical_time_atom_state_claimed': False,
            'all_photon_numbers_resummed_by_the_original_marked_GKSL': True,
            'instantaneous_law_keeps_Gaussian_past_operator_certification_horizon': True,
            'finite_operator_bank_error_extrapolated': False,
            'independent_vacuum_baths': True, 'source_scope': 'fixed-flight time-flat optics; original BSM open-loop detection law',
            'no_quantum_feedback_during_this_open_loop': True,
            'resolved_groups': [list(g) for g, _, _ in groups],
            'loss_Gram': [[v.serialize() for v in row] for row in loss],
            'future_atom_field_dilation': 'apply each same-source natural dilation on (tau-flight_s,tau]; keep the resulting in-flight field',
            'pre_gate_input_required': 'source-issued complete unobserved GKSL coimage at each retarded gate-start cut',
            'pre_gate_nonzero_time_replaced_by_input_or_I': False,
            'post_receipt_memory_or_field_reset': False,
            'source_bindings': _bindings(), 'controller_advance': False}
        self._seal = _digest(self._value)
        _ISSUED[id(self)] = self._seal, groups, transfer, gram, loss, gate.record()

    def record(self):
        _CHECK(); field._closed(self)
        owned = _ISSUED.get(id(self))
        _require(type(self) is RetardedGaussianBSMSource and set(vars(self)) ==
                 {'_field', '_gate', '_groups', '_transfer', '_gram', '_loss', '_value', '_seal'} and
                 owned is not None and self._seal == owned[0] and self._groups is owned[1] and
                 self._transfer is owned[2] and self._gram is owned[3] and self._loss is owned[4] and
                 self._gate.record() == owned[5] and _digest(self._value) == self._seal and
                 self._value['source_bindings'] == _bindings() and
                 driven.DrivenGaussianFieldSource.record(self._field) == self._value['complete_driven_field_source'],
                 'retarded source bath, optical transfer, original mark or executed action changed')
        return _copy(self._value)

    def local_times(self, detector_time):
        raw = RetardedGaussianBSMSource.record(self)['complete_driven_field_source']
        time = full.nonnegative(detector_time)
        return tuple(time-Q(a)-Q(b) for a, b in zip(raw['flight_seconds'], raw['emission_origins_seconds']))

    def _drift(self, matrix, times, bits):
        result = {}; error = Q(0)
        for side, time in enumerate(times):
            if time < 0:
                continue
            raw = self._value['complete_driven_field_source']['Gaussian_source_legs'][side]
            h, price = gaussian.GaussianAtomicPulseSource.hamiltonian(self._field._pulses[side], time, bits=bits)
            loss = gaussian._matrix(raw['complete_natural_R_per_second'])
            k = {key: value*dipole.ComplexRadical(0, -1) for key, value in h.items()}
            _add(k, loss, Q(-1, 2))
            _add(result, joint._operator_left(matrix, side, k))
            _add(result, joint._operator_right(matrix, side, dipole.matrix_adjoint(k)))
            error += 2*price
        return result, error

    def _detected(self, matrix, times, port):
        result = {}
        for _, rate, modes in self._groups:
            for mu, first in modes:
                if times[first[0]] < 0:
                    continue
                for nu, second in modes:
                    if times[second[0]] >= 0:
                        coefficient = self._transfer[port][mu]*self._transfer[port][nu].conjugate()*rate
                        if coefficient:
                            _add(result, _recycle(matrix, first, second), coefficient)
        return result

    def _unobserved(self, matrix, times, bits):
        result, scalar_error = RetardedGaussianBSMSource._drift(self, matrix, times, bits)
        for _, rate, modes in self._groups:
            for mu, first in modes:
                if times[first[0]] < 0:
                    continue
                for nu, second in modes:
                    if times[second[0]] >= 0 and self._loss[nu][mu]:
                        _add(result, _recycle(matrix, first, second), rate*self._loss[nu][mu])
        return result, scalar_error

    def independent_atomic_action(self, detector_time, matrix, *, bits=160):
        RetardedGaussianBSMSource.record(self); gaussian._precision(bits)
        times = RetardedGaussianBSMSource.local_times(self, detector_time); matrix = joint._matrix(matrix)
        result, error = RetardedGaussianBSMSource._drift(self, matrix, times, bits)
        for _, rate, modes in self._groups:
            for _, value in modes:
                if times[value[0]] >= 0:
                    _add(result, _recycle(matrix, value, value), rate)
        return result, error

    def marked_action(self, detector_time, state, *, bits=160):
        record = RetardedGaussianBSMSource.record(self); gaussian._precision(bits)
        g0, g1 = map(Q, record['gate_seconds'])
        _require(g0 <= full.nonnegative(detector_time) <= g1,
                 'the original BSM marked law is restricted to its fixed detector gate')
        times = RetardedGaussianBSMSource.local_times(self, detector_time)
        blocks = bsm.BSMSource.blocks(self._gate, state)
        beta = tuple(map(Q, record['BG_source']['BG_rates_per_second']))
        result = {}; source_error = Q(0)
        for mark, matrix in blocks.items():
            stay, error = RetardedGaussianBSMSource._unobserved(self, matrix, times, bits)
            source_error += error*bsm._entry_norm(matrix, bits=bits)
            _add(stay, matrix, -sum(beta, Q(0)))
            for port in range(4):
                move = RetardedGaussianBSMSource._detected(self, matrix, times, port)
                _add(move, matrix, beta[port])
                target = bsm.BSMSource.target(self._gate, mark, port)
                _add(result, {(target, i, j): value for (i, j), value in move.items()})
            _add(result, {(mark, i, j): value for (i, j), value in stay.items()})
        return result, field._price_upper(source_error, bits)

    def pending_action_and_flux(self, detector_time, state, *, bits=160):
        result, error = RetardedGaussianBSMSource.marked_action(self, detector_time, state, bits=bits)
        pending = {}; flux = [{}, {}, {}, {}]
        for (mark, i, j), value in result.items():
            if mark.receipt is None:
                _add(pending, {(mark, i, j): value})
            else:
                _add(flux[mark.receipt], {(i, j): value})
        _require(all(mark.receipt is None for mark in bsm.BSMSource.blocks(self._gate, state)),
                 'first-receipt flux consumes only the complete original pending mother')
        return {'source_record': RetardedGaussianBSMSource.record(self), 'physical_detector_seconds': str(detector_time),
                'retarded_local_source_seconds': list(map(str, RetardedGaussianBSMSource.local_times(self, detector_time))),
                'pending_generator': pending, 'four_pattern_retarded_flux': flux,
                'scalar_generator_trace_norm_error_per_second': str(error),
                'physical_time_atom_state_claimed': False, 'source_bindings': _bindings()}


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    helpers = (_require, _copy, _digest, _bindings, _add, _recycle, _closed_groups, _function, _signature, _check,
        driven.DrivenGaussianFieldSource.record, gaussian.GaussianAtomicPulseSource.hamiltonian,
        gaussian._matrix, gaussian._precision, original.PortBackgroundLaw.record,
        optical.CommonOpticalReadout.from_record, joint.passive_transfer, joint._matrix,
        joint._operator_left, joint._operator_right, bsm.BSMSource.blocks, bsm.BSMSource.target,
        bsm.BSMSource.record, bsm.BSMSource.from_record,
        bsm._entry_norm, field._price_upper, field._closed, field._add, dipole.matrix_adjoint)
    methods = tuple(_function(v) for v in vars(RetardedGaussianBSMSource).values() if callable(v) or isinstance(v, classmethod))
    return tuple(map(_function, helpers)), methods, SCHEMA, joint.DIMENSION


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
             driven._CHECK is _FIELD_CHECK, 'retarded Gaussian source execution closure changed')
    _FIELD_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
