"""One passive four-port readout generates native fluorescence and BSM sources.

Garthoff 2021 sec.2.6.3 pp31-33 binds both loading fluorescence paths to the
same BSM detectors.  This producer fixes the corresponding shared raw optical
parameters.  It retains the existing frequency-flat instantaneous model;
resolved spectral transmission and the two-arm propagation kernel are separate
source responsibilities.
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import apd_window_history as apd
import atom_photon_source as optics
import bsm_retry_source as bsm
import fluorescence_channel as channel
import joint_fluorescence_presence as joint
import munich_atomic_programme as atomic
import persistent_reload_source as persistent
import trap_reload_source as trap


SCHEMA = 'stage10-common-native-BSM-four-port-optical-source/v1'
ALL_PORTS = (True, True, True, True)
PUBLIC_SOURCE = {
    'url': 'https://edoc.ub.uni-muenchen.de/28956/1/Garthoff_Robert_Sebastian.pdf',
    'sha256': '730f2cf60ce7a58fe8433e3e4b9d5c242584837aa63ba417bd74bf5286338f91',
    'section': '2.6.3', 'printed_pages': [31, 32, 33], 'figure': '2.14',
    'hardware_relation': 'both traps send loading fluorescence to the same BSM detectors',
    '2016_arrival_gate_seconds': '3/25000000',
    '2021_208ns_not_substituted': True}


def _copy(value):
    return json.loads(channel._canonical(value))


def _matrix(matrix):
    return [[value.serialize() for value in row] for row in matrix]


def _read_matrix(record):
    return tuple(tuple(channel._complex_record(value) for value in row) for row in record)


def _mask(value):
    channel._require(type(value) is tuple and len(value) == 4 and all(type(bit) is bool for bit in value),
                     'four physical detector-port bits required; an atom/arm mask is not a port mask')
    return value


def _bindings():
    return {Path(module.__file__).name: hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
            for module in (apd, optics, bsm, channel, joint, atomic, persistent, trap)} | {
            Path(__file__).name: hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}


class CommonOpticalReadout:
    def __init__(self, owner, *, collection_a, collection_b, splitter, efficiencies, background_rates):
        channel._require(type(owner) is atomic.MunichAtomicProgramme,
                         'one closed common atomic owner required; a target jump is not input')
        owner = atomic.MunichAtomicProgramme.from_record(atomic.MunichAtomicProgramme.record(owner))
        gate, _ = atomic.MunichAtomicProgramme.bsm_gate(owner, collection_a=collection_a,
            collection_b=collection_b, splitter=splitter, efficiencies=efficiencies, background_rates=background_rates)
        transfer = bsm.optical_transfer(*gate.collections, gate.splitter, gate.efficiencies)
        self._record = {'schema': SCHEMA, 'common_atomic_owner': owner.record(),
            'collection_a': _matrix(gate.collections[0]), 'collection_b': _matrix(gate.collections[1]),
            'splitter': _matrix(gate.splitter), 'efficiencies': list(map(str, gate.efficiencies)),
            'background_rates': list(map(str, gate.background_rates)), 'physical_ports': [list(port) for port in bsm.PORTS],
            'generated_four_by_six_transfer': _matrix(transfer), 'public_hardware_source': _copy(PUBLIC_SOURCE),
            'shared_parameters': 'same collections, splitter, four efficiencies and four port backgrounds in every readout',
            'native_observation': 'sum selected physical detector ports; no which-atom label',
            'model_scope': 'frequency-flat instantaneous passive six-mode transfer',
            'uncovered_source_coordinates': ['resolved spectral transmission of D1/other frequency modes',
                                           'two-arm time/phase propagation and photon flight',
                                           'field-dependent extra stray-light backgrounds'],
            'actual_optical_calibration_identified': False, 'actual_port_mask_identified': False,
            'source_bindings': _bindings(), 'controller_advance': False}
        self._seal = channel._canonical(self._record)

    def record(self):
        if _guard is not _GUARD_FUNCTION or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('common optical source execution guard changed')
        _guard()
        channel._require(type(self) is CommonOpticalReadout and set(vars(self)) == {'_record', '_seal'} and
                         channel._canonical(self._record) == self._seal and self._record['source_bindings'] == _bindings(),
                         'shared optical source, parameters or callback changed')
        return _copy(self._record)

    @classmethod
    def from_record(cls, record):
        channel._require(cls is CommonOpticalReadout and type(record) is dict and record.get('schema') == SCHEMA,
                         'closed shared optical source record required')
        result = cls(atomic.MunichAtomicProgramme.from_record(record['common_atomic_owner']),
            collection_a=_read_matrix(record['collection_a']), collection_b=_read_matrix(record['collection_b']),
            splitter=_read_matrix(record['splitter']), efficiencies=tuple(record['efficiencies']),
            background_rates=tuple(record['background_rates']))
        channel._require(result.record() == record, 'common owner, shared transfer, port noise or scope changed')
        return result

    def _parameters(self, port_mask):
        record, mask = CommonOpticalReadout.record(self), _mask(port_mask)
        transfer = _read_matrix(record['generated_four_by_six_transfer'])
        selected = tuple(tuple(value if enabled else value*0 for value in row)
                         for enabled, row in zip(mask, transfer))
        background = sum((Q(rate) for enabled, rate in zip(mask, record['background_rates']) if enabled), Q(0))
        joint.passive_transfer(selected)
        return selected, background

    def _native_report(self, model, port_mask, source):
        record = CommonOpticalReadout.record(self)
        transfer, background = CommonOpticalReadout._parameters(self, port_mask)
        return {'schema': SCHEMA+'/native', 'common_optical_source': record, 'port_mask': list(port_mask),
            'selected_transfer': _matrix(transfer), 'selected_background_rate': str(background),
            'unmerged_four_background_rates': record['background_rates'],
            'owned_native_cell': model, 'raw_shared_counter_source': source.record(),
            'background_added_once': True, 'which_atom_information_added': False,
            'physical_port_addresses_preserved': True, 'controller_advance': False}

    def base_counter(self, duration, *, threshold=1, port_mask=ALL_PORTS):
        record = CommonOpticalReadout.record(self)
        owner = atomic.MunichAtomicProgramme.from_record(record['common_atomic_owner'])
        base = atomic.MunichAtomicProgramme.atomic_base(owner)
        transfer, background = CommonOpticalReadout._parameters(self, port_mask)
        source = joint.JointCounterGenerator(*(atomic.AtomicBase.segment(base, side, duration) for side in (0, 1)),
                    threshold=threshold, background_rate=background, collection=transfer)
        return source, CommonOpticalReadout._native_report(self, None, port_mask, source)

    def native_cell(self, first, second, cuts, cell_index, *, threshold=1, port_mask=ALL_PORTS, compilation_bits=160):
        record = CommonOpticalReadout.record(self)
        owner = atomic.MunichAtomicProgramme.from_record(record['common_atomic_owner'])
        transfer, background = CommonOpticalReadout._parameters(self, port_mask)
        source, model = atomic.MunichAtomicProgramme.native_cell(owner, first, second, cuts, cell_index,
                  threshold=threshold, background_rate=background, collection=transfer, bits=compilation_bits)
        return source, CommonOpticalReadout._native_report(self, model, port_mask, source)

    def apd_cell(self, first, second, cuts, cell_index, *, threshold=1, port_mask=ALL_PORTS,
                 maximum_threshold=None, compilation_bits=160):
        record = CommonOpticalReadout.record(self)
        owner = atomic.MunichAtomicProgramme.from_record(record['common_atomic_owner'])
        transfer, background = CommonOpticalReadout._parameters(self, port_mask)
        source = apd.APDWindowHistorySource.from_atomic_cell(owner, first, second, cuts, cell_index,
                   threshold=threshold, background_rate=background, collection=transfer,
                   maximum_threshold=maximum_threshold, compilation_bits=compilation_bits)
        model = source.record()['owned_atomic_cell']
        raw = joint.JointCounterGenerator.from_record(source.record()['original_shared_source'])
        report = CommonOpticalReadout._native_report(self, model, port_mask, raw)
        report['schema'] = SCHEMA+'/APD'
        report['raw_APD_source'] = source.record()
        return source, report

    def bsm_gate(self, *, compilation_bits=160):
        record = CommonOpticalReadout.record(self)
        owner = atomic.MunichAtomicProgramme.from_record(record['common_atomic_owner'])
        source, model = atomic.MunichAtomicProgramme.bsm_gate(owner,
            collection_a=_read_matrix(record['collection_a']), collection_b=_read_matrix(record['collection_b']),
            splitter=_read_matrix(record['splitter']), efficiencies=tuple(record['efficiencies']),
            background_rates=tuple(record['background_rates']), bits=compilation_bits)
        return source, {'schema': SCHEMA+'/BSM', 'common_optical_source': record,
            'owned_BSM_gate': model, 'raw_BSM_source': source.record(),
            'compilation_bits': compilation_bits,
            'four_port_backgrounds_added_in_original_BSM_once': True,
            'original_2016_gate_seconds': str(bsm.GATE_SECONDS), 'controller_advance': False}

    def persistent_source(self, *, reservoir_occupations, capture_couplings, drives, rules,
                          poll_period_seconds, poll_phase_seconds, field_phase_origin_seconds,
                          maximum_cell_seconds, phase_policy, arrival_poll_order,
                          port_mask=ALL_PORTS, compilation_bits=160):
        record = CommonOpticalReadout.record(self)
        owner = atomic.MunichAtomicProgramme.from_record(record['common_atomic_owner'])
        transfer, background = CommonOpticalReadout._parameters(self, port_mask)
        source = persistent.PersistentReloadSource(owner, reservoir_occupations=reservoir_occupations,
            capture_couplings=capture_couplings, drives=drives, rules=rules,
            background_rate=background, collection=transfer, poll_period_seconds=poll_period_seconds,
            poll_phase_seconds=poll_phase_seconds, field_phase_origin_seconds=field_phase_origin_seconds,
            maximum_cell_seconds=maximum_cell_seconds, phase_policy=phase_policy,
            arrival_poll_order=arrival_poll_order, compilation_bits=compilation_bits)
        raw = persistent.PersistentReloadSource.record(source)
        counter = joint.JointCounterGenerator.from_record(raw['shared_APD']['original_shared_source'])
        report = CommonOpticalReadout._native_report(self, None, port_mask, counter)
        report.update(schema=SCHEMA+'/persistent', raw_persistent_source=raw,
                      persistent_state_and_CEM_entry_preserved=True)
        return source, report

    def verify_native(self, report):
        channel._require(type(report) is dict and report.get('schema') in (SCHEMA+'/native', SCHEMA+'/APD') and
                         report.get('common_optical_source') == CommonOpticalReadout.record(self),
                         'same source-generated native optical restriction required')
        model, mask = report['owned_native_cell'], _mask(tuple(report['port_mask']))
        raw = joint.JointCounterGenerator.from_record(report['raw_shared_counter_source'])
        if model is None:
            _, expected = CommonOpticalReadout.base_counter(self, raw.duration, threshold=raw.threshold, port_mask=mask)
        else:
            method = CommonOpticalReadout.apd_cell if report['schema'] == SCHEMA+'/APD' else CommonOpticalReadout.native_cell
            args = {} if report['schema'] != SCHEMA+'/APD' else {
                    'maximum_threshold': report['raw_APD_source']['maximum_threshold']}
            _, expected = method(self, atomic._read_phase(model['first_phase']), atomic._read_phase(model['second_phase']),
                tuple(map(Q, model['cuts'])), model['cell_index'], threshold=raw.threshold,
                port_mask=mask, compilation_bits=model['compilation_bits'], **args)
        channel._require(expected == report, 'native mask, transfer, background, common owner or original source changed')
        return True

    def verify_bsm(self, report):
        channel._require(type(report) is dict and report.get('schema') == SCHEMA+'/BSM' and
                         report.get('common_optical_source') == CommonOpticalReadout.record(self),
                         'same source-generated BSM optical restriction required')
        _, expected = CommonOpticalReadout.bsm_gate(self, compilation_bits=report['compilation_bits'])
        channel._require(expected == report, 'BSM collection, efficiency, port noise, common owner or gate changed')
        return True

    def verify_persistent(self, report):
        channel._require(type(report) is dict and report.get('schema') == SCHEMA+'/persistent' and
                         report.get('common_optical_source') == CommonOpticalReadout.record(self),
                         'same source-generated persistent optical restriction required')
        raw = report['raw_persistent_source']
        captures = tuple(trap.ReloadSource.from_record(item) for item in raw['capture_sources'])
        _, expected = CommonOpticalReadout.persistent_source(self,
            reservoir_occupations=tuple(item.occupations for item in captures),
            capture_couplings=tuple(item.couplings for item in captures),
            drives=tuple(tuple(atomic.Drive.from_record(item) for item in side) for side in raw['drives']),
            rules=tuple(persistent.PollRule.from_record(item) for item in raw['rules']),
            poll_period_seconds=raw['poll_period_seconds'], poll_phase_seconds=raw['poll_phase_seconds'],
            field_phase_origin_seconds=raw['field_phase_origin_seconds'],
            maximum_cell_seconds=raw['maximum_cell_seconds'], phase_policy=raw['phase_policy'],
            arrival_poll_order=raw['arrival_poll_order'], port_mask=_mask(tuple(report['port_mask'])),
            compilation_bits=raw['compilation_bits'])
        channel._require(expected == report, 'persistent common owner, shared optics, background or source controls changed')
        return True


def _signature():
    functions = (_copy, _matrix, _read_matrix, _mask, _bindings, _signature, _guard,
        CommonOpticalReadout.__init__, CommonOpticalReadout.record, CommonOpticalReadout.from_record.__func__,
        CommonOpticalReadout._parameters, CommonOpticalReadout._native_report, CommonOpticalReadout.base_counter,
        CommonOpticalReadout.native_cell, CommonOpticalReadout.apd_cell, CommonOpticalReadout.bsm_gate,
        CommonOpticalReadout.persistent_source, CommonOpticalReadout.verify_native,
        CommonOpticalReadout.verify_bsm, CommonOpticalReadout.verify_persistent,
        atomic.MunichAtomicProgramme.from_record.__func__, atomic.MunichAtomicProgramme.record,
        atomic.MunichAtomicProgramme.atomic_base, atomic.MunichAtomicProgramme.native_cell,
        atomic.MunichAtomicProgramme.bsm_gate, atomic._read_phase, atomic.AtomicBase.segment,
        bsm.optical_transfer, bsm.BSMSource.__init__, bsm.BSMSource.record, bsm.BSMSource.port_action,
        joint.JointCounterGenerator.__init__, joint.JointCounterGenerator.from_record.__func__,
        joint.JointCounterGenerator.record, joint.JointCounterGenerator.action,
        joint.JointCounterGenerator.detected_action, joint.JointCounterGenerator.independent_atomic_action,
        joint.passive_transfer, optics.collection_matrix, optics.beam_splitter_matrix,
        apd.APDWindowHistorySource.from_atomic_cell.__func__, persistent.PersistentReloadSource.__init__,
        apd.APDWindowHistorySource.record, apd.APDWindowHistorySource.from_record.__func__,
        persistent.PersistentReloadSource.record, persistent.PersistentReloadSource.from_record.__func__,
        persistent.PollRule.from_record.__func__, trap.ReloadSource.from_record.__func__,
        atomic.Drive.from_record.__func__)
    return (tuple((id(f), id(f.__code__), repr(f.__defaults__), repr(f.__kwdefaults__)) for f in functions),
            tuple(bsm.PORTS), tuple(ALL_PORTS), channel._canonical(PUBLIC_SOURCE))


def _guard():
    if not (_signature is _SIGNATURE and _signature.__code__ is _SIGNATURE_CODE and _signature() == _EXPECTED):
        raise ValueError('common optical source execution closure changed')


_SIGNATURE = _signature
_SIGNATURE_CODE = _signature.__code__
_GUARD_FUNCTION = _guard
_GUARD_CODE = _guard.__code__
_EXPECTED = _signature()
