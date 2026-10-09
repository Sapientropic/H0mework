"""The paid MP waveform leaf, with its complete ion-birth response.

The original MI residual certificate is consumed as paid evidence.  Its
adjoint observable is an effect, never a forward quantum poststate.  The
neutral compression removes pre-existing ION population from the birth count.
"""
from fractions import Fraction as Q
import gzip
import hashlib
import json
from pathlib import Path

import atomic_dipole as dipole
import atomic_full_forward as full
import atomic_modes as modes
import gated_atomic_response as gated
import mode_prefix_intake as paid
import raw_command_family as commands
import registration_joint_transport as transport
import registration_window_domain as domain
import window_cem_source as window


BASE = Path(__file__).resolve().parent
SCHEMA = 'stage10-paid-candidate-complete-birth-response/v1'
PRIMITIVES = ('u_x', 'd_x', 'u_plus_d_x', 'u_plus_i_d_x')
_GENERATED = set()


def _require(condition, reason):
    if not condition:
        raise ValueError(reason)


def _copy(value):
    return json.loads(json.dumps(value))


def _digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def _code():
    names = ('candidate_record_response.py', 'atomic_dipole.py', 'atomic_full_forward.py',
             'atomic_modes.py', 'gated_atomic_response.py', 'mode_prefix_intake.py',
             'raw_command_family.py', 'registration_joint_transport.py',
             'registration_window_domain.py', 'window_cem_source.py')
    return {name: hashlib.sha256((BASE/name).read_bytes()).hexdigest() for name in names}


def _execution_signature():
    functions = (_require, _copy, _digest, _code, _execution_signature,
                 _read_bound, _paid_inputs, _build, _side_response, _primitive, _primitive_row,
                 paid.consume, paid.frozen, domain.paid_joint_domains, domain.normalized_pulse_domain,
                 domain.source_registration_point, transport.source_for_settings, transport._side_programs,
                 commands.compile_commands, gated._native_law, gated._partition, full.initial_densities,
                 gated._read_matrix, gated._record, full._add, full._hermitian,
                 dipole.State.__init__, dipole.State.__eq__, dipole.State.__hash__,
                 dipole.source_qubit_bridge, full.Generator.__init__, full.Segment.from_record.__func__,
                 window.WindowCEMSource.__init__, window.WindowCEMSource.phases,
                 window.FragmentRegistration.gates, window.FragmentRegistration.kappa,
                 window.WindowCEMSource.record, window.WindowCEMSource.from_record.__func__,
                 CandidateRecordResponse.from_paid_run.__func__, CandidateRecordResponse.from_record.__func__,
                 CandidateRecordResponse.record, CandidateRecordResponse.certify,
                 CandidateRecordResponse.verify, CandidateRecordResponse.window_source,
                 CandidateRecordResponse.primitive_response, CandidateRecordResponse.verify_primitive_response,
                 CandidateRecordResponse.family_inlet)
    basis = tuple((state.family, state.f, state.m) for state in dipole.STATES)
    indices = tuple((state.family, state.f, state.m, index) for state, index in dipole.INDEX.items())
    return (tuple((id(function), id(function.__code__)) for function in functions),
            id(dipole.State), basis, indices, dipole.ION, tuple(PRIMITIVES), tuple(full.TOMOGRAPHY),
            full.DIMENSION, full.COMPLEX_COORDINATES)


def _read_bound(binding):
    _require(type(binding) is dict and type(binding.get('path')) is str,
             'paid gzip evidence binding required')
    path = BASE/binding['path']
    _require(path.parent == BASE and path.name == binding['path'], 'paid evidence outside source corridor')
    raw = path.read_bytes()
    _require(len(raw) == binding['bytes'] and hashlib.sha256(raw).hexdigest() == binding['sha256'],
             'paid evidence bytes changed')
    decoded = gzip.decompress(raw)
    _require(hashlib.sha256(decoded).hexdigest() == binding['decoded_sha256'] and
             ('decoded_bytes' not in binding or len(decoded) == binding['decoded_bytes']),
             'paid decoded evidence changed')
    return json.loads(decoded)


def _paid_inputs():
    prior = domain.paid_joint_domains()
    freeze = prior['prior_full_joint_membership']['science_freeze']
    candidate_raw = paid.frozen(BASE/'hardware-inverse-first-hi0002.json', freeze)
    mode_raw = paid.frozen(BASE/'mode-forward-mi0001.json.gz', freeze)
    candidate = json.loads(candidate_raw)
    mi = json.loads(gzip.decompress(mode_raw))
    receipt = _read_bound(mi['full_receipt'])
    _require(receipt['schema'] == mi['schema'] == 'stage10-raw-hardware-mode-forward-mi0001/v1' and
             receipt['status'] == mi['status'] == 'source_probability_enclosures_generated',
             'paid complete MI receipt required')
    wr_raw = paid.frozen(BASE/'registration-joint-first-wr0001.json.gz')
    wr = json.loads(gzip.decompress(wr_raw))
    _require(wr['schema'] == 'stage10-raw-registration-joint-transport/v1' and wr['verified'] is True and
             wr['paid_source_domain'] == prior, 'WR and MP must consume the same paid source')
    for binding in wr['source_bindings']:
        path = full.ROOT/binding['path']
        _require(path.parent == BASE and hashlib.sha256(paid.frozen(path, wr['science_freeze'])).hexdigest()
                 == binding['sha256'], 'WR original source binding changed')
    return prior, candidate, mi, receipt, wr, {
        'MP_first_sha256': prior['prior_full_joint_membership']['first_sha256'],
        'MP_science_freeze': freeze, 'HI_raw_sha256': hashlib.sha256(candidate_raw).hexdigest(),
        'MI_summary_sha256': hashlib.sha256(mode_raw).hexdigest(), 'MI_full_receipt': mi['full_receipt'],
        'WR_raw_sha256': hashlib.sha256(wr_raw).hexdigest(), 'WR_science_freeze': wr['science_freeze']}


def _side_response(program, registration, background, certificate, binding):
    raw = program.segments[0]
    _require(certificate['schema'] == 'stage10-full-atom-mode-enclosure/v1' and
             certificate['raw_program'] == raw.record() and
             certificate['physical_dimension'] == full.DIMENSION and
             certificate['observable_complex_coordinates'] == full.COMPLEX_COORDINATES,
             'paid adjoint certificate belongs to a different complete raw source')
    partition = gated._partition(raw, registration, Q(0))
    eta = 1-registration.probabilities[0]
    _require(partition and all(Q(item['kappa']) == eta for item in partition),
             'all candidate ion-birth times must have the original full gate')
    law = gated._native_law(raw, registration, Q(0), partition)
    observed = gated._read_matrix(certificate['observable_center'])
    physical = {key: value for key, value in observed.items() if dipole.ION not in key}
    born = {key: (eta*a, eta*b) for key, (a, b) in physical.items()}
    curve_error = eta*Q(certificate['operator_error_bound'])
    command_error = eta*program.command_trace_norm_error
    error = curve_error+command_error
    click = {key: ((1-background)*a, (1-background)*b) for key, (a, b) in born.items()}
    for i in range(full.DIMENSION):
        full._add(click, (i, i), background)
    _require(full._hermitian(born) and full._hermitian(click), 'paid full-complex response is not Hermitian')
    return {'raw_command_program': program.record(), 'raw_registration': registration.record(),
            'raw_background': str(background), 'paid_mode_witness_binding': binding,
            'paid_mode_certificate_sha256': _digest(certificate), 'paid_mode_count': certificate['modes'],
            'gate_partition': partition, 'native_birth_source_law': law,
            'full_physical_birth_effect_center': gated._record(physical),
            'physical_birth_operator_error_bound': str(Q(certificate['operator_error_bound'])+program.command_trace_norm_error),
            'positive_physical_birth_bound': {'lower': '0', 'upper': '1', 'upper_support': 'I-PiION'},
            'full_born_effect_center': gated._record(born), 'full_click_effect_center': gated._record(click),
            'curve_operator_error_bound': str(curve_error), 'command_operator_error_bound': str(command_error),
            'operator_error_bound': str(error), 'click_operator_error_bound': str((1-background)*error),
            'positive_born_bound': {'lower': '0', 'upper': str(eta), 'upper_support': 'I-PiION'},
            'positive_click_bound': [str(background), str(background+(1-background)*eta)],
            'adjoint_birth_identity': 'eta * (E_T^*(PiION)-PiION); neutral compression of the paid centre',
            'initial_ION_birth_mass': '0', 'background_composed_once': True,
            'physical_dimension': full.DIMENSION, 'observable_complex_coordinates': full.COMPLEX_COORDINATES,
            'paid_residual_receipt_consumed': True, 'residual_solver_reexecuted': False,
            'forward_quantum_poststate_generated': False}


def _build(run_name, settings, coordinates):
    _require(type(run_name) is str and run_name in ('2016-04-15', '2016-06-14'), 'one original paid run required')
    _require(type(settings) in (tuple, list) and len(settings) == 2 and
             all(type(value) is int and value in (0, 1) for value in settings), 'two original physical settings required')
    _require(type(coordinates) in (tuple, list) and len(coordinates) == 2 and
             all(type(row) in (tuple, list) and len(row) == 2 for row in coordinates),
             'two exact source registration-face coordinates required')
    coordinates = tuple(tuple(full.nonnegative(value) for value in row) for row in coordinates)
    prior, candidate, mi, receipt, wr, evidence = _paid_inputs()
    run = next(item for item in candidate['runs'] if item['run'] == run_name)
    old = next(item for item in mi['runs'] if item['run'] == run_name)
    complete = next(item for item in receipt['runs'] if item['run'] == run_name)
    template = full.Segment.from_record(candidate['raw_template'])
    geometry = prior['window_geometry']
    _require(geometry == domain.normalized_pulse_domain(template), 'WR geometry belongs to different raw pulse controls')
    source = transport.source_for_settings(run, template, settings, geometry=geometry,
                                           registration_coordinates=coordinates)
    programs = transport._side_programs(run, template)
    original = next(item['source_reduction'] for item in wr['source_reductions']
                    if item['run'] == run_name and item['settings'] == list(settings))
    default = transport.source_for_settings(run, template, settings, geometry=geometry)
    _require(original['raw_source'] == default.record(), 'WR raw waveform/clock differs from the candidate leaf')
    for phase in source.phases():
        for side in (0, 1):
            _require(not phase.ion_rates[side] or phase.kappas[side] == 1-source.registrations[side].probabilities[0],
                     'candidate active ion phase is not fully covered')
    sides = []
    for index, side in enumerate(('alice', 'bob')):
        selected = settings[index]
        saved = next(item for item in old['settings'] if (item['side'], item['setting']) == (side, selected))
        full_saved = next(item for item in complete['settings'] if (item['side'], item['setting']) == (side, selected))
        program = programs[index][selected]
        _require(full_saved['witness'] == saved['witness'] and full_saved['program'] == program.record(),
                 'paid complete mode evidence changed its original command')
        _require(Q(full_saved['combined_operator_error']) == Q(saved['combined_operator_error']) ==
                 Q(full_saved['mode_certificate']['operator_error_bound'])+program.command_trace_norm_error,
                 'paid complete mode and raw command prices differ')
        witness = _read_bound(saved['witness'])
        _require(set(witness) == {'raw_program', 'mode_bits', 'modes'} and
                 witness['raw_program'] == program.segments[0].record() and
                 witness['mode_bits'] == full_saved['mode_certificate']['mode_bits'] and
                 len(witness['modes']) == full_saved['mode_certificate']['modes'],
                 'paid mode witness belongs to different original controls')
        sides.append(_side_response(program, source.registrations[index], source.backgrounds[index],
                                    full_saved['mode_certificate'], saved['witness']))
    return {'schema': SCHEMA, 'run': run_name, 'settings': list(settings),
            'registration_coordinates': [[str(value) for value in row] for row in coordinates],
            'paid_evidence': evidence, 'raw_template': template.record(), 'window_geometry': geometry,
            'raw_window_source': source.record(), 'responses': sides,
            'input_domain': 'every positive full33 input; birth effect annihilates pre-existing ION',
            'fixed_candidate_leaf_role': 'paid static hypothesis leaf, not identified actual parameters',
            'dynamic_return_contract': {
                'required_mother': 'whole first-receipt mother generated by the same complete hardware leaf',
                'measurement_leaf': {'raw_template': template.record(),
                                     'raw_transfers': [programs[i][settings[i]].record()['transfer'] for i in (0, 1)],
                                     'raw_backgrounds': list(map(str, source.backgrounds)),
                                     'raw_registrations': [item.record() for item in source.registrations]},
                'seconds_per_source_unit': str(source.seconds_per_unit),
                'unbound_raw_coordinates': ['native ground loading and capture', 'cool/repump/pump tones',
                                          'shared APD collection, threshold and background', 'preparation/excitation',
                                          'BSM splitter, efficiencies, background and arrival offsets'],
                'same_lambda_dynamic_mother_supplied': False, 'positive_determinant_assumed': False},
            'forward_poststate_generated': False, 'actual_clock_programme_identified': False,
            'actual_hardware_uniquely_identified': False, 'new_numerical_solves': 0,
            'new_statistical_executions': 0, 'archive_files_read': 0, 'controller_advance': False,
            'source_code': _code()}


def _primitive(name):
    if type(name) is str and name in PRIMITIVES:
        state = full.initial_densities()[PRIMITIVES.index(name)]
        record = {'producer': 'atomic_full_forward.initial_densities', 'primitive': name}
    else:
        _require(type(name) in (tuple, list) and len(name) == 3 and type(name[0]) is str and
                 all(value is None or type(value) is int for value in name[1:]),
                 'original named atomic primitive required; a density matrix is not input')
        named = dipole.State(*name)
        _require(named in dipole.INDEX, 'primitive outside the original retained 33-state basis')
        index = dipole.INDEX[named]
        state = {(index, index): (Q(1), Q(0))}
        record = {'producer': 'atomic_dipole.STATES basis projector', 'primitive': list(name)}
    return state, {**record, 'full_state': gated._record(state), 'trace': '1',
                   'positive_source_primitive': True, 'actual_history_inlet_identified': False}


def _primitive_row(response, primitive):
    state, inlet = _primitive(primitive)
    born = gated._read_matrix(response['full_physical_birth_effect_center'])
    center = Q(0)
    imaginary = Q(0)
    for (i, j), (a, b) in born.items():
        x, y = state.get((j, i), (Q(0), Q(0)))
        center += a*x-b*y
        imaginary += a*y+b*x
    _require(not imaginary, 'full-complex source pairing is not real')
    neutral = sum((value[0] for (i, j), value in state.items() if i == j and i != dipole.ION), Q(0))
    physical_error = Q(response['physical_birth_operator_error_bound'])*neutral
    physical_lo, physical_hi = max(Q(0), center-physical_error), min(neutral, center+physical_error)
    eta = Q(response['positive_born_bound']['upper'])
    lo, hi = eta*physical_lo, eta*physical_hi
    _require(lo <= hi, 'paid operator interval and positive source bound are disjoint')
    d = Q(response['raw_background'])
    return {'source_primitive_inlet': inlet,
            'physical_birth_mass_interval': [str(physical_lo), str(physical_hi)],
            'physical_birth_center': str(center), 'physical_birth_operator_payment': str(physical_error),
            'born_mass_interval': [str(lo), str(hi)],
            'born_center': str(eta*center), 'born_operator_payment': str(eta*physical_error),
            'click_mass_interval': [str(d+(1-d)*lo), str(d+(1-d)*hi)],
            'law': 'physical birth=Tr((E^*(PiION)-PiION) rho); accepted B=eta*(E^*(PiION)-PiION); click=d+(1-d)*Tr(B rho)',
            'full_complex_input_paired': True, 'forward_poststate_generated': False}


class CandidateRecordResponse:
    def __init__(self, *args, **kwargs):
        raise ValueError('closed from_paid_run factory required; raw targets and callbacks are not inputs')

    @classmethod
    def from_paid_run(cls, run, settings=(0, 0), *, registration_coordinates=((0, 0), (0, 0))):
        if not (cls is CandidateRecordResponse and
                _execution_signature is _EXPECTED_SIGNATURE_FUNCTION and
                _execution_signature.__code__ is _EXPECTED_SIGNATURE_CODE and
                _execution_signature() == _EXPECTED_EXECUTION):
            raise ValueError('candidate source execution closure changed')
        frame = _build(run, settings, registration_coordinates)
        result = object.__new__(cls)
        result._frame = _copy(frame)
        result._seal = _digest(frame)
        result._signature = _execution_signature()
        _GENERATED.add(result._seal)
        return result

    @classmethod
    def from_record(cls, record):
        _require(type(record) is dict and record.get('schema') == SCHEMA, 'closed candidate source record required')
        result = cls.from_paid_run(record['run'], record['settings'],
                                   registration_coordinates=record['registration_coordinates'])
        _require(result.record() == record, 'candidate source record differs from paid original controls')
        return result

    def record(self):
        if not (type(self) is CandidateRecordResponse and set(vars(self)) == {'_frame', '_seal', '_signature'} and
                _execution_signature is _EXPECTED_SIGNATURE_FUNCTION and
                _execution_signature.__code__ is _EXPECTED_SIGNATURE_CODE and
                self._signature == _execution_signature() == _EXPECTED_EXECUTION and
                self._seal in _GENERATED and _digest(self._frame) == self._seal and
                self._frame['source_code'] == _code()):
            raise ValueError('candidate source snapshot or execution closure changed')
        return _copy(self._frame)

    def certify(self):
        return {'schema': SCHEMA+'/certificate', 'source_record': CandidateRecordResponse.record(self),
                'source_record_sha256': self._seal, 'full_input_operator_rows_generated': True,
                'physical_poststate_replaced': False, 'actual_hardware_uniquely_identified': False,
                'controller_advance': False}

    def verify(self, report):
        _require(report == CandidateRecordResponse.certify(self), 'candidate birth response certificate mismatch')
        return True

    def window_source(self):
        return window.WindowCEMSource.from_record(CandidateRecordResponse.record(self)['raw_window_source'])

    def primitive_response(self, side, primitive='u_x'):
        _require(type(side) is int and side in (0, 1), 'original local side required')
        record = CandidateRecordResponse.record(self)
        return {'schema': SCHEMA+'/primitive-row', 'source_record_sha256': self._seal,
                'run': record['run'], 'settings': record['settings'], 'side': side,
                **_primitive_row(record['responses'][side], primitive),
                'input_scope': 'source-produced primitive, not the actual dynamic history mother',
                'actual_hardware_uniquely_identified': False, 'controller_advance': False}

    def verify_primitive_response(self, row):
        _require(type(row) is dict and row.get('schema') == SCHEMA+'/primitive-row',
                 'source primitive response row required')
        primitive = row['source_primitive_inlet']['primitive']
        _require(_copy(row) == CandidateRecordResponse.primitive_response(self, row['side'], primitive),
                 'candidate primitive response row mismatch')
        return True

    def family_inlet(self, primitives=('u_x', 'd_x')):
        """Original WindowDetectorFamily input; forward witnesses remain required."""
        _require(type(primitives) in (tuple, list) and len(primitives) == 2, 'two source atomic primitives required')
        record = CandidateRecordResponse.record(self)
        left, left_record = _primitive(primitives[0])
        right, right_record = _primitive(primitives[1])
        _require(not any(dipole.ION in key for state in (left, right) for key in state),
                 'fresh occupied WindowCEM inlet must be neutral')
        marked = {}
        for (i, j), (a, b) in left.items():
            for (k, l), (c, d) in right.items():
                marked[window.INITIAL, 33*i+k, 33*j+l] = dipole.ComplexRadical(a*c-b*d, a*d+b*c)
        recipe = {'producer': SCHEMA+'/source-primitive-pair', 'candidate_source_sha256': self._seal,
                  'local_primitives': [left_record, right_record], 'run': record['run'],
                  'settings': record['settings'], 'seconds_per_source_unit': record['dynamic_return_contract']['seconds_per_source_unit'],
                  'actual_history_mother_identified': False, 'adjoint_modes_are_forward_witnesses': False}
        return CandidateRecordResponse.window_source(self), marked, recipe


_EXPECTED_SIGNATURE_FUNCTION = _execution_signature
_EXPECTED_SIGNATURE_CODE = _execution_signature.__code__
_EXPECTED_EXECUTION = _execution_signature()
