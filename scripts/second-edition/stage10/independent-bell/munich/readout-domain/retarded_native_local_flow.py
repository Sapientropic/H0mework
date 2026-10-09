"""The original return action generates the complete first high-poll state.

The recent-count coimage makes the original APD observation certain before
expiry.  Its quantum marginal is therefore the tensor of the two original
local TP flows.  Complete signed Hermitian factors, both carrier frames and
the original time/field/queue mother remain attached to that action.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import copy
import numpy as np

import retarded_native_count_coimage as coimage
import factorized_local_phase_source as factors
import fourier_local_phase_source as fourier

frame, inlet, actual = coimage.frame, coimage.inlet, coimage.actual
channel, full, dipole, local, joint = frame.channel, frame.full, frame.dipole, frame.local, frame.joint
SCHEMA = 'stage10-original-retarded-native-complete-local-flow/v1'
_COIMAGE_CHECK, _FRAME_CHECK, _FACTOR_CHECK, _FOURIER_CHECK = (
    coimage._CHECK, frame._GUARD, factors._CHECK, fourier._GUARD)
_ISSUED = {}


def _require(value, message):
    if not value:
        raise ValueError(message)


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__), *(Path(m.__file__) for m in (coimage, frame, factors, fourier, actual)))}


def _local_commute(h, matrix):
    result = {}
    for key, value in dipole.matrix_product(h, matrix).items():
        local._add(result, key, dipole.ComplexRadical(0, -1)*value)
    for key, value in dipole.matrix_product(matrix, h).items():
        local._add(result, key, dipole.ComplexRadical(0, 1)*value)
    return result


class _LocalPhase:
    def __init__(self, cell, side):
        _require(type(side) is int and side in (0, 1), 'original native local side required')
        self.original = frame._ConstantSource(cell)
        self.side, self.duration, self.threshold = side, self.original.duration, 0

    def action(self, state):
        _CHECK()
        _require(all(c == 0 for c, _, _ in state), 'one full native local quantum block required')
        matrix = {(i, j): value for (_, i, j), value in state.items()}
        result = self.original.raw.sources[self.side].atomic_action(matrix)
        for key, value in _local_commute(self.original.z[self.side], matrix).items():
            local._add(result, key, value)
        if self.original.enabled[self.side]:
            for operator in self.original.captures[self.side].birth_operators.values():
                adjoint = dipole.matrix_adjoint(operator)
                loss = dipole.matrix_product(adjoint, operator)
                for key, value in dipole.matrix_product(dipole.matrix_product(operator, matrix), adjoint).items():
                    local._add(result, key, value)
                for term in (dipole.matrix_product(loss, matrix), dipole.matrix_product(matrix, loss)):
                    for key, value in term.items():
                        local._add(result, key, -value*Q(1, 2))
        return {(0, i, j): value for (i, j), value in result.items()}


class _Kernel(channel.SourceKernel):
    def __init__(self, cell, side, bits):
        self.source = _LocalPhase(cell, side)
        self.dimension, self.threshold, self.bits = full.DIMENSION, 0, bits
        self.columns, self.exact_columns, self.errors = {}, {}, {}


class _Columns:
    def __init__(self, kernel):
        _require(type(kernel) is _Kernel, 'fixed original native local kernel required')
        self.kernel, self.bits, self.frequencies = kernel, kernel.bits, ()

    def action(self, component, matrix):
        _require(component == 'static', 'one original constant native source action required')
        lifted = {(0, i, j): value for (i, j), value in matrix.items()}
        answer = {(i, j): value for (_, i, j), value in self.kernel.action(lifted).items()}
        rounded, quantization = fourier.exact._dyadic_state(answer, self.bits)
        return rounded, self.kernel.coefficient_error(lifted)+quantization


def _rotate(matrix, cell, age_source_units, sign, bits):
    frequencies = {line: Q(value) for line, value in cell['line_carrier_reciprocal_source_units'].items()}
    result = {}; price = Q(0); phases = {}
    for (i, j), value in matrix.items():
        frequency = frequencies.get(dipole.STATES[i].family, Q(0))-frequencies.get(dipole.STATES[j].family, Q(0))
        angle = sign*frequency*age_source_units
        if angle not in phases:
            centre, error = frame.modes.complex_exponential(0, angle, bits=bits) if angle else ((1, 0), Q(0))
            phases[angle] = dipole.ComplexRadical(*centre), error
        phase, error = phases[angle]
        local._add(result, (i, j), phase*value)
        price += error*frame.bsm._entry_norm({(i, j): value}, bits=bits)
    # Project the entire approximate curve to Hermitian matrices.  Exact
    # unitary conjugation commutes with this contraction.
    hermitian = {}
    for i, j in set(result) | {(j, i) for i, j in result}:
        value = (result.get((i, j), dipole.ComplexRadical())+
                 result.get((j, i), dipole.ComplexRadical()).conjugate())*Q(1, 2)
        local._add(hermitian, (i, j), value)
    return hermitian, price


def _centre(matrix, bits):
    result = {}; price = Q(0)
    for (i, j), value in matrix.items():
        a, da = full.radical_midpoint(value.real, bits)
        b, db = full.radical_midpoint(value.imag, bits)
        full._add(result, (i, j), a, b); price += da+db
    return result, price


def _piece(kernel, piece, mode_bits, exponential_bits):
    _require(type(piece) is dict and set(piece) == {'duration', 'modes'}, 'complete native source curve required')
    return fourier._piece(_Columns(kernel), piece, Q(0), mode_bits, exponential_bits)


def _certify_local(cell, side, initial, pieces, duration, *, mode_bits=96, coefficient_bits=192,
                   exponential_bits=192):
    _CHECK(); actual.cem.window._precisions(mode_bits, coefficient_bits, exponential_bits)
    initial = channel._initial(initial, full.DIMENSION)
    _require(type(pieces) is list and duration >= 0, 'complete native curve and nonnegative duration required')
    centre, rounding = _centre(initial, coefficient_bits)
    kernel = _Kernel(cell, side, coefficient_bits)
    elapsed = Q(0); price = rounding; payments = []
    for piece in pieces:
        width, begin, end, errors, diagnostics = _piece(kernel, piece, mode_bits, exponential_bits)
        join = fourier._difference(begin, centre)
        price += join+sum(errors.values(), Q(0)); elapsed += width
        _require(elapsed <= duration, 'native local curve crossed its original first-poll clock')
        payments.append({'duration': str(width), 'join_price': str(join),
            'original_source_prices': {key: str(value) for key, value in errors.items()}, 'modes': diagnostics})
        centre = end
    _require(elapsed == duration, 'native local curve must cover the entire return-to-poll clock')
    endpoint = {(i, j): dipole.ComplexRadical(a, b) for (i, j), (a, b) in centre.items()}
    return {'source_side': side, 'source_native_duration': str(duration),
        'complete_initial_local_matrix': channel._input_record(initial),
        'untrusted_local_curve': actual.records._copy(pieces), 'complete_local_endpoint': channel._input_record(endpoint),
        'whole_local_trace_norm_error': str(fourier._upper_price(price, coefficient_bits)),
        'source_residual_payments': payments, 'source_columns_checked': len(kernel.columns),
        'local_factor_positivity_assumed': False}


def _proposal_endpoint(piece, mode_bits):
    quantum = 1 << mode_bits; width = float(Q(piece['duration'])); result = {}
    for mode in piece['modes']:
        lr, li = mode['lambda']; scalar = np.exp(complex(lr/quantum, li/quantum)*width)
        for coefficient in mode['coefficients']:
            for i, j, a, b in coefficient:
                result[i, j] = result.get((i, j), 0j)+complex(a/quantum, b/quantum)*scalar
    answer = {}
    for i, j in set(result) | {(j, i) for i, j in result}:
        value = (result.get((i, j), 0j)+result.get((j, i), 0j).conjugate())/2
        _require(np.isfinite(value), 'finite original native curve proposal required')
        a, b = round(float(value.real)*quantum), round(float(value.imag)*quantum)
        if a or b:
            answer[0, i, j] = Q(a, quantum), Q(b, quantum)
    return answer


def _generate_local(cell, side, initial, duration, *, slices=1, order=16, mode_bits=96,
                    coefficient_bits=192, representation='exponential', krylov_dimension=1089):
    _CHECK()
    actual.cem.window._precisions(mode_bits, coefficient_bits, 192)
    _require(type(slices) is int and 1 <= slices <= 65536 and type(order) is int and 0 <= order <= 128,
             'finite original native curve budget required')
    _require(representation in ('exponential', 'polynomial') and type(krylov_dimension) is int and
             1 <= krylov_dimension <= 1089, 'named native representation and finite frequency budget required')
    _require(duration >= 0, 'nonnegative original native duration required')
    if not duration:
        return []
    centre, _ = _centre(channel._initial(initial, full.DIMENSION), coefficient_bits)
    current = {(0, i, j): value for (i, j), value in centre.items()}
    kernel = _Kernel(cell, side, coefficient_bits); quantum = 1 << mode_bits
    width = duration/slices; pieces = []
    for _ in range(slices):
        if representation == 'polynomial':
            coefficients = []; term = current
            for degree in range(order+1):
                encoded = [[i, j, round(a*quantum), round(b*quantum)] for (_, i, j), (a, b) in sorted(term.items())
                           if round(a*quantum) or round(b*quantum)]
                coefficients.append(encoded)
                image = kernel.action(term)
                term = {key: (a*width/Q(degree+1), b*width/Q(degree+1)) for key, (a, b) in image.items()}
                term, _ = fourier.exact._dyadic_state(term, coefficient_bits)
            modes = [{'lambda': [0, 0], 'frequency_word': [], 'coefficients': coefficients}]
        else:
            coordinates = kernel.reachable(tuple(current), max_coordinates=1089)
            index = {key: n for n, key in enumerate(coordinates)}
            entries = [(index[out], index[key], complex(float(a), float(b)))
                       for key in coordinates for out, (a, b) in kernel.column(key).items()]
            rows = np.array([a for a, _, _ in entries], dtype=np.int64)
            columns = np.array([b for _, b, _ in entries], dtype=np.int64)
            values = np.array([v for _, _, v in entries], dtype=np.complex128)
            vector = np.array([complex(float(current.get(k, (0, 0))[0]), float(current.get(k, (0, 0))[1]))
                               for k in coordinates], dtype=np.complex128)
            norm = np.linalg.norm(vector); modes = []
            if norm:
                maximum = min(krylov_dimension, len(coordinates)); used = maximum
                basis = np.zeros((len(coordinates), maximum+1), dtype=np.complex128)
                hessenberg = np.zeros((maximum+1, maximum), dtype=np.complex128); basis[:, 0] = vector/norm
                for n in range(maximum):
                    image = np.zeros_like(vector); np.add.at(image, rows, values*basis[columns, n])
                    for _ in range(2):
                        projections = basis[:, :n+1].conj().T@image
                        hessenberg[:n+1, n] += projections; image -= basis[:, :n+1]@projections
                    residual = np.linalg.norm(image); hessenberg[n+1, n] = residual
                    if residual <= 1e-13:
                        used = n+1; break
                    basis[:, n+1] = image/residual
                exponents, eigenvectors = np.linalg.eig(hessenberg[:used, :used])
                start = np.zeros(used, dtype=np.complex128); start[0] = norm
                amplitudes = (basis[:, :used]@eigenvectors)*np.linalg.solve(eigenvectors, start)
                for exponent, amplitude in zip(exponents, amplitudes.T):
                    encoded = []
                    for (_, i, j), value in zip(coordinates, amplitude):
                        a, b = round(float(value.real)*quantum), round(float(value.imag)*quantum)
                        if a or b:
                            encoded.append([i, j, a, b])
                    modes.append({'lambda': [round(float(min(0., exponent.real))*quantum),
                        round(float(exponent.imag)*quantum)], 'frequency_word': [], 'coefficients': [encoded]})
            if not modes:
                modes = [{'lambda': [0, 0], 'frequency_word': [], 'coefficients': [[]]}]
        piece = {'duration': str(width), 'modes': modes}; pieces.append(piece)
        current = _proposal_endpoint(piece, mode_bits)
    return pieces


def _inventory(cell, initial, initial_age, bits):
    inventory, terms = factors._factor_inventory(factors._decompose(initial))
    rotated = [[], []]; rotation_error = [{}, {}]
    for side, entries in enumerate(inventory):
        for item in entries:
            matrix, error = _rotate(channel._read_input(item['initial_local_matrix'], full.DIMENSION),
                                    cell, initial_age, 1, bits)
            rotated[side].append({'factor_id': item['factor_id'], 'initial_local_matrix': channel._input_record(matrix)})
            rotation_error[side][item['factor_id']] = error
    return inventory, rotated, terms, rotation_error


def _generate_image_trials(cell, initial, duration, initial_age, *, exponential_bits=192, **budget):
    actual.cem.window._precisions(budget.get('mode_bits', 96), budget.get('coefficient_bits', 192), exponential_bits)
    _, inventory, _, _ = _inventory(cell, initial, initial_age, exponential_bits)
    return [[{'factor_id': item['factor_id'], 'untrusted_local_curve': _generate_local(cell, side,
              channel._read_input(item['initial_local_matrix'], full.DIMENSION), duration, **budget)}
             for item in entries] for side, entries in enumerate(inventory)]


def _image(cell, initial, witnesses, duration, initial_age, final_age, *, mode_bits=96,
           coefficient_bits=192, exponential_bits=192):
    _CHECK(); actual.cem.window._precisions(mode_bits, coefficient_bits, exponential_bits)
    initial = channel._initial(initial, joint.DIMENSION)
    inventory, rotated, terms, rotation_errors = _inventory(cell, initial, initial_age, exponential_bits)
    _require(type(witnesses) is list and len(witnesses) == 2, 'two complete source-generated native factor inventories required')
    endpoints = [{}, {}]; reports = [[], []]
    for side, (entries, curves) in enumerate(zip(rotated, witnesses)):
        _require(type(curves) is list and [row['factor_id'] for row in curves] == [row['factor_id'] for row in entries] and
                 all(type(row) is dict and set(row) == {'factor_id', 'untrusted_local_curve'} for row in curves),
                 'every original native signed factor identity is required')
        for item, row in zip(entries, curves):
            report = _certify_local(cell, side, channel._read_input(item['initial_local_matrix'], full.DIMENSION),
                row['untrusted_local_curve'], duration, mode_bits=mode_bits,
                coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
            endpoint, rotation = _rotate(channel._read_input(report['complete_local_endpoint'], full.DIMENSION),
                                          cell, final_age, -1, exponential_bits)
            price = rotation_errors[side][item['factor_id']]+Q(report['whole_local_trace_norm_error'])+rotation
            endpoints[side][item['factor_id']] = endpoint, price
            reports[side].append({'factor_id': item['factor_id'], 'original_local_flow_certificate': report,
                'initial_frame_scalar_price': str(rotation_errors[side][item['factor_id']]),
                'final_frame_scalar_price': str(rotation), 'complete_physical_local_endpoint': channel._input_record(endpoint)})
    result = {}; error = Q(0)
    for first, second in terms:
        a, ea = endpoints[0][first]; b, eb = endpoints[1][second]
        increment, _, _ = factors._tensor_price(a, b, ea, eb, coefficient_bits); error += increment
        factors._add(result, factors._tensor(a, b))
    return {'schema': SCHEMA+'/complete-anchor-image', 'original_constant_native_cell': actual.records._copy(cell),
        'complete_initial_joint_matrix': channel._input_record(initial), 'source_native_duration': str(duration),
        'source_initial_frame_age': str(initial_age), 'source_final_frame_age': str(final_age),
        'source_factor_inventory': inventory, 'source_tensor_factor_ids': terms,
        'untrusted_witness_inventory': actual.records._copy(witnesses), 'two_complete_local_native_certificates': reports,
        'complete_quantum_endpoint': channel._input_record(result),
        'whole_new_native_trace_norm_error': str(fourier._upper_price(error, coefficient_bits)),
        'source_full_Z_natural_bath_capture_included': True, 'both_original_carrier_frames_applied': True,
        'local_factor_positivity_assumed': False, 'background_reapplied': False, 'APD_collection_erased_by_original_TP_identity': True,
        'precision': dict(mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits),
        'source_bindings': _bindings(), 'actual_hardware_member_asserted': False, 'controller_advance': False}


def _clock_difference(cell, clock, duration, initial_age, final_age, bits):
    gamma = Q(clock['Gamma_numerical_centre'])
    normalized, angular = coimage._rotating_bound(cell, bits)
    radius = Q(clock['Gamma_numerical_error'])
    _require(gamma > 0 and radius >= 0, 'original positive reference clock and enclosure required')
    return min(Q(2), radius*(normalized*duration+
        2*angular*(abs(initial_age)+abs(final_age)))/gamma)


def declared_native_trials(owner, initial, duration_source_units, *, cell_index=0, initial_frame_age=0, **budget):
    _CHECK()
    _require(type(owner) is frame.NativeToneFrame, 'closed original NativeToneFrame required')
    frame.NativeToneFrame.record(owner)
    cell = frame.NativeToneFrame.cell(owner, cell_index)
    duration = full.nonnegative(duration_source_units); age = full.nonnegative(initial_frame_age)
    return _generate_image_trials(cell, initial, duration, age, **budget)


def certify_declared_native(owner, initial, witnesses, duration_source_units, *, cell_index=0,
                            initial_frame_age=0, **precision):
    _CHECK()
    _require(type(owner) is frame.NativeToneFrame, 'closed original NativeToneFrame required')
    raw = frame.NativeToneFrame.record(owner); cell = frame.NativeToneFrame.cell(owner, cell_index)
    duration = full.nonnegative(duration_source_units); age = full.nonnegative(initial_frame_age)
    result = _image(cell, initial, witnesses, duration, age, age+duration, **precision)
    result.update(declared_original_native_source=raw,
                  declared_original_native_cell_index=cell_index,
                  scope='declared-source complete quantum flow control; no retarded actual occurrence supplied')
    return result


def verify_declared_native(owner, report):
    _require(type(report) is dict and report.get('schema') == SCHEMA+'/complete-anchor-image',
             'complete declared native flow report required')
    initial = channel._read_input(report['complete_initial_joint_matrix'], joint.DIMENSION)
    expected = certify_declared_native(owner, initial, report['untrusted_witness_inventory'],
        report['source_native_duration'], initial_frame_age=report['source_initial_frame_age'],
        cell_index=report['declared_original_native_cell_index'], **report['precision'])
    _require(expected == report, 'declared original native source, frame, full endpoint or price changed')
    return True


class RetardedNativeLocalFlow:
    def __init__(self, source, record_source, event, first, second, admitted):
        _CHECK()
        _require(type(source) is coimage.RetardedNativeCountCoimage, 'closed original recent-count coimage required')
        value = coimage.RetardedNativeCountCoimage.consume(source, record_source, event, first, second, admitted)
        self._coimage, self._record_source = source, record_source
        self._event, self._first, self._second, self._admitted = (
            actual.records._copy(event), copy.deepcopy(first), copy.deepcopy(second), copy.deepcopy(admitted))
        self._value = value; self._seal = _digest(value)
        _ISSUED[id(self)] = (source, record_source, self._seal)

    def record(self):
        _CHECK(); coimage.field._closed(self)
        _require(type(self) is RetardedNativeLocalFlow and set(vars(self)) == {
            '_coimage', '_record_source', '_event', '_first', '_second', '_admitted', '_value', '_seal'} and
            _ISSUED.get(id(self)) == (self._coimage, self._record_source, self._seal) and
            _digest(self._value) == self._seal and
            self._value['original_CEM_occurrence'] == _digest(self._event), 'original CEM/native same-occurrence source changed')
        coimage.RetardedNativeCountCoimage.record(self._coimage)
        actual.RetardedActualRecordMeasure.record(self._record_source)
        _require(self._record_source._source._measure._certificate._inlet is self._coimage._source,
                 'the native endpoint must retain the very original retarded inlet')
        return actual.records._copy(self._value)

    def _anchor(self, anchor):
        raw = RetardedNativeLocalFlow.record(self); facts = raw['source_generated_return_and_high_poll']
        lower, upper = map(Q, facts['receipt_support_seconds'])
        anchor = (lower+upper)/2 if anchor is None else full.nonnegative(anchor)
        _require(lower <= anchor <= upper, 'native anchor must belong to the entire original record cell')
        parent = self._coimage._source._value['source_issued_two_pump_source']['reference_local_parent']
        returned = anchor+Q(facts['CEM_completion_offset_seconds'])
        poll = coimage._next_poll(returned, Q(facts['source_poll_phase_seconds']), Q(facts['source_poll_period_seconds']))
        faces = [face for face in parent['reference_first_poll_ready']['count_faces'] if face['PC_ready']]
        policy = raw['source_record']['raw_return_policy']
        origin = coimage._phase_origin(parent, policy, faces[0], returned)
        cell = coimage._native_cell(parent, facts['source_return_high_transitions'][0])
        gamma = Q(parent['reference_clock']['Gamma_numerical_centre'])
        return raw, parent, facts, anchor, cell, gamma*(poll-returned), gamma*(returned-origin), gamma*(poll-origin)

    def generate_trials(self, *, anchor=None, **budget):
        raw, _, _, _, cell, duration, age, _ = RetardedNativeLocalFlow._anchor(self, anchor)
        initial = channel._read_input(raw['complete_atomic_poststate_at_CEM_completion'], joint.DIMENSION)
        return _generate_image_trials(cell, initial, duration, age, **budget)

    def certify(self, witnesses, *, anchor=None, mode_bits=96, coefficient_bits=192, exponential_bits=192):
        raw, parent, facts, anchor, cell, duration, initial_age, final_age = RetardedNativeLocalFlow._anchor(self, anchor)
        initial = channel._read_input(raw['complete_atomic_poststate_at_CEM_completion'], joint.DIMENSION)
        old = Q(raw['CEM_poststate_trace_norm_error'])
        numeric = _image(cell, initial, witnesses, duration, initial_age, final_age,
                         mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
        lower, upper = map(Q, facts['receipt_support_seconds']); policy = raw['source_record']['raw_return_policy']
        faces = [face for face in parent['reference_first_poll_ready']['count_faces'] if face['PC_ready']]
        returned = anchor+Q(facts['CEM_completion_offset_seconds'])
        origin = coimage._phase_origin(parent, policy, faces[0], returned)
        families = []; difference = Q(0)
        for index, face in enumerate(faces):
            envelope = coimage._native_family_envelope(parent, facts, policy, lower, upper, anchor, index, coefficient_bits)
            same_action = (coimage._native_cell(parent, facts['source_return_high_transitions'][index]) == cell and
                           coimage._phase_origin(parent, policy, face, returned) == origin)
            # A count face with a different original control retains its
            # entire CP fibre.  No unobserved face is selected or duplicated.
            bound = Q(envelope['whole_native_operator_difference_per_input_norm']) if same_action else Q(2)
            difference = max(difference, bound)
            families.append({'source_ready_face_index': index, 'same_anchor_action': same_action,
                'whole_operator_difference_to_anchor_upper': str(bound), 'source_time_family': envelope,
                'original_high_successor': facts['source_return_high_transitions'][index]['first_native_high_successor']})
        norm = frame.bsm._entry_norm(initial, bits=coefficient_bits); true_norm = norm+old
        gamma_difference = _clock_difference(cell, parent['reference_clock'], duration,
                                             initial_age, final_age, coefficient_bits)
        tail, tail_components = actual._continuing_tail(self._record_source._source,
            Q(facts['raw_return_time_support_seconds'][0]), coefficient_bits)
        time_price, gamma_price, tail_price = (value*true_norm for value in (difference, gamma_difference, tail))
        new = Q(numeric['whole_new_native_trace_norm_error'])
        error = old+new+time_price+gamma_price+tail_price
        matrix = channel._read_input(numeric['complete_quantum_endpoint'], joint.DIMENSION)
        centre, rounding = full.radical_midpoint(joint._trace(matrix).real, coefficient_bits)
        low, high = max(Q(0), centre-rounding-error), max(Q(0), centre+rounding+error)
        source_mass = tuple(map(Q, self._event['selected_mass_bounds']))
        _require(self._event['probability_interpretation_source']['certified'] and
                 0 <= source_mass[0] <= source_mass[1], 'original positive CEM source mass required')
        return {'schema': SCHEMA+'/same-occurrence-first-high-poll', 'original_CEM_return_coimage': raw,
            'source_record_anchor_receipt_seconds': str(anchor), 'complete_anchor_native_image': numeric,
            'source_all_Ready_face_native_families': families, 'complete_quantum_endpoint': numeric['complete_quantum_endpoint'],
            'whole_CEM_input_error_transported_once': str(old), 'new_native_numeric_error': str(new),
            'whole_receipt_and_Ready_face_operator_family_error': str(fourier._upper_price(time_price, coefficient_bits)),
            'whole_reference_Gamma_family_error': str(fourier._upper_price(gamma_price, coefficient_bits)),
            'continuing_Gaussian_native_difference_price': str(fourier._upper_price(tail_price, coefficient_bits)),
            'continuing_Gaussian_native_tail_components': tail_components,
            'complete_native_trace_norm_error': str(fourier._upper_price(error, coefficient_bits)),
            'source_trace_normalizer': {'centre': self._event['selected_mass_centre'],
                'bounds': list(map(str, source_mass)), 'strictly_positive': source_mass[0] > 0,
                'origin': 'original selected CEM mass / complete native TP / certain next high coimage',
                'source_mass_preserved_on_every_time_and_Ready_face': True,
                'state_normalized': False, 'caller_normalizer_used': False},
            'numeric_endpoint_trace_diagnostic': {'centre': str(centre), 'bounds': list(map(str, (low, high))),
                'full_numeric_operator_error_used': True},
            'next_source_high_poll_epoch': raw['new_confirmation_epoch'],
            'all_native_polls_use_original_high_observation': True,
            'all_high_successors_are_PC_ready': all(row['original_high_successor']['PC_ready'] for row in families),
            'whole_quantum_time_field_queue_successor_mother': {
                'original_complete_mother': raw['complete_quantum_time_field_queue_mother'],
                'source_same_occurrence_return_coimage': raw['source_record'],
                'source_all_Ready_face_native_maps': families,
                'source_map': 'original return clock and frame / two full local TP flows / original next high poll',
                'original_queue_and_new_arrival_fibres_retained': True,
                'quantum_time_correlation_paid_before_marginal_read': True,
                'literal_queue_representative_used': False, 'queue_reset': False},
            'full_native_quantum_state_constructed': True, 'full_nextRaw_history_scored': False,
            'untrusted_witness_inventory': actual.records._copy(witnesses),
            'precision': dict(mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits),
            'source_bindings': _bindings(), 'actual_hardware_member_asserted': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False}

    def verify(self, report):
        _require(type(report) is dict and report.get('schema') == SCHEMA+'/same-occurrence-first-high-poll',
                 'original complete native high-poll report required')
        rebuilt = coimage.RetardedNativeCountCoimage.consume(self._coimage, self._record_source, self._event,
            self._first, self._second, self._admitted)
        _require(rebuilt == RetardedNativeLocalFlow.record(self), 'same original CEM occurrence required')
        expected = RetardedNativeLocalFlow.certify(self, report['untrusted_witness_inventory'],
            anchor=report['source_record_anchor_receipt_seconds'], **report['precision'])
        _require(expected == report, 'complete native action, frame, whole mother or error changed')
        return True


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    return tuple(map(_function, (_require, _digest, _bindings, _local_commute, _rotate, _centre, _piece,
        _certify_local, _proposal_endpoint, _generate_local, _inventory, _generate_image_trials, _image,
        _clock_difference,
        declared_native_trials, certify_declared_native, verify_declared_native, _function, _signature, _check,
        _LocalPhase.__init__, _LocalPhase.action, _Kernel.__init__, _Columns.__init__, _Columns.action,
        RetardedNativeLocalFlow.__init__, RetardedNativeLocalFlow.record, RetardedNativeLocalFlow._anchor,
        RetardedNativeLocalFlow.generate_trials, RetardedNativeLocalFlow.certify, RetardedNativeLocalFlow.verify,
        coimage.RetardedNativeCountCoimage.record, coimage.RetardedNativeCountCoimage.consume,
        coimage._native_cell, coimage._native_family_envelope, coimage._phase_origin, coimage._rotating_bound,
        frame.NativeToneFrame.record, frame.NativeToneFrame.cell, frame._ConstantSource.__init__,
        local.CounterGenerator.atomic_action, channel.SourceKernel.column, channel.SourceKernel.action,
        channel.SourceKernel.coefficient_error, channel.SourceKernel.reachable,
        factors._decompose, factors._factor_inventory, factors._tensor, factors._tensor_price,
        fourier._piece, fourier.exact._dyadic_state, actual._continuing_tail,
        actual.cem.window._precisions))), SCHEMA


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
        coimage._CHECK is _COIMAGE_CHECK and frame._GUARD is _FRAME_CHECK and factors._CHECK is _FACTOR_CHECK and
        fourier._GUARD is _FOURIER_CHECK, 'original retarded native local execution changed')
    _COIMAGE_CHECK(); _FRAME_CHECK(); _FACTOR_CHECK(); _FOURIER_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
