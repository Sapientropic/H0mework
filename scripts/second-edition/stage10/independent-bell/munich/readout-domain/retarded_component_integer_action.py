"""Complete retarded source components on a common integer coefficient grid.

Only small local source operators are compiled.  A complete marked matrix is
then acted on with integer additions and products; no joint supermatrix or
entrywise radical arithmetic is constructed.  This is a checked action, not
a state, positivity, trajectory, or event-time certificate.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json
from math import factorial

import retarded_gaussian_trajectory_source as trajectory
import retarded_receipt_trajectory_certificate as checked

dipole, full, field, channel, bsm = (trajectory.dipole, trajectory.full,
    trajectory.field, trajectory.channel, trajectory.bsm)
SCHEMA = 'stage10-source-retarded-component-integer-action/v1'
_SOURCE_CHECK = trajectory._CHECK
_CERTIFICATE_CHECK = checked._CHECK
_ISSUED = {}
_KERNELS = {}
_COLUMNS = {}


def _require(value, message):
    if not value:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__), *(Path(m.__file__) for m in
          (trajectory, checked, trajectory.retarded, trajectory.density, dipole, full, field, channel, bsm)))}


def _primitive_digest(source):
    raw = source._value['retarded_source']; driven = raw['complete_driven_field_source']
    legs = [{name: leg[name] for name in ('carrier_angular_frequency_per_second', 'centre_seconds',
        'sigma_squared_seconds', 'phase_radians')} for leg in driven['Gaussian_source_legs']]
    return _digest({'parts': trajectory._parts_digest(source._parts),
        'groups': [[list(group), str(rate), [[mu, side, channel._input_record(operator)]
                     for mu, (side, operator) in modes]] for group, rate, modes in source._law._groups],
        'transfer': [[v.serialize() for v in row] for row in source._law._transfer],
        'loss': [[v.serialize() for v in row] for row in source._law._loss],
        'gate': bsm.BSMSource.record(source._law._gate), 'BG': raw['BG_source']['BG_rates_per_second'],
        'flight': driven['flight_seconds'], 'origins': driven['emission_origins_seconds'], 'legs': legs,
        'marks': [[list(m.counts), m.receipt] for m in source._marks], 'gate_seconds': raw['gate_seconds']})


def _component(value):
    value = tuple(value) if type(value) is list else value
    _require(value in trajectory.COMPONENTS, 'original source component required')
    return value


def _nearest(numerator, denominator):
    value = (abs(numerator) + denominator//2)//denominator
    return -value if numerator < 0 else value


def _ceil(value):
    return -(-value.numerator//value.denominator)


def _dyadic(numerator, bits):
    if not numerator:
        return Q(0)
    # The numerator and this power-of-two denominator are made coprime by
    # counting trailing bits, avoiding a whole-state pass through big GCDs.
    shift = min(bits, (abs(numerator) & -abs(numerator)).bit_length()-1)
    value = object.__new__(Q)
    value._numerator = numerator >> shift
    value._denominator = 1 << (bits-shift)
    return value


def _quantize(value, bits):
    grid = 1 << bits
    real, er = full.radical_midpoint(value.real, bits)
    imag, ei = full.radical_midpoint(value.imag, bits)
    a = _nearest(real.numerator*grid, real.denominator)
    b = _nearest(imag.numerator*grid, imag.denominator)
    error = er+ei+abs(real-Q(a, grid))+abs(imag-Q(b, grid))
    return a, b, _ceil(error*grid)


def _sum(target, key, value):
    if value:
        target[key] = target.get(key, dipole.ComplexRadical())+value
        if not target[key]:
            del target[key]


def _operator(target, side, operator):
    for (out, before), value in operator.items():
        _sum(target, ((side,), (before,), (out,), -1), value)
        _sum(target, ((2+side,), (before,), (out,), -1), value.conjugate())


def _paths(source, component, active, absorbed):
    result = {}
    if absorbed:
        if component == 'quiet':
            legs = source._value['retarded_source']['complete_driven_field_source']['Gaussian_source_legs']
            for side, on in enumerate(active):
                if on:
                    operator = {(i, i): dipole.ComplexRadical(0,
                        Q(legs[side]['carrier_angular_frequency_per_second']))
                        for i, state in enumerate(dipole.STATES) if state.family == 'D2'}
                    _operator(result, side, operator)
        return result
    if component == 'quiet':
        for side, on in enumerate(active):
            if on:
                _operator(result, side, source._parts[side][0])
        rates = tuple(map(Q, source._value['retarded_source']['BG_source']['BG_rates_per_second']))
        _sum(result, ((), (), (), -1), dipole.ComplexRadical(-sum(rates, Q(0))))
        for port, rate in enumerate(rates):
            _sum(result, ((), (), (), port), dipole.ComplexRadical(rate))
    elif component[0] == 'drive':
        side = component[1]
        if active[side]:
            _operator(result, side, source._parts[side][1])
        return result
    law = source._law
    for group, rate, modes in law._groups:
        for mu, (side, first) in modes:
            for nu, (other, second) in modes:
                if not (active[side] and active[other]):
                    continue
                cross = group[0] == 'D2' and side != other
                if (component == 'quiet' and cross) or (component != 'quiet' and
                        not (cross and (side, other) == component[1:])):
                    continue
                coefficients = [(-1, rate*law._loss[nu][mu])]
                coefficients.extend((port, rate*law._transfer[port][mu]*
                    law._transfer[port][nu].conjugate()) for port in range(4))
                for (out, before), a in first.items():
                    for (end, start), b in second.items():
                        product = a*b.conjugate()
                        for route, coefficient in coefficients:
                            _sum(result, ((side, 2+other), (before, start),
                                (out, end), route), product*coefficient)
    return result


def _compile(source, component, active, absorbed, bits):
    exact = _paths(source, component, active, absorbed)
    groups = {}
    for (axes, before, after, route), value in sorted(exact.items()):
        a, b, error = _quantize(value, bits)
        groups.setdefault(axes, {}).setdefault(before, []).append((after, route, a, b, error))
    error = norm = 0
    for columns in groups.values():
        error += max((sum(row[4] for row in rows) for rows in columns.values()), default=0)
        norm += max((sum(abs(row[2])+abs(row[3])+row[4] for row in rows)
                     for rows in columns.values()), default=0)
    rows = [[list(axes), list(before), list(after), route, a, b, e]
        for axes, columns in sorted(groups.items()) for before, paths in sorted(columns.items())
        for after, route, a, b, e in paths]
    return {'groups': groups, 'error': error, 'norm': norm, 'rows': rows}


def _kernel_record(kernel, bits):
    return {'source_generated_sparse_paths': kernel['rows'],
        'coefficient_bits': bits, 'entry_L1_operator_error_upper': str(Q(kernel['error'], 1 << bits)),
        'entry_L1_operator_norm_upper': str(Q(kernel['norm'], 1 << bits))}


def _marked_coordinates(source, key):
    _require(type(key) is tuple and len(key) == 3, 'original Mark and full pair coordinates required')
    mark, i, j = key
    _require(type(mark) is bsm.Mark and mark in source._marks and type(i) is int and type(j) is int and
        0 <= i < full.DIMENSION**2 and 0 <= j < full.DIMENSION**2,
        'complete original source Mark and full33 pair coordinate required')
    return mark, (*divmod(i, full.DIMENSION), *divmod(j, full.DIMENSION))


def _input_grid(source, state):
    _require(type(state) is dict, 'complete dyadic marked coefficient matrix required')
    bits = 0
    for key, pair in state.items():
        _marked_coordinates(source, key)
        _require(type(pair) is tuple and len(pair) == 2 and all(type(x) is Q for x in pair),
                 'exact complex rational coefficient pairs required')
        for value in pair:
            denominator = value.denominator
            _require(denominator & (denominator-1) == 0,
                     'integer action consumes a dyadic witness; general input requires paid quantization')
            bits = max(bits, denominator.bit_length()-1)
    _require(bits <= 1024, 'registered finite input coefficient grid required')
    integers = {key: tuple(value.numerator << (bits-value.denominator.bit_length()+1)
                    for value in pair) for key, pair in state.items() if any(pair)}
    return integers, bits


def _apply(source, kernels, integers, input_bits, coefficient_bits, output_bits, targets):
    result = {}; coefficient_error = 0; touched = False
    for key, (real, imag) in integers.items():
        mark, coords = _marked_coordinates(source, key)
        kernel = kernels[mark.receipt is not None]
        magnitude = abs(real)+abs(imag)
        for axes, columns in kernel['groups'].items():
            before = tuple(coords[axis] for axis in axes)
            for after, route, a, b, error in columns.get(before, ()):
                touched = True
                values = list(coords)
                for axis, value in zip(axes, after):
                    values[axis] = value
                target = mark if route == -1 else targets[mark, route]
                out = (target, full.DIMENSION*values[0]+values[1], full.DIMENSION*values[2]+values[3])
                x, y = result.get(out, (0, 0))
                result[out] = x+real*a-imag*b, y+real*b+imag*a
                coefficient_error += magnitude*error
    exponent = input_bits+coefficient_bits
    rounding = 0; answer = {}
    for key, pair in result.items():
        if output_bits < exponent:
            denominator = 1 << (exponent-output_bits)
            a, b = (_nearest(value, denominator) for value in pair)
            rounding += abs(pair[0]-a*denominator)+abs(pair[1]-b*denominator)
        else:
            a, b = (value << (output_bits-exponent) for value in pair)
        if a or b:
            answer[key] = a, b
    error = Q(coefficient_error+rounding, 1 << exponent)
    return answer, error, not touched, Q(coefficient_error, 1 << exponent), Q(rounding, 1 << exponent)


class RetardedComponentIntegerAction:
    def __init__(self, source, *, coefficient_bits=192):
        _CHECK(); field._closed(source); trajectory.gaussian._precision(coefficient_bits)
        _require(type(source) is trajectory.RetardedGaussianTrajectorySource,
                 'closed original RetardedGaussianTrajectorySource required; no caller G or target image')
        raw = trajectory.RetardedGaussianTrajectorySource.record(source)
        self._source, self._bits, self._kernels = source, coefficient_bits, {}
        self._targets = {(mark, port): bsm.BSMSource.target(source._law._gate, mark, port)
                         for mark in source._marks for port in range(4)}
        self._value = {'schema': SCHEMA, 'original_trajectory_source': raw, 'coefficient_bits': coefficient_bits,
            'source_bindings': _bindings(), 'generated_mark_inventory': raw['generated_stopped_marks'],
            'source_operator_axes': ['bra A', 'bra B', 'ket A', 'ket B'],
            'original_full33_pair_and_all_capped_counts_kept': True,
            'active_arm_and_absorbed_frame_counterflow_kept': True,
            'source_natural_loss_transfer_BG_and_drive_phase_paid': True,
            'joint_supermatrix_constructed': False, 'target_state_or_result_is_input': False,
            'input_positivity_certified': False, 'controller_advance': False}
        self._seal = _digest(self._value)
        _ISSUED[id(self)] = self._seal, source, self._kernels, self._targets, _digest(
            [[list(m.counts), m.receipt, port, list(t.counts), t.receipt]
             for (m, port), t in self._targets.items()]), _primitive_digest(source)

    def _runtime(self):
        _CHECK(); owned = _ISSUED.get(id(self))
        _require(type(self) is RetardedComponentIntegerAction and set(vars(self)) ==
            {'_source', '_bits', '_kernels', '_targets', '_value', '_seal'} and owned is not None and
            self._seal == owned[0] and self._source is owned[1] and self._kernels is owned[2] and
            self._targets is owned[3] and self._digest_targets() == owned[4] and
            _primitive_digest(self._source) == owned[5] and
            self._bits == self._value['coefficient_bits'], 'integer action source primitives or owner changed')

    def record(self):
        RetardedComponentIntegerAction._runtime(self); field._closed(self); owned = _ISSUED.get(id(self))
        _require(type(self) is RetardedComponentIntegerAction and set(vars(self)) ==
            {'_source', '_bits', '_kernels', '_targets', '_value', '_seal'} and owned is not None and
            (self._seal, self._source, self._kernels, self._targets) == owned[:4] and
            self._digest_targets() == owned[4] and _digest(self._value) == self._seal and
            self._value['source_bindings'] == _bindings() and self._bits == self._value['coefficient_bits'] and
            trajectory.RetardedGaussianTrajectorySource.record(self._source) == self._value['original_trajectory_source'],
            'integer action source, original Mark targets or owner changed')
        return _copy(self._value)

    def _digest_targets(self):
        return _digest([[list(m.counts), m.receipt, port, list(t.counts), t.receipt]
            for (m, port), t in self._targets.items()])

    def _kernel(self, component, active, absorbed):
        key = component, active, absorbed
        if key not in self._kernels:
            kernel = _compile(self._source, component, active, absorbed, self._bits)
            value = kernel, _digest(_kernel_record(kernel, self._bits))
            self._kernels[key] = value
            _KERNELS[id(self), key] = value
        kernel, seal = self._kernels[key]
        issued = _KERNELS.get((id(self), key))
        _require(issued is not None and kernel is issued[0] and seal == issued[1] and
            _digest(_kernel_record(kernel, self._bits)) == seal and
            [[list(axes), list(before), list(after), route, a, b, e]
             for axes, columns in sorted(kernel['groups'].items()) for before, paths in sorted(columns.items())
             for after, route, a, b, e in paths] == kernel['rows'], 'compiled source coefficient table changed')
        return kernel

    def compile(self, component, *, slice_start):
        raw = RetardedComponentIntegerAction.record(self); component = _component(component)
        _, active = trajectory.RetardedGaussianTrajectorySource._clock(self._source, slice_start)
        active = tuple(active)
        return {'schema': SCHEMA+'/compiled', 'source_record': raw, 'component': component,
            'source_slice_start_seconds': str(full.nonnegative(slice_start)), 'source_active_legs': list(active),
            'pending_kernel': _kernel_record(self._kernel(component, active, False), self._bits),
            'absorbed_kernel': _kernel_record(self._kernel(component, active, True), self._bits)}

    def verify_compilation(self, report):
        _require(type(report) is dict, 'source compilation report required')
        expected = RetardedComponentIntegerAction.compile(self, report['component'],
            slice_start=report['source_slice_start_seconds'])
        _require(_copy(report) == _copy(expected), 'compiled image, price, source or clock changed')
        return True

    def _action(self, component, state, active, output_bits):
        RetardedComponentIntegerAction._runtime(self)
        component = _component(component); trajectory.gaussian._precision(output_bits)
        _require(type(active) is tuple and len(active) == 2 and all(type(x) is bool for x in active),
                 'complete two-arm source activation required')
        integers, input_bits = _input_grid(self._source, state)
        kernels = {value: self._kernel(component, active, value) for value in (False, True)}
        result, error, zero, primitive, rounding = _apply(self._source, kernels, integers,
            input_bits, self._bits, output_bits, self._targets)
        pairs = {key: (_dyadic(a, output_bits), _dyadic(b, output_bits)) for key, (a, b) in result.items()}
        return pairs, error, zero, {'primitive_coefficient_rounding_per_second': str(primitive),
            'complete_output_grid_rounding_per_second': str(rounding),
            'input_bits': input_bits, 'output_bits': output_bits, 'source_active_legs': list(active)}

    def action_pairs(self, component, state, *, slice_start, output_bits=None):
        RetardedComponentIntegerAction.record(self)
        _, active = trajectory.RetardedGaussianTrajectorySource._clock(self._source, slice_start)
        return RetardedComponentIntegerAction._action(self, component, state, tuple(active),
            self._bits if output_bits is None else output_bits)

    def phase_error(self, component, state, active):
        RetardedComponentIntegerAction._runtime(self); component = _component(component)
        if component != 'quiet' and component[0] == 'drive' and active[component[1]]:
            integers, bits = _input_grid(self._source, state)
            total = sum(abs(a)+abs(b) for (mark, _, _), (a, b) in integers.items() if mark.receipt is None)
            return self._source._parts[component[1]][3]*Q(total, 1 << bits)
        return Q(0)

    def component_action_and_price(self, component, state, *, slice_start, output_bits=None):
        RetardedComponentIntegerAction.record(self); component = _component(component)
        bits = self._bits if output_bits is None else output_bits
        blocks = trajectory.RetardedGaussianTrajectorySource._blocks(self._source, state)
        exact = {(mark, i, j): value for mark, matrix in blocks.items() for (i, j), value in matrix.items()}
        pairs = {}; input_price = Q(0)
        for key, value in exact.items():
            a, b, error = _quantize(value, bits)
            if a or b:
                pairs[key] = _dyadic(a, bits), _dyadic(b, bits)
            input_price += Q(error, 1 << bits)
        _, active = trajectory.RetardedGaussianTrajectorySource._clock(self._source, slice_start)
        active = tuple(active)
        result, price, zero, details = RetardedComponentIntegerAction._action(self, component, pairs, active, bits)
        norm = max(self._kernel(component, active, absorbed)['norm'] for absorbed in (False, True))
        input_payment = input_price*Q(norm, 1 << self._bits)
        phase = RetardedComponentIntegerAction.phase_error(self, component, pairs, active)
        if component != 'quiet' and component[0] == 'drive' and active[component[1]]:
            phase += self._source._parts[component[1]][3]*input_price
        details.update({'input_quantization_per_second': str(input_payment),
            'source_drive_phase_per_second': str(phase), 'input_state_positivity_certified': False,
            'source_generated_zero_support': zero})
        return {key: dipole.ComplexRadical(*pair) for key, pair in result.items()}, price+input_payment+phase, details


class IntegerColumns:
    """The original checker/writer column protocol, with whole integer actions."""
    def __init__(self, source, bits=192):
        self.source, self.bits = source, bits
        self.owner = RetardedComponentIntegerAction(source, coefficient_bits=bits)
        _COLUMNS[id(self)] = source, bits, self.owner

    def _closed(self):
        _CHECK(); owned = _COLUMNS.get(id(self))
        _require(type(self) is IntegerColumns and set(vars(self)) == {'source', 'bits', 'owner'} and
            owned is not None and self.source is owned[0] and self.bits == owned[1] and self.owner is owned[2] and
            self.owner._source is self.source, 'closed original integer column owner required')

    def action(self, component, state, active):
        IntegerColumns._closed(self)
        image, price, zero, _ = RetardedComponentIntegerAction._action(self.owner, component, state, tuple(active), self.bits)
        return image, price, zero

    def phase_error(self, component, state, active):
        IntegerColumns._closed(self)
        return RetardedComponentIntegerAction.phase_error(self.owner, component, state, tuple(active))


class _ProposalColumns:
    def __init__(self, source, bits, maximum_count_sum):
        self.columns = IntegerColumns(source, bits)
        self.bits, self.maximum_count_sum, self.cache = bits, maximum_count_sum, {}

    def action(self, component, state, active):
        # These dictionaries are private immutable-by-use polynomial terms
        # of this writer.  Memoization is not consumed by the independent
        # checker, which always constructs fresh IntegerColumns.
        RetardedComponentIntegerAction._runtime(self.columns.owner)
        key = component, id(state), active
        saved = self.cache.get(key)
        if saved is not None and saved[0] is state:
            return saved[1]
        image, price, zero = IntegerColumns.action(self.columns, component, state, active)
        if self.maximum_count_sum is not None:
            image = {key: value for key, value in image.items()
                     if sum(key[0].counts) <= self.maximum_count_sum}
        result = image, price, zero
        self.cache[key] = state, result
        return result


def generate_trial(source, initial=None, stop=None, *, start=None, slices=1,
                   order=16, mode_bits=96, envelope_order=10, maximum_count_sum=2):
    """Produce an untrusted curve with the original complete issued inlet.

    The count budget affects only the proposal.  The checked action and the
    independent residual retain all original capped-count Marks.
    """
    _CHECK(); _CERTIFICATE_CHECK()
    _require(type(source) is checked.RetardedReceiptTrajectoryCertificate,
             'closed original continuous receipt source required')
    raw = checked.RetardedReceiptTrajectoryCertificate.record(source)
    _require(maximum_count_sum is None or (type(maximum_count_sum) is int and maximum_count_sum >= 0),
             'nonnegative proposal count budget or explicit complete override required')
    original, _, issued = checked.RetardedReceiptTrajectoryCertificate._input(source, initial, 0)
    g0, g1 = map(Q, raw['stopped_trajectory_source']['retarded_source']['gate_seconds'])
    start = g0 if start is None else full.nonnegative(start)
    stop = g1 if stop is None else full.nonnegative(stop)
    _require(g0 <= start <= stop <= g1 and (not issued or start == g0), 'original complete source input cut required')
    trajectory.gaussian._precision(mode_bits)
    _require(type(slices) is int and slices > 0 and type(order) is int and 0 <= order <= 64,
             'finite untrusted numerical budget required')
    _, current, _, _ = checked._initial(source._source, original, start, mode_bits)
    columns = _ProposalColumns(source._source, mode_bits, maximum_count_sum)
    driven = raw['stopped_trajectory_source']['retarded_source']['complete_driven_field_source']
    births = tuple(Q(a)+Q(b) for a, b in zip(driven['flight_seconds'], driven['emission_origins_seconds']))
    edges = sorted({start+n*(stop-start)/slices for n in range(slices+1)} |
                   {birth for birth in births if start < birth < stop})
    pieces = []
    for origin, end in zip(edges, edges[1:]):
        width = end-origin
        active, descriptors = checked._descriptors(source._source, columns, origin, end, [current], envelope_order)
        modes = [current]
        for degree in range(order):
            derivative = {}
            for component, frequency, polynomial, _, _ in descriptors:
                for j in range(degree+1):
                    scalar = dipole.ComplexRadical()
                    for k, (a, b) in enumerate(polynomial[:j+1]):
                        scalar += dipole.ComplexRadical(a, b)*checked._power(
                            dipole.ComplexRadical(0, frequency*width), j-k)*Q(1, factorial(j-k))
                    pair = scalar.real.as_rational(), scalar.imag.as_rational()
                    if pair == (0, 0):
                        continue
                    image, _, _ = _ProposalColumns.action(columns, component, modes[degree-j], active)
                    checked._add(derivative, image, pair)
            proposal = {key: (a*width/(degree+1), b*width/(degree+1))
                        for key, (a, b) in derivative.items()}
            proposal, _ = checked.fourier.exact._dyadic_state(checked._hermitian(proposal), mode_bits)
            modes.append(proposal)
        pieces.append({'duration_seconds': str(width), 'modes': [{'lambda_per_second': ['0', '0'],
            'coefficients': [checked._rows(matrix, mode_bits) for matrix in modes]}]})
        current = {}
        for matrix in modes:
            checked._add(current, matrix)
    return {'schema': checked.SCHEMA+'/untrusted-curve', 'source_record': raw,
        'complete_initial_marked_state': checked._record_state(original), 'source_issued_input_used': issued,
        'source_detector_interval_seconds': list(map(str, (start, stop))), 'mode_bits': mode_bits,
        'pieces': pieces, 'writer_correctness_assumed': False}


def certify(source, trial, *, upstream_error=0, coefficient_bits=192, exponential_bits=192, envelope_order=10):
    """Original complete defect formula with independently enclosed integer G actions."""
    _CHECK(); _CERTIFICATE_CHECK()
    _require(type(source) is checked.RetardedReceiptTrajectoryCertificate,
             'closed original continuous receipt source required')
    raw = checked.RetardedReceiptTrajectoryCertificate.record(source)
    _require(type(trial) is dict and set(trial) == {'schema', 'source_record', 'complete_initial_marked_state',
        'source_issued_input_used', 'source_detector_interval_seconds', 'mode_bits', 'pieces',
        'writer_correctness_assumed'} and trial['schema'] == checked.SCHEMA+'/untrusted-curve' and
        trial['source_record'] == raw and trial['writer_correctness_assumed'] is False,
        'curve must bind its complete original stopped source')
    mode_bits = trial['mode_bits']
    for bits in (mode_bits, coefficient_bits, exponential_bits):
        trajectory.gaussian._precision(bits)
    if source._inlet is None:
        initial, inherited, issued = checked.RetardedReceiptTrajectoryCertificate._input(
            source, trial['complete_initial_marked_state'], upstream_error)
    else:
        initial, inherited, issued = checked.RetardedReceiptTrajectoryCertificate._input(source, None, upstream_error)
        _require(checked._record_state(initial) == trial['complete_initial_marked_state'], 'issued source input changed')
    _require(trial['source_issued_input_used'] is issued and type(trial['pieces']) is list, 'input issuance is source-owned')
    start, stop = map(full.nonnegative, trial['source_detector_interval_seconds'])
    trajectory.RetardedGaussianTrajectorySource._clock(source._source, start)
    trajectory.RetardedGaussianTrajectorySource._clock(source._source, stop)
    _require(start <= stop and (not issued or start == Q(raw['stopped_trajectory_source']['retarded_source']['gate_seconds'][0])),
             'complete original source interval required')
    _, current, entry, initial_norm = checked._initial(source._source, initial, start, coefficient_bits)
    if issued:
        initial_norm = min(initial_norm, Q(raw['source_issued_inlet']['source_centre_trace_norm_upper']))
    columns = IntegerColumns(source._source, coefficient_bits)
    time = start; accumulated = entry; records = []
    for piece in trial['pieces']:
        before = accumulated
        width, current, uniform, endpoint, detail = checked._piece(source._source, columns,
            piece, current, time, mode_bits, exponential_bits, envelope_order)
        time += width; accumulated += uniform+endpoint
        detail['previous_rotating_endpoint_error'] = str(field._price_upper(before, coefficient_bits))
        records.append(detail)
    _require(time == stop, 'complete curve coverage required')
    physical, frame = trajectory.RetardedGaussianTrajectorySource.frame(source._source, stop, checked._exact(current))
    model, model_record = checked._gamma_price(source._source, initial_norm, start, stop, coefficient_bits)
    return {'schema': SCHEMA+'/checked-complete-curve', 'source_record': raw, 'untrusted_trial': _copy(trial),
        'integer_action_source': RetardedComponentIntegerAction.record(columns.owner), 'source_bindings': _bindings(),
        'complete_physical_marked_endpoint': checked._record_state(physical),
        'whole_upstream_trace_norm_error_once': str(inherited),
        'source_initial_trace_norm_upper': str(field._price_upper(initial_norm, coefficient_bits)),
        'source_rotating_curve_error': str(field._price_upper(accumulated, coefficient_bits)),
        'physical_frame_readout_error': str(field._price_upper(frame, coefficient_bits)),
        'mathematical_Gamma_full_marked_price': str(field._price_upper(model, coefficient_bits)),
        'Gamma_price_components': model_record,
        'global_trace_norm_error': str(field._price_upper(inherited+accumulated+frame+model, coefficient_bits)),
        'source_detector_interval_seconds': list(map(str, (start, stop))), 'piece_records': records,
        'source_issued_input_used': issued, 'actual_hardware_member_asserted': False,
        'endpoint_price_substituted_for_uniform_error': False, 'Hermitian_CPTP_contraction_used': True,
        'coefficient_bits': coefficient_bits, 'exponential_bits': exponential_bits, 'envelope_order': envelope_order}


def verify(source, report):
    _require(type(report) is dict and report.get('schema') == SCHEMA+'/checked-complete-curve',
             'named complete integer-action curve certificate required')
    expected = certify(source, report['untrusted_trial'], upstream_error=(
        report['whole_upstream_trace_norm_error_once'] if source._inlet is None else 0),
        coefficient_bits=report['coefficient_bits'], exponential_bits=report['exponential_bits'],
        envelope_order=report['envelope_order'])
    _require(expected == report, 'complete original residual, integer price or endpoint changed')
    return expected


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    helpers = (_require, _copy, _digest, _bindings, _primitive_digest, _component, _nearest, _ceil, _dyadic, _quantize, _sum, _operator,
        _paths, _compile, _kernel_record, _marked_coordinates, _input_grid, _apply, _function, _signature, _check,
        generate_trial, certify, verify, checked._descriptors, checked._initial, checked._piece,
        checked._gamma_price, checked._record_state, checked._exact, checked._hermitian, checked._add, checked._power,
        checked.RetardedReceiptTrajectoryCertificate.record, checked.RetardedReceiptTrajectoryCertificate._input,
        full.radical_midpoint, field._closed, channel._canonical, bsm.BSMSource.target,
        trajectory.RetardedGaussianTrajectorySource.record, trajectory.RetardedGaussianTrajectorySource._clock,
        trajectory.RetardedGaussianTrajectorySource._blocks, Q.__new__)
    classes = tuple(tuple(_function(v) for v in vars(cls).values() if callable(v))
                    for cls in (RetardedComponentIntegerAction, IntegerColumns, _ProposalColumns))
    return tuple(map(_function, helpers)), classes, SCHEMA, full.DIMENSION, trajectory.COMPONENTS, tuple(dipole.STATES)


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
        trajectory._CHECK is _SOURCE_CHECK and checked._CHECK is _CERTIFICATE_CHECK,
        'retarded integer action execution closure changed')
    _SOURCE_CHECK(); _CERTIFICATE_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
