"""Untrusted NumPy proposals for the original complete retarded source.

The source issues the initial matrix and every small local path.  Floating
arithmetic only proposes dyadic polynomial coefficients.  Certification is
left to retarded_component_integer_action.certify on all original Marks.
"""
from fractions import Fraction as Q
from math import factorial

import numpy as np
import retarded_component_integer_action as integer

checked, trajectory = integer.checked, integer.trajectory
full, dipole, bsm = integer.full, integer.dipole, integer.bsm


def _require(value, message):
    if not value:
        raise ValueError(message)


def policy(*, maximum_count_sum=2, mode_bits=96):
    return {'writer': 'source-local-path NumPy scalar-convolution proposal',
        'numerical_candidate_maximum_capped_count_sum': maximum_count_sum,
        'candidate_coefficient_bits': mode_bits,
        'all_original_initial_coordinates_retained': True,
        'cached_component_images': False, 'count_projection_is_physical_source_support': False,
        'floating_arithmetic_is_certified': False,
        'independent_checker': 'retarded_component_integer_action.certify, all original Marks'}


class _State:
    def __init__(self, keys, values):
        self.keys, self.values = keys, values


class _Paths:
    def __init__(self, source, initial, maximum_count_sum, bits):
        self.owner = integer.RetardedComponentIntegerAction(source, coefficient_bits=bits)
        self.source, self.bits, self.cache = source, bits, {}
        self.marks = source._marks
        self.ids = {mark: n for n, mark in enumerate(self.marks)}
        self.dimension = full.DIMENSION**2
        self.size = self.dimension**2
        allowed = tuple(maximum_count_sum is None or sum(m.counts) <= maximum_count_sum for m in self.marks)
        initial_marks = {mark for mark, _, _ in initial}
        included = tuple(n for n, mark in enumerate(self.marks) if allowed[n] or mark in initial_marks)
        self.global_ids = np.asarray(included, dtype=np.int64)
        self.compact = np.full(len(self.marks), -1, dtype=np.int64)
        self.compact[self.global_ids] = np.arange(len(included), dtype=np.int64)
        self.allowed = np.asarray(allowed, dtype=np.bool_)
        self.absorbed = np.asarray([m.receipt is not None for m in self.marks], dtype=np.bool_)
        # The stopped source has only frame counterflow on receipt blocks;
        # the unstopped gate's later count targets are outside this inventory.
        self.targets = np.asarray([[self.ids[mark if mark.receipt is not None else self.owner._targets[mark, port]]
                                    for port in range(4)] for mark in self.marks], dtype=np.int64)
        self.strides = (self.dimension*full.DIMENSION, self.dimension, full.DIMENSION, 1)
        self.length = len(included)*self.size

    def input(self, pairs):
        rows = sorted((self.ids[mark]*self.size+i*self.dimension+j, complex(float(a), float(b)))
                      for (mark, i, j), (a, b) in pairs.items() if a or b)
        return _State(np.fromiter((key for key, _ in rows), dtype=np.int64, count=len(rows)),
                      np.fromiter((value for _, value in rows), dtype=np.complex128, count=len(rows)))

    def add(self, target, state, coefficient):
        if coefficient and state.keys.size:
            marks, coords = np.divmod(state.keys, self.size)
            addresses = self.compact[marks]*self.size+coords
            _require(np.all(addresses >= 0), 'original initial Marks must remain in the numerical carrier')
            target[addresses] += coefficient*state.values

    def state(self, dense, *, quantize_bits=None):
        if quantize_bits is not None:
            dense.real[:] = np.ldexp(np.rint(np.ldexp(dense.real, quantize_bits)), -quantize_bits)
            dense.imag[:] = np.ldexp(np.rint(np.ldexp(dense.imag, quantize_bits)), -quantize_bits)
        _require(np.all(np.isfinite(dense)), 'finite numerical proposal budget exhausted')
        compact = np.flatnonzero(dense)
        marks, coords = np.divmod(compact, self.size)
        keys = self.global_ids[marks]*self.size+coords
        return _State(keys, dense[compact].copy())

    def groups(self, component, active, absorbed):
        key = component, active, absorbed
        if key not in self.cache:
            kernel = integer.RetardedComponentIntegerAction._kernel(self.owner, component, active, absorbed)
            answer = []
            for axes, columns in kernel['groups'].items():
                dimension = full.DIMENSION**len(axes)
                count = max(map(len, columns.values()), default=0)
                coefficient = np.zeros((count, dimension), dtype=np.complex128)
                route = np.full((count, dimension), -1, dtype=np.int8)
                delta = np.zeros((count, dimension), dtype=np.int64)
                for before, paths in columns.items():
                    address = 0
                    for value in before:
                        address = full.DIMENSION*address+value
                    for n, (after, port, a, b, _) in enumerate(paths):
                        coefficient[n, address] = complex(float(integer._dyadic(a, self.bits)),
                                                         float(integer._dyadic(b, self.bits)))
                        route[n, address] = port
                        delta[n, address] = sum((out-start)*self.strides[axis]
                                               for axis, start, out in zip(axes, before, after))
                _require(np.all(np.isfinite(coefficient)), 'finite source coefficient proposal required')
                answer.append((axes, coefficient, route, delta))
            self.cache[key] = answer
        return self.cache[key]

    def action(self, component, state, active, target):
        integer.RetardedComponentIntegerAction._runtime(self.owner)
        if not state.keys.size:
            return
        marks, quantum = np.divmod(state.keys, self.size)
        row, column = np.divmod(quantum, self.dimension)
        coords = (row//full.DIMENSION, row%full.DIMENSION,
                  column//full.DIMENSION, column%full.DIMENSION)
        for absorbed in (False, True):
            admitted = self.absorbed[marks] == absorbed
            if not np.any(admitted):
                continue
            for axes, coefficients, routes, deltas in self.groups(component, active, absorbed):
                selector = np.zeros(state.keys.size, dtype=np.int64)
                for axis in axes:
                    selector = full.DIMENSION*selector+coords[axis]
                for values, ports, offsets in zip(coefficients, routes, deltas):
                    factors = values[selector]
                    selected = admitted & (factors != 0)
                    if not np.any(selected):
                        continue
                    input_marks = marks[selected]
                    port = ports[selector[selected]]
                    destination_marks = input_marks.copy()
                    moving = port >= 0
                    destination_marks[moving] = self.targets[input_marks[moving], port[moving]]
                    retain = self.allowed[destination_marks]
                    if not np.any(retain):
                        continue
                    destinations = (self.compact[destination_marks]*self.size+quantum[selected]+
                                    offsets[selector[selected]])
                    np.add.at(target, destinations[retain],
                              (factors[selected]*state.values[selected])[retain])

    def rows(self, state, bits):
        result = []
        for key, value in zip(state.keys, state.values):
            n, quantum = divmod(int(key), self.size)
            i, j = divmod(quantum, self.dimension)
            mark = self.marks[n]
            a = int(np.rint(np.ldexp(value.real, bits)))
            b = int(np.rint(np.ldexp(value.imag, bits)))
            if a or b:
                result.append([list(mark.counts), mark.receipt, i, j, a, b])
        return result


def _scalars(source, origin, end, order, envelope_order):
    raw = trajectory.RetardedGaussianTrajectorySource.slice_components(
        source, origin, end, envelope_order=envelope_order)
    result = []
    for item in raw['components']:
        component = integer._component(item['component'])
        polynomial = item['polynomial_coefficients']
        if polynomial and type(polynomial[0]) is list:
            polynomial = [complex(float(Q(a)), float(Q(b))) for a, b in polynomial]
        else:
            polynomial = [complex(float(Q(a))) for a in polynomial]
        word = 1j*float(Q(item['exact_frequency_per_second'])*(end-origin))
        exponential = [1+0j]
        for n in range(1, order+1):
            exponential.append(exponential[-1]*word/n)
        scalar = [sum(polynomial[k]*exponential[n-k] for k in range(min(n+1, len(polynomial))))
                  for n in range(order+1)]
        _require(np.all(np.isfinite(scalar)), 'finite scalar word proposal required')
        result.append((component, scalar))
    return tuple(raw['source_active_legs']), result


def generate_trial(source, initial=None, stop=None, *, start=None, slices=1,
                   order=16, mode_bits=96, envelope_order=10, maximum_count_sum=2,
                   progress=None):
    """Return a complete original-schema proposal; no numerical result is certified."""
    integer._CHECK()
    _require(type(source) is checked.RetardedReceiptTrajectoryCertificate,
             'closed original continuous receipt source required')
    raw = checked.RetardedReceiptTrajectoryCertificate.record(source)
    _require(maximum_count_sum is None or (type(maximum_count_sum) is int and maximum_count_sum >= 0),
             'nonnegative numerical count budget or explicit complete override required')
    original, _, issued = checked.RetardedReceiptTrajectoryCertificate._input(source, initial, 0)
    g0, g1 = map(Q, raw['stopped_trajectory_source']['retarded_source']['gate_seconds'])
    start = g0 if start is None else full.nonnegative(start)
    stop = g1 if stop is None else full.nonnegative(stop)
    _require(g0 <= start <= stop <= g1 and (not issued or start == g0), 'original source input cut required')
    trajectory.gaussian._precision(mode_bits)
    _require(type(slices) is int and slices > 0 and type(order) is int and 0 <= order <= 64,
             'finite numerical proposal budget required')
    _, pairs, _, _ = checked._initial(source._source, original, start, mode_bits)
    paths = _Paths(source._source, pairs, maximum_count_sum, mode_bits)
    current = paths.input(pairs)
    driven = raw['stopped_trajectory_source']['retarded_source']['complete_driven_field_source']
    births = tuple(Q(a)+Q(b) for a, b in zip(driven['flight_seconds'], driven['emission_origins_seconds']))
    edges = sorted({start+n*(stop-start)/slices for n in range(slices+1)} |
                   {birth for birth in births if start < birth < stop})
    pieces = []
    convolution = np.zeros(paths.length, dtype=np.complex128)
    derivative = np.zeros_like(convolution)
    for origin, end in zip(edges, edges[1:]):
        width = end-origin
        active, descriptors = _scalars(source._source, origin, end, order, envelope_order)
        modes = [current]
        for degree in range(order):
            derivative.fill(0)
            for component, scalars in descriptors:
                convolution.fill(0)
                for j in range(degree+1):
                    paths.add(convolution, modes[degree-j], scalars[j])
                paths.action(component, paths.state(convolution), active, derivative)
            derivative *= float(width/Q(degree+1))
            matrix = derivative.reshape(len(paths.global_ids), paths.dimension, paths.dimension)
            matrix += matrix.conjugate().swapaxes(1, 2)
            matrix *= .5
            modes.append(paths.state(derivative, quantize_bits=mode_bits))
            if progress is not None:
                progress({'completed_degree': degree+1, 'complete_nonzero_coordinates': int(modes[-1].keys.size),
                          'source_interval_seconds': [str(origin), str(end)]})
        pieces.append({'duration_seconds': str(width), 'modes': [{'lambda_per_second': ['0', '0'],
            'coefficients': [paths.rows(mode, mode_bits) for mode in modes]}]})
        convolution.fill(0)
        for mode in modes:
            paths.add(convolution, mode, 1)
        current = paths.state(convolution, quantize_bits=mode_bits)
    return {'schema': checked.SCHEMA+'/untrusted-curve', 'source_record': raw,
        'complete_initial_marked_state': checked._record_state(original), 'source_issued_input_used': issued,
        'source_detector_interval_seconds': [str(start), str(stop)], 'mode_bits': mode_bits,
        'pieces': pieces, 'writer_correctness_assumed': False}
