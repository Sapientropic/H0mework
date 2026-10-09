"""The original free/registered generator acts directly on two local factors."""
from fractions import Fraction as Q

import retarded_registered_duhamel_rha0031 as source
import factorized_local_phase_source as factors

trajectory, dipole, joint, bsm = source.trajectory, source.dipole, source.joint, source.bsm
SCHEMA = 'stage10-original-registered-tensor-action/rha0034'
PARTS = ('registered', 'free', 'full')


def _local(matrix):
    source.require(type(matrix) is dict and all(type(key) is tuple and len(key) == 2 and
        all(type(i) is int and 0 <= i < 33 for i in key) for key in matrix), 'complete local33 matrix coordinates required')
    return {key: dipole.complex_exact(value) for key, value in matrix.items() if value}


def _row(result, target, coefficient, *, left=None, right=None):
    coefficient = dipole.complex_exact(coefficient)
    if coefficient:
        result.append((target, coefficient, tuple(left or (None, None)), tuple(right or (None, None))))


def _rows(original, part, component, mark, active):
    rows = []
    if part in ('free', 'full'):
        if mark.receipt is not None:
            if component == 'quiet':
                legs = original._value['retarded_source']['complete_driven_field_source']['Gaussian_source_legs']
                for side, on in enumerate(active):
                    if on:
                        k = {(i, i): dipole.ComplexRadical(0, Q(legs[side]['carrier_angular_frequency_per_second']))
                             for i, state in enumerate(dipole.STATES) if state.family == 'D2'}
                        left, right = [None, None], [None, None]
                        left[side] = k; right[side] = dipole.matrix_adjoint(k)
                        _row(rows, mark, 1, left=left); _row(rows, mark, 1, right=right)
        elif component == 'quiet' or component[0] == 'drive':
            for side, on in enumerate(active):
                if not on or (component != 'quiet' and component[1] != side): continue
                k = original._parts[side][0 if component == 'quiet' else 1]
                left, right = [None, None], [None, None]
                left[side] = k; right[side] = dipole.matrix_adjoint(k)
                _row(rows, mark, 1, left=left); _row(rows, mark, 1, right=right)
                if component == 'quiet':
                    for rate, jump in original._parts[side][2]:
                        left, right = [None, None], [None, None]
                        left[side] = jump; right[side] = dipole.matrix_adjoint(jump)
                        _row(rows, mark, rate, left=left, right=right)
    if part in ('registered', 'full') and mark.receipt is None:
        if component == 'quiet':
            beta = map(Q, original._value['retarded_source']['BG_source']['BG_rates_per_second'])
            for port, rate in enumerate(beta):
                _row(rows, bsm.BSMSource.target(original._law._gate, mark, port), rate)
                _row(rows, mark, -rate)
        if component == 'quiet' or component[0] == 'cross':
            for group, rate, modes in original._law._groups:
                for mu, (side, first) in modes:
                    for nu, (other, second) in modes:
                        if not (active[side] and active[other]): continue
                        cross = group[0] == 'D2' and side != other
                        if (component == 'quiet' and cross) or (component != 'quiet' and
                            not (cross and (side, other) == component[1:])): continue
                        left, right = [None, None], [None, None]
                        left[side] = first; right[other] = dipole.matrix_adjoint(second)
                        for port in range(4):
                            coefficient = rate*original._law._transfer[port][mu]*original._law._transfer[port][nu].conjugate()
                            target = bsm.BSMSource.target(original._law._gate, mark, port)
                            _row(rows, target, coefficient, left=left, right=right)
                            _row(rows, mark, -coefficient, left=left, right=right)
    return rows


def _multiply(matrix, left, right):
    value = matrix if left is None else dipole.matrix_product(left, matrix)
    return value if right is None else dipole.matrix_product(value, right)


def _apply_rows(rows, coefficient, first, second):
    result = []
    for target, scale, left, right in rows:
        a = _multiply(first, left[0], right[0]); b = _multiply(second, left[1], right[1])
        if a and b: result.append((target, coefficient*scale, a, b))
    return result


def merge(terms):
    result = {}
    for mark, scale, a, b in terms:
        key = mark, source.digest(trajectory.channel._input_record(a)), source.digest(trajectory.channel._input_record(b))
        if key not in result: result[key] = [mark, dipole.ComplexRadical(), a, b]
        result[key][1] += scale
    return tuple(tuple(row) for row in result.values() if row[1])


def expand(terms):
    result = {}
    for mark, coefficient, first, second in terms:
        trajectory._mark(result, mark, factors._tensor(first, second), coefficient)
    return result


def _terms(original, terms):
    result = []
    for mark, scale, first, second in terms:
        source.require(mark in original._marks, 'complete source-generated Mark identity required')
        result.append((mark, dipole.complex_exact(scale), _local(first), _local(second)))
    return result


def _apply(original, part, component, terms, active):
    result = []
    for mark, scale, first, second in terms:
        result.extend(_apply_rows(_rows(original, part, component, mark, active), scale, first, second))
    return merge(result)


def apply(split, component, terms, *, slice_start, part='registered'):
    source.require(type(split) is source.RetardedRegisteredDuhamelSource, 'closed original registered split required')
    split.record(); component = tuple(component) if isinstance(component, list) else component
    source.require(component in trajectory.COMPONENTS and part in PARTS, 'original component and explicit free/registered/full part required')
    original = split._source; _, active = original._clock(slice_start)
    return _apply(original, part, component, _terms(original, terms), active)


def layer_rhs(split, component, layers, *, slice_start):
    source.require(type(split) is source.RetardedRegisteredDuhamelSource, 'closed original registered split required')
    split.record(); component = tuple(component) if isinstance(component, list) else component
    source.require(component in trajectory.COMPONENTS and type(layers) in (list, tuple) and
        1 <= len(layers) <= 129, 'finite original component layers required')
    original = split._source; _, active = original._clock(slice_start)
    values = [_terms(original, terms) for terms in layers]; result = []
    for index, terms in enumerate(values):
        free = _apply(original, 'free', component, terms, active)
        forcing = _apply(original, 'registered', component, values[index-1], active) if index else ()
        result.append(merge((*free, *forcing)))
    return tuple(result)


def program_record(rows):
    return [{'target': {'counts': list(mark.counts), 'receipt': mark.receipt}, 'coefficient': coefficient.serialize(),
        'left_operators': [None if a is None else trajectory.channel._input_record(a) for a in left],
        'right_operators': [None if a is None else trajectory.channel._input_record(a) for a in right]}
        for mark, coefficient, left, right in rows]
