"""The original complete-Z CEM generates terminal registration restrictions.

Full acceptance gates make new ion births commute with terminal marking.
An incoming ION restriction stays unregistered; only an originally neutral
cohort receives the generated efficiency.  The private mother is retained.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib

import full_zeeman_cem_source as cem

SCHEMA = 'stage10-full-Z-CEM-source-terminal-registration-reduction/v1'
_SOURCE_CHECK = cem._CHECK


def _require(value, message):
    if not value:
        raise ValueError(message)


def _mark(matrix, eta, occupied):
    if occupied:
        return cem.window._terminal_local_marking(matrix, eta)
    _require(all(i == j == cem.dipole.ION for i, j in matrix), 'original Empty cohort restriction required')
    return {(0, i, j): value for (i, j), value in matrix.items()}


def _marked_action(atom, z, kappa, marked):
    result = cem.window._local_marked_action(atom, kappa, marked)
    for seen in (0, 1):
        matrix = {(i, j): value for (m, i, j), value in marked.items() if m == seen}
        for (i, j), value in _commute(z, matrix).items():
            cem.local._add(result, (seen, i, j), value)
    return result


def _commute(z, matrix):
    left = cem.dipole.matrix_product(z, matrix)
    right = cem.dipole.matrix_product(matrix, z)
    result = {}
    for key in set(left) | set(right):
        value = cem.dipole.ComplexRadical(0, -1)*(left.get(key, cem.dipole.ComplexRadical())-
                                                right.get(key, cem.dipole.ComplexRadical()))
        if value:
            result[key] = value
    return result


def _bindings():
    return {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in
            (Path(__file__), Path(cem.__file__), Path(cem.window.__file__))}


def certify(source):
    _CHECK(); cem._closed(source)
    _require(type(source) is cem.FullZeemanCEMSource,
             'closed original complete-Z CEM source required; target effects are not input')
    raw = cem.FullZeemanCEMSource.record(source)
    geometry = cem.FullZeemanCEMSource.geometry_source(source)
    base = cem.window.constant_gate_reduction(geometry)
    units = tuple((i, j) for i in range(cem.full.DIMENSION) for j in range(cem.full.DIMENSION)
                  if (i == cem.dipole.ION) == (j == cem.dipole.ION))
    rows = []; checked = set()
    for phase in source.phases():
        sides = []
        for side, (atom, z, kappa, registration) in enumerate(zip(
                phase._original.sources, phase._z, phase._original.kappas, geometry.registrations)):
            eta = 1-registration.probabilities[0]
            _require(not any(i == cem.dipole.ION or j == cem.dipole.ION for i, j in z),
                     'source Zeeman Hamiltonian must preserve the original neutral/ION split')
            primitive = atom.program.record(); primitive.pop('duration')
            signature = cem.channel._digest([primitive, cem.channel._input_record(z), str(eta), str(kappa)])
            if signature not in checked:
                for i, j in units:
                    matrix = {(i, j): cem.dipole.ComplexRadical(1)}
                    first = _marked_action(atom, z, kappa, _mark(matrix, eta, True))
                    complete = atom.atomic_action(matrix)
                    for key, value in _commute(z, matrix).items():
                        cem.local._add(complete, key, value)
                    second = _mark(complete, eta, True)
                    _require(first == second, 'complete source Z or ion-registration intertwiner changed')
                checked.add(signature)
            empty = {(cem.dipole.ION, cem.dipole.ION): cem.dipole.ComplexRadical(1)}
            _require(not _marked_action(atom, z, kappa, _mark(empty, eta, False)),
                     'an incoming Empty cohort must remain a fresh unregistered CEM input')
            sides.append({'side': side, 'eta': str(eta), 'complete_Z_terminal_commutation_checked': True,
                          'incoming_Empty_has_no_new_birth': True, 'local_block_basis_units': len(units)})
        rows.append({'phase_index': phase.index, 'sides': sides})
    return {'schema': SCHEMA, 'source_record': raw, 'original_geometry_reduction': base,
        'complete_Z_phase_inventory': rows, 'distinct_Z_and_eta_bases_checked': len(checked),
        'source_input_split': 'four original neutral/ION cohort restrictions; no cross-cohort coherence erased',
        'initial_ION_backfilled_as_registered_birth': False,
        'whole_channel_tensor_factorization': 'source local A tensor source local B',
        'background_OR_composed_once': True, 'numeric_channel_witness_supplied': False,
        'complete_CEM_output_generated_here': False, 'actual_hardware_uniquely_identified': False,
        'source_bindings': _bindings(), 'controller_advance': False}


def verify(source, report):
    _require(certify(source) == report, 'original full-Z terminal source certificate changed')
    return report


def _function(value):
    value = getattr(value, '__func__', value)
    return id(value), id(getattr(value, '__code__', None))


def _signature():
    return tuple(map(_function, (_require, _mark, _marked_action, _commute, _bindings, certify, verify,
        _function, _signature, _check, cem.FullZeemanCEMSource.record, cem.FullZeemanCEMSource.geometry_source,
        cem.FullZeemanCEMSource.phases, cem.window.constant_gate_reduction,
        cem.window._terminal_local_marking, cem.window._local_marked_action,
        cem.dipole.matrix_product, cem.local._add, cem.channel._input_record))), SCHEMA


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and cem._CHECK is _SOURCE_CHECK,
             'source complete-Z terminal reduction execution changed')
    _SOURCE_CHECK()


_CHECK, _SIGNATURE = _check, _signature
_EXPECTED = _signature()
