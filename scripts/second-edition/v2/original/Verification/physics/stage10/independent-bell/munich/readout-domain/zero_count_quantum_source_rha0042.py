"""All priority-issued no-count queries restrict the same quantum generator."""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import first_receipt_flux_source_rha0040 as flux
import registered_tensor_action_rha0034 as tensor
import retarded_gate_inlet_factors as inlet_factors
import completed_retarded_inlet_rha0028 as paid

base, trajectory = flux.base, tensor.trajectory
dipole, joint, channel, gaussian, bsm = base.dipole, base.joint, base.channel, base.gaussian, base.bsm
SCHEMA = 'stage10-source-priority-zero-count-quantum-generator/rha0042'
_ISSUED = {}


def _bindings():
    return {Path(p).name: hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in
        (__file__, *(m.__file__ for m in (flux, tensor, trajectory, inlet_factors, paid)))}


def _inside(mark, ports):
    return mark.receipt is None and not any(mark.counts[p] for p in ports)


def _merge(rows):
    result = {}
    for _, coefficient, left, right in rows:
        operators = [[None if a is None else channel._input_record(a) for a in side] for side in (left, right)]
        key = base.digest(operators)
        if key not in result:
            result[key] = [dipole.ComplexRadical(), left, right]
        result[key][0] += coefficient
    return tuple(tuple(row) for row in result.values() if row[0])


class NoCountQuantumSource:
    def __init__(self, original, priority, query=None):
        base.require(type(original) is trajectory.RetardedGaussianTrajectorySource and
            type(priority) is flux.FirstReceiptFluxSource and original._law is priority._original,
            'same closed original trajectory and source-issued priority queries required')
        raw, inventory = original.record(), priority.record()['complete_no_count_queries']
        if query is None:
            query = next((r['query'] for r in inventory if r['requires_coupled_no_count_flow']), 'all')
        selected = [r for r in inventory if r['query'] == query]
        base.require(type(query) is str and len(selected) == 1, 'original priority-issued no-count query required')
        ports = tuple(selected[0]['forbidden_ports'])
        for mark in original._marks:
            for port in range(4):
                target = bsm.BSMSource.target(original._law._gate, mark, port)
                base.require(_inside(target, ports) == (_inside(mark, ports) and port not in ports),
                             'original no-count projector is not closed under the actual Mark transition')
        programs = []
        for active in ((False, False), (False, True), (True, False), (True, True)):
            components = []
            for component in trajectory.COMPONENTS:
                rows = self._compile(original, ports, component, active)
                components.append({'component': component, 'rows': [
                    {'coefficient': c.serialize(),
                     'left_operators': [None if a is None else channel._input_record(a) for a in left],
                     'right_operators': [None if a is None else channel._input_record(a) for a in right]}
                    for c, left, right in rows]})
            programs.append({'source_active_legs': list(active), 'components': components})
        self._source, self._priority, self._ports = original, priority, ports
        self._value = {'schema': SCHEMA, 'original_trajectory_source': raw,
            'original_priority_source_sha256': base.digest(priority.record()), 'query': selected[0],
            'source_component_programs': programs, 'original_Mark_port_projectors_checked': 4*len(original._marks),
            'generator': 'original natural TP action minus forbidden coherent port actions and forbidden BG',
            'coordinates': 'the original two D2 rotating frames; both local clocks retained',
            'all_original_Gaussian_natural_and_cross_arm_components_retained': True,
            'source_action_is_CP_TNI': True, 'local_factorization_assumed': False,
            'old_Mark_state_bank_required_for_this_query': False, 'source_bindings': _bindings(),
            'complete_curve_certified': False, 'CEM_time_mother_issued': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False}
        self._seal = base.digest(self._value)
        _ISSUED[id(self)] = original, priority, ports, self._seal

    @staticmethod
    def _compile(original, ports, component, active):
        rows = tensor._rows(original, 'full', component, bsm.INITIAL, active)
        return _merge(row for row in rows if _inside(row[0], ports))

    def record(self):
        base.require(type(self) is NoCountQuantumSource and set(vars(self)) ==
            {'_source', '_priority', '_ports', '_value', '_seal'} and
            _ISSUED.get(id(self)) == (self._source, self._priority, self._ports, self._seal) and
            base.digest(self._value) == self._seal and self._value['source_bindings'] == _bindings() and
            self._source._law is self._priority._original and self._source.record() == self._value['original_trajectory_source'] and
            base.digest(self._priority.record()) == self._value['original_priority_source_sha256'],
            'original quantum source, priority, generated program or query changed')
        return json.loads(channel._canonical(self._value))

    def project(self, state):
        self.record()
        result = {}
        for mark, matrix in self._source._blocks(state).items():
            if _inside(mark, self._ports):
                base.law._add(result, matrix)
        return result

    def component_action(self, component, matrix, *, slice_start):
        self.record()
        component = tuple(component) if isinstance(component, list) else component
        base.require(component in trajectory.COMPONENTS, 'original source component required')
        _, active = self._source._clock(slice_start)
        matrix = joint._matrix(matrix)
        result = {}
        for coefficient, left, right in self._compile(self._source, self._ports, component, active):
            value = matrix
            for side in (0, 1):
                if left[side] is not None:
                    value = joint._operator_left(value, side, left[side])
                if right[side] is not None:
                    value = joint._operator_right(value, side, right[side])
            base.law._add(result, value, coefficient)
        return result

    def tensor_component_action(self, component, terms, *, slice_start):
        self.record()
        component = tuple(component) if isinstance(component, list) else component
        base.require(component in trajectory.COMPONENTS, 'original source component required')
        _, active = self._source._clock(slice_start)
        rows = self._compile(self._source, self._ports, component, active)
        result = []
        for scale, first, second in terms:
            first, second, scale = tensor._local(first), tensor._local(second), dipole.complex_exact(scale)
            for coefficient, left, right in rows:
                a = tensor._multiply(first, left[0], right[0])
                b = tensor._multiply(second, left[1], right[1])
                if a and b:
                    result.append((bsm.INITIAL, scale*coefficient, a, b))
        return tuple((scale, a, b) for _, scale, a, b in tensor.merge(result))

    def slice_components(self, start, stop, *, envelope_order=20):
        self.record()
        result = self._source.slice_components(start, stop, envelope_order=envelope_order)
        return {**result, 'source_record': self.record(), 'same_original_scalar_components': True}

    def physical_action(self, time, matrix):
        self.record()
        self._source._clock(time)
        matrix = joint._matrix(matrix)
        law = self._source._law
        value, error = law.independent_atomic_action(time, matrix, bits=self._source._value['scalar_bits'])
        times = law.local_times(time)
        for port in self._ports:
            base.law._add(value, law._detected(matrix, times, port), -1)
        beta = sum((Q(law.record()['BG_source']['BG_rates_per_second'][p]) for p in self._ports), Q(0))
        base.law._add(value, joint._matrix(matrix), -beta)
        return value, error


class NoCountPrimalInlet:
    def __init__(self, current, query):
        base.require(type(current) is paid.inlet.PreparedRetardedGaussianInlet and
            type(query) is NoCountQuantumSource and current._law is query._source._law,
            'same source-issued complete retarded inlet and quantum query required')
        raw = current.record()
        inlet_factors.factor_terms(raw, expected_local_cuts=tuple(query._source._clock(Q(raw['fixed_detector_gate_start_seconds']))[0]))
        self._current, self._query = current, query
        self._value = {'schema': SCHEMA+'/source-primal-inlet', 'source_current_sha256': base.digest(raw),
            'quantum_query_sha256': base.digest(query.record()), 'source_factor_ids': raw['source_factor_ids'],
            'checked_local_density_inventories': raw['checked_local_density_inventories'],
            'actual_retarded_local_cuts_seconds': raw['actual_retarded_local_cuts_seconds'],
            'source_positive_mass_upper': raw['source_positive_mass_upper'],
            'old_whole_input_error_once': raw['whole_retarded_gate_input_error'],
            'caller_initial_matrix_used': False, 'signed_factor_positivity_assumed': False,
            'actual_hardware_uniquely_identified': False, 'controller_advance': False}
        self._seal = base.digest(self._value)
        _ISSUED[id(self)] = current, query, self._seal

    def record(self):
        base.require(type(self) is NoCountPrimalInlet and set(vars(self)) ==
            {'_current', '_query', '_value', '_seal'} and
            _ISSUED.get(id(self)) == (self._current, self._query, self._seal) and
            base.digest(self._value) == self._seal and self._current._law is self._query._source._law and
            base.digest(self._current.record()) == self._value['source_current_sha256'] and
            base.digest(self._query.record()) == self._value['quantum_query_sha256'],
            'complete original no-count inlet, factor incidence or query changed')
        return json.loads(channel._canonical(self._value))

    def physical_factor_terms(self):
        self.record()
        return tuple((dipole.ComplexRadical(1), a, b) for a, b in inlet_factors.factor_terms(self._current.record()))
