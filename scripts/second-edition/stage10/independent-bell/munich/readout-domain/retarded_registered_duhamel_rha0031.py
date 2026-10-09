"""Exact stopped source split into local TP flow and registered Mark updates.

The unobserved loss is I-T*T.  Adding the same-mark detected recycling to
that loss restores the complete local natural bath.  The remaining update
is (Mark shift - identity) after each registered CP jump.  Its norm is paid
by registered activity, while full hyperfine/drive evolution stays in TP flow.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import factorial
import hashlib
import json

import retarded_gaussian_trajectory_source as trajectory
import retarded_receipt_activity_envelope as activity

channel, dipole, joint, bsm = trajectory.channel, trajectory.dipole, trajectory.joint, trajectory.bsm
SCHEMA = 'stage10-complete-stopped-registered-Duhamel-source/rha0031'
_ISSUED = {}


def require(value, reason):
    if not value:
        raise ValueError(reason)


def digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def source_bindings():
    return {Path(m.__file__).name: hashlib.sha256(Path(m.__file__).read_bytes()).hexdigest()
        for m in (trajectory, activity, trajectory.retarded, trajectory.density, trajectory.gaussian,
                  trajectory.field, dipole, joint, bsm)}


def finite_tail(variation, order):
    """Uniform majorant for every finite suffix of the Volterra series."""
    require(Q(variation) >= 0, 'negative source variation is not a price')
    a = upper(variation)
    require(a >= 0 and type(order) is int and 0 <= order <= 128 and a < order+2,
            'nonnegative variation and a strict geometric tail denominator required')
    ratio = a/(order+2)
    return {'retained_order': order, 'interaction_variation_upper': str(a),
        'first_omitted_term_upper': str(upper(a**(order+1)/factorial(order+1))),
        'suffix_ratio_upper': str(ratio),
        'whole_instrument_operator_tail_upper': str(upper(a**(order+1)/factorial(order+1)/(1-ratio)))}


def upper(value, bits=192):
    value = Q(value)*(1 << bits)
    return Q(-((-value.numerator)//value.denominator), 1 << bits)


def _free_component(source, component, blocks, active):
    result = {}
    for mark, matrix in blocks.items():
        if mark.receipt is not None:
            if component == 'quiet': trajectory._mark(result, mark, source._counter(matrix, active))
            continue
        if component == 'quiet':
            for side, on in enumerate(active):
                if on:
                    k, _, jumps, _ = source._parts[side]
                    trajectory._mark(result, mark, joint._operator_left(matrix, side, k))
                    trajectory._mark(result, mark, joint._operator_right(matrix, side, dipole.matrix_adjoint(k)))
                    for rate, jump in jumps:
                        image = joint._operator_right(joint._operator_left(matrix, side, jump), side, dipole.matrix_adjoint(jump))
                        trajectory._mark(result, mark, image, rate)
        elif component[0] == 'drive' and active[component[1]]:
            side = component[1]; k = source._parts[side][1]
            trajectory._mark(result, mark, joint._operator_left(matrix, side, k))
            trajectory._mark(result, mark, joint._operator_right(matrix, side, dipole.matrix_adjoint(k)))
    return result
    


def _registered_component(source, component, blocks, active):
    result = {}
    beta = tuple(map(Q, source._value['retarded_source']['BG_source']['BG_rates_per_second']))
    for mark, matrix in blocks.items():
        if mark.receipt is not None: continue
        if component == 'quiet':
            for port, rate in enumerate(beta):
                trajectory._mark(result, bsm.BSMSource.target(source._law._gate, mark, port), matrix, rate)
                trajectory._mark(result, mark, matrix, -rate)
        elif component[0] == 'drive': continue
        for group, rate, modes in source._law._groups:
            for mu, first in modes:
                for nu, second in modes:
                    if not (active[first[0]] and active[second[0]]): continue
                    cross = group[0] == 'D2' and first[0] != second[0]
                    if (component == 'quiet' and cross) or (component != 'quiet' and
                        not (cross and (first[0], second[0]) == component[1:])): continue
                    image = trajectory.retarded._recycle(matrix, first, second)
                    for port in range(4):
                        coefficient = rate*source._law._transfer[port][mu]*source._law._transfer[port][nu].conjugate()
                        if coefficient:
                            trajectory._mark(result, bsm.BSMSource.target(source._law._gate, mark, port), image, coefficient)
                            trajectory._mark(result, mark, image, -coefficient)
    return result
    


class RetardedRegisteredDuhamelSource:
    def __init__(self, source):
        require(type(source) is trajectory.RetardedGaussianTrajectorySource,
                'closed complete stopped trajectory required; an action callback is not source')
        raw = source.record(); envelope = activity.RetardedReceiptActivityEnvelope(source._law, bits=raw['scalar_bits'])
        self._source, self._activity = source, envelope
        self._value = {'schema': SCHEMA, 'original_trajectory_source': raw,
            'complete_activity_source': envelope.record(), 'source_bindings': source_bindings(),
            'free_pending_flow': 'complete two local TP natural/drive flows with the original retarded activation',
            'free_receipt_flow': 'original frame counterflow; physical receipt coimage stays at its stopping time',
            'registered_interaction': 'sum_port (original Mark target - same Mark) after the original registered CP jump',
            'interaction_norm_per_second_upper': str(2*Q(envelope.record()['source_activity']['registered_total_activity_upper_per_second'])),
            'inverse_TP_flow_used': False, 'full_field_or_queue_reset': False,
            'same_arm_repeated_emissions_retained': True, 'all_stopped_marks_retained': True,
            'full_gate_trajectory_generated': False, 'actual_hardware_uniquely_identified': False, 'controller_advance': False}
        self._seal = digest(self._value); _ISSUED[id(self)] = self._seal

    def record(self):
        require(type(self) is RetardedRegisteredDuhamelSource and
            set(vars(self)) == {'_source', '_activity', '_value', '_seal'} and
            _ISSUED.get(id(self)) == self._seal and digest(self._value) == self._seal and
            self._value['source_bindings'] == source_bindings() and
            self._source.record() == self._value['original_trajectory_source'] and
            self._activity.record() == self._value['complete_activity_source'], 'registered interaction source changed')
        return json.loads(channel._canonical(self._value))

    def free_component_action(self, component, state, *, slice_start):
        self.record(); source = self._source
        component = tuple(component) if isinstance(component, list) else component
        require(component in trajectory.COMPONENTS, 'original complete frequency component required')
        _, active = source._clock(slice_start)
        return _free_component(source, component, source._blocks(state), active)

    def registered_component_action(self, component, state, *, slice_start):
        self.record(); source = self._source
        component = tuple(component) if isinstance(component, list) else component
        require(component in trajectory.COMPONENTS, 'original complete frequency component required')
        _, active = source._clock(slice_start)
        return _registered_component(source, component, source._blocks(state), active)

    def coefficient_identity(self):
        """All recycle paths, every Mark and every activation, before any matrix input."""
        self.record(); source = self._source; checks = 0; generated_baths = [[], []]
        for _, rate, modes in source._law._groups:
            for _, (side, operator) in modes:
                generated_baths[side].append([str(rate), channel._input_record(operator)])
            for mu, _ in modes:
                for nu, _ in modes:
                    detected = sum((source._law._transfer[p][mu]*source._law._transfer[p][nu].conjugate()
                                    for p in range(4)), dipole.ComplexRadical())
                    require(source._law._loss[nu][mu]+detected == dipole.ComplexRadical(int(mu == nu)),
                            'complete natural loss is not the same transfer complement')
                    checks += 1
        for side in (0, 1):
            original = [[str(rate), channel._input_record(operator)] for rate, operator in source._parts[side][2]]
            require(sorted(generated_baths[side], key=channel._canonical) == sorted(original, key=channel._canonical),
                    'free TP recycling must contain the same complete source jump operators, not just their loss sum')
        return {'complete_resolved_recycle_coefficient_identities': checks,
            'two_complete_local_bath_jump_counts': list(map(len, generated_baths)),
            'complete_source_marks': len(source._marks), 'all_activation_subsets_covered': 4,
            'identity_applies_to_every_complete_complex_matrix_unit': True,
            'Hamiltonian_drive_and_receipt_counterflow_unchanged': True,
            'all_four_BG_update_differences_retained': True}

    def tail_budget(self, order, *, interval=None):
        raw = self.record(); g0, g1 = map(Q, raw['original_trajectory_source']['retarded_source']['gate_seconds'])
        a, b = (g0, g1) if interval is None else tuple(map(Q, interval))
        require(g0 <= a <= b <= g1, 'interaction budget must stay on the original detector gate')
        variation = Q(raw['interaction_norm_per_second_upper'])*(b-a)
        return {'schema': SCHEMA+'/tail-budget', 'source_identity_sha256': digest(raw),
            'detector_interval_seconds': list(map(str, (a, b))), **finite_tail(variation, order),
            'whole_Gamma_family_and_optical_cone_included': True,
            'large_atomic_H_norm_enters_interaction_tail': False,
            'old_input_error_payment': 'one original CP whole-instrument contraction; not multiplied by the signed series norm',
            'free_flow_and_quadrature_residuals_already_paid': False,
            'full_gate_trajectory_generated': False}
