"""One raw CEM programme generates its continuous detector CP family.

Raw registration types are sampled once per possible local birth; the ion
sink forbids a second local birth across all waveform phases.  Backgrounds
are independent one-time OR operations.  Coefficients below are source
probabilities, not a prior over hardware parameters.  A repeated reload
history reuses these maps at its fixed parameter and does not select one
vertex for all later births.
"""
from fractions import Fraction as Q
from itertools import product
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import fluorescence_channel as channel
import fluorescence_presence as local
import joint_fluorescence_presence as joint
import projected_window_cem as projected
import window_cem_source as window


SCHEMA = 'stage10-window-continuous-detector-CP-family/v1'
PARAMETERS = tuple(product(range(4), repeat=2))
BACKGROUND_VERTICES = tuple(product((0, 1), repeat=2))


def _copy(value):
    return json.loads(channel._canonical(value))


def _fresh(source):
    channel._require(type(source) is window.WindowCEMSource,
                     'closed original WindowCEMSource required; target effects are not input')
    return window.WindowCEMSource.from_record(source.record())


def _simplex(values):
    channel._require(type(values) in (tuple, list) and len(values) == 4, 'four raw registration probabilities required')
    values = tuple(full.nonnegative(value) for value in values)
    channel._require(sum(values, Q(0)) == 1, 'raw registration simplex required')
    return values


def _background(values):
    channel._require(type(values) in (tuple, list) and len(values) == 2, 'two raw background probabilities required')
    values = tuple(full.nonnegative(value) for value in values)
    channel._require(all(value <= 1 for value in values), 'raw background cube required')
    return values


def structural_certificate(source):
    source = _fresh(source)
    inventory, sink_checks, birth_checks = [], 0, 0
    for phase in source.phases():
        sides = []
        channel._require(type(phase).independent_atomic_action is joint.JointCounterGenerator.independent_atomic_action,
                         'original local tensor generator required')
        for side, atom in enumerate(phase.sources):
            channel._require(all((i == dipole.ION) == (j == dipole.ION)
                                 for i, j in atom.hamiltonian), 'raw Hamiltonian refills the ion sink')
            for jump in atom.jumps:
                channel._require(all((i == dipole.ION) == (j == dipole.ION) for i, j in jump.matrix),
                                 'raw natural jump refills the ion sink')
            channel._require(atom.outgoing[dipole.ION] == 0 and
                             not atom.atomic_action({(dipole.ION, dipole.ION): dipole.ComplexRadical(1)}),
                             'original ion sink must be absorbing')
            rates = phase.ion_rates[side]
            channel._require(dipole.ION not in rates, 'ion birth cannot start at the sink')
            # Every local complex matrix unit, including neutral/ION
            # coherences; the spectator remains a complete off-diagonal unit.
            for i in range(33):
                for j in range(33):
                    row, column = ((33*i+1, 33*j+2) if side == 0 else (33+i, 66+j))
                    target = ((33*dipole.ION+1, 33*dipole.ION+2) if side == 0
                              else (33+dipole.ION, 66+dipole.ION))
                    rate = rates.get(i, Q(0)) if i == j else Q(0)
                    actual = phase.ion_birth_action({(row, column): dipole.ComplexRadical(0, 1)}, side)
                    expected = {target: dipole.ComplexRadical(0, rate)} if rate else {}
                    channel._require(actual == expected, 'original full-complex tensor birth column changed')
                    birth_checks += 1
            gates = source.registrations[side].gates(phase.interval_start)
            coefficients = (0, gates[1], gates[0], int(any(gates)))
            channel._require(sum((Q(c)*p for c, p in zip(coefficients,
                                  source.registrations[side].probabilities)), Q(0)) == phase.kappas[side],
                             'raw simplex-to-kappa source mapping changed')
            for mark in window.MARKS:
                target = mark.with_click(side)
                channel._require(target.clicks[side] == 1 and target.clicks[1-side] == mark.clicks[1-side],
                                 'birth marking must retain the other side')
            sink_checks += 1
            sides.append({'side': side, 'kappa_coefficients_p00_p01_p10_p11': list(coefficients),
                          'full_local_matrix_units_checked': 33**2, 'sink_absorbing': True,
                          'natural_operator_entries_checked': sum(len(jump.matrix) for jump in atom.jumps)})
        inventory.append({'raw_phase': phase.record(), 'sides': sides})
    repeated = []
    for before in source.phases():
        for after in source.phases():
            for side in (0, 1):
                row, column = ((33*dipole.ION+1, 33*dipole.ION+2) if side == 0
                               else (33+dipole.ION, 66+dipole.ION))
                channel._require(not after.ion_birth_action({(row, column): dipole.ComplexRadical(0, 1)}, side),
                                 'a later phase permits a repeated same-side birth')
                repeated.append([before.index, after.index, side])
    return {'raw_source': source.record(), 'phase_inventory': inventory,
            'full_complex_birth_columns_checked': birth_checks, 'absorbing_local_source_checks': sink_checks,
            'cross_phase_same_side_birth_zero_inventory': repeated,
            'source_factorization': 'local GKSL tensor sum; birth is local sink jump tensor spectator identity',
            'generated_nilpotence': 'image(D_s) lies in ION_s; every phase and opposite-side operation preserves it; D_s kills it',
            'time_ordered_degree_bound': {'q_A': 1, 'q_B': 1, 'background_A': 1, 'background_B': 1},
            'latent_source_construction': 'sample each raw registration type once per local birth, keep it through all phases; sample BG once at cutoff',
            'registration_vertices': 16, 'complete_instrument_restrictions': 64,
            'initial_and_final_Empty_coherences_covered': True, 'terminal_probability_only': False,
            'flight_window_geometry_fixed': True, 'long_reload_history_degree_one_claimed': False,
            'actual_hardware_uniquely_identified': False}


def _trace(matrix):
    value = sum((entry for (i, j), entry in matrix.items() if i == j), dipole.ComplexRadical())
    channel._require(not value.imag, 'Hermitian full-state trace required')
    if set(value.real.terms) <= {1}:
        return value.real.as_rational(), Q(0)
    return full.radical_midpoint(value.real, 160)


def _select(state, clicks):
    channel._require(type(clicks) is tuple and clicks in window.REGISTRATION_ORDER and
                     all(type(bit) is int for bit in clicks), 'original accepted-bit outcome required')
    return {(i, j): value for (mark, i, j), value in state.items() if mark.clicks == clicks}


def _noise(state, backgrounds):
    result = {}
    for (mark, i, j), value in state.items():
        for noise in BACKGROUND_VERTICES:
            weight = Q(1)
            for bit, probability in zip(noise, backgrounds):
                weight *= probability if bit else 1-probability
            target = window.Mark(tuple(int(bool(a or b)) for a, b in zip(mark.clicks, noise)))
            local._add(result, (target, i, j), weight*value)
    return result


def _simplex_box(box):
    if box is None:
        return tuple(tuple(Q(int(index == column)) for column in range(4)) for index in range(4))
    channel._require(type(box) in (tuple, list) and len(box) == 4, 'four registration coordinate bounds required')
    bounds = tuple(tuple(map(full.exact, pair)) for pair in box)
    channel._require(all(len(pair) == 2 and 0 <= pair[0] <= pair[1] <= 1 for pair in bounds),
                     'legal exact simplex coordinate bounds required')
    vertices = set()
    for free in range(4):
        fixed = tuple(index for index in range(4) if index != free)
        for ends in product((0, 1), repeat=3):
            point = [Q(0)]*4
            for index, end in zip(fixed, ends):
                point[index] = bounds[index][end]
            point[free] = 1-sum(point, Q(0))
            if all(lo <= value <= hi for value, (lo, hi) in zip(point, bounds)):
                vertices.add(tuple(point))
    channel._require(vertices, 'registration box has empty simplex intersection')
    return tuple(sorted(vertices))


class WindowDetectorFamily:
    def __init__(self, source):
        self._source = _fresh(source)
        self._raw_source = _copy(self._source.record())
        self._structure = structural_certificate(self._source)
        self._record_seal = channel._canonical({'schema': SCHEMA, 'original_source': self._raw_source,
                                               'structural_certificate': self._structure})
        self._verified_snapshot = None

    def record(self):
        channel._require(not any(name in vars(self) for name in (
            'record', 'source_at', '_vertex', 'generate', '_cache_signature', 'verify', 'vertex_states', 'evaluate', 'condition', 'enclose')),
            'source family operations cannot be replaced by callbacks')
        channel._require(self._source.record() == self._raw_source, 'original detector source changed')
        record = {'schema': SCHEMA, 'original_source': self._raw_source, 'structural_certificate': self._structure}
        channel._require(channel._canonical(record) == self._record_seal, 'source-only structural certificate changed')
        return _copy(record)

    @classmethod
    def from_record(cls, record):
        channel._require(type(record) is dict and record.get('schema') == SCHEMA, 'closed detector CP-family record required')
        result = cls(window.WindowCEMSource.from_record(record['original_source']))
        channel._require(result.record() == record, 'raw detector family or source-only structural certificate changed')
        return result

    def source_at(self, q_a, q_b, backgrounds):
        self.record()
        points, backgrounds = (_simplex(q_a), _simplex(q_b)), _background(backgrounds)
        source = _fresh(self._source)
        registrations = tuple(window.FragmentRegistration(point, old.electron_flight, old.ion_flight,
                            old.electron_window, old.ion_window) for point, old in zip(points, source.registrations))
        return window.WindowCEMSource(*source.waveforms, registrations=registrations,
                    backgrounds=backgrounds, logic_deadlines=source.logic_deadlines,
                    seconds_per_unit=source.seconds_per_unit, interval_start=source.interval_start)

    def _vertex(self, a, b):
        return self.source_at(tuple(Q(int(a == i)) for i in range(4)),
                              tuple(Q(int(b == i)) for i in range(4)), (0, 0))

    def generate(self, initial_marked, *, upstream_error=0, source_recipe=None, trial_provider=None,
                 taylor_order=8, mode_bits=60, coefficient_bits=160, exponential_bits=160):
        self.record()
        indexed = window._initial_marked(initial_marked)
        initial = {(window.index_mark(c), i, j): value for (c, i, j), value in indexed.items()}
        old = full.nonnegative(upstream_error)
        recipe = {} if source_recipe is None else _copy(source_recipe)
        vertices = []
        for a, b in PARAMETERS:
            source, state, error, certificates = self._vertex(a, b), dict(initial), Q(0), []
            for phase in source.phases():
                pieces = (projected.taylor_trials(phase, state, order=taylor_order, mode_bits=mode_bits,
                               coefficient_bits=coefficient_bits) if trial_provider is None else
                          trial_provider(a, b, phase.index, dict(state)))
                certificate = window.certify_step(phase, state, pieces, upstream_error=error,
                                mode_bits=mode_bits, coefficient_bits=coefficient_bits, exponential_bits=exponential_bits)
                state, error = window.marked_poststate(certificate)
                certificates.append(certificate)
            vertices.append({'registration': [a, b], 'raw_vertex_source': source.record(),
                             'phase_certificates': certificates,
                             'pre_background_marked_poststate': window._marked_record(window._initial_marked(state)),
                             'local_trace_norm_error': str(error)})
        return _copy({'schema': SCHEMA, 'family_record': self.record(),
                      'initial_marked_state': window._marked_record(indexed),
                      'upstream_trace_norm_error': str(old), 'source_recipe': recipe,
                      'interval': [str(self._source.interval_start), str(self._source.interval_start+self._source.duration)],
                      'seconds_per_source_unit': str(self._source.seconds_per_unit),
                      'vertices': vertices, 'precision': [mode_bits, coefficient_bits, exponential_bits],
                      'background_is_analytic_single_cutoff_OR': True, 'vertex_old_error_paid_inside_certificates': False,
                      'full_Mark_quantum_poststates_retained': True, 'literal_cohort_reconstructed': False,
                      'coefficient_weights_are_parameter_prior': False, 'actual_hardware_uniquely_identified': False})

    def _cache_signature(self, report):
        methods = (window.certify_step, window.verify_step_certificate,
            window.WindowCEMPhase.action, window.WindowCEMPhase.ion_birth_action,
            window.FragmentRegistration.kappa, window.WindowCEMSource.background_action,
            window.WindowCEMPhase.__init__, window.WindowCEMPhase.from_record.__func__, window.WindowCEMPhase.record,
            window.WindowCEMSource.__init__, window.WindowCEMSource.from_record.__func__,
            window.WindowCEMSource.record, window.WindowCEMSource.phases,
            window.FragmentRegistration.__init__, window.FragmentRegistration.from_record.__func__,
            window.FragmentRegistration.record, window.FragmentRegistration.gates,
            local.CounterGenerator.__init__, local.CounterGenerator.atomic_action,
            type(self).__init__, getattr(type(self).from_record, '__func__', type(self).from_record), type(self).record,
            type(self).source_at, type(self)._vertex, type(self).generate, type(self)._cache_signature,
            type(self).verify, type(self).vertex_states, type(self).evaluate, type(self).condition, type(self).enclose,
            _fresh, _simplex, _background, _copy, structural_certificate, _select, _noise, _trace, _simplex_box)
        return (channel._canonical(report), channel._canonical(window._bindings()), tuple(id(value) for value in methods),
                PARAMETERS, BACKGROUND_VERTICES, window.REGISTRATION_ORDER)

    def verify(self, report):
        channel._require(type(report) is dict and report.get('family_record') == self.record(),
                         'same complete original detector family required')
        snapshot = self._cache_signature(report)
        if self._verified_snapshot == snapshot:
            return True
        channel._require(len(report['vertices']) == 16, 'all sixteen source registration vertices required')
        saved = {}
        for (a, b), item in zip(PARAMETERS, report['vertices']):
            source = self._vertex(a, b)
            channel._require(item['registration'] == [a, b] and item['raw_vertex_source'] == source.record(),
                             'complete source-owned vertex order required')
            channel._require(len(item['phase_certificates']) == len(source.partition), 'all original phases required')
            state, error = window._read_marked(report['initial_marked_state']), Q(0)
            for phase, certificate in zip(source.phases(), item['phase_certificates']):
                window.verify_step_certificate(certificate, phase, state, upstream_error=error)
                state, error = window.marked_poststate(certificate)
                saved[a, b, phase.index] = certificate['trial_pieces']
        expected = self.generate(window._read_marked(report['initial_marked_state']),
                    upstream_error=report['upstream_trace_norm_error'], source_recipe=report['source_recipe'],
                    trial_provider=lambda a, b, phase, state: saved[a, b, phase],
                    mode_bits=report['precision'][0], coefficient_bits=report['precision'][1],
                    exponential_bits=report['precision'][2])
        channel._require(expected == report, 'full vertex source, state, recipe, time or price changed')
        self._verified_snapshot = snapshot
        return True

    def vertex_states(self, report):
        self.record()
        self.verify(report)
        return {tuple(item['registration']): {'state': window._read_marked(item['pre_background_marked_poststate']),
                 'local_error': Q(item['local_trace_norm_error'])} for item in report['vertices']}

    def evaluate(self, report, q_a, q_b, backgrounds):
        vertices = self.vertex_states(report)
        q_a, q_b, backgrounds = _simplex(q_a), _simplex(q_b), _background(backgrounds)
        state, local_error, coefficients = {}, Q(0), []
        for a, b in PARAMETERS:
            weight = q_a[a]*q_b[b]
            item = vertices[a, b]
            local_error += weight*item['local_error']
            for key, value in item['state'].items():
                local._add(state, key, weight*value)
            for noise in BACKGROUND_VERTICES:
                full_weight = weight
                for bit, probability in zip(noise, backgrounds):
                    full_weight *= probability if bit else 1-probability
                coefficients.append({'registration': [a, b], 'background_OR': list(noise), 'weight': str(full_weight)})
        state = _noise(state, backgrounds)
        error = Q(report['upstream_trace_norm_error'])+local_error
        metadata = {'theta_source': self.source_at(q_a, q_b, backgrounds).record(),
                    'family_source': self.record(), 'initial_marked_state': report['initial_marked_state'],
                    'source_recipe': report['source_recipe'], 'interval': report['interval'],
                    'seconds_per_source_unit': report['seconds_per_source_unit'],
                    'source_coefficients': coefficients,
                    'marked_poststate_center': window._marked_record(window._initial_marked(state)),
                    'upstream_trace_norm_error': report['upstream_trace_norm_error'],
                    'weighted_vertex_local_error': str(local_error), 'trace_norm_error': str(error),
                    'whole_old_error_paid_once': True, 'normalized_vertex_average_used': False,
                    'input_positivity_certified_here': False,
                    'source_recipe_is_provenance_certificate': False,
                    'physical_source_membership_certified': False}
        return {'state': state, 'trace_norm_error': error, 'record': _copy(metadata)}

    def condition(self, report, q_a, q_b, backgrounds, *, clicks):
        self.record()
        result = self.evaluate(report, q_a, q_b, backgrounds)
        matrix = _select(result['state'], clicks)
        mass, rounding = _trace(matrix)
        error = result['trace_norm_error']+rounding
        lower = mass-error
        channel._require(lower > 0, 'theta-indexed whole event normalizer is unresolved')
        norm = projected.bsm._entry_norm(matrix)
        price = error/lower+norm*error/(lower*mass)
        normalized = {key: value*(1/mass) for key, value in matrix.items()}
        return {'state': matrix, 'mass': mass, 'mass_interval': (lower, mass+error),
                'unnormalized_trace_norm_error': error, 'normalized_poststate': normalized,
                'trace_norm_error': price, 'positive_input_required_for_physical_posterior': True,
                'record': _copy({'evaluation': result['record'], 'clicks': list(clicks),
                    'complete_selected_matrix': channel._input_record(matrix), 'event_mass': str(mass),
                    'event_mass_bounds': list(map(str, (lower, mass+error))),
                    'normalized_complete_matrix': channel._input_record(normalized), 'trace_norm_error': str(price),
                    'whole_event_normalizer_used': True, 'normalized_vertex_average_used': False,
                    'positive_input_required_for_physical_posterior': True,
                    'input_positivity_certified_here': False,
                    'source_recipe_is_provenance_certificate': False})}

    def enclose(self, report, *, q_a_box=None, q_b_box=None, background_box=None):
        self.verify(report)
        a_vertices, b_vertices = _simplex_box(q_a_box), _simplex_box(q_b_box)
        bounds = ((Q(0), Q(1)),)*2 if background_box is None else tuple(tuple(map(full.exact, pair)) for pair in background_box)
        channel._require(len(bounds) == 2 and all(len(pair) == 2 and 0 <= pair[0] <= pair[1] <= 1 for pair in bounds),
                         'exact background coordinate box required')
        endpoints = tuple(sorted(set(product(*bounds))))
        outcomes = {clicks: [] for clicks in window.REGISTRATION_ORDER}
        maximum_error = Q(0)
        for q_a, q_b, backgrounds in product(a_vertices, b_vertices, endpoints):
            evaluated = self.evaluate(report, q_a, q_b, backgrounds)
            error = evaluated['trace_norm_error']
            maximum_error = max(maximum_error, error)
            for clicks in window.REGISTRATION_ORDER:
                mass, rounding = _trace(_select(evaluated['state'], clicks))
                outcomes[clicks].append((mass-error-rounding, mass+error+rounding))
        initial = window.forget_marks(window._read_marked(report['initial_marked_state']))
        total, rounding = _trace(initial)
        old = Q(report['upstream_trace_norm_error'])
        lower, upper = total-old-rounding, total+old+rounding
        rows = []
        for clicks in window.REGISTRATION_ORDER:
            lo = min(pair[0] for pair in outcomes[clicks])
            hi = max(pair[1] for pair in outcomes[clicks])
            probability = [str(max(Q(0), lo/upper)), str(min(Q(1), hi/lower))] if lower > 0 else None
            rows.append({'clicks': list(clicks), 'unnormalized_mass_bounds': list(map(str, (lo, hi))),
                         'probability_bounds_for_positive_input': probability})
        return _copy({'family_record': self.record(), 'source_recipe': report['source_recipe'],
                'q_A_simplex_box_vertices': [list(map(str, point)) for point in a_vertices],
                'q_B_simplex_box_vertices': [list(map(str, point)) for point in b_vertices],
                'background_box_endpoints': [list(map(str, point)) for point in endpoints],
                'parameter_corner_count': len(a_vertices)*len(b_vertices)*len(endpoints),
                'outcomes': rows, 'whole_trace_norm_error_upper': str(maximum_error),
                'input_trace_bounds': list(map(str, (lower, upper))),
                'generated_extrema': 'multi-affine scalar mass and weighted error on exact simplex-product polytope',
                'positive_input_required_for_probability': True, 'input_positivity_certified_here': False,
                'source_recipe_is_provenance_certificate': False, 'normalized_vertex_average_used': False,
                'normalized_full_state_box_claimed': False, 'long_history_degree_one_claimed': False})
