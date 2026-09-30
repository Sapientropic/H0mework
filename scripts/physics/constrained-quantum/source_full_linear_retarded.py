#!/usr/bin/env python3
"""Complete source tail retarded propagator, in the actual dual/scalar/primal order.

All spatial Fourier coefficients are the original realified coefficients.
The240-complex matter inverses use source2/4-dimensional blocks and their
single Yukawa feed, while the122-scalar inverse consumes the original70-field
Green numerator. No1082-dimensional inverse or spectral measure is supplied
as input.
"""
from __future__ import annotations

from functools import cached_property
import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID
from source_full_linear_split import SourceFullLinearSplit, K, realify
from source_lorentz_contact import clean, equal, encode

Z = s.Symbol('retarded_laplace')


def decode(record):
    local = {str(k): k for k in K}
    local.update({'lambda': Z, 'source_laplace': Z, str(Z): Z})
    return s.SparseMatrix(*record['shape'], {(int(i), int(j)): s.sympify(value.replace('lambda', str(Z)), locals=local)
                                            for i, j, value in record['entries']})


def rational(A):
    return s.SparseMatrix(A).applyfunc(lambda value: s.cancel(s.together(value), extension=True))


def equal_rational(A, B):
    residual = rational(A-B)
    assert not residual.todok(), list(residual.todok().items())[:2]


def norm_bound(A):
    A = s.SparseMatrix(A)
    rows = [sum(abs(v) for (i, _), v in A.todok().items() if i == r) for r in range(A.rows)]
    cols = [sum(abs(v) for (_, j), v in A.todok().items() if j == c) for c in range(A.cols)]
    return s.simplify(s.sqrt(max(rows, default=0)*max(cols, default=0)))


def coefficient_conjugate(A):
    """Conjugate only polynomial coefficients, leaving Laplace z unchanged."""
    return s.SparseMatrix(A).applyfunc(lambda value: s.conjugate(value).xreplace({s.conjugate(Z): Z}))


class SourceMatterResolvent:
    def __init__(self, coefficients):
        self.coefficients = coefficients
        self.A = clean(coefficients[0]+sum((s.I*k*matrix for k, matrix in zip(K, coefficients[1:])),
                                          s.zeros(coefficients[0].rows)))
        self.groups = sorted([sorted(group) for group in self.A.strongly_connected_components()], key=min)
        self.owner = {index: number for number, group in enumerate(self.groups) for index in group}
        diagonal, off = {}, {}
        for (i, j), value in self.A.todok().items():
            (diagonal if self.owner[i] == self.owner[j] else off)[i, j] = value
        self.diagonal = s.SparseMatrix(self.A.rows, self.A.cols, diagonal)
        self.off = s.SparseMatrix(self.A.rows, self.A.cols, off)
        targets = {self.owner[i] for i, _ in off}
        sources = {self.owner[j] for _, j in off}
        assert not (targets & sources)
        assert not self.off.free_symbols
        self.leaves, self.leaf_of_group = [], []
        cache = {}
        for indices in self.groups:
            A = self.A.extract(indices, indices)
            key = tuple(A)
            if key not in cache:
                M = Z*s.eye(A.rows)-A
                numerator = clean(M.adjugate(method="berkowitz"))
                denominator = s.expand(M.det(method='berkowitz'))
                equal(M*numerator, denominator*s.eye(A.rows))
                equal(numerator*M, denominator*s.eye(A.rows))
                cache[key] = len(self.leaves)
                self.leaves.append({'A': A, 'numerator': numerator, 'denominator': denominator})
            self.leaf_of_group.append(cache[key])
        assert max(map(len, self.groups)) <= 4
        self.off_blocks = []
        for left, right in sorted({(self.owner[i], self.owner[j]) for i, j in off}):
            a, b = self.leaves[self.leaf_of_group[left]], self.leaves[self.leaf_of_group[right]]
            feed = self.off.extract(self.groups[left], self.groups[right])
            numerator = clean(a['numerator']*feed*b['numerator'])
            equal((Z*s.eye(a['A'].rows)-a['A'])*numerator,
                  a['denominator']*feed*b['numerator'])
            equal(numerator*(Z*s.eye(b['A'].rows)-b['A']),
                  b['denominator']*a['numerator']*feed)
            self.off_blocks.append({'left': left, 'right': right, 'feed': feed,
                                    'numerator': numerator,
                                    'denominator': a['denominator']*b['denominator']})

    def _diagonal_apply(self, forcing, laplace, momentum, conjugate_branch=False):
        output = s.MutableSparseMatrix.zeros(forcing.rows, forcing.cols)
        replace = {Z: laplace, **dict(zip(K, momentum))}
        evaluated = {}
        for indices, leaf_index in zip(self.groups, self.leaf_of_group):
            right = s.SparseMatrix(forcing.extract(indices, range(forcing.cols)))
            if not right.todok():
                continue
            if leaf_index in evaluated:
                block = evaluated[leaf_index]*right
                for local, global_index in enumerate(indices):
                    output[global_index, :] = block[local, :]
                continue
            leaf = self.leaves[leaf_index]
            num, den = leaf['numerator'], leaf['denominator']
            if conjugate_branch:
                num = coefficient_conjugate(num).subs(dict(zip(K, [-k for k in K])), simultaneous=True)
                den = s.conjugate(den).xreplace({s.conjugate(Z): Z}).subs(dict(zip(K, [-k for k in K])), simultaneous=True)
            evaluated[leaf_index] = num.subs(replace)/den.subs(replace)
            block = evaluated[leaf_index]*right
            for local, global_index in enumerate(indices):
                output[global_index, :] = block[local, :]
        return s.SparseMatrix(output)

    def apply(self, forcing, laplace=Z, momentum=K, conjugate_branch=False):
        first = self._diagonal_apply(forcing, laplace, momentum, conjugate_branch)
        off = self.off.conjugate() if conjugate_branch else self.off
        return first+self._diagonal_apply(off*first, laplace, momentum, conjugate_branch)

    def real_apply(self, forcing, laplace=Z, momentum=K):
        n = self.A.rows
        assert forcing.rows == 2*n
        # U uses the same normalized complex branches as the original real
        # action. The inverse U restores real/imaginary field coordinates.
        plus = self.apply(forcing[:n, :]+s.I*forcing[n:, :], laplace, momentum)
        minus = self.apply(forcing[:n, :]-s.I*forcing[n:, :], laplace, momentum, True)
        return s.SparseMatrix.vstack((plus+minus)/2, (plus-minus)/(2*s.I))

    def receipt(self):
        return {'complex_dimension': self.A.rows,
                'source_components': [{'indices': indices, 'inverse_leaf': leaf} for indices, leaf in zip(self.groups, self.leaf_of_group)],
                'exact_inverse_leaves': [{'generator': encode(row['A']), 'numerator': encode(row['numerator']),
                                          'denominator': str(row['denominator'])} for row in self.leaves],
                'original_between_block_Yukawa': encode(self.off),
                'between_block_feed_count': len(self.off_blocks),
                'source_and_target_block_sets_disjoint': True,
                'inverse': 'R=R0+R0*N*R0; N*R0*N=0 by the actual disjoint source/target blocks',
                'both_sides_checked': 'Every diagonal leaf and every actual off-block polynomial numerator has both source identities; no path with two off-block feeds exists.'}


class SourceFullLinearRetarded:
    def __init__(self):
        self.source = SourceFullLinearSplit()
        self.blocks = self.source.tail_blocks()
        self.dimensions = (480, 122, 480)
        self.B, self.C = self.blocks['dual_to_scalar'], self.blocks['scalar_to_primal']
        self.dual = SourceMatterResolvent(self.blocks['complex_dual_coefficients'])
        self.primal = SourceMatterResolvent(self.blocks['complex_primal_coefficients'])
        self._scalar_inverse()

    def _scalar_inverse(self):
        record = self.source.scalar_record
        numerator = decode(record['original_Green_numerator'])
        denominator = s.sympify(record['original_Green_denominator'].replace('lambda', str(Z)), locals={str(Z): Z, **dict(zip(map(str, K), K))})
        R, N = self.source.R, self.source.N
        gram = clean(R.T*R); inverse = clean(gram.inv())
        q_numerator = clean(inverse*R.T*numerator*R/N)
        L = clean(self.blocks['scalar'][61:, :61]/N)
        whole = clean(s.Matrix.vstack(
            (Z*q_numerator).row_join(-N*q_numerator*inverse),
            (N*L*q_numerator).row_join(Z*gram*q_numerator*inverse)))
        M = Z*s.eye(122)-self.blocks['scalar']
        equal(M*whole, denominator*s.eye(122))
        equal(whole*M, denominator*s.eye(122))
        self.scalar_numerator, self.scalar_denominator = whole, denominator

    def scalar_apply(self, forcing, laplace=Z, momentum=K):
        replace = {Z: laplace, **dict(zip(K, momentum))}
        return self.scalar_numerator.subs(replace)*forcing/self.scalar_denominator.subs(replace)

    def resolvent_action(self, forcing, laplace=Z, momentum=K):
        """Actual complete source inverse, in (dual,scalar,primal) order."""
        dual = self.dual.real_apply(forcing[0], laplace, momentum)
        scalar = self.scalar_apply(forcing[1]+self.B*dual, laplace, momentum)
        primal = self.primal.real_apply(forcing[2]+self.C*scalar, laplace, momentum)
        return dual, scalar, primal

    def tail_matrix(self, momentum=K):
        replace = dict(zip(K, momentum)); values = {}
        for row, col, matrix in [(0, 0, self.blocks['dual']), (480, 480, self.blocks['scalar']),
                                  (602, 602, self.blocks['primal']), (480, 0, self.B), (602, 480, self.C)]:
            for (i, j), value in matrix.todok().items():
                values[row+i, col+j] = value.subs(replace)
        return s.SparseMatrix(1082, 1082, values)

    def time_jet(self, order, initial, momentum=K):
        assert isinstance(order, int) and order >= 0
        A = self.tail_matrix(momentum)
        value = initial
        for _ in range(order):
            value = clean(A*value)
        return value

    def invariant_time_state(self, initial_indices, momentum=K):
        """Exact reachable source state, without a momentum or spectral truncation."""
        A = self.tail_matrix(momentum)
        reached = set(initial_indices)
        while True:
            grown = reached | {i for i, j in A.todok() if j in reached}
            if grown == reached:
                break
            reached = grown
        indices = sorted(reached)
        injection = s.SparseMatrix(1082, len(indices), {(value, i): 1 for i, value in enumerate(indices)})
        generator = A.extract(indices, indices)
        equal(A*injection, injection*generator)
        return injection, generator

    def retarded_time_expression(self, time, initial, momentum=K):
        """Actual finite-state matrix-exponential expression for any source data."""
        injection, generator = self.invariant_time_state(
            sorted({i for i, _ in s.SparseMatrix(initial).todok()}), momentum)
        state = injection.T*initial
        # Unevaluated MatrixExpr exp is the exact convergent matrix exponential,
        # not an uncomputed integral or a finite time-series approximation.
        return {'injection': injection, 'generator': generator, 'initial': state,
                'matrix_exponential': s.exp(time*s.ImmutableMatrix(generator), evaluate=False)}

    def global_bounds(self):
        energy = json.loads((HERE/'scalar_momentum_energy.json').read_bytes())
        assert energy['root'] == ROOT_ID
        equal(self.blocks['scalar'], decode(self.source.scalar_record['canonical_generator']))
        alpha = 2*self.source.N
        matter = {}
        for name in ('dual', 'primal'):
            A = self.blocks[name]
            A0 = clean(A.subs(dict.fromkeys(K, 0)))
            spatial = [clean(A.diff(k)) for k in K]
            for coefficient in spatial:
                equal(coefficient+coefficient.H, s.zeros(480))
            H = clean((A0+A0.H)/2)
            row_sums = [s.simplify(sum(abs(H[i, j]) for j in range(480))) for i in range(480)]
            bound = max(row_sums)
            assert s.simplify(bound-alpha) == 0
            matter[name] = {'all_three_Fourier_principals_skew_Hermitian': True,
                            'Hermitian_constant_max_absolute_row_sum': str(bound),
                            'uniform_all_real_momentum_flow_bound': 'exp(alpha*abs(t))'}
        beta = s.sympify(energy['coordinate_time_growth_beta'])
        cs = s.sympify(energy['canonical_flow_constant_C'])
        assert s.simplify(beta-alpha) > 0
        b, c = norm_bound(self.B), norm_bound(self.C)
        return {'matter': matter, 'alpha': str(alpha), 'beta': str(beta),
                'scalar_C': str(cs), 'B_norm_bound': str(b), 'C_norm_bound': str(c),
                'beta_minus_alpha': str(s.simplify(beta-alpha)),
                'scalar_bound_m': 'm(k)=scalar_C*sqrt(1+|k|^2)',
                'time_bound': '||E(t,k)|| <= exp(beta*abs(t))*(2+m+m*(b+c)*abs(t)+m*b*c*t^2/2)',
                'proof': 'Hermitian-part differential inequality gives the two matter bounds. The same source scalar122 uses its certified comparison energy. One and two ordered Duhamel integrations give |t| and |t|^2/2, respectively.',
                'safe_half_plane': 'Re(z)>beta for the complete1082 tail, every real k, without a momentum cutoff',
                'active289_or_active126_uniform_beta_claimed': False,
                'resolvent_bound': 'dD=1/(Re(z)-alpha); dS=m/(Re(z)-beta); ||R|| <= 2*dD+dS+dS*b*dD+dD*c*dS+dD*c*dS*b*dD',
                'Laplace_identity': 'Absolute convergence and integration by parts give integral_0^infty exp(-z*t) E(t,k) dt=(zI-A(k))^-1.',
                'proper_clock_beta': str(s.simplify(beta/self.source.N)),
                'comparison_norm_is_physical_Hilbert_normalization': False}

    def physical_phase(self):
        record, C = self.source.phase, self.source.C
        frequency = s.sympify(record['source_frequency'])
        primal = s.diag(*map(s.sympify, record['primal_rates_in_units_frequency']))
        dual = s.diag(*map(s.sympify, record['dual_rates_in_units_frequency']))
        Dp, Dd = clean(C.H*primal*C), clean(C.H*dual*C)
        E, K0 = clean(C.H*self.source.E*C), clean(C.H*self.source.K0*C)
        original = clean(self.source.N*C.H*(decode(record['original_constant_B'])+decode(record['original_Y']))*C)
        equal(Dd*E+E*Dp, s.zeros(240))
        equal(K0, original+s.I*frequency*E*Dp)
        assert Dd != -Dp
        time = s.Symbol('phase_time', real=True)
        for rate in set(Dp.diagonal()) | set(Dd.diagonal()):
            a = frequency*rate
            rotation = s.Matrix([[s.cos(a*time), -s.sin(a*time)], [s.sin(a*time), s.cos(a*time)]])
            equal((rotation.T*rotation-s.eye(2)).applyfunc(s.trigsimp), s.zeros(2))
            equal(rotation.diff(time), s.Matrix([[0, -a], [a, 0]])*rotation)
            equal(rotation.subs(time, 0), s.eye(2))
        self.phase_rates = {'primal': Dp, 'dual': Dd}
        return {'frequency': str(frequency), 'primal_complement_rates': [str(Dp[i, i]) for i in range(240)],
                'dual_complement_rates': [str(Dd[i, i]) for i in range(240)],
                'dual_kinetic_pairing_identity': 'Dd*E+E*Dp=0',
                'stationary_density_identity': 'Kstat=Koriginal+i*frequency*E*Dp',
                'same_index_dual_equals_minus_primal_negative_control': True,
                'rotation': 'R_r(t)=[[cos(frequency*r*t),-sin(frequency*r*t)],[sin(frequency*r*t),cos(frequency*r*t)]], coordinatewise',
                'original_retarded': 'R(t)*Theta(t-s)*exp((t-s)Astat(k))*R(s)^-1; R=diag(R_dual,I122,R_primal)',
                'original_generator': 'Rprime*R^-1+R*Astat*R^-1',
                'original_time_delta_initial_value': 'R(s)*I1082*R(s)^-1=I1082',
                'orthogonal_endpoint_rotations_preserve_bounds': True,
                'time_reparametrized': False,
                'proper_clock': 'tau=N*t; no independently chosen clock or leg normalization',
                'stationary_Laplace_poles_identified_with_composite_measure': False}

    def phase_matrix(self, time):
        if not hasattr(self, 'phase_rates'):
            self.physical_phase()
        frequency = s.sympify(self.source.phase['source_frequency'])
        entries = {(480+i, 480+i): s.Integer(1) for i in range(122)}
        for name, offset in [('dual', 0), ('primal', 602)]:
            rates = self.phase_rates[name]
            for i in range(240):
                angle = frequency*rates[i, i]*time
                entries[offset+i, offset+i] = s.cos(angle)
                entries[offset+i, offset+240+i] = -s.sin(angle)
                entries[offset+240+i, offset+i] = s.sin(angle)
                entries[offset+240+i, offset+240+i] = s.cos(angle)
        return s.SparseMatrix(1082, 1082, entries)

    def original_time_state(self, time, initial_time, initial, momentum=K):
        """Exact factored original-phase solution, with the actual two endpoints."""
        stationary_initial = self.phase_matrix(-initial_time)*initial
        state = self.retarded_time_expression(time-initial_time, stationary_initial, momentum)
        state['injection'] = self.phase_matrix(time)*state['injection']
        return state

    def source_time_consumer(self):
        cascade = clean(self.C*self.blocks['scalar']*self.B)
        equal(self.C*self.B, s.zeros(480))
        assert len(cascade.todok()) == 24 and not cascade.free_symbols
        row, column = sorted(cascade.todok())[0]
        momenta = json.loads((HERE/'retained_hamiltonian_reduction.json').read_bytes())['source_momenta']
        momentum = tuple(map(s.sympify, momenta[-1]['momentum']))
        initial = s.SparseMatrix(1082, 1, {(column, 0): 1})
        state = self.retarded_time_expression(s.Symbol('source_time', real=True), initial, momentum)
        injection, generator = state['injection'], state['generator']
        equal(injection*(injection.T*initial), initial)
        jet2, jet3 = self.time_jet(2, initial, momentum), self.time_jet(3, initial, momentum)
        equal(jet2[602:, :], s.zeros(480, 1))
        equal(jet3[602:, :], cascade[:, column])
        assert jet3[602+row, 0] != 0
        # Consume the public full inverse on this original dual forcing. Its
        # scalar and primal responses are both retained, and backwritten.
        laplace = s.Integer(2)
        response = tuple(rational(x) for x in self.resolvent_action(
            (initial[:480, :], s.zeros(122, 1), s.zeros(480, 1)), laplace, momentum))
        whole = s.SparseMatrix.vstack(*response)
        equal_rational((laplace*s.eye(1082)-self.tail_matrix(momentum))*whole, initial)
        assert response[1].todok() and response[2].todok()
        # The converse orientation is evaluated on nonzero data in all three
        # blocks, in addition to every source leaf's polynomial two-sided proof.
        trial = clean(initial+s.SparseMatrix(1082, 1, {(480, 0): 1, (602+row, 0): 1}))
        forcing = clean((laplace*s.eye(1082)-self.tail_matrix(momentum))*trial)
        recovered = s.SparseMatrix.vstack(*self.resolvent_action(
            (forcing[:480, :], forcing[480:602, :], forcing[602:, :]), laplace, momentum))
        equal_rational(recovered, trial)
        return {'momentum': list(map(str, momentum)), 'dual_initial_coordinate': column,
                'primal_reader_coordinate': row, 'exact_invariant_time_state_dimension': generator.rows,
                'state_embedding_source_indices': [i for i in range(1082) if any(injection[i, j] for j in range(injection.cols))],
                'state_generator': encode(generator), 'state_initial': encode(injection.T*initial),
                'all_time_source_solution': 'u(t)=injection*exp(t*state_generator)*state_initial',
                'all_time_identity_checked': 'A*injection=injection*state_generator; injection*state_initial=original dual coordinate',
                'two_hop_second_time_derivative_zero': True,
                'two_hop_third_time_derivative': str(jet3[602+row, 0]),
                'whole_two_hop_third_derivative': encode(cascade),
                'actual_safe_laplace': str(laplace),
                'whole1082_response': encode(whole), 'original_full_equation_backwrite': True,
                'opposite_inverse_orientation_actual_all_three_block_data': True,
                'small_state_is_exact_source_invariant_restriction_not_Galerkin': True}


def bindings(paths):
    output = {}
    for path in paths:
        output[str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return output


def main():
    started = time.monotonic()
    model = SourceFullLinearRetarded()
    print('PASS actual matter source2/4 blocks and scalar122: all polynomial left/right inverse identities', flush=True)
    bounds = model.global_bounds()
    print('PASS all real momentum source half-plane and full triangular time bounds', flush=True)
    phase = model.physical_phase()
    print('PASS original distinct primal/dual phases, density and kinetic pairing', flush=True)
    consumer = model.source_time_consumer()
    print('PASS actual nonzero dual->scalar->primal source time state and full1082 inverse backwrite', flush=True)
    split = json.loads((HERE/'source_full_linear_split.json').read_bytes())
    assert split['root'] == ROOT_ID
    cauchy = json.loads((HERE/'source_first_order_cauchy.json').read_bytes())
    witness = cauchy['analytic_Cauchy_source_construction']['nonempty_source_witness']
    assert witness['original_bosonic_source_rate_zero']
    assert witness['full252_primal_rate_equals_unshifted_original_H']
    orbit = json.loads((HERE/'source_stationary_cauchy_orbit.json').read_bytes())
    assert orbit['root'] == ROOT_ID
    assert orbit['all_original_density_coefficients_including_temporal_phase_jets_checked']
    assert orbit['stationary_full252_primal_and_dual_constant_exact']
    assert list(map(s.sympify, orbit['primal_integer_rates'])) == list(map(s.sympify, model.source.phase['primal_rates_in_units_frequency']))
    assert list(map(s.sympify, orbit['independent_dual_integer_rates'])) == list(map(s.sympify, model.source.phase['dual_rates_in_units_frequency']))
    omega = s.sympify(orbit['source_frequency'])
    original_rates = orbit['actual_original_source_rates']
    for name in ['e', 'Omega', 'A', 'F', 'phi', 'U']:
        assert not decode(original_rates[name]).todok()
    equal(decode(original_rates['psi']), s.I*omega*s.diag(*orbit['primal_integer_rates'])*model.source.psi0)
    equal(decode(original_rates['chi']), s.I*omega*model.source.chi0*s.diag(*orbit['independent_dual_integer_rates']))
    assert decode(original_rates['psi']).todok() and decode(original_rates['chi']).todok()
    print('PASS same actual source Cauchy orbit and distinct full252 original matter rates', flush=True)
    source_hashes = split['source_sha256']
    for path, digest in source_hashes.items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
    paths = [HERE/name for name in ['source_full_linear_retarded.py', 'source_full_linear_split.py', 'source_full_linear_split.json', 'independent_source_full_linear_split.json',
        'scalar_canonical_phase.py', 'scalar_canonical_phase.json', 'independent_scalar_canonical_phase.json',
        'scalar_momentum_energy.py', 'scalar_momentum_energy.json', 'independent_scalar_momentum_energy.json',
        'retained_hamiltonian_reduction.json', 'source_first_order_cauchy.json', 'independent_source_first_order_cauchy.json',
        'source_stationary_cauchy_orbit.py', 'source_stationary_cauchy_orbit.json']]
    paths += [BASE/'full-phase/receipt.json']
    inputs = bindings(paths)
    for record in (split, orbit):
        for key in ('source_sha256', 'input_sha256'):
            for path, digest in record[key].items():
                assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
                inputs[path] = digest
    output = {'root': ROOT_ID, 'source_sha256': source_hashes, 'input_sha256': inputs,
              'verdict': 'SOURCE_COMPLETE_1082_TAIL_RETARDED_INVERSE_AND_TIME_PROPAGATOR_GENERATED',
              'scope': 'Complete1082 retarded tail along the actual original source Cauchy phase orbit, represented by its exact stationary source Jacobi coefficients.',
              'dimensions': {'dual': 480, 'scalar': 122, 'primal': 480, 'total': 1082},
              'dual_inverse': model.dual.receipt(), 'primal_inverse': model.primal.receipt(),
              'scalar_inverse': {'denominator': str(model.scalar_denominator),
                  'exact_numerator_recipe': {'Q': 'Gram^-1*R.T*original_Green_numerator70*R/N', 'Gram': 'R.T*R',
                    'L': 'As[61:,:61]/N', 'blocks': [['z*Q', '-N*Q*Gram^-1'], ['N*L*Q', 'z*Gram*Q*Gram^-1']],
                    'original_Green_and_R_source': 'scalar_canonical_phase.json',
                    'computed_matrix_API': 'SourceFullLinearRetarded.scalar_numerator'},
                  'original70_Green_to_canonical122_both_sides_zero': True},
              'actual_source_maps': {'dual_to_scalar': encode(model.B), 'scalar_to_primal': encode(model.C)},
              'whole_inverse': [['Rd', '0', '0'], ['Rs*B*Rd', 'Rs', '0'], ['Rp*C*Rs*B*Rd', 'Rp*C*Rs', 'Rp']],
              'whole_two_sided_identity': 'Source diagonal polynomial identities and the two actual lower off-blocks give (zI-A)R=R(zI-A)=I1082; every path of three off-block edges is absent.',
              'retarded_time': {'initial': 'E(0)=I1082', 'equation': '(partial_t-A(k))*Theta(t)*E(t,k)=delta(t)*I1082',
                  'construction': 'E=exp(t*A), with actual finite source coefficients; equivalently diagonal flows plus one and two ordered Duhamel integrals.',
                  'full_forcing_consumer': 'u(t)=E(t)u0+integral_0^t E(t-s)f(s)ds; public resolvent_action handles arbitrary full1082 forcing',
                  'convergence': 'Finite matrix exponential is entire. The source comparison bounds pay the retarded Laplace transform on Re(z)>beta.'},
              'global_bounds': bounds, 'physical_phase_restoration': phase,
              'actual_two_stage_time_consumer': consumer,
              'literal_source_Cauchy_readback': {'bosonic_rates_zero': True, 'primal_rate_is_original_H': True,
                  'all1500_rates_assumed_zero': False, 'actual_full_orbit_variation_identification_consumed': True,
                  'source_orbit_original_Euler_argument': orbit['original_Euler_all_time_argument'],
                  'complete_stationary_Jacobi_bridge': orbit['Jacobi_consumer']},
              'active289_canonical79_dual24_preserved': True,
              'active126_phase_only_at_already_generated_momenta': split['actual_phase_inventory_at_source_momenta'],
              'interacting_composite_spectral_measure_generated': False,
              'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_full_linear_retarded.json').write_text(json.dumps(output, indent=2, ensure_ascii=False)+'\n')
    print('PASS full source retarded receipt', output['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
