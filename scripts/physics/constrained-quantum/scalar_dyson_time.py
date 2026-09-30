#!/usr/bin/env python3
"""Actual all61 scalar interaction-picture time primitives on the CAR domain.

Each source coefficient is integrated by a finite, explicitly constructed
augmented matrix exponential.  Its generator is a Kronecker sum of the
original scalar phase and the original incoming/outgoing matter generators.
No inverse at a resonance, finite momentum lattice, or boson vacuum is used.
The scalar free evolution is the linear CCR automorphism, not an assumed
polynomial-domain exponential of its quadratic state Hamiltonian.
"""
from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import itertools
import json
from pathlib import Path
import time

import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from full_matter_ports import clean, equal, encode

KIN = s.symbols('kin1:4', real=True)
KOUT = s.symbols('kout1:4', real=True)
KAPPA = s.symbols('kap1:4', real=True)


def components(indices, entries):
    graph = {i: set() for i in indices}
    for i, j in entries:
        if i in graph and j in graph:
            graph[i].add(j)
            graph[j].add(i)
    seen, answer = set(), []
    for i in indices:
        if i in seen:
            continue
        todo, part = [i], []
        seen.add(i)
        while todo:
            j = todo.pop()
            part.append(j)
            for k in graph[j] - seen:
                seen.add(k)
                todo.append(k)
        answer.append(sorted(part))
    return answer


def vectorize(matrix):
    return s.SparseMatrix(matrix.rows * matrix.cols, 1,
        {(j * matrix.rows + i, 0): value for (i, j), value in matrix.todok().items()})


def unvectorize(vector, rows, cols):
    assert vector.shape == (rows * cols, 1)
    return s.SparseMatrix(rows, cols,
        {(i % rows, i // rows): value for (i, _), value in vector.todok().items()})


def augmented_primitive(L, initial):
    """O exp(t G) v is the entire primitive of exp(t L) initial."""
    n = L.rows
    assert L.shape == (n, n) and initial.shape == (n, 1)
    G = s.SparseMatrix.vstack(s.SparseMatrix.hstack(L, initial), s.zeros(1, n + 1))
    v = s.SparseMatrix(n + 1, 1, {(n, 0): 1})
    O = s.SparseMatrix.hstack(s.eye(n), s.zeros(n, 1))
    last = s.SparseMatrix(1, n + 1, {(0, n): 1})
    equal(O * v, s.zeros(n, 1))
    equal(last * v, s.ones(1, 1))
    equal(last * G, s.zeros(1, n + 1))
    equal(O * G, L * O + initial * last)
    equal(G * v, s.SparseMatrix.vstack(initial, s.zeros(1, 1)))
    # y(0)=0, y'=L y+initial, and y'=exp(t L) initial.  These
    # identities integrate the source signal even if L has zero eigenvalues.
    return {'G': G, 'initial': v, 'output': O}


def ordered_integral_step(signal_L, signal_initial, previous):
    """Realize integral_0^t signal(s) tensor previous_integral(s) ds.

    The first tensor factor is the later-time left operator.  Its order is
    retained; callers must not permute boson factors when assembling CAR words.
    """
    m, d, r = signal_L.rows, previous['G'].rows, previous['output'].rows
    driver = clean(s.kronecker_product(signal_L, s.eye(d)) +
                   s.kronecker_product(s.eye(m), previous['G']))
    initial_driver = s.kronecker_product(signal_initial, previous['initial'])
    product_output = s.kronecker_product(s.eye(m), previous['output'])
    n = m * r
    G = s.SparseMatrix.vstack(
        s.SparseMatrix.hstack(s.zeros(n), product_output),
        s.SparseMatrix.hstack(s.zeros(m * d, n), driver))
    initial = s.SparseMatrix.vstack(s.zeros(n, 1), initial_driver)
    output = s.SparseMatrix.hstack(s.eye(n), s.zeros(n, m * d))
    read_driver = s.SparseMatrix.hstack(s.zeros(m * d, n), s.eye(m * d))
    equal(output * initial, s.zeros(n, 1))
    equal(output * G, product_output * read_driver)
    equal(read_driver * G, driver * read_driver)
    equal(read_driver * initial, initial_driver)
    return {'G': G, 'initial': initial, 'output': output}


class ScalarDysonTime:
    def __init__(self):
        self.phase = json.loads((HERE / 'scalar_joint_hamiltonian.json').read_text())
        self.source = json.loads((HERE / 'scalar_canonical_phase.json').read_text())
        self.matter = json.loads((HERE / 'full-matter-ports.json').read_text())
        self.grade = json.loads((HERE / 'scalar_dyson_fixed_N.json').read_text())
        self.grade_audit = json.loads((HERE / 'independent_scalar_dyson_fixed_N.json').read_text())
        for record in [self.phase, self.source, self.matter, self.grade, self.grade_audit]:
            assert record['root'] == ROOT_ID
            for key in ('source_sha256', 'input_sha256'):
                for path, digest in record.get(key, {}).items():
                    assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, path
        assert self.phase['source_sha256'] == self.source['source_sha256'] == self.matter['source_sha256']
        self.H = {name: decode(value) for name, value in self.matter['stationary_Hamiltonian_coefficients'].items()}
        self.A = {name: clean(-s.I * value) for name, value in self.H.items()}
        self.W = [decode(row['canonical_matter_vertex']) for row in self.source['projected_CAR_couplings']]
        self.E = decode(self.matter['density_temporal_principal'])
        self.Ei = decode(self.matter['density_temporal_inverse'])
        equal(self.E * self.Ei, s.eye(252))
        for row, W in zip(self.source['projected_CAR_couplings'], self.W):
            equal(W, -s.I * self.Ei * decode(row['density_vertex']))
        old_k = {symbol for symbol in decode(self.phase['real_phase_generator']).free_symbols}
        substitution = {symbol: KAPPA[int(str(symbol)[1:]) - 1] for symbol in old_k}
        self.scalar_A = clean(decode(self.phase['real_phase_generator']).subs(substitution))
        self.scalar_zero_A = decode(self.phase['zero_mode']['generator'])
        inside = [degree for degree in (6, 2, 4) for _ in itertools.combinations(range(7), degree)]
        self.grades = {degree: [spin * 63 + i for spin in range(4) for i, value in enumerate(inside) if value == degree]
                       for degree in (6, 2, 4)}
        self.target = set(self.grades[6])
        self.incoming = set(self.grades[2])
        edges = set().union(*(set(A.todok()) for A in self.A.values()))
        self.target_blocks = components(self.grades[6], edges)
        self.input_blocks = components(self.grades[2], edges)
        self.phase_blocks = components(list(range(244)), self.scalar_A.todok())
        self.zero_blocks = components(list(range(122)), self.scalar_zero_A.todok())
        self.target_map = {i: j for j, block in enumerate(self.target_blocks) for i in block}
        self.input_map = {i: j for j, block in enumerate(self.input_blocks) for i in block}
        for A in self.A.values():
            assert all(i in self.target for (i, j) in A.todok() if j in self.target)
            assert all(j in self.incoming for (i, j) in A.todok() if i in self.incoming)
        for W in self.W:
            assert all(i in self.target and j in self.incoming for i, j in W.todok())
        self._generator_cache = {}

    def actual_A(self, momentum, branch):
        assert branch in (1, -1)
        if branch == 1:
            return clean(self.A['constant'] + sum(
                (momentum[j] * self.A[f'k{j+1}'] for j in range(3)), s.zeros(252)))
        # H_minus(k)=-conjugate(H_plus(-k)); hence A_minus(k)=conjugate(A_plus(-k)).
        return clean(self.actual_A([-k for k in momentum], 1).conjugate())

    def catalogue(self, *, zero=False):
        blocks = self.zero_blocks if zero else self.phase_blocks
        positions = 61 if zero else 122
        mapping = {i: j for j, block in enumerate(blocks) for i in block}
        triples = defaultdict(dict)
        for a, W in enumerate(self.W):
            labels = (a,) if zero else (a, a + 61)
            for (i, j), value in W.todok().items():
                for phase_index in labels:
                    assert phase_index < positions
                    key = (mapping[phase_index], self.target_map[i], self.input_map[j])
                    triples[key][(phase_index, i, j)] = value
        return sorted(triples.items())

    def state(self, key, entries, sign, branch, *, zero=False):
        assert sign in (1, -1) and branch in (1, -1)
        phase_blocks = self.zero_blocks if zero else self.phase_blocks
        scalar_A = self.scalar_zero_A if zero else self.scalar_A
        scalar_ids = phase_blocks[key[0]]
        out_ids, in_ids = self.target_blocks[key[1]], self.input_blocks[key[2]]
        r, d, f = len(scalar_ids), len(out_ids), len(in_ids)
        scalar_part = scalar_A.extract(scalar_ids, scalar_ids)
        Aout = self.actual_A(KOUT, branch).extract(out_ids, out_ids)
        Ain = self.actual_A(KIN, branch).extract(in_ids, in_ids)
        cache_key = (zero, key, branch)
        if cache_key not in self._generator_cache:
            matrix_drift = s.kronecker_product(s.eye(f), -Aout) + s.kronecker_product(Ain.T, s.eye(d))
            self._generator_cache[cache_key] = clean(
                s.kronecker_product(scalar_part.T, s.eye(d * f)) +
                s.kronecker_product(s.eye(r), matrix_drift))
        L = self._generator_cache[cache_key]
        local_phase = {i: j for j, i in enumerate(scalar_ids)}
        local_out = {i: j for j, i in enumerate(out_ids)}
        local_in = {i: j for j, i in enumerate(in_ids)}
        v = s.SparseMatrix.zeros(r * d * f, 1)
        for (phase_index, i, j), value in entries.items():
            # Exact source Fourier pair: cosine 1/sqrt2, sine +/- i/sqrt2.
            weight = s.Integer(1) if zero else (1 if phase_index < 61 else sign * s.I) / s.sqrt(2)
            vertex = value if branch == 1 else -s.conjugate(value)
            pos = local_phase[phase_index] * d * f + local_in[j] * d + local_out[i]
            v[pos, 0] = s.expand(-s.I * weight * vertex)
        assert v.todok()
        primitive = augmented_primitive(L, v)
        # Independent coefficient differentiation of the same source signal:
        # X_b'=sum_c As[c,b] X_c - Aout X_b + X_b Ain.
        matrices = [unvectorize(v[a*d*f:(a+1)*d*f, :], d, f) for a in range(r)]
        direct = []
        for b in range(r):
            next_value = sum((scalar_part[c, b] * matrices[c] for c in range(r)), s.zeros(d, f))
            direct.append(vectorize(clean(next_value - Aout * matrices[b] + matrices[b] * Ain)))
        equal(L * v, s.SparseMatrix.vstack(*direct))
        # Original temporal equations use E(-i W)+V=0, while this -iW is
        # the actual interaction-picture generator, not the density vertex V.
        equal(primitive['output'] * primitive['G'] * primitive['initial'], v)
        equal(primitive['output'] * primitive['G']**2 * primitive['initial'], L * v)
        return {'key': list(key), 'sign': sign, 'branch': branch, 'zero_mode': zero,
            'phase_indices': scalar_ids, 'target_indices': out_ids, 'input_indices': in_ids,
            'signal_L': L, 'signal_initial': v, 'scalar_part': scalar_part,
            'incoming_A2': Ain, 'outgoing_A6': Aout, 'primitive': primitive}


def main():
    started = time.monotonic()
    native = ScalarDysonTime()
    output_states = []
    pair_states = []
    covered = set()
    for zero in (False, True):
        catalogue = native.catalogue(zero=zero)
        for branch in (1, -1):
            for sign in ((1,) if zero else (1, -1)):
                for key, entries in catalogue:
                    state = native.state(key, entries, sign, branch, zero=zero)
                    for phase_index, _, _ in entries:
                        covered.add(phase_index % 61)
                    if not zero and branch == 1 and sign == 1:
                        pair_states.append(state)
                    output_states.append({
                        'key': state['key'], 'sign': sign, 'branch': branch, 'zero_mode': zero,
                        'phase_indices': state['phase_indices'], 'target_indices': state['target_indices'],
                        'input_indices': state['input_indices'],
                        'signal_state_dimension': state['signal_L'].rows,
                        'primitive_state_dimension': state['primitive']['G'].rows,
                        'signal_initial': encode(state['signal_initial']),
                        'initial_zero_and_derivative_original_signal': True,
                        'generator_coefficient_identity': True})
                print('PASS actual time primitives', 'zero' if zero else 'pair', branch, sign,
                      len(catalogue), 'source blocks', flush=True)
    assert covered == set(range(61))
    # Actual two-insertion ordered primitive. The source input has two
    # distinct particles and the source normal-product coefficient is 27/125;
    # the complete N1 catalogue above remains the authoritative coefficient
    # inventory. This is a consumer of its first two different target blocks.
    first = next(state for state in pair_states if 0 in state['target_indices'] and 145 in state['input_indices'])
    second = next(state for state in pair_states if 1 in state['target_indices'] and 152 in state['input_indices'])
    ordered = ordered_integral_step(second['signal_L'], second['signal_initial'], first['primitive'])
    equal(ordered['output'] * ordered['initial'], s.zeros(ordered['output'].rows, 1))
    equal(ordered['output'] * ordered['G'] * ordered['initial'], s.zeros(ordered['output'].rows, 1))
    second_jet = clean(ordered['output'] * ordered['G']**2 * ordered['initial'])
    equal(second_jet, s.kronecker_product(second['signal_initial'], first['signal_initial']))
    assert second_jet.todok()
    print('PASS actual ordered N2 time primitive', ordered['G'].rows,
          'states, nonzero source second derivative', flush=True)

    paths = [HERE / name for name in [
        'scalar_joint_hamiltonian.json', 'independent_scalar_joint_hamiltonian.json',
        'scalar_canonical_phase.json', 'full-matter-ports.json',
        'scalar_dyson_fixed_N.json', 'independent_scalar_dyson_fixed_N.json',
        'FockRaising.lean', 'FockRaisingTensor.lean', 'fock_raising_audit.json', 'scalar_dyson_time.py']]
    result = {'root': ROOT_ID, 'source_sha256': native.phase['source_sha256'],
        'scope': 'ALL61_SOURCE_CCR_CAR_INTERACTION_PICTURE_FINITE_MATRIX_EXPONENTIAL_TIME_PRIMITIVES',
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'incoming_momentum': list(map(str, KIN)), 'outgoing_momentum': list(map(str, KOUT)),
        'scalar_pair_momentum': list(map(str, KAPPA)),
        'momentum_consumer': 'substitute kout=kin+sign*kappa; no discretization, periodization or aliasing',
        'matter_generator': 'A_plus(k)=-i H_stationary(k)=-E^-1 K_density(k); A_minus(k)=conjugate(A_plus(-k))',
        'real_action_branches': 'W_plus=W; W_minus=-conjugate(W); exact source 1/sqrt2 Fourier-pair coefficients retained; no added physical mode inventory',
        'scalar_pair_phase_dimension': 244, 'scalar_zero_phase_dimension': 122,
        'scalar_pair_components': dict(Counter(map(len, native.phase_blocks))),
        'scalar_zero_components': dict(Counter(map(len, native.zero_blocks))),
        'matter_target_blocks': native.target_blocks, 'matter_input_blocks': native.input_blocks,
        'pair_component_catalogue_count': len(native.catalogue()),
        'zero_component_catalogue_count': len(native.catalogue(zero=True)),
        'all61_canonical_vertices_covered': sorted(covered),
        'primitive_states': output_states,
        'largest_primitive_state_dimension': max(row['primitive_state_dimension'] for row in output_states),
        'signal_generator_formula': 'L=As^T tensor I_(d*f)+I_r tensor (I_f tensor (-A6out)+A2in^T tensor I_d)',
        'primitive_generator_formula': 'G=[[L,v],[0,0]], initial=e_last, output=[I,0]; Y(t)=output exp(tG) initial',
        'primitive_equations': 'Y(0)=0; Yprime=L Y+v=exp(tL)v, including zero eigenvalues and resonances',
        'coefficient_interpretation': 'Y_b(t)=integral_0^t sum_a exp(As*s)[a,b] exp(-Aout*s)(-i FourierWeight_a W_a)exp(Ain*s) ds, generated by the displayed finite exponential',
        'N1_actual_interaction_picture_solution': 'U_I(t)=I+sum_blocks,b phase_initial[b] tensor embedded_Y_b(t) shift(sign*kappa); U_I(0)=I; U_Iprime=B_I U_I with B_I=-i V_I because every product of two matter insertions is zero',
        'independent_dual': 'same CAR creator column equation has reversed shift and opposite transpose; the source-conjugate real branch is distinct from this independent momentum',
        'N1_derivative_residual_mechanism': 'B_I(t)Y(s)=0 from all61 Lambda6 image/annihilator plus incoming/outgoing free intertwining; no boson factors reordered',
        'ordered_N2_consumer': {'left_source_key': second['key'], 'right_source_key': first['key'],
            'state_dimension': ordered['G'].rows, 'output_dimension': ordered['output'].rows,
            'initial_zero': True, 'first_derivative_zero': True,
            'second_derivative': encode(second_jet), 'left_boson_factor_stays_left': True},
        'general_ordered_integral_API': 'ordered_integral_step(L_signal,v_signal,previous): finite Kronecker driver and integrator, actual initial/derivative identities',
        'fixed_N_use': 'ordered_integral_step generates finite chronological coefficient primitives; FockRaisingTensor supplies the strict arbitrary-N word bound on its stated finite CAR number sectors; installation on the continuous antisymmetric N-body domain remains a separate consumer',
        'continuum_domain': 'N1: original finite scalar Fourier-pair Weyl automorphism with arbitrary continuous incoming matter momentum; the generated primitive acts on smooth compactly supported full252 branch wavefunctions by the displayed exact momentum shifts',
        'continuous_N_body_carrier': 'antisymmetric f(p1,...,pN;i1,...,iN), with particle-line sums and shifts; finite Fock(Fin504) tensor momentum functions is not substituted for this carrier',
        'N2_scope': 'one actual ordered double-integral coefficient realization, not the assembled complete continuous two-particle evolution; its scalar factors keep their original order',
        'physical_Hilbert_completion_or_free_boson_state_exp_assumed': False,
        'full_four_block_interacting_spectrum_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE / 'scalar_dyson_time.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS all61 actual scalar Dyson time primitives', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
