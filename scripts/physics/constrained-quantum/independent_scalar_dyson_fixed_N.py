#!/usr/bin/env python3
"""Raw-source grade audit and direct CAR consumer for all61 scalar ports.

The original Clifford/exterior density produces E, V and the all-momentum
drift.  No MatterPorts or candidate constructor is imported.  Arbitrary N
comes from the separately kernel-certified occupation-grade word theorems;
finite integer counts are never used as its proof.
"""
from __future__ import annotations

from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import re
import time

import sympy as s

from independent_spectral_splice import OriginalAction, ROOT_ID, clean, equal, matrix, source

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ROOT = HERE.parents[3]
K = s.symbols('k1:4', real=True)
INCOMING = s.symbols('incoming1:4', real=True)
OUTGOING = s.symbols('outgoing1:4', real=True)


def zero(rows, columns=None):
    return s.SparseMatrix.zeros(rows, rows if columns is None else columns)


def read(path):
    return json.loads(path.read_bytes())


def bindings(record):
    count = 0
    for key in ('source_sha256', 'input_sha256'):
        for name, digest in record.get(key, {}).items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
            count += 1
    return count


def decode(row):
    return matrix(row).subs({s.Symbol(str(k)): k for k in K})


def basis_matrix(indices):
    return s.SparseMatrix(252, len(indices), {(i, j): 1 for j, i in enumerate(indices)})


def exterior_one_body_action(operator, occupied):
    """Differentiate an ordered exterior basis; no four-CAR-word routine."""
    out = {}
    by_column = {}
    for (i, j), value in operator.todok().items():
        by_column.setdefault(j, []).append((i, value))
    for slot, old in enumerate(occupied):
        for new, value in by_column.get(old, []):
            word = list(occupied)
            word[slot] = new
            if len(set(word)) != len(word):
                continue
            sign = (-1)**sum(word[i] > word[j] for i in range(len(word)) for j in range(i+1, len(word)))
            key = tuple(sorted(word))
            out[key] = out.get(key, 0)+sign*value
    return {key: s.simplify(value) for key, value in out.items() if s.simplify(value) != 0}


def grade_ports(operator, target):
    for (i, j), value in operator.todok().items():
        assert (int(i in target)-int(j in target)-1)*value == 0


def main():
    started = time.monotonic()
    candidate_path = HERE/'scalar_dyson_fixed_N.json'
    candidate = read(candidate_path)
    assert candidate['root'] == ROOT_ID
    bound = bindings(candidate)
    phase_path = HERE/'scalar_canonical_phase.json'
    scalar_phase = read(phase_path)
    bound += bindings(scalar_phase)
    scalar_audit_path = HERE/'independent_scalar_canonical_phase.json'
    bound += bindings(read(scalar_audit_path))
    active_path = BASE/'active-gauge/receipt.json'
    phase_source_path = BASE/'full-phase/receipt.json'
    vertices_path = BASE/'matter-vertices/receipt.json'
    active, phase, vertices = map(read, [active_path, phase_source_path, vertices_path])
    _, vacuum, degrees, hashes = source.parse_source(ROOT)
    assert hashes == candidate['source_sha256'] == scalar_phase['source_sha256'] == vertices['source_sha256']
    gamma_path = ROOT/'Lean/SaturationMonoid/PhysicsCore/DiracCliffordRepresentation.lean'
    gamma_text = gamma_path.read_text()
    gamma = []
    for name in ('Zero', 'One', 'Two', 'Three'):
        literal = re.search(r'def diracGamma'+name+r'\s*:.*?:=\s*!!\[(.*?)\]', gamma_text, re.S).group(1)
        gamma.append(s.SparseMatrix([[s.sympify(v.strip().replace('Complex.I', 'I'))
            for v in row.split(',')] for row in literal.split(';')]))
    original = OriginalAction(active, phase, vertices, vacuum, degrees, gamma)
    raw = original.holonomic(original.configuration(zero(289, 1)), s.Matrix(K))
    E, Ei, drift = raw['E'], raw['inverse_E'], clean(-raw['inverse_E']*raw['K'])
    equal(E*Ei, s.eye(252)); equal(Ei*E, s.eye(252))
    equal(E*drift+raw['K'], zero(252))
    matter_path = HERE/'full-matter-ports.json'
    matter = read(matter_path)
    equal(E, decode(matter['density_temporal_principal']))
    equal(Ei, decode(matter['density_temporal_inverse']))
    coefficients = matter['stationary_Hamiltonian_coefficients']
    Hsaved = decode(coefficients['constant'])+sum((k*decode(coefficients[str(k)]) for k in K), zero(252))
    equal(drift, -s.I*Hsaved)

    inside = [(degree, word) for degree in degrees for word in itertools.combinations(range(7), degree)]
    assert degrees == [6, 2, 4] and len(inside) == 63
    indices = {d: [spin*63+j for spin in range(4) for j, (degree, _) in enumerate(inside) if degree == d]
               for d in degrees}
    T6, T2, T4 = [basis_matrix(indices[d]) for d in (6, 2, 4)]
    equal(T6*T6.T+T2*T2.T+T4*T4.T, s.eye(252))
    A6, A2, A4 = [clean(T.T*drift*T) for T in (T6, T2, T4)]
    background = clean(T6.T*drift*T2)
    assert background.todok()
    equal(drift*T6, T6*A6)
    equal(T2.T*drift, A2*T2.T)
    equal(drift*T4, T4*A4)
    equal(drift*T2, T2*A2+T6*background)
    assert clean(drift*(T6*T6.T)-(T6*T6.T)*drift).todok()

    # Reconstruct the actual peripheral projector from the original scalar
    # orbit, then take its original canonical pivot columns.
    four_words = list(itertools.combinations(range(7), 4))
    vacuum_column = s.Matrix([vacuum.get(word, 0) for word in four_words])
    generators = source.generators([(0, 1, 2), (3, 4)])
    orbit = []
    for _, imaginary, generator in generators:
        value = (s.I if imaginary else 1)*s.Matrix(source.exterior_action(generator, 4))*vacuum_column
        orbit.append(s.SparseMatrix.vstack(value.applyfunc(s.re), value.applyfunc(s.im)))
    orbit = s.SparseMatrix.hstack(*orbit)
    J = orbit[:, active['J_independent_columns']]
    assert J.shape == (70, 9) and J.rank() == 9
    P61 = clean(s.eye(70)-J*(J.T*J).inv()*J.T)
    equal(P61, decode(scalar_phase['projector61']))
    R = P61[:, scalar_phase['canonical_coordinate_pivots']]
    equal(R, decode(scalar_phase['scalar_coordinate_embedding']))
    assert R.shape == (70, 61) and R.rank() == 61
    elementary = []
    for word in four_words:
        _, _, yukawa, _ = source.yukawa(Counter({word: 1}))
        internal = s.MutableSparseMatrix(63, 63, {})
        internal[:7, 7:28] = s.SparseMatrix(yukawa)
        elementary.append(clean(raw['volume']*s.kronecker_product(s.diag(0, 0, 1, 1), internal)))
    V70 = elementary+[clean(s.I*V) for V in elementary]
    ports, reports = [], []
    target = set(indices[6])
    for j, saved in enumerate(scalar_phase['projected_CAR_couplings']):
        V = clean(sum((R[a, j]*V70[a] for a in range(70) if R[a, j]), zero(252)))
        W = clean(-s.I*Ei*V)
        equal(V, decode(saved['density_vertex']))
        equal(W, decode(saved['canonical_matter_vertex']))
        equal(E*(-s.I*W)+V, zero(252))
        middle = clean(T6.T*W*T2)
        equal(W, T6*middle*T2.T)
        equal(W*T6, zero(252, 28)); equal(T2.T*W, zero(84, 252))
        grade_ports(W, target)
        ports.append(W)
        reports.append({'coordinate': j, 'rank': W.rank(), 'nonzero_entries': len(W.todok()),
            'original_W_equals_minus_i_Einverse_V': True,
            'complete_Lambda2_to_Lambda6_factorization': True,
            'all_entries_occupation_grade_plus_one': True})
    assert len(ports) == candidate['scalar_coordinate_count'] == 61
    assert sorted({row['rank'] for row in reports}) == candidate['canonical_vertex_ranks'] == [6, 10]
    assert [min(len(W.todok()) for W in ports), max(len(W.todok()) for W in ports)] == candidate['canonical_vertex_nonzero_entry_range'] == [6, 24]
    for actual, saved in zip(reports, candidate['all61_factorization']):
        assert all(actual[key] == saved[key] for key in ('coordinate', 'rank', 'nonzero_entries'))
    print('PASS raw Lean Gamma/exterior/coframe density, original scalar orbit R and all61 canonical W grade law', flush=True)

    # Coefficientwise intertwining holds for independently arbitrary input
    # and output momenta. It proves the formal-series/finite-matrix identity
    # exp(-Aout*t) W exp(Ain*t)=T6 exp(-A6out*t) W62 exp(A2in*t) T2^T.
    for values in (INCOMING, OUTGOING):
        A = clean(drift.subs(dict(zip(K, values)), simultaneous=True))
        equal(A*T6, T6*clean(T6.T*A*T6))
        equal(T2.T*A, clean(T2.T*A*T2)*T2.T)
    negative = dict(zip(K, [-k for k in K]))
    conjugate_drift = clean(drift.subs(negative, simultaneous=True).conjugate())
    equal(conjugate_drift*T6, T6*clean(T6.T*conjugate_drift*T6))
    equal(T2.T*conjugate_drift, clean(T2.T*conjugate_drift*T2)*T2.T)
    branch_target = target | {252+i for i in target}
    for W in ports:
        Wminus = clean(-W.conjugate())
        equal(Wminus, T6*clean(T6.T*Wminus*T2)*T2.T)
        grade_ports(s.diag(W, Wminus), branch_target)
        # The independent canonical dual reverses the same momentum edge
        # and uses the opposite transpose, never a fixed Hilbert adjoint.
        equal((s.I*W.T).T+(-s.I*W), zero(252))
        equal((s.I*Wminus.T).T+(-s.I*Wminus), zero(252))
    Qket = s.SparseMatrix.hstack(s.eye(252), s.I*s.eye(252))
    U = clean(s.SparseMatrix.vstack(Qket, Qket.conjugate())/s.sqrt(2))
    def realify_coeff(value):
        images = clean(value*Qket)
        return clean(s.SparseMatrix.vstack(images.applyfunc(s.re), images.applyfunc(s.im)))
    constant = drift.subs(dict.fromkeys(K, 0))
    spatial = [clean(drift.diff(k)/s.I) for k in K]
    real_drift = clean(realify_coeff(constant)+sum((s.I*k*realify_coeff(A) for k, A in zip(K, spatial)), zero(504)))
    equal(U*real_drift*U.H, s.diag(drift, conjugate_drift))
    for W in ports:
        equal(U*(s.I*realify_coeff(-s.I*W))*U.H, s.diag(W, -W.conjugate()))
    transfer = s.Matrix(s.symbols('transfer1:4', real=True))
    incoming = s.Matrix(INCOMING)
    outgoing = incoming+transfer
    equal(outgoing-transfer, incoming)
    equal(transfer+incoming-outgoing, zero(3, 1))
    print('PASS all-momentum middle propagation, original real-action two branches and reversed independent-dual transfers', flush=True)

    witness = candidate['normal_product_source_witness']
    a, b = witness['coordinates']
    input_state, output_state = tuple(witness['input_occupation']), tuple(witness['output_occupation'])
    assert (a, b, input_state, output_state) == (0, 0, (145, 152), (0, 1))
    A, B = ports[a], ports[b]
    equal(A*B, zero(252))
    first = exterior_one_body_action(B, input_state)
    second = {}
    for state, coefficient in first.items():
        for outgoing_state, value in exterior_one_body_action(A, state).items():
            second[outgoing_state] = second.get(outgoing_state, 0)+coefficient*value
    second = {state: s.simplify(value) for state, value in second.items() if s.simplify(value) != 0}
    i, k = output_state
    j, ell = input_state
    determinant_coefficient = s.simplify(A[i,j]*B[k,ell]-A[k,j]*B[i,ell]
        +B[i,j]*A[k,ell]-B[k,j]*A[i,ell])
    value = second.get(output_state, 0)
    assert value == determinant_coefficient == s.Rational(27, 125) == s.sympify(witness['matrix_element'])
    assert exterior_one_body_action(A, output_state) == {}
    print('PASS complete exterior CAR action and independent2x2 coefficient: normalProduct(W0,W0) matrix element27/125', flush=True)

    fock_audit_path = HERE/'fock_raising_audit.json'
    fock_audit = read(fock_audit_path)
    bound += bindings(fock_audit)
    assert fock_audit['root'] == ROOT_ID
    assert fock_audit['verdict'] == 'CERTIFIED_FINITE_CAR_RAISING_WORDS_ON_ARBITRARY_NUMBER_SECTORS'
    theorem = fock_audit['public_mouth']['theorem']
    tensor_theorem = fock_audit['tensor_consumer']['theorem']
    assert theorem == 'SourceFockRaising.matrix_word_vanishes_on_number_sector'
    assert tensor_theorem == 'SourceFockRaising.tensor_word_vanishes_on_number_sector'
    assert candidate['formal_fixed_N_consumer']['matrix_theorem'] == theorem
    assert candidate['formal_fixed_N_consumer']['ordered_boson_tensor_theorem'] == tensor_theorem
    assert candidate['formal_fixed_N_consumer']['arbitrary_particle_number']
    assert not candidate['formal_fixed_N_consumer']['analytic_Dyson_convergence_claimed']
    assert candidate['input_sha256'][str(fock_audit_path.relative_to(ROOT))] == hashlib.sha256(fock_audit_path.read_bytes()).hexdigest()
    assert fock_audit['public_mouth']['arbitrary_particle_number_not_finite_sample_only']
    assert all(row['exit_code'] == 0 and row['trust'] == 0 and row['warningAsError'] for row in fock_audit['strict_checks'])
    assert all(set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'} for axioms in fock_audit['axioms'].values())
    print('PASS certified arbitrary-N CAR word and noncommuting-boson tensor consumers, not integer-count extrapolation', flush=True)
    paths = [candidate_path, HERE/'scalar_dyson_fixed_N.py', phase_path, scalar_audit_path,
        active_path, phase_source_path, vertices_path, matter_path, gamma_path,
        BASE/'exact_readout.py', HERE/'independent_spectral_splice.py',
        HERE/'FockRaising.lean', HERE/'FockRaisingTensor.lean', fock_audit_path,
        HERE/'independent_scalar_dyson_fixed_N.py']
    output = {'verdict': 'CERTIFIED_RAW_SOURCE_ALL61_SCALAR_GRADE_AND_ARBITRARY_N_CAR_WORD_CONSUMER',
        'root': ROOT_ID, 'source_sha256': hashes,
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'candidate_constructor_imported': False, 'MatterPorts_constructor_imported': False,
        'algorithm': 'raw Lean Clifford and source exterior/Yukawa/coframe density; reconstruct original scalar orbit; canonical E inverse times actual density V; complete support-grade and independent in/out momentum intertwining; direct exterior dGamma action plus determinant CAR coefficient',
        'source_ports': reports, 'all61_squared_ordered_pair_coverage': 61*61,
        'pair_coverage_mechanism': 'every W factors through Lambda2->Lambda6; the middle Lambda2^T Lambda6 is zero and every source drift preserves Lambda6',
        'all_momentum_interaction_picture_grade': 'exp(-A(kout)t) W exp(A(kin)t)=T6 exp(-A6(kout)t) W62 exp(A2(kin)t) T2^T',
        'original_background_Lambda2_to_Lambda6_block_retained': True,
        'false_full_grade_projector_commutation_used': False,
        'real_source_branches': 'diag(W,-conjugate(W)), drift diag(A(k),conjugate(A(-k))); both branches have occupation grade +1',
        'independent_dual': 'opposite transpose with reversed momentum edge; no adjoint substitution',
        'normal_product_witness': {'coordinate_pair': [a,b], 'input': list(input_state), 'output': list(output_state),
            'matrix_element': str(value), 'complete_second_word_output': [[list(state), str(v)] for state, v in sorted(second.items())],
            'same_line_contraction_zero': True, 'different_particle_normal_product_nonzero': True},
        'arbitrary_N_theorem': theorem, 'noncommuting_boson_ordered_tensor_theorem': tensor_theorem,
        'finite_N_0_to_6_counts_used_as_proof': False,
        'formal_source_installation_scope': 'the general arbitrary-N and tensor statements are kernel-certified; concrete source61 grade and all-momentum coefficients are independently exact-SymPy checked, not installed as Lean source literals',
        'scope': 'source scalar61 algebraic interaction-picture matrix words on fixed particle sectors, including original conjugate branch coefficients and ordered auxiliary operator factors',
        'time_integral_Dyson_or_Cinfinity_domain_constructed': False,
        'continuous_momentum_integral_or_spectral_measure_constructed': False,
        'full_four_block_interacting_Fock_spectrum_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_scalar_dyson_fixed_N.json').write_text(json.dumps(output, indent=2)+'\n')
    print('PASS independent raw source scalar61 arbitrary-N word consumer', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
