#!/usr/bin/env python3
"""Independent original-action consistency and Ward Hamiltonian quotient audit.

The consistent subspace is recomputed by projecting the full relation kernel
of [Omega C, -Energy C], not by importing the candidate's cokernel algorithm.
All time equations are matrix polynomial identities, not frequency samples.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ROOT = HERE.parents[3]
ROOT_ID = ('positiveSmoothUnifiedSource; repaired Dirac-dual; SpinPair.actual; '
           'visit10/tick16/materialEntry -> tick17 unchanged')
P = s.symbols('p0:4')
K = s.symbols('k1:4', real=True)
LAM = s.Symbol('audit_lambda')
DOMAIN = s.QQ.algebraic_field(s.sqrt(30), s.sqrt(2), s.I)


def parse(value):
    value = re.sub(r'\b(?:lambda|source_laplace)\b', str(LAM), value)
    return s.sympify(value, locals={str(v): v for v in (*P, *K, LAM)})


def decode(record):
    return s.SparseMatrix(*record['shape'], {(i, j): parse(v) for i, j, v in record['entries']})


def exact(value):
    return DM.from_Matrix(value).convert_to(DOMAIN).to_sparse()


def eye(size):
    return DM.eye((size, size), DOMAIN).to_sparse()


def zero(value):
    assert value.is_zero_matrix


def rank(value):
    return len(value.rref()[1])


def kernel(value):
    return value.nullspace(divide_last=True).transpose()


def dagger(value):
    return exact(value.to_Matrix().conjugate().T)


def encode(value):
    if isinstance(value, DM):
        value = value.to_Matrix()
    return {'shape': list(value.shape), 'entries': [[i, j, str(s.expand(v))]
            for (i, j), v in sorted(s.SparseMatrix(value).todok().items())]}


def check_bindings(record):
    count = 0
    for key in ('source_sha256', 'input_sha256'):
        for name, digest in record.get(key, {}).items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
            count += 1
    return count


def polynomial(entries, size):
    result = s.MutableSparseMatrix(size, size, {})
    for i, j, powers, value in entries:
        result[i, j] += parse(value)*s.prod(p**n for p, n in zip(P, powers))
    return s.SparseMatrix(result).applyfunc(s.expand)


def relation_chain(omega, energy):
    """Maximal consistent initial states via admissible (derivative,state) pairs."""
    C = eye(omega.shape[0])
    steps = []
    while True:
        width = C.shape[1]
        relation = DM.hstack(omega*C, -(energy*C))
        pairs = kernel(relation)
        positions = pairs.extract(range(width, 2*width), range(pairs.shape[1]))
        pivots = positions.rref()[1]
        next_width = len(pivots)
        steps.append({'carrier_dimension': width, 'new_constraints': width-next_width})
        if next_width == width:
            return C, steps
        assert next_width < width
        C = C*positions.extract(range(width), pivots)


def audit_momentum(row, source_operator, original_gauge, phase_record):
    momentum = tuple(parse(v) for v in row['momentum'])
    assert len(momentum) == 3 and all(v.is_real and not v.free_symbols for v in momentum)
    substitution = dict(zip(P, [LAM, *[s.I*v for v in momentum]]))
    symbol = source_operator.subs(substitution).applyfunc(s.expand)
    K0, K1, K2 = [exact(symbol.applyfunc(lambda v: v.coeff(LAM, n))) for n in range(3)]
    assert symbol == (K0.to_Matrix()+LAM*K1.to_Matrix()+LAM**2*K2.to_Matrix())
    O242 = exact(s.BlockMatrix([[K1.to_Matrix(), K2.to_Matrix()],
                               [-K2.to_Matrix(), s.zeros(121)]]).as_explicit())
    E242 = exact(s.diag(-K0.to_Matrix(), -K2.to_Matrix()))
    phase_substitution = dict(zip(K, momentum))
    zero(O242-exact(decode(phase_record['presymplectic_form']).subs(phase_substitution)))
    zero(E242-exact(decode(phase_record['Legendre_energy_hessian']).subs(phase_substitution)))
    zero(dagger(O242)+O242); zero(dagger(E242)-E242)
    assert rank(K2) == 51
    section = exact(decode(row['velocity_quotient_section']))
    retract = exact(decode(row['velocity_quotient_retraction']))
    assert section.shape == (242, 172) and retract.shape == (172, 242)
    zero(retract*section-eye(172))
    removed = eye(242)-section*retract
    zero(O242*removed); zero(E242*removed)
    # The removed70 coordinates are exactly the velocity kernel, not fields.
    assert rank(removed) == 70
    zero(removed.extract(range(121), range(242)))
    velocity_kernel = kernel(K2)
    pure_kernel = exact(s.SparseMatrix.vstack(s.zeros(121, 70), velocity_kernel.to_Matrix()))
    zero(retract*pure_kernel)
    assert rank(DM.hstack(removed, pure_kernel)) == 70
    O, E = dagger(section)*O242*section, dagger(section)*E242*section
    zero(dagger(O)+O); zero(dagger(E)-E)

    independent_C, chain = relation_chain(O, E)
    assert chain == row['consistent_initial_data_chain']
    C = exact(decode(row['consistent_initial_data_embedding']))
    assert rank(C) == C.shape[1] == independent_C.shape[1]
    assert rank(DM.hstack(C, independent_C)) == C.shape[1]
    A = exact(decode(row['consistent_generator']))
    zero(O*C*A-E*C)
    free = exact(decode(row['free_derivative_directions']))
    zero(O*C*free)
    assert rank(free) == free.shape[1] == C.shape[1]-rank(O*C)
    omega, energy = dagger(C)*O*C, dagger(C)*E*C
    zero(dagger(omega)+omega); zero(dagger(energy)-energy)
    zero(omega*A-energy); zero(dagger(A)*omega+omega*A)
    radical = kernel(omega)
    zero(energy*radical)
    assert radical.shape[1] == row['original_Ward_radical_dimension'] == 12
    # Differentiate y(t)=Y exp(t A) directly in the original121 Euler symbol.
    Y = (section*C).extract(range(121), range(C.shape[1]))
    zero(K0*Y+K1*Y*A+K2*Y*A*A)
    print('PASS original121 polynomial-time Euler, exact velocity kernel and independently projected consistency chain', momentum, chain, flush=True)

    G = original_gauge.subs(substitution).applyfunc(s.expand)
    assert not (symbol*G).applyfunc(s.expand).todok()
    jet = s.SparseMatrix.vstack(G, LAM*G)
    degree = max(s.degree(v, LAM) for v in jet.todok().values())
    saved_coordinates = row['original_Ward_jet_coordinates']
    assert len(saved_coordinates) == degree+1
    previous = DM.zeros((172, 9), DOMAIN)
    coordinates = []
    for n, saved in enumerate(saved_coordinates):
        raw = exact(jet.applyfunc(lambda v: s.expand(v).coeff(LAM, n)))
        coefficient = retract*raw
        z = exact(decode(saved))
        zero(C*z-coefficient)
        zero(O*previous-E*coefficient)
        zero(omega*z)
        coordinates.append(z)
        previous = coefficient
    zero(O*previous)
    ward_span = DM.hstack(*coordinates)
    assert rank(ward_span) == radical.shape[1]
    assert rank(DM.hstack(ward_span, radical)) == radical.shape[1]
    print('PASS all nine original Ward functions and derivative jets cover the complete twelve-dimensional radical', momentum, flush=True)

    Q = exact(decode(row['quotient_map']))
    B = exact(decode(row['quotient_section']))
    Aq = exact(decode(row['Hamiltonian_generator']))
    Oq = exact(decode(row['nondegenerate_phase_form']))
    Eq = exact(decode(row['Hamiltonian_energy']))
    assert Q.shape == (126, C.shape[1]) and B.shape == (C.shape[1], 126)
    zero(Q*B-eye(126)); zero(Q*radical)
    assert rank(Q) == 126 and C.shape[1]-rank(Q) == radical.shape[1]
    zero(Aq-Q*A*B); zero(Q*A-Aq*Q); zero(Q*free)
    zero(Oq-dagger(B)*omega*B); zero(Eq-dagger(B)*energy*B)
    zero(dagger(Oq)+Oq); zero(dagger(Eq)-Eq)
    assert rank(Oq) == 126
    zero(Oq*Aq-Eq); zero(dagger(Aq)*Oq+Oq*Aq)
    # These pullbacks prove that the quotient energy and phase do not depend
    # on the selected computational section, rather than choosing a new action.
    zero(dagger(Q)*Oq*Q-omega); zero(dagger(Q)*Eq*Q-energy)
    characteristic = s.Poly.from_list([DOMAIN.to_sympy(v) for v in Aq.charpoly()], LAM)
    claimed = s.Poly(parse(row['linearized_characteristic_polynomial']), LAM)
    assert s.expand(characteristic.as_expr()-claimed.as_expr()) == 0 and characteristic.degree() == 126
    assert row['dynamic_quotient_dimension'] == 126
    print('PASS original-action nondegenerate126 Hamiltonian quotient, section independence and full time-flow transport', momentum, flush=True)
    return {'momentum': list(map(str, momentum)), 'consistency_chain': chain,
        'source242_common_velocity_kernel_dimension': 70, 'retained_phase_dimension': 172,
        'consistent_initial_data_dimension': C.shape[1], 'ambient_Omega_rank': rank(O),
        'Omega_on_consistent_carrier_rank': rank(O*C), 'free_derivative_dimension': free.shape[1],
        'complete_source_Ward_jet_radical_dimension': radical.shape[1],
        'quotient_dimension': 126, 'all_time_original_Euler_identity_checked': True,
        'all_time_quotient_flow_intertwining_checked': True,
        'quotient_phase_and_energy_pullback_checked': True,
        'linearized_characteristic_polynomial': str(s.factor(characteristic.as_expr()))}


def main():
    started = time.monotonic()
    candidate_path = HERE/'retained_hamiltonian_reduction.json'
    candidate = json.loads(candidate_path.read_bytes())
    assert candidate['root'] == ROOT_ID
    bound = check_bindings(candidate)
    phase_path = HERE/'retained_matter_action.json'
    phase = json.loads(phase_path.read_bytes())
    assert phase['root'] == ROOT_ID and phase['source_sha256'] == candidate['source_sha256']
    bound += check_bindings(phase)
    audit_path = HERE/'independent_retained_matter_action.json'
    bound += check_bindings(json.loads(audit_path.read_bytes()))
    active_path = BASE/'active-gauge/receipt.json'
    active = json.loads(active_path.read_bytes())
    for name, digest in candidate['source_sha256'].items():
        assert active['source_sha256'][name] == digest
    source_operator = polynomial(active['primitive_121_Fourier_Jacobi_entries'], 121)
    assert not (source_operator-decode(phase['retained_operator'])).applyfunc(s.expand).todok()
    exchange_path = BASE/'matter-vertices/exchange.json'
    exchange = json.loads(exchange_path.read_bytes())
    F = decode(exchange['full_polynomial_field_change'])
    original_gauge = F[:121, 112:121]
    assert original_gauge == decode(phase['normal_coordinate_change'])[:, 112:121]
    original_full = polynomial(active['Fourier_Jacobi_entries'], 289)
    assert not (original_full*F[:, 112:121]).applyfunc(s.expand).todok()
    print('PASS original full289 Ward columns and primitive121 polynomial source, current source/receipt bindings', bound, flush=True)
    dynamic_path = HERE/'dynamic.json'
    dynamic = json.loads(dynamic_path.read_bytes())
    actual = next(row for row in dynamic['samples'] if row['name'] == 'energy_transfer')
    momentum = tuple(s.simplify(v/s.I) for v in decode(actual['transfer'])[1:, 0])
    rows = candidate['source_momenta']
    assert len(rows) == 2
    assert [tuple(parse(v) for v in row['momentum']) for row in rows] == [(0, 0, 0), momentum]
    results = [audit_momentum(row, source_operator, original_gauge, phase) for row in rows]
    spectrum_path = BASE/'canonical-active/spectrum/receipt.json'
    spectrum = json.loads(spectrum_path.read_bytes())
    scale_path = BASE/'matter-modes/source.json'
    scale = parse(json.loads(scale_path.read_bytes())['time_scale'])
    u = s.Symbol('u')
    expected = s.Poly(1, LAM)
    for group in ('canonical_q_zero_factors', 'complement_q_zero_factors'):
        for factor, multiplicity in spectrum[group].items():
            expected *= s.Poly(s.sympify(factor).subs(u, LAM/scale), LAM).monic()**multiplicity
    zero_polynomial = s.Poly(parse(results[0]['linearized_characteristic_polynomial']), LAM)
    assert s.expand(zero_polynomial.as_expr()-expected.monic().as_expr()) == 0 and expected.degree() == 126
    print('PASS exact zero-momentum126 characteristic equals the original canonical79/dual24 divisors with source time scale', flush=True)
    paths = [candidate_path, HERE/'retained_hamiltonian_reduction.py', phase_path, audit_path,
             active_path, exchange_path, dynamic_path, spectrum_path, scale_path,
             HERE/'independent_retained_hamiltonian_reduction.py']
    output = {'verdict': 'CERTIFIED_ORIGINAL_SOURCE_CONSISTENCY_CHAIN_WARD_RADICAL_AND_HAMILTONIAN_QUOTIENT',
        'root': ROOT_ID, 'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'candidate_constructor_imported': False,
        'algorithm': 'original primitive121 and full289 Ward polynomials; relation-kernel projection consistency chain; exact complete ranks/nullspaces, source Ward coefficient span, all-time original Euler and quotient matrix identities',
        'source_momenta': results, 'zero_characteristic_matches_original_response_divisors': True,
        'source_auxiliary_Schur_repeated': False,
        'dimension_convention': 'fixed complex Fourier-coordinate dimensions; a real nonzero-momentum field retains the conjugate negative-momentum readback',
        'scope': 'homogeneous original mixed Jacobi action at the two displayed source momenta; original9 Ward function jets generate its complete radical and nondegenerate126 Hamiltonian quotient',
        'momentum_rank_uniformity_claimed': False, 'mixed_matter_assigned_bosonic_CCR': False,
        'interacting_composite_pole_or_decay_measure_claimed': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'independent_retained_hamiltonian_reduction.json').write_text(json.dumps(output, indent=2)+'\n')
    print('PASS independent original Ward Hamiltonian quotient certification', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
