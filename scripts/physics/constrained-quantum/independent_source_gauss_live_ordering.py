#!/usr/bin/env python3
"""Independent variable-coefficient Gauss ordering and wavepacket consumer.

Matrix inverse derivatives are obtained by Gauss--Jordan elimination over
the first-order scalar coefficient ring. A genuine61-variable smooth local
wavepacket is then acted on by nested normal momenta, solving their original
linear equations and differentiating those equations before the next action.
"""
from __future__ import annotations

from fractions import Fraction
import hashlib
import itertools
import json
import time

import sympy as s

from independent_source_gauss_quantum_current import (
    exterior_bits, polynomial_real_action, exterior_current, apply_state,
    add_terms, normalize_state)
from independent_source_gauge_legendre import (
    HERE, BASE, ROOT, ROOT_ID, source, bindings, clean, decode, encode, equal, read)


def zero(value):
    assert s.cancel(value) == 0, value


def frac(value):
    value = s.Rational(value)
    return Fraction(int(value.p), int(value.q))


def inverse_first_order(D, dD):
    """Scalar dual-number elimination; no matrix inverse derivative formula."""
    n = D.rows
    rows = [[(frac(D[i, j]), frac(dD[i, j])) for j in range(n)]+
            [(Fraction(int(i == j)), Fraction(0)) for j in range(n)] for i in range(n)]
    def mul(x, y): return (x[0]*y[0], x[0]*y[1]+x[1]*y[0])
    def sub(x, y): return (x[0]-y[0], x[1]-y[1])
    for column in range(n):
        pivot = next(i for i in range(column, n) if rows[i][column][0])
        rows[column], rows[pivot] = rows[pivot], rows[column]
        a, b = rows[column][column]
        inv = (1/a, -b/a**2)
        rows[column] = [mul(inv, x) for x in rows[column]]
        for i in range(n):
            if i == column:
                continue
            coefficient = rows[i][column]
            rows[i] = [sub(x, mul(coefficient, y)) for x, y in zip(rows[i], rows[column])]
    return tuple(s.Matrix(n, n, lambda i, j: s.Rational(rows[i][n+j][order].numerator,
                                                      rows[i][n+j][order].denominator)) for order in range(2))


def state_matrix(vectors):
    labels = sorted({state for vector in vectors for state in vector})
    return labels, s.Matrix(len(vectors), len(labels), lambda i, j: vectors[i].get(labels[j], 0))


def solve_operator_rows(Dtranspose, vectors):
    labels, matrix = state_matrix(vectors)
    result, free = Dtranspose.gauss_jordan_solve(matrix)
    assert free.rows == 0
    return [normalize_state({label: result[i, j] for j, label in enumerate(labels)}) for i in range(result.rows)]


def weighted_matrix_rows(A, vectors):
    return [add_terms((A[i, j], vectors[j]) for j in range(A.cols)) for i in range(A.rows)]


def matrix_norm_inf(A):
    return max(sum(abs(A[i, j]) for j in range(A.cols)) for i in range(A.rows))


def main():
    began = time.monotonic()
    path = HERE/'source_gauss_live_ordering.json'; saved = read(path); count = bindings(saved)
    assert saved['root'] == ROOT_ID
    _, vacuum, degrees, hashes = source.parse_source(ROOT)
    assert hashes == saved['source_sha256']
    fundamental = [s.SparseMatrix(M)*(s.I if imaginary else 1)
                   for _, imaginary, M in source.generators([(0, 1, 2), (3, 4)])]
    rho = [polynomial_real_action(exterior_bits(T, 4)) for T in fundamental]
    matter = [clean(s.kronecker_product(s.eye(4), s.diag(*[exterior_bits(T, k) for k in degrees]))) for T in fundamental]
    v = s.Matrix([vacuum.get(word, 0) for word in itertools.combinations(range(7), 4)]+[0]*35)
    orbit = clean(s.Matrix.hstack(*[T*v for T in rho]))
    broken = list(orbit.rref()[1]); select = s.eye(12)[:, broken]; O = orbit*select
    null = s.Matrix.hstack(*orbit.T.nullspace())
    projector = clean(null*(null.T*null).inv()*null.T)
    R = projector[:, list(projector.rref()[1])]
    dual = clean(R.row_join(O).inv().T[:, :61])
    gram = clean(O.T*O); normal_dual = clean(O*gram.inv())
    eta = s.Matrix(s.symbols('normal_coordinate0:9', real=True))
    for T in rho:
        zero(s.trace(dual.T*T*R)); zero(s.trace(normal_dual.T*T*O))
        normal_coefficients = O.T*T*(v+O*eta)
        normal_commutator = -s.I*sum(gram.inv()[a, j]*s.diff(normal_coefficients[a], eta[j])
                                    for a in range(9) for j in range(9))
        zero(normal_commutator)
    T = [clean(dual.T*rho[a]*R) for a in broken]
    equal(s.Matrix.hstack(*[dual.T*rho[a]*v for a in broken]), s.zeros(61, 9))
    x = decode(saved['actual_off_source_scalar_coordinates'])
    equal(x, s.Matrix([s.Rational((3*j+1) % 7-3, 100) for j in range(61)]))
    phi = v+R*x
    D = clean(O.T*s.Matrix.hstack(*[rho[a]*phi for a in broken]))
    Dpartial = [clean(O.T*s.Matrix.hstack(*[rho[a]*R[:, j] for a in broken])) for j in range(61)]
    b = [clean(M*x) for M in T]
    directional_D = [clean(sum((direction[j]*Dpartial[j] for j in range(61)), s.zeros(9))) for direction in b]
    inverse_and_derivatives = [inverse_first_order(D.T, derivative.T) for derivative in directional_D]
    F = inverse_and_derivatives[0][0]
    derivatives = [value[1] for value in inverse_and_derivatives]
    for value, derivative, dD in zip(inverse_and_derivatives, derivatives, directional_D):
        equal(value[0], F)
        equal(D.T*derivative+dD.T*F, s.zeros(9))
    active_path = BASE/'active-gauge/receipt.json'; active = read(active_path)
    e = s.Matrix(active['actual_background']['coframe']).applyfunc(s.sympify)
    N = e[0, 0]; zero(N*N-s.Rational(54, 125)); h00 = -1/N
    K = clean(F.T*gram*F/(2*h00))
    L = clean(-s.I*sum((F[:, c].T*gram*derivatives[c] for c in range(9)), s.zeros(1, 9))/(2*h00))
    equal(K, decode(saved['actual_off_source_quadratic_coefficient']))
    equal(L, decode(saved['actual_off_source_linear_coefficient']))
    assert len(L.todok()) == 9
    Dsource = O.T*s.Matrix.hstack(*[rho[a]*v for a in broken])
    equal(Dsource, gram)
    source_F, source_derivative = inverse_first_order(gram.T, s.zeros(9))
    equal(source_derivative, s.zeros(9))
    equal(source_F.T*gram*source_F/(2*h00), -N*gram.inv()/2)
    print('PASS raw source blocks/traces and all9 true inverse derivatives by scalar dual-number elimination', flush=True)

    # Wavepacket: eta(y)*exp(-|y|^2/2)*(1+i ell.y+(m.y)^2/2)|5,258>,
    # y=x-x0. eta=1 near0 and has compact support in the explicit ball below.
    # Its exact value/gradient/Hessian retain every61 coordinate direction.
    ell = s.Matrix([s.Rational(j+1, 67) for j in range(61)])
    m = s.Matrix([s.Rational((j % 7)-3, 53) for j in range(61)])
    gradient = s.I*ell
    Hessian = m*m.T-s.eye(61)
    # ||D0^-T (D(x)^T-D0^T)||inf <1/2 on the support is obtained with
    # transposed derivative matrices, so use their exact norms for the guard.
    radius = s.cancel(1/(2*matrix_norm_inf(F)*sum(matrix_norm_inf(A.T) for A in Dpartial)))
    assert radius > 0
    state = (5, 258)
    original_wave = {state: s.S.One}
    charges = [clean(s.diag(s.I*matter[a], s.I*matter[a].conjugate())) for a in broken]
    Jwave = [exterior_current(Q, state) for Q in charges]
    assert any(Jwave)
    Gwave = [add_terms([(-s.I*(b[c].T*gradient)[0], original_wave), (1, Jwave[c])]) for c in range(9)]
    # Derivative of the actual inner current, including derivative of its
    # vector field: d_ba(b_c.grad psi)=(T_c b_a).grad psi+b_c.Hess psi.b_a.
    dG = []
    for aa in range(9):
        rows = []
        for c in range(9):
            scalar = -s.I*(((T[c]*b[aa]).T*gradient)[0]+(b[c].T*Hessian*b[aa])[0])
            rows.append(add_terms([(scalar, original_wave), ((b[aa].T*gradient)[0], Jwave[c])]))
        dG.append(rows)
    zeta_wave = solve_operator_rows(D.T, [add_terms([(-1, row)]) for row in Gwave])
    zeta_derivatives = []
    for aa in range(9):
        coefficient_change = weighted_matrix_rows(directional_D[aa].T, zeta_wave)
        rhs = [add_terms([(-1, dG[aa][c]), (-1, coefficient_change[c])]) for c in range(9)]
        zeta_derivatives.append(solve_operator_rows(D.T, rhs))
    nested = []
    for bb in range(9):
        G_inner = [add_terms([(-s.I, zeta_derivatives[c][bb]), (1, apply_state(charges[c], zeta_wave[bb]))]) for c in range(9)]
        outer = solve_operator_rows(D.T, [add_terms([(-1, row)]) for row in G_inner])
        nested += [(gram[aa, bb]/(2*h00), outer[aa]) for aa in range(9)]
    actual_nested = add_terms(nested)
    GG = [[add_terms([(-s.I, dG[c][d]), (1, apply_state(charges[c], Gwave[d]))]) for d in range(9)] for c in range(9)]
    quadratic = add_terms((K[c, d], GG[c][d]) for c in range(9) for d in range(9))
    correction = add_terms((L[0, d], Gwave[d]) for d in range(9))
    defect = add_terms([(1, actual_nested), (-1, quadratic), (-1, correction)])
    assert defect == {}
    assert correction and actual_nested
    omitted = add_terms([(1, actual_nested), (-1, quadratic)])
    assert omitted == correction
    print('PASS actual61-variable compact wavepacket: nested zeta differential actions equal K GG+L G, omittedL has nonzero output', flush=True)

    from source_gauss_live_ordering import SourceGaussLiveOrdering
    public = SourceGaussLiveOrdering()
    observed = public.coefficients(e, x)
    equal(observed['D'], D); equal(observed['F'], F)
    for actual, expected in zip(observed['scalar_vectors'], b): equal(actual, expected)
    for actual, expected in zip(observed['directional_F'], derivatives): equal(actual, expected)
    equal(observed['linear'], L); equal(observed['quadratic'], K)
    equal(public.coefficients(e, s.zeros(61, 1))['linear'], s.zeros(1, 9))
    wave_encode = lambda values: [[list(label), str(value)] for label, value in sorted(values.items())]
    paths = [path, HERE/'source_gauss_live_ordering.py', HERE/'independent_source_gauss_live_ordering.py',
             HERE/'independent_source_gauss_quantum_current.py', HERE/'independent_source_gauss_quantum_current.json',
             HERE/'independent_source_scalar_gauss_reduction.json', HERE/'independent_source_gauge_legendre.py', active_path]
    result = {'root': ROOT_ID, 'source_sha256': hashes,
        'verdict': 'CERTIFIED_LIVE_GAUSS_ORDERED_COEFFICIENT_IDENTITY_AND_ACTUAL_VARIABLE_WAVEPACKET_CONSUMER',
        'input_sha256': {str(q.relative_to(ROOT)): hashlib.sha256(q.read_bytes()).hexdigest() for q in paths},
        'candidate_bindings_checked': count,
        'all24_original_tangent_and_normal_divergence_traces_zero': True,
        'all12_original_normal_xi_phi_commutators_directly_zero': True,
        'all9_matrix_inverse_directional_derivatives_from_scalar_dual_elimination': True,
        'source_L_zero_and_nine_off_source_L_entries_nonzero': True,
        'actual_variable_coefficient_CCR_wavepacket': {
            'scalar_dimensions': 61, 'wavepacket': 'eta(y)*exp(-|y|^2/2)*(1+i ell.y+(m.y)^2/2)|5,258>, y=x-x0',
            'eta': 'A smooth compact cutoff equal1 for |y|<=r/2 and0 for |y|>=r; r is the generated inverse-norm radius below.',
            'support_radius': str(radius), 'support_inverse_norm_guard': '||F0 (D(x)^T-D0^T)||inf<1/2 inside the support, so every coefficient is smooth there',
            'value_gradient_Hessian': {'value': '1', 'coordinate_indices': 'j=0,...,60',
                'ell_j': '(j+1)/67', 'm_j': '((j mod7)-3)/53',
                'gradient': 'i*ell', 'Hessian': 'm*m^T-I61',
                'all61_gradient_and_all3721_Hessian_entries_used_in_operator_action': True},
            'matter_input': list(state), 'both_original_real_CAR_branches_retained': True,
            'nested_normal_momentum_action': wave_encode(actual_nested),
            'coefficient_commutator_correction_action': wave_encode(correction),
            'nested_minus_KGG_minus_LG': [], 'omitting_L_nonzero': True,
            'calculation_method': 'Solve D^T h=-G psi, implicitly differentiate that equation under all9 actual current vector fields, then apply the outer normal momenta. This does not insert the index formula for L into the nested action.'},
        'generic_local_operator_argument': 'The actual scalar CCR current obeys [G_c,F]=-i b_c.partial F, while the other tensor factors commute with F. Applying the product rule to the left-ordered equation D^T zeta=-G gives K GG+L G throughout det(D)!=0. The executable wavepacket consumer independently reads both sides at the full off-source61-coordinate point.',
        'component_common_invariant_domain': {
            'space': 'C_c^infinity(U_scalar) tensor polynomial(gauge36) tensor finite CAR(Fin504), with U_scalar={x:det D(v+R*x)!=0} and fixed source-admissible coframe e; any fixed finite particle sector is also invariant.',
            'operators': 'All9 G_c, zeta_a=-sum_c F_ac G_c, and the ordered normal-momentum square zeta^T Gram zeta/(2h00).',
            'support': 'Each scalar wavefunction has compact support K contained in U_scalar. Multiplication by F,K,L and every finite scalar differentiation preserve that same support. D^-1 is smooth on U_scalar, so every finite repeated action remains C_c^infinity with support in K.',
            'remaining_factors': 'The homogeneous gauge CCR moment maps are linear vector fields and preserve each bounded polynomial-degree space. The original dGamma(Q_c) preserves particle number and the finite CAR algebraic domain.',
            'claim': 'An actual common invariant operator domain for this ordered component; no completed Hilbert adjoint, full joint Hamiltonian domain or time-evolution invariance is inferred.'},
        'public_complete_coefficient_API_checked': True,
        'full70_position_and_normal_momentum_constraints_imposed_as_simultaneous_operator_equalities': False,
        'Hilbert_adjoint_Cauchy_spectrum_or_decay_claimed': False,
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_gauss_live_ordering.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print(result['verdict'], result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
