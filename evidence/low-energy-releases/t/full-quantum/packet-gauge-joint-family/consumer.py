#!/usr/bin/env python3
"""Native X0, exact amplitude derivative and the full-family time boundary."""
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
BASE = FQ.parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(FQ/'packet-gauge-kernel'))
import propagation as original

clean, encode = original.clean, original.encode
x, epsilon, a, U, u, q = s.symbols('x epsilon a U u q', real=True)


def read(path):
    data = path.read_bytes()
    return json.loads(gzip.decompress(data) if path.suffix == '.gz' else data)


def matrix(record):
    return original.matrix(record, {str(t): t for t in [x, epsilon, a, U, u, q]})


def main():
    began = time.monotonic()
    files = [HERE/'source.json', HERE/'proper.json', HERE/'contour.json',
        BASE/'active-gauge/receipt.json', FQ/'packet-field/pole-source.json',
        FQ/'packet-gauge-causal/source.json', FQ/'packet-gauge-joint-momentum-jet/jets.json.gz']
    source, proper, contour, actual, pole, frame, previous = map(read, files)
    H0, H1, H2, K0, K1, C1, C2 = [matrix(source[name]) for name in ['H0', 'H1', 'H2', 'K0', 'K1', 'C1', 'C2']]
    L, Li = matrix(frame['L']), matrix(frame['L_inverse'])
    N = s.sympify(actual['source_lapse'])
    c = N*s.sqrt(2)
    rho = s.Rational(1, 131072)
    Fhat = s.Poly(s.sympify(source['complete_Fhat'], locals={'U': U}), U, domain=s.QQ)
    degree = Fhat.degree()
    assert degree == 6
    def reduction(M):
        out = s.MutableSparseMatrix(M.rows, degree, {})
        for (i, power), coefficient in s.SparseMatrix(M).todok().items():
            for (j,), value in s.Poly(U**power, U, domain=s.QQ).rem(Fhat).terms():
                out[i, j] += value*coefficient
        return clean(out)
    def columns(record):
        out = {}
        for i, _, text in record['entries']:
            expression = s.Poly(s.sympify(text, locals={'u': u, 'q': q}).subs(q, rho), u)
            assert all(power % 2 == 0 for (power,), value in expression.terms())
            for (power,), value in expression.terms():
                out[i, power//2] = value
        return reduction(s.SparseMatrix(289, 1+max(j for i, j in out), out))
    A, B, Z = [columns(pole[name]) for name in
        ['pair_numerator_linear', 'pair_numerator_constant', 'source_projection_numerator']]
    assert Z == matrix(source['original_source_numerator'])
    X0 = clean(c*x*A+B)
    I0raw = s.zeros(289, degree+1)
    I0raw[:, :degree] = c*c*x*x*Z
    I0raw[:, 1:] -= c*c*Z
    I0 = reduction(I0raw)
    assert clean(H0*X0-I0) == s.zeros(289, degree)
    removed = source['removed']
    kept = [i for i in range(289) if i not in removed]
    assert X0.extract(removed, range(degree)) == s.zeros(9, degree)
    assert clean(K0.T.subs(x, -x).conjugate()*I0) == s.zeros(9, degree)
    pole_denominator = s.expand(s.sympify(source['source_denominator'], locals={'U': U})*(c*c*x*x-c*c*U))
    at = {x: 6*(1-s.I)}
    assert s.expand(pole_denominator.subs(at)-s.sympify(previous['common_incoming_theta_denominator'], locals={'U': U})) == 0
    assert clean(L*X0.subs(at)-matrix(previous['X0_numerator_coefficients'])) == s.zeros(289, degree)
    assert clean(Li.T*I0.subs(at)-matrix(previous['I0_numerator_coefficients'])) == s.zeros(289, degree)
    # The old record's order0 is first amplitude insertion at external s=0.
    first = previous['derivatives'][0]
    X1world = matrix(first['X1_numerator_coefficients'])
    I1world = matrix(first['I1_numerator_coefficients'])
    X1, I1 = clean(Li*X1world), clean(L.T*I1world)
    assert clean(H0.subs(at)*X1+H1.subs(at)*X0.subs(at)-I1) == s.zeros(289, degree)
    assert X1.extract(removed, range(degree)) == s.zeros(9, degree)
    assert I1.extract(kept, range(degree)) == s.zeros(280, degree)
    minusK = K0.subs(x, -x).conjugate().subs(at)
    assert clean(minusK.T*I1+K1.T*I0.subs(at)+C1.T*X0.subs(at)) == s.zeros(9, degree)
    # The actual inverse family is unique in this section and analytic in
    # epsilon on the generated disk; these equations identify its derivative.
    fpoly = s.Poly(Fhat.as_expr(), U, domain=s.QQ_I)
    def witness(M, row):
        expression = s.expand(sum(M[row, j]*U**j for j in range(degree)))
        for radical in [1, s.sqrt(2), s.sqrt(15), s.sqrt(30)]:
            try:
                polynomial = s.Poly(s.expand(expression/radical), U, domain=s.QQ_I)
            except s.polys.polyerrors.CoercionFailed:
                continue
            if polynomial and polynomial.gcd(fpoly).degree() == 0:
                return {'row': row, 'radical': str(radical), 'gcd_with_complete_Fhat': 0}
        raise AssertionError(('no actual source witness', row))
    response_witness = witness(X1world, 57)
    assert clean(H2*K0+H1*K1) == -C2 and C2.todok()

    # Proper's coefficients are in the source sqrt-basis and normalized112.
    # Primitive retained rows need no higher auxiliary Laurent coefficients.
    keep112 = source['keep121']
    scaled_tau1 = matrix(proper['section_coefficients']['1'])
    spatialA = [i for i, row in enumerate(actual['fields'])
        if row['group'] == 'gauge_A' and row['coordinate'][0] in [1, 2, 3]]
    for row in spatialA:
        if row in keep112:
            assert scaled_tau1.row(keep112.index(row)) == s.zeros(1, 24)
    for row in spatialA:
        assert all(col in spatialA for (i, col), value in L.todok().items() if i == row)
    bg = [i for i, row in enumerate(actual['fields']) if row['group'] == 'gauge_B']
    assert Z.extract(bg, range(degree)) == s.zeros(72, degree)
    assert not any(row in removed for row in bg)
    # Therefore the actual all-epsilon response always satisfies E_B^lin=0.
    # Its spatial A kernels have zero initial values, so D_Aepsilon Xepsilon
    # is strictly proper; this is the native initial-source boundary feed.
    scales = matrix(frame['scales103'])
    diagonal = [s.Integer(1)]*9+[scales[i, i] for i in range(103)]
    source_first = s.zeros(289, degree)
    for i, row in enumerate(keep112):
        for j in range(degree):
            source_first[row, j] = s.expand(diagonal[i]*sum(
                radical*scaled_tau1[i, j+6*k].subs(a, 0)
                for k, radical in enumerate([1, s.sqrt(2), s.sqrt(15), s.sqrt(30)])))
    assert clean(c*source_first.extract(keep112, range(degree))-A.extract(keep112, range(degree))) == s.zeros(112, degree)
    initial_witness = None
    world_initial = clean(L*source_first)
    for row in [9, 10, 15, 16]:
        assert all(col < 121 for (i, col), value in L.todok().items() if i == row)
        try:
            initial_witness = witness(world_initial, row)
            break
        except AssertionError:
            continue
    assert initial_witness
    output = {'scope': 'STRIKE_ORIGINAL_JOINT_FINITE_FAMILY_DIRECT_SOURCE_AND_TIME_BOUNDARY_CONSUMERS',
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in files},
        'native_source_sha256': source['native_source_sha256'],
        'epsilon0_full_variable_frequency_X0_identity': True,
        'epsilon1_same_JointMomentumJet_external_s0_not_s_derivative': True,
        'amplitude_derivative_original289_rows_and_Noether': True,
        'same_fixed_incoming_U_and_original_denominator': True,
        'nonzero_g00_amplitude_response': response_witness,
        'drop_new_E2_C2_contact_fails_Ward': len(C2.todok()),
        'all_parameter_spatial_A_kernel_initial_zero': True,
        'space_rotation_does_not_mix_time_A_initial_into_spatial_A': True,
        'all72_auxiliary_source_components_zero': True,
        'linearized_constitutive_graph_for_all_epsilon': True,
        'first_curvature_transfer_strictly_proper': True,
        'genuine_time_A_initial_nonzero_at_original_root': initial_witness,
        'causal_boundary': 'Yepsilon(0)=0; spatial A time derivatives at0 vanish since their chi(0)=0; first curvature field at0=0. Hence native B^[2](Y(t),Y(s)) vanishes at t=0 or s=0 without Jprime.',
        'native_reader_halfplane': 'Integration of partial_t+partial_s on this actual B^[2] has no boundary term and gives conjugate(z)+w; weak reader is -(left+right).',
        'first_time_zero_contact_retained': True,
        'new_Lean_declarations': 0, 'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'consumer.json').write_text(json.dumps(output, indent=2)+'\n')
    print('PASS native variable-frequency X0, true amplitude response and all-family causal reader boundary',
          output['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
