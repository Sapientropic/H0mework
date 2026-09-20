#!/usr/bin/env python3
"""Two source phases after exact low-momentum elimination of 77 massive rows.

The Taylor graph is computed from the original canonical operator.  Its finite
remainder, original phase normalization and all 289 Euler rows are retained.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def decode(entries, rows, cols):
    return s.SparseMatrix(rows, cols, {(i, j): s.sympify(value) for i, j, value in entries})


def encode(matrix):
    return {"shape": list(matrix.shape), "entries": [
        [int(i), int(j), str(value)]
        for (i, j), value in sorted(s.SparseMatrix(matrix).todok().items())]}


def homogeneous(matrix, variables):
    result = {}
    for (i, j), value in s.SparseMatrix(matrix).todok().items():
        for powers, coefficient in s.Poly(value, *variables).terms():
            degree = sum(powers)
            if degree not in result:
                result[degree] = s.MutableSparseMatrix(*matrix.shape, {})
            result[degree][i, j] += coefficient * s.prod(
                variable**power for variable, power in zip(variables, powers))
    return {degree: clean(value) for degree, value in result.items()}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()
    base = args.root / "Verification/physics/low-energy-phenomenology"
    source = json.loads((base / "active-gauge/receipt.json").read_text())
    origin = json.loads((base / "active-gauge/origin.json").read_text())
    canonical = json.loads((base / "canonical-active/receipt.json").read_text())
    p = s.symbols("p0 p1 p2 p3")
    variables = s.symbols("u q1 q2 q3")
    u, *q = variables
    n = s.sympify(source["source_lapse"])
    substitution = dict(zip(p, [n*s.sqrt(2)*u, *(s.I*s.sqrt(2)*v for v in q)]))
    neg = dict(zip(variables, [-v for v in variables]))
    order = 4
    scaling = []
    for index in canonical["retained_canonical_fields"]:
        field = canonical["source_fields"][index]
        value = s.S.One
        if field["group"] == "gauge_A":
            value = s.sqrt(2) * (n if field["coordinate"][0] == 0 else 1)
        if field["group"] == "coframe" and field["coordinate"][1] == 0:
            value = n
        scaling.append(value)
    scale = s.diag(*scaling)
    inverse_scale = s.diag(*[1/value for value in scaling])
    native = decode(canonical["canonical_quotient_operator"], 79, 79).subs(substitution)
    G = clean(scale * native * scale / n)
    Gparts = homogeneous(G, variables)
    assert set(Gparts) == {0, 1, 2}
    assert clean(G.subs(neg, simultaneous=True).T - G) == s.zeros(79)
    # QQ(i) coefficients follow from the source field scaling, not fitted constants.
    for part in Gparts.values():
        for value in part.todok().values():
            s.Poly(value, *variables, domain=s.QQ_I)
    C = decode(canonical["canonical_embedding_112_by_88"], 112, 88)
    R = decode(canonical["constant_whole_equation_readback_112_by_88"], 112, 88)
    Q = decode(canonical["quotient_readback"], 79, 88).subs(substitution)
    section = decode(canonical["quotient_section"], 88, 79)
    Z289 = decode(origin["source_289_mode_columns"], 289, 5)[:, [1, 3]]
    phase = clean(inverse_scale * Q * R.T * Z289[9:121, :])
    P = phase.subs(dict.fromkeys(variables, 0))
    assert Gparts[0]*P == s.zeros(79, 2) and P.rank() == 2
    pivot = list(P.T.rref()[1])
    retained = [i for i in range(79) if i not in pivot]
    E = s.SparseMatrix(79, 77, {(row, col): 1 for col, row in enumerate(retained)})
    T = P.row_join(E)
    inverse_T = T.inv(method="DM")
    assert T*inverse_T == inverse_T*T == s.eye(79)
    source_phase_shift = E.T*(phase-P)
    assert clean(phase-P-E*source_phase_shift) == s.zeros(79, 2)
    assert inverse_T[:2, :]*phase == s.eye(2)
    D = {degree: clean(E.T*part*E) for degree, part in Gparts.items()}
    B = {degree: clean(E.T*part*P) for degree, part in Gparts.items()}
    A = {degree: clean(P.T*part*P) for degree, part in Gparts.items()}
    H = {degree: clean(P.T*part*E) for degree, part in Gparts.items()}
    assert B[0] == s.zeros(77, 2) and A[0] == A[1] == s.zeros(2)
    D0 = DomainMatrix.from_Matrix(D[0]).convert_to(s.QQ_I)
    D0inv = D0.inv().to_Matrix()
    assert D[0]*D0inv == D0inv*D[0] == s.eye(77)
    W = {0: s.zeros(77, 2)}
    for degree in range(1, order+1):
        rhs = B.get(degree, s.zeros(77, 2))
        for offset in (1, 2):
            if degree >= offset:
                rhs += D[offset]*W[degree-offset]
        W[degree] = clean(-D0inv*rhs)
        print("heavy Taylor graph degree", degree, "entries", len(W[degree].todok()), flush=True)
    graph = clean(P+E*sum(W.values(), s.zeros(77, 2)))
    transformed_rows = clean(T.T*G*graph)
    light = homogeneous(transformed_rows[:2, :], variables)
    heavy = homogeneous(transformed_rows[2:, :], variables)
    assert all(value == s.zeros(77, 2) for degree, value in heavy.items() if degree <= order)
    light_jet = clean(sum((value for degree, value in light.items() if degree <= order), s.zeros(2)))
    row_lift = inverse_T.T[:, :2]
    remainder = clean(G*graph-row_lift*light_jet)
    remainder_parts = homogeneous(remainder, variables)
    assert min(remainder_parts) >= order+1
    assert clean(light_jet.subs(neg, simultaneous=True).T-light_jet) == s.zeros(2)
    radius_squared = sum(v*v for v in q)
    expected_second = s.diag(s.Rational(32, 11)*u*u+s.Rational(160, 67)*radius_squared,
        -40*u*u+s.Rational(2500, 81)*radius_squared)
    assert clean(light[2]-expected_second) == s.zeros(2)
    assert light.get(3, s.zeros(2)) == s.zeros(2)
    # This constant normalization recovers the original phase angles at every momentum.
    assert clean(inverse_T[:2, :]*graph-s.eye(2)) == s.zeros(2)
    assert clean(graph-phase-E*(sum(W.values(), s.zeros(77, 2))-source_phase_shift)) == s.zeros(79, 2)
    print("source phase quadratic operator:", expected_second, flush=True)
    print("source phase fourth derivative operator:", light[4].applyfunc(s.factor), flush=True)
    # Reconstruct the original field and equation embeddings, including the scalar Ward rows.
    def original_matrix(entries, rows, cols):
        matrix = s.MutableSparseMatrix(rows, cols, {})
        for row, col, powers, value in entries:
            matrix[row, col] += s.sympify(value)*s.prod(
                substitution[variable]**power for variable, power in zip(p, powers))
        return clean(matrix)
    field_lift = s.MutableSparseMatrix(289, 79, {})
    field_lift[9:121, :] = clean(C*section*scale)
    for step in reversed(source["algebraic_Schur_steps"]):
        for row, col, powers, value in step["write_back_auxiliary_from_retained"]:
            field_lift[row, :] += s.sympify(value)*s.prod(
                substitution[variable]**power for variable, power in zip(p, powers))*field_lift[col, :]
        field_lift = clean(field_lift)
    gauge = original_matrix(source["source_primitive_gauge_tangent"], 289, 12)[:121, :]
    broken = source["Ward_constraint_elimination"]["broken_parameter_columns"]
    tangent = gauge[:, broken]
    assert tangent[:9, :] == s.eye(9)
    ward_lift = (-tangent[9:, :].subs(neg, simultaneous=True).T).col_join(s.eye(112))
    equation_lift = s.MutableSparseMatrix(289, 79, {})
    equation_lift[:121, :] = clean(ward_lift*R*Q.subs(neg, simultaneous=True).T*inverse_scale*n)
    original = original_matrix(source["Fourier_Jacobi_entries"], 289, 289)
    assert clean(original*field_lift-equation_lift*G) == s.zeros(289, 79)
    full_graph = clean(field_lift*graph)
    full_remainder = clean(equation_lift*remainder)
    full_light_lift = clean(equation_lift*row_lift)
    assert clean(original*full_graph-full_light_lift*light_jet-full_remainder) == s.zeros(289, 2)
    assert min(homogeneous(full_remainder, variables)) >= order+1
    # Finite Taylor action agrees with its Schur operator through fourth order.
    action = homogeneous(clean(graph.subs(neg, simultaneous=True).T*G*graph), variables)
    for degree in range(order+1):
        assert action.get(degree, s.zeros(2)) == light.get(degree, s.zeros(2))
    # Check both low-momentum branches against the independently generated source slopes.
    det2 = s.factor(expected_second.det())
    original_slopes = [s.simplify(2*n*n*(-s.Rational(160, 67)/s.Rational(32, 11))/2),
        s.simplify(2*n*n*(-s.Rational(2500, 81)/(-40))/2)]
    assert original_slopes == [-s.Rational(594, 1675), s.Rational(1, 3)]
    quartic_slopes = []
    for index, time_coefficient in enumerate((s.Rational(32, 11), -40)):
        c1 = original_slopes[index]/n**2
        on_shell = s.expand(light[4][index, index].subs(u*u, c1*radius_squared))
        correction = s.cancel(-on_shell/(time_coefficient*radius_squared**2))
        assert not correction.has(*variables)
        quartic_slopes.append(s.simplify(n*n*correction/2))
    # Linearize the actual vector and axial phase Noether densities.  The latter
    # includes the spatial coframe cofactor, not just its matter bilinear.
    seed = s.Matrix(source["actual_background"]["primal_H"])
    gamma0 = s.kronecker_product(s.Matrix([[0,0,1,0],[0,0,0,1],[-1,0,0,0],[0,-1,0,0]]),s.eye(3))
    gamma5 = s.diag(*([-1]*6+[1]*6))
    swap = gamma0*gamma5
    dual_seed = s.sqrt(2)*seed.T*swap
    currents = s.MutableSparseMatrix(2, 289, {})
    for index, field in enumerate(source["fields"]):
        group = field["group"]
        if group in ("primal_H", "dual_H"):
            imaginary, spin, color = field["coordinate"]
            basis = s.zeros(12, 1)
            basis[3*spin+color] = s.I**imaginary
            for row, operator in enumerate((-gamma0, swap)):
                value = dual_seed*operator*basis if group == "primal_H" else basis.T*operator*seed
                currents[row, index] = s.re(value[0])
        if group == "coframe":
            a, mu = field["coordinate"]
            if a == mu and mu != 0:
                currents[1, index] = 4*s.sqrt(2)
    current_response = homogeneous(clean(currents*full_graph), variables)
    expected_charge = s.diag(-16*s.sqrt(2)*u/11, 20*s.sqrt(2)*u)
    assert current_response.get(0, s.zeros(2)) == s.zeros(2)
    assert clean(current_response[1]-expected_charge) == s.zeros(2)
    print("source Noether densities at first derivative order:", expected_charge, flush=True)
    print("native lambda-squared fourth-order coefficients:", quartic_slopes, flush=True)
    result = {
        "scope": "ORIGINAL_CANONICAL_SOURCE_PHASE_EFFECTIVE_QUADRATIC_ACTION",
        "coordinates": {"u": "lambda/(N*sqrt(2))", "qj": "kj/sqrt(2)", "p0": "lambda", "pj": "I*kj"},
        "source_phase_names": [origin["source_mode_names"][i] for i in (1, 3)],
        "source_phase_columns_289": encode(Z289), "field_scaling": list(map(str, scaling)),
        "source_phase_section": encode(phase), "constant_phase_basis": encode(P),
        "phase_pivot_indices": pivot, "heavy_indices": retained,
        "phase_and_heavy_basis_inverse": encode(inverse_T),
        "heavy_origin_inverse": encode(D0inv), "heavy_origin_determinant": str(D0.domain.to_sympy(D0.det())),
        "heavy_graph_homogeneous": {str(degree): encode(value) for degree, value in W.items() if degree},
        "effective_operator_homogeneous": {str(degree): encode(value) for degree, value in light.items() if degree <= order},
        "normalized_effective_operator_through_order_four": encode(light_jet),
        "normalized_leading_determinant": str(det2),
        "native_lambda_squared_per_k_squared": list(map(str, original_slopes)),
        "native_lambda_squared_per_k_fourth": list(map(str, quartic_slopes)),
        "native_leading_Lagrangian": "-8/(11*N)*dt(phi)^2 + 40*N/67*sum_i di(phi)^2 + 10/N*dt(theta)^2 + 625*N/81*sum_i di(theta)^2",
        "source_phase_Noether_density_covectors": encode(currents),
        "source_phase_Noether_density_response": {str(degree): encode(value) for degree,value in current_response.items()},
        "native_Noether_density_leading_response": "delta J_phi^0=-16/(11*N)*dt(phi); delta J_theta^0=20/N*dt(theta); background J_theta^0=4*sqrt(2)",
        "normalized_remainder_homogeneous": {str(degree): encode(value) for degree, value in remainder_parts.items()},
        "source_field_lift_289_by_79": encode(field_lift),
        "source_equation_lift_289_by_79": encode(equation_lift),
        "source_phase_field_through_order_four": encode(full_graph),
        "full_equation_effective_row_lift": encode(full_light_lift),
        "full_equation_remainder": encode(full_remainder),
        "all_original_289_rows_with_exact_remainder": True,
        "all_four_momenta_checked": True, "heavy_remainder_starts_at_degree": min(heavy),
        "full_remainder_starts_at_degree": min(homogeneous(full_remainder, variables)),
        "finite_action_matches_schur_through_order_four": True,
        "physical_particle_or_quantum_vacuum_identification": False,
        "elapsed_seconds": round(time.monotonic()-started, 3)}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, ensure_ascii=False, indent=2)+"\n")
    print("PASS: all four momenta; original phase angles; 77-field elimination; all 289 rows with exact degree-five remainder", flush=True)


if __name__ == "__main__":
    main()
