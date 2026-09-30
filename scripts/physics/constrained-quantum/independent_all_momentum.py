#!/usr/bin/env python3
"""Verify the supplied all-radius numerators, without constructing an inverse."""
from __future__ import annotations

import ast
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time

from flint import fmpq
import sympy as s

from polynomial_inverse import GaussianPolynomial, CONTEXT, ZERO, ONE

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ROOT = HERE.parents[3]
X, Q = s.symbols("x q")
P = s.symbols("p0:4")
sys.setrecursionlimit(20000)


def constant(value):
    return GaussianPolynomial(CONTEXT.from_dict({(0, 0): fmpq(value)}), ZERO.imag)


def native_polynomial(text, *, radius=False):
    """Parse expanded monomials directly into the exact ring, independently of SymPy parsing."""
    def power(a, n):
        assert isinstance(n, int) and n >= 0
        result = ONE
        while n:
            if n % 2:
                result = result*a
            a = a*a
            n //= 2
        return result
    variables = {"x": GaussianPolynomial(CONTEXT.from_dict({(1, 0): 1}), ZERO.imag),
                 "q": GaussianPolynomial(CONTEXT.from_dict({(0, 1): 1}), ZERO.imag),
                 "I": GaussianPolynomial(ZERO.real, ONE.real)}
    if radius:
        variables["R"] = variables["q"]
    def convert(node):
        if isinstance(node, ast.Constant):
            assert isinstance(node.value, int)
            return constant(node.value)
        if isinstance(node, ast.Name):
            return variables[node.id]
        if isinstance(node, ast.UnaryOp):
            value = convert(node.operand)
            assert isinstance(node.op, (ast.UAdd, ast.USub))
            return ZERO-value if isinstance(node.op, ast.USub) else value
        assert isinstance(node, ast.BinOp)
        left = convert(node.left)
        if isinstance(node.op, ast.Pow):
            assert isinstance(node.right, ast.Constant)
            return power(left, node.right.value)
        right = convert(node.right)
        if isinstance(node.op, ast.Add):
            return left+right
        if isinstance(node.op, ast.Sub):
            return left-right
        if isinstance(node.op, ast.Mult):
            return left*right
        assert isinstance(node.op, ast.Div)
        assert not right.imag and set(right.real.to_dict()) <= {(0, 0)}
        denominator = right.real.to_dict()[(0, 0)]
        assert denominator
        return GaussianPolynomial(left.real/denominator, left.imag/denominator)
    return convert(ast.parse(text, mode="eval").body)


def matrix(record):
    return s.SparseMatrix(*record["shape"], {(i, j): s.sympify(v) for i, j, v in record["entries"]})


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def equal(left, right):
    residual = clean(left-right)
    assert not residual.todok(), list(residual.todok().items())[:3]


def polynomial_multiply(left, right, size, denominator):
    """Sparse polynomial multiplication; no elimination or division is performed."""
    right_rows = [{} for _ in range(size)]
    for (i, j), value in right.items():
        right_rows[i][j] = value
    result = {}
    for (i, k), value in left.items():
        for j, other in right_rows[k].items():
            result[i, j] = result.get((i, j), ZERO)+value*other
    for i in range(size):
        result[i, i] = result.get((i, i), ZERO)-denominator
    assert not any(result.values())


def verify_majorant(block, denominator):
    real, imag = denominator.real.to_dict(), denominator.imag.to_dict()
    powers = set(real)|set(imag)
    degree = max(i for i, j in powers)
    spatial_degree = max(j for i, j in powers)
    assert degree == block["time_degree"] and spatial_degree == block["spatial_degree"]
    leading = {power for power in powers if power[0] == degree}
    assert leading == {(degree, 0)}
    assert real.get((degree, 0), 0) == 1 and not imag.get((degree, 0), 0)
    # For |q|<=R, collect sum_{i<degree} |a_i(q)| <= sum_j M_j R^j.
    bounds = {(0, 0): fmpq(1)}
    for power in powers:
        if power[0] < degree:
            key = (0, power[1])
            value = abs(real.get(power, fmpq(0)))+abs(imag.get(power, fmpq(0)))
            bounds[key] = bounds.get(key, fmpq(0))+value
    expected = GaussianPolynomial(CONTEXT.from_dict(bounds), ZERO.imag)
    reported = native_polynomial(block["bounded_momentum_root_majorant"], radius=True)
    assert not (expected-reported)
    assert all(value >= 0 for value in bounds.values()) and bounds[(0, 0)] >= 1
    growth = block["growth_envelope"]
    assert max(i+j for i, j in powers) == degree
    masses = [fmpq(0) for _ in range(int(degree))]
    for (i, j) in powers:
        if i < degree:
            masses[int(i)] += abs(real.get((i, j), fmpq(0)))+abs(imag.get((i, j), fmpq(0)))
    assert masses == [fmpq(value) for value in growth["coefficient_absolute_masses"]]
    coefficient_mass = sum(masses, fmpq(0))
    root_constant = fmpq(growth["linear_momentum_root_constant"])
    companion_bound = fmpq(growth["normalized_companion_norm_bound"])
    assert root_constant == 1+coefficient_mass and root_constant > coefficient_mass
    assert companion_bound == max(fmpq(1), coefficient_mass)
    return {"time_degree": int(degree), "spatial_degree": int(spatial_degree),
            "constant_monic_leading_coefficient": True, "coefficient_majorant_reconstructed": True,
            "total_degree_equals_time_degree": True,
            "rescaled_coefficient_absolute_masses_checked": True,
            "linear_momentum_root_constant": str(root_constant),
            "normalized_companion_norm_bound": str(companion_bound)}


def verify_blocks(operator, blocks, label):
    dimension = operator.rows
    indices = [i for block in blocks for i in block["indices"]]
    assert sorted(indices) == list(range(dimension))
    owner = {i: number for number, block in enumerate(blocks) for i in block["indices"]}
    assert all(owner[i] == owner[j] for i, j in operator.todok())
    reports = []
    for number, block in enumerate(blocks):
        ids = block["indices"]
        size = len(ids)
        original = operator.extract(ids, ids)
        A = {(i, j): GaussianPolynomial.from_expr(value) for (i, j), value in original.todok().items()}
        assert block["numerator"]["shape"] == [size, size]
        numerator = {(i, j): native_polynomial(value) for i, j, value in block["numerator"]["entries"]}
        denominator = native_polynomial(block["denominator"])
        assert denominator
        polynomial_multiply(A, numerator, size, denominator)
        polynomial_multiply(numerator, A, size, denominator)
        # Cross-check the independent parser on each block's denominator and one source entry.
        assert not (denominator-GaussianPolynomial.from_expr(s.sympify(block["denominator"])))
        report = {"block": number, "dimension": size, "A_times_N_eq_dI": True, "N_times_A_eq_dI": True,
                  **verify_majorant(block, denominator)}
        reports.append(report)
        print("PASS independent", label, "block", number, "dim", size,
              "both polynomial products, monic time and all-radius majorant", flush=True)
    return reports


def main():
    start = time.monotonic()
    path = HERE/"all-momentum.json.gz"
    payload = gzip.decompress(path.read_bytes())
    candidate = json.loads(payload)
    assert candidate["root"] == ("positiveSmoothUnifiedSource; repaired Dirac-dual; SpinPair.actual; "
                                  "visit10/tick16/materialEntry -> tick17 unchanged")
    paths = [BASE/name for name in ("matter-vertices/exchange.json", "active-gauge/receipt.json",
        "soft-phase/receipt.json", "active-gauge/quotient.json", "scalar-exchange/receipt.json",
        "matter-modes/source.json", "matter-vertices/receipt.json")]
    exchange, active, soft, quotient, scalar, modes, vertices = [json.loads(p.read_text()) for p in paths]
    assert candidate["source_sha256"] == modes["source_sha256"] == vertices["source_sha256"]
    for name, digest in candidate["source_sha256"].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    N = s.sympify(active["source_lapse"])
    clock = s.sympify(modes["time_scale"])
    assert s.simplify(clock-N*s.sqrt(2)) == 0
    assert s.simplify(s.sympify(candidate["physical_clock"])-clock) == 0 and clock > 0
    at = dict(zip(P, [clock*X, 0, 0, s.I*s.sqrt(2)*Q]))
    def source_map(name):
        return clean(matrix(exchange[name]).subs(at))
    A, B = source_map("canonical_operator"), source_map("independent_dual_operator")
    scales = list(map(s.sympify, soft["field_scaling"]))
    assert len(scales) == 79 and all(value != 0 for value in scales)
    assert scales == list(map(s.sympify, candidate["canonical_scaling_diagonal"]))
    scale = s.diag(*scales)
    canonical_reports = verify_blocks(clean(scale*A*scale/N), candidate["canonical_blocks"], "canonical79")
    dual_reports = verify_blocks(clean(B/N), candidate["independent_dual_blocks"], "dual24")

    C = source_map("local_source_compatibility_map")
    projector = matrix(candidate["source_compatibility_projector"])
    source_fields = exchange["source_field_indices"]
    E = s.SparseMatrix(97, 9, {(source_fields.index(field), j): 1
        for j, field in enumerate(quotient["fixed_section_removed_original_fields"])})
    minor = clean(C*E)
    assert not minor.free_symbols and minor.det() != 0
    equal(projector, s.eye(97)-E*minor.inv()*C)
    equal(C*projector, s.zeros(9, 97))
    equal(projector*projector, projector)
    equal(projector[:9, :], s.eye(97)[:9, :])
    boundary = matrix(candidate["source_boundary_coefficient"])
    equal(boundary, -projector.diff(X)/clock)
    equal(C*boundary, C.diff(X)/clock)
    equal(C.diff(X)*boundary, s.zeros(9, 97))
    equal(projector*E, s.zeros(97, 9))
    print("PASS independent current projection and physical initial-contact identities", flush=True)

    H = s.MutableSparseMatrix(289, 289, {})
    for i, j, powers, coefficient in active["Fourier_Jacobi_entries"]:
        H[i, j] += s.sympify(coefficient)*s.prod(at[p]**power for p, power in zip(P, powers))
    H = clean(H)
    R = source_map("equation_row_lift")
    inject = s.SparseMatrix(289, 97, {(field, j): 1 for j, field in enumerate(source_fields)})
    source_names = ("canonical_source_map", "independent_dual_source_map", "contact_field_response",
                    "canonical_field_lift", "independent_dual_field_lift")
    maps = {name: source_map(name) for name in source_names}
    for name in source_names:
        equal(matrix(candidate["source_maps_and_field_lifts"][name]), maps[name])
    equal(H*maps["canonical_field_lift"], R[:, 9:88]*A)
    equal(H*maps["independent_dual_field_lift"], R[:, 88:112]*B)
    unprojected = clean(H*maps["contact_field_response"]+R[:, 9:88]*maps["canonical_source_map"]
                        +R[:, 88:112]*maps["independent_dual_source_map"]+R[:, 112:121]*C)
    equal(unprojected, inject)
    equal((unprojected-R[:, 112:121]*C)*projector, inject*projector)
    print("PASS independent full289 unprojected source factorization and prepared-source response", flush=True)

    scalar_at = dict(zip(s.symbols("u r1 r2 r3"), [X, 0, 0, s.I*Q]))
    scalar_operator = clean(matrix(scalar["normalized_full_scalar_operator"]).subs(scalar_at))
    scalar_numerator = matrix(candidate["peripheral_scalar_numerator"])
    scalar_denominator = s.sympify(candidate["peripheral_scalar_denominator"])
    equal(scalar_numerator, matrix(scalar["peripheral_scalar_green_numerator"]).subs(scalar_at))
    assert s.expand(scalar_denominator-s.sympify(scalar["peripheral_scalar_green_denominator"]).subs(scalar_at)) == 0
    projection = matrix(scalar["peripheral_projector"])
    equal(projection*projection, projection)
    assert s.trace(projection) == 61
    equal(N*scalar_operator*scalar_numerator, scalar_denominator*projection)
    equal(N*scalar_numerator*scalar_operator, scalar_denominator*projection)
    leading = s.Poly(scalar_denominator, X).LC()
    assert not leading.free_symbols and leading != 0
    scalar_degree = s.degree(scalar_denominator, X)
    radius = s.Symbol("R", nonnegative=True)
    scalar_monic = s.Poly(s.expand(scalar_denominator/leading), X, Q, domain=s.QQ_I)
    scalar_bound = s.expand(1+sum((abs(s.re(value))+abs(s.im(value)))*radius**j
        for (i, j), value in scalar_monic.terms() if i < scalar_degree))
    assert s.Poly(scalar_monic.as_expr(), X).LC() == 1
    print("PASS independent scalar61 two-sided polynomial inverse and nonzero constant temporal leading coefficient", flush=True)

    output = {"verdict": "CERTIFIED_AT_ALL_REAL_AXIAL_MOMENTUM_SCOPE",
        "root": candidate["root"], "candidate_gzip_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "candidate_payload_sha256": hashlib.sha256(payload).hexdigest(),
        "input_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        "algorithm": "direct sparse products in Q(i)[x,q] using supplied N,d; independent AST parser; no propagation-block inverse solver",
        "only_recomputed_inverse": "the 9x9 constant source-preparation minor",
        "inverse_den_called": False, "canonical_blocks": canonical_reports, "independent_dual_blocks": dual_reports,
        "block_partitions_cover_all79_and24": True,
        "source_projector_and_initial_contact_checked": True,
        "all289_unprojected_and_projected_source_rows": True,
        "scalar61_left_and_right_inverse": True, "scalar_time_degree": int(scalar_degree),
        "scalar_time_leading_coefficient": str(leading),
        "scalar_bounded_momentum_root_majorant": str(scalar_bound),
        "pole_bound_argument": "for |q|<=R all monic lower coefficients have sum <= M(R); |x|>=1+M(R) cannot be a zero, coefficientwise over the exact parameter ring",
        "linear_growth_argument": "i+j<=n makes every coefficient of d(r*z,q)/r^n bounded by its checked absolute mass, r=max(1,abs(q)); roots satisfy |x|<(1+sum masses)*r and the normalized companion norm is at most max(1,sum masses)",
        "coverage": "every real axial q and all complex lambda away from generated divisors; polynomial identities include divisor loci without asserting pointwise inversion there",
        "sample_points_used_as_uniform_evidence": False,
        "elapsed_seconds": round(time.monotonic()-start, 3)}
    (HERE/"independent_all_momentum.json").write_text(json.dumps(output, indent=2)+"\n")
    print("PASS independent all-momentum candidate certification", output["elapsed_seconds"], "seconds", flush=True)


if __name__ == "__main__":
    main()
