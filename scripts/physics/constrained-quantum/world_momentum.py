#!/usr/bin/env python3
"""The same axial source response transported by the paired Borel frame.

Fields use L, covariant sources use L^(-T), and opposite spatial momenta use
the same frame with opposite signed radius.  No new source occurrence or
independent inverse is introduced.
"""
from __future__ import annotations

from functools import lru_cache
import gzip
import importlib.util
import json
from pathlib import Path
import sys
import time

import sympy as s

from dynamic import BASE, HERE, P, ROOT_ID, SourceExchange, decode, read


X, Q = s.symbols("x q")


@lru_cache(None)
def scalar_clean(value):
    return s.simplify(s.expand(value))


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(scalar_clean)


def equal(left, right):
    assert not clean(left - right).todok()


def encode(matrix):
    return {"shape": list(matrix.shape), "entries": [
        [int(i), int(j), str(v)] for (i, j), v in sorted(clean(matrix).todok().items())]}


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def verify_rotation_inputs(source, finite, transport):
    """Replay only the existing exact circle certificates, not the old pipeline."""
    directory = BASE / "active-gauge/rotation"
    helper = load_module("finite", directory / "finite.py")
    quotient_helper = load_module("source_quotient_transport", directory / "quotient_transport.py")
    _, coefficients = helper.source_integer_coefficients(source.active)
    symmetry = read("active-gauge/symmetries.json")
    _, tangent = helper.source_integer_coefficients({"Fourier_Jacobi_entries": symmetry["source_symmetry_tangents_112"]})
    _, reduced = helper.source_integer_coefficients({"Fourier_Jacobi_entries": source.active["equivalent_112_Fourier_Jacobi_entries"]})
    source_rows = set(source.order)
    checks = []
    for entry, quotient in zip(finite["certificates"], transport["certificates"]):
        field = {(i, j): tuple(values) for i, j, values in entry["field_numerator"]}
        spatial = {(i, j): tuple(values) for i, j, values in entry["spatial_numerator"]}
        assert all((i in source_rows) == (j in source_rows) for i, j in field)
        helper.field_inverse(field, entry["field_constant_denominator"])
        slots = helper.finite_congruence(coefficients, spatial, entry["field_constant_denominator"], field)
        assert slots == entry["exact_zero_congruence_coefficient_slots"]
        regenerated = quotient_helper.verify(tangent, reduced, entry)
        assert regenerated == quotient
        checks.append({"axis": entry["axis"], "all289_congruence_slots": slots,
                       "whole_inverse_polynomial": True, "all97_source_coordinates_preserved": True,
                       "same_nine_tangent_image_transported": True})
    print("PASS all three original integer-polynomial circle and tangent certificates; complete97 source subspace", flush=True)
    return checks


def quarter(cosine, sine):
    if cosine == -1:
        return s.Integer(1)
    half = s.sqrt((1 + cosine) / 2)
    return scalar_clean(sine / (2 * half * (1 + half)))


@lru_cache(None)
def circle_value(coefficients, power, cosine, sine, inverse=False):
    """Evaluate the frozen quarter-angle polynomial through its half angle.

    z^(2m)/(1+z²)^d=(1-a)^m(1+a)^(d-m)/2^d and the
    odd formula has one b, where a=cos(theta/2), b=sin(theta/2).
    This avoids expanding nested quarter-angle denominators repeatedly.
    """
    a, b = s.symbols("half_cos half_sin")
    value = s.Integer(0)
    for n, coefficient in enumerate(coefficients):
        m = n // 2
        weight = (1 - a) ** m * (1 + a) ** (power - m) if n % 2 == 0 else b * (1 - a) ** m * (1 + a) ** (power - m - 1)
        value += coefficient * weight / 2 ** power
    half_cos = s.sqrt((1 + cosine) / 2)
    half_sin = s.Integer(1) if cosine == -1 else sine / (2 * half_cos)
    if inverse:
        half_sin = -half_sin
    return scalar_clean(s.expand(value).subs({a: half_cos, b: half_sin}))


def circle(entry, cosine, sine, inverse=False):
    field = s.SparseMatrix(289, 289, {(i, j): circle_value(tuple(values), 4, cosine, sine, inverse)
        / entry["field_constant_denominator"] for i, j, values in entry["field_numerator"]})
    spatial = s.SparseMatrix(4, 4, {(i, j): circle_value(tuple(values), 2, cosine, sine, inverse)
                                   for i, j, values in entry["spatial_numerator"]})
    return clean(field), clean(spatial)


def paired_frame(momentum, finite):
    k = s.Matrix(momentum)
    if k == s.zeros(3, 1):
        return {"field": s.eye(289), "inverse": s.eye(289), "rotation": s.eye(4),
                "q": s.Integer(0), "parameters": [s.Integer(0), s.Integer(0)],
                "angles": [(s.Integer(1), s.Integer(0)), (s.Integer(1), s.Integer(0))]}
    first = next(k[i] for i in [2, 1, 0] if k[i] != 0)
    sign = s.sign(first)
    assert sign in [-1, 1]
    representative = sign * k
    radius = scalar_clean(s.sqrt((k.T * k)[0]))
    transverse = scalar_clean(s.sqrt(representative[0] ** 2 + representative[1] ** 2))
    cy, sy = scalar_clean(representative[2] / radius), scalar_clean(transverse / radius)
    cz, sz = (s.Integer(1), s.Integer(0)) if transverse == 0 else (
        scalar_clean(representative[0] / transverse), scalar_clean(representative[1] / transverse))
    Y, Ry = circle(finite["certificates"][1], cy, sy)
    Z, Rz = circle(finite["certificates"][2], cz, sz)
    Yi, _ = circle(finite["certificates"][1], cy, sy, True)
    Zi, _ = circle(finite["certificates"][2], cz, sz, True)
    frame, inverse, rotation = clean(Z * Y), clean(Yi * Zi), clean(Ry * Rz)
    equal(frame * inverse, s.eye(289))
    equal(inverse * frame, s.eye(289))
    equal(rotation * s.Matrix([0, *k]), s.Matrix([0, 0, 0, sign * radius]))
    assert not any(v.has(X) for v in frame.todok().values())
    return {"field": frame, "inverse": inverse, "rotation": rotation,
            "q": scalar_clean(sign * radius / s.sqrt(2)),
            "parameters": [quarter(cy, sy), quarter(cz, sz)], "angles": [(cy, sy), (cz, sz)]}


def evaluate(record, xvalue, qvalue):
    return s.SparseMatrix(*record["shape"], {(i, j): scalar_clean(s.sympify(v, locals={"x": xvalue, "q": qvalue}))
                                           for i, j, v in record["entries"]})


def apply_inverse(blocks, rhs, xvalue, qvalue):
    result = s.zeros(rhs.rows, rhs.cols)
    for block in blocks:
        indices = block["indices"]
        force = rhs.extract(indices, range(rhs.cols))
        if force == s.zeros(*force.shape):
            continue
        denominator = scalar_clean(s.sympify(block["denominator"], locals={"x": xvalue, "q": qvalue}))
        assert denominator != 0
        answer = s.zeros(len(indices), rhs.cols)
        needed = {j for j in range(len(indices)) if any(force[j, c] != 0 for c in range(rhs.cols))}
        for i, j, value in block["numerator"]["entries"]:
            if j in needed:
                entry = scalar_clean(s.sympify(value, locals={"x": xvalue, "q": qvalue}))
                for col in range(rhs.cols):
                    if force[j, col] != 0:
                        answer[i, col] += entry * force[j, col]
        answer = clean(answer / denominator)
        for i, row in enumerate(indices):
            for col in range(rhs.cols):
                result[row, col] = answer[i, col]
    return clean(result)


def axial_response(source, axial, current, xvalue, qvalue):
    r = s.Matrix([source.clock * xvalue, 0, 0, s.I * s.sqrt(2) * qvalue])
    maps = {key: evaluate(value, xvalue, qvalue) for key, value in axial["source_maps_and_field_lifts"].items()}
    scaling = s.diag(*map(s.sympify, axial["canonical_scaling_diagonal"]))
    f79, f24 = clean(maps["canonical_source_map"] * current), clean(maps["independent_dual_source_map"] * current)
    x79 = clean(scaling * apply_inverse(axial["canonical_blocks"], scaling * f79, xvalue, qvalue) / source.N)
    x24 = clean(apply_inverse(axial["independent_dual_blocks"], f24, xvalue, qvalue) / source.N)
    equal(source.at("canonical_operator", r) * x79, f79)
    equal(source.at("independent_dual_operator", r) * x24, f24)
    field = clean(maps["contact_field_response"] * current + maps["canonical_field_lift"] * x79
                  + maps["independent_dual_field_lift"] * x24)
    equal(source.action(r) * field, source.injection * current)
    return field


def source_transport(source, axial, frame, xvalue, world_raw):
    L, Li = frame["field"], frame["inverse"]
    Ls, Lsi = L.extract(source.order, source.order), Li.extract(source.order, source.order)
    equal(Ls * Lsi, s.eye(97))
    Pax = evaluate(axial["source_compatibility_projector"], xvalue, frame["q"])
    Bax = evaluate(axial["source_boundary_coefficient"], xvalue, frame["q"])
    axis_raw = clean(Ls.T * world_raw)
    axis_current = clean(Pax * axis_raw)
    world_current = clean(Lsi.T * axis_current)
    world_projector = clean(Lsi.T * Pax * Ls.T)
    world_boundary = clean(Lsi.T * Bax * Ls.T)
    equal(world_projector * world_projector, world_projector)
    equal(world_projector * world_raw, world_current)
    axis_field = axial_response(source, axial, axis_current, xvalue, frame["q"])
    world_field = clean(L * axis_field)
    equal(L.T * source.injection * world_current, source.injection * axis_current)
    return {"field": world_field, "axis_field": axis_field, "current": world_current,
            "axis_current": axis_current, "projector": world_projector, "boundary": world_boundary,
            "wrong_boundary_difference": clean(world_boundary - Ls * Bax * Ls.T)}


def polynomial_equal(left, right):
    assert not s.SparseMatrix(left - right).applyfunc(s.expand).todok()


def verify_scalar_rotation_inputs(source, finite, scalar_rotations):
    """All-angle scalar congruence, active restriction and projected faces."""
    assert scalar_rotations["source_sha256"] == source.vertices["source_sha256"]
    z, u, r1, r2, r3 = s.symbols("z u r1 r2 r3")
    denominator = (1 + z * z) ** 2
    operator = decode(source.scalar["normalized_full_scalar_operator"])
    constant = operator.subs({u: 0, r1: 0, r2: 0, r3: 0})
    linear = [operator.diff(r).subs({u: 0, r1: 0, r2: 0, r3: 0}) for r in [r1, r2, r3]]
    polynomial_equal(operator, constant + 2 * (u * u - r1 * r1 - r2 * r2 - r3 * r3) * s.eye(70)
                     + sum((r * matrix for r, matrix in zip([r1, r2, r3], linear)), s.zeros(70)))
    J = decode(source.scalar["full_scalar_source_split_active_map"]).T
    projectors = {key: decode(source.scalar[key]) for key in
                  ["peripheral_projector", "singlet_projector", "doublet_projector"]}
    polynomial_equal(projectors["singlet_projector"] + projectors["doublet_projector"],
                     projectors["peripheral_projector"])
    assert [s.trace(projectors[key]) for key in projectors] == [61, 25, 36]
    result = []
    for entry, active in zip(scalar_rotations["certificates"], finite["certificates"]):
        scalar = decode(entry["scalar_70_numerator"])
        rotation = decode(entry["spatial_numerator"])
        old_rotation = s.SparseMatrix(4, 4, {(i, j): sum(v * z ** n for n, v in enumerate(coefficients))
            for i, j, coefficients in active["spatial_numerator"]})
        polynomial_equal(rotation, old_rotation[1:, 1:])
        polynomial_equal(rotation.T * rotation, denominator ** 2 * s.eye(3))
        polynomial_equal(scalar.T * scalar, denominator ** 2 * s.eye(70))
        polynomial_equal(scalar * scalar.T, denominator ** 2 * s.eye(70))
        polynomial_equal(scalar.subs(z, -z), scalar.T)
        polynomial_equal(constant * scalar, scalar * constant)
        for axis in range(3):
            polynomial_equal(sum((rotation[axis, other] * linear[other] * scalar
                                  for other in range(3)), s.zeros(70)),
                             denominator * scalar * linear[axis])
        for projector in projectors.values():
            polynomial_equal(scalar * projector, projector * scalar)
        active_scalar = s.SparseMatrix(9, 9, {(i, j): sum(v * z ** n for n, v in enumerate(coefficients))
            for i, j, coefficients in active["field_numerator"] if i < 9 and j < 9})
        polynomial_equal(active["field_constant_denominator"] * denominator * scalar * J,
                         J * active_scalar)
        assert entry["original_nonzero_M_intertwines"]
        assert entry["full_source_time_and_spatial_coefficients_intertwine"]
        result.append({"axis": entry["axis"], "all_angle_scalar70_two_sided_inverse": True,
                       "all_frequency_and_three_momentum_operator_coefficients": True,
                       "active_J9_restriction_matches_same289_circle": True,
                       "peripheral61_singlet25_doublet36_preserved": True,
                       "field_source_pairing_preserved": True})
    print("PASS all-angle full70 scalar covariance, same J9 restriction and 61=25+36 faces", flush=True)
    return result


def scalar_circle(entry, cosine, sine, inverse=False):
    z = s.Symbol("z")
    values = {}
    for i, j, expression in entry["scalar_70_numerator"]["entries"]:
        polynomial = s.Poly(s.sympify(expression), z, domain=s.QQ)
        coefficients = tuple(polynomial.nth(n) for n in range(5))
        values[i, j] = circle_value(coefficients, 2, cosine, sine, inverse)
    return clean(s.SparseMatrix(70, 70, values))


def scalar_paired_frame(frame, scalar_rotations):
    (cy, sy), (cz, sz) = frame["angles"]
    Y = scalar_circle(scalar_rotations["certificates"][1], cy, sy)
    Z = scalar_circle(scalar_rotations["certificates"][2], cz, sz)
    Yi = scalar_circle(scalar_rotations["certificates"][1], cy, sy, True)
    Zi = scalar_circle(scalar_rotations["certificates"][2], cz, sz, True)
    field, inverse = clean(Z * Y), clean(Yi * Zi)
    equal(field * inverse, s.eye(70))
    equal(inverse, field.T)
    return field, inverse


def scalar_world_response(source, axial, scalar_rotations, finite):
    # Both quarter angles are finite and rational, and all three physical
    # momentum components are nonzero.  The frame is still selected from k.
    momentum = s.sqrt(2) * s.Matrix([-s.Rational(168, 625), s.Rational(576, 625), s.Rational(7, 25)])
    frame = paired_frame(momentum, finite)
    assert frame["parameters"] == [s.Rational(1, 3), s.Rational(1, 2)]
    scalar, inverse = scalar_paired_frame(frame, scalar_rotations)
    reflected = paired_frame(-momentum, finite)
    negative_scalar, _ = scalar_paired_frame(reflected, scalar_rotations)
    equal(scalar, negative_scalar)
    J = decode(source.scalar["full_scalar_source_split_active_map"]).T
    equal(scalar * J, J * frame["field"][:9, :9])
    peripheral = decode(source.scalar["peripheral_projector"])
    equal(scalar * peripheral * scalar.T, peripheral)
    xvalue = 6 - s.I
    numerator = evaluate(axial["peripheral_scalar_numerator"], xvalue, frame["q"])
    denominator = scalar_clean(s.sympify(axial["peripheral_scalar_denominator"],
                                        locals={"x": xvalue, "q": frame["q"]}))
    assert denominator != 0
    green_axis = clean(numerator / denominator)
    green_world = clean(scalar * green_axis * scalar.T)
    variables = s.symbols("u r1 r2 r3")
    actual = decode(source.scalar["normalized_full_scalar_operator"])
    world_operator = clean(actual.subs(dict(zip(variables,
        [xvalue, *[s.I * k / s.sqrt(2) for k in momentum]]))))
    axis_operator = clean(actual.subs(dict(zip(variables, [xvalue, 0, 0, s.I * frame["q"]]))))
    equal(scalar.T * world_operator * scalar, axis_operator)
    equal(source.N * world_operator * green_world, peripheral)
    equal(source.N * green_world * world_operator, peripheral)
    equal(peripheral * green_world, green_world)
    equal(green_world * peripheral, green_world)
    equal(J.T * green_world, s.zeros(9, 70))
    equal(green_world * J, s.zeros(70, 9))
    # A source is pulled to the axis by S70^T.  Using S70 in that slot is
    # wrong even though the real scalar representation itself is orthogonal.
    wrong_source_variance = clean(source.N * world_operator * scalar * green_axis * scalar - peripheral)
    assert wrong_source_variance != s.zeros(70)
    wrong_phase_operator = clean(actual.subs(dict(zip(variables,
        [xvalue, *[k / s.sqrt(2) for k in momentum]]))))
    wrong_phase = clean(source.N * wrong_phase_operator * green_world - peripheral)
    assert wrong_phase != s.zeros(70)
    def witness(matrix):
        (i, j), value = next(iter(matrix.todok().items()))
        return {"row": int(i), "column": int(j), "value": str(value), "nonzero_entries": len(matrix.todok())}
    print("PASS nonaxial completeP61 scalar Green left/right identities and wrong variance/Fourier phase controls", flush=True)
    return {"physical_momentum": encode(momentum), "paired_parameters_y_z": ["1/3", "1/2"],
        "signed_axial_q": str(frame["q"]), "physical_lambda": str(source.clock * xvalue),
        "scalar70_frame": encode(scalar), "world_green70": encode(green_world),
        "whole_P61_left_inverse": True, "whole_P61_right_inverse": True,
        "all70_source_columns_consumed": True, "active9_annihilated_by_peripheral_response": True,
        "same_scalar_frame_for_opposite_momenta": True,
        "wrong_source_pullback_variance": witness(wrong_source_variance),
        "omitted_spatial_Fourier_I": witness(wrong_phase)}


def main():
    began = time.monotonic()
    source = SourceExchange()
    axial = json.loads(gzip.decompress((HERE / "all-momentum.json.gz").read_bytes()))
    assert axial["root"] == ROOT_ID and axial["source_sha256"] == source.vertices["source_sha256"]
    finite, quotient = read("active-gauge/rotation/finite.json"), read("active-gauge/rotation/quotient-transport.json")
    checks = verify_rotation_inputs(source, finite, quotient)
    scalar_rotations = read("canonical-peripheral/rotation/receipt.json")
    scalar_checks = verify_scalar_rotation_inputs(source, finite, scalar_rotations)
    # This is precisely the half-angle evaluation used by the existing circle
    # polynomials, checked before concrete paired frames are selected.
    z = s.Symbol("z")
    for power in [2, 4]:
        for n in range(2 * power + 1):
            a, b = (1 - z * z) / (1 + z * z), 2 * z / (1 + z * z)
            m = n // 2
            weight = (1 - a) ** m * (1 + a) ** (power - m) if n % 2 == 0 else b * (1 - a) ** m * (1 + a) ** (power - m - 1)
            assert s.cancel(weight / 2 ** power - z ** n / (1 + z * z) ** power) == 0

    dynamic = json.loads((HERE / "dynamic.json").read_text())
    old = next(v for v in dynamic["samples"] if v["name"] == "energy_transfer")
    transfer, raw, reader = decode(old["transfer"]), decode(old["first_current"]), decode(old["second_current"])
    momentum = clean(transfer[1:, :] / s.I)
    frame = paired_frame(momentum, finite)
    reflected = paired_frame(-momentum, finite)
    equal(frame["field"], reflected["field"])
    assert frame["q"] == -reflected["q"]
    xvalue = scalar_clean(transfer[0] / source.clock)
    value = source_transport(source, axial, frame, xvalue, raw)
    equal(value["current"], raw)
    equal(source.action(transfer) * value["field"], source.injection * raw)
    equal(source.at("local_source_compatibility_map", transfer) * value["current"], s.zeros(9, 1))
    difference = clean(value["field"] - decode(old["response"]["field289"]))
    equal(source.action(transfer) * difference, s.zeros(289, 1))
    equal(reader.T * source.injection.T * difference, s.zeros(1, 1))
    consumers = [{"label": "actual_energy_transfer", "physical_momentum": encode(momentum),
        "paired_parameters_y_z": list(map(str, frame["parameters"])), "signed_axial_q": str(frame["q"]),
        "field289": encode(value["field"]), "actual_current_retained": True,
        "all289_rows": True, "same_frame_for_opposite_momenta": True,
        "fixed_section_field_difference_nonzero": bool(difference.todok()),
        "fixed_section_difference_is_source_null": True, "other_actual_current_pairing_difference": "0"}]
    print("PASS actual energy-transfer world field, full289 rows and compatible reader across sections", flush=True)

    bad_momentum = s.Matrix([3 * s.sqrt(2) / 5, 4 * s.sqrt(2) / 5, 0])
    bad_transfer = s.Matrix([source.clock * (6 - s.I), *[s.I * k for k in bad_momentum]])
    removed = read("active-gauge/quotient.json")["fixed_section_removed_original_fields"]
    columns = [source.order.index(i) for i in removed]
    bad_ward = source.at("local_source_compatibility_map", bad_transfer)
    assert bad_ward[:, columns].det() == 0
    bad_frame = paired_frame(bad_momentum, finite)
    probe = s.zeros(97, 1)
    probe[9] = 1
    bad = source_transport(source, axial, bad_frame, 6 - s.I, probe)
    assert bad["current"] != s.zeros(97, 1)
    equal(bad_ward * bad["current"], s.zeros(9, 1))
    equal(source.action(bad_transfer) * bad["field"], source.injection * bad["current"])
    symbolic_transfer = s.Matrix([source.clock * X, *[s.I * k for k in bad_momentum]])
    Ls = bad_frame["field"].extract(source.order, source.order)
    Lsi = bad_frame["inverse"].extract(source.order, source.order)
    projector = clean(Lsi.T * evaluate(axial["source_compatibility_projector"], X, bad_frame["q"]) * Ls.T)
    equal(source.at("local_source_compatibility_map", symbolic_transfer) * projector, s.zeros(9, 97))
    equal(-projector.diff(X) / source.clock, bad["boundary"])
    consumers.append({"label": "old_world_minor_zero", "physical_momentum": encode(bad_momentum),
        "k1_squared": "18/25", "old_world_minor_determinant": "0",
        "paired_parameters_y_z": list(map(str, bad_frame["parameters"])), "signed_axial_q": str(bad_frame["q"]),
        "raw_source": encode(probe), "prepared_world_source": encode(bad["current"]),
        "field289": encode(bad["field"]), "all289_rows": True,
        "all_frequency_world_Ward_projector_zero": True,
        "actual_initial_boundary_uses_inverse_transpose": True,
        "wrong_field_variance_boundary_difference_nonzero": bool(bad["wrong_boundary_difference"].todok())})
    print("PASS old-minor-zero world direction with all-frequency Ward and actual full289 response", flush=True)

    zero_frame = paired_frame(s.zeros(3, 1), finite)
    zero = source_transport(source, axial, zero_frame, 6 - s.I, probe)
    equal(zero["field"], zero["axis_field"])
    equal(source.action(s.Matrix([source.clock * (6 - s.I), 0, 0, 0])) * zero["field"],
          source.injection * zero["current"])
    consumers.append({"label": "zero_momentum_native_identity", "field_frame": "I289",
                      "source_frame": "I97", "signed_axial_q": "0", "all289_rows": True})
    print("PASS zero-momentum native identity response", flush=True)
    scalar_consumer = scalar_world_response(source, axial, scalar_rotations, finite)
    scalar_zero, _ = scalar_paired_frame(zero_frame, scalar_rotations)
    equal(scalar_zero, s.eye(70))
    output = {"root": ROOT_ID, "source_sha256": source.vertices["source_sha256"],
        "scope": "SAME_ROOT_ALL_THREE_MOMENTUM_FOUR_BLOCK_SOURCE_RESPONSE_TRANSPORT",
        "axial_input": "Verification/physics/low-energy-phenomenology/external-composite-decay/all-momentum.json.gz",
        "exact_circle_checks": checks,
        "formal_frame_producers": ["PacketField.pairedParameters_negative", "PacketField.pairedRotation_alignment",
                                    "PacketField.borelParameters_measurable"],
        "frame_recipe": {"line_sign": "sign(firstNonzero(k_z,k_y,k_x))", "representative": "line_sign*k",
            "rotation": "R=Ry(y)Rz(z); Rk=(0,0,line_sign*|k|)",
            "field": "L=Sz(z)Sy(y)", "inverse": "Li=Sy(-y)Sz(-z)",
            "source": "j_axis=L_source^T*j_world; j_world=L_source^(-T)*j_axis",
            "world_response": "Y_world=L*G_axis(lambda,q)*P_axis(lambda,q)*L_source^T*j_world",
            "world_Ward_projection": "P_world=L_source^(-T)*P_axis*L_source^T",
            "world_initial_boundary": "B_world=L_source^(-T)*B_axis*L_source^T",
            "signed_radius": "q=line_sign*|k|/sqrt(2)", "zero_momentum": "L=I289",
            "opposite_momenta": "same y,z,L; q changes sign", "time_poles": "L independent of lambda, so no new temporal poles"},
        "all_radius_identity": "H_world G_world_prepared=injection P_world, from exact all-circle congruences and generated all-radius axial two-sided inverses",
        "focused_consumers": consumers,
        "peripheral_scalar61_transport": {"status": "ALL_THREE_MOMENTUM_PROJECTED_SCALAR_GREEN_CLOSED",
            "circle_input": "Verification/physics/low-energy-phenomenology/canonical-peripheral/rotation/receipt.json",
            "all_angle_polynomial_checks": scalar_checks,
            "same_paired_frame": "S70(k)=S70_Z(z)S70_Y(y); inverse=S70_Y(-y)S70_Z(-z)=S70(k)^T",
            "source_variance": "z_axis=S70^T*z_world; z_world=S70^(-T)*z_axis",
            "world_green": "G61_world=S70*G61_axis(lambda,q)*S70^T",
            "universal_projected_identity": "N*K70_world*G61_world=P61=N*G61_world*K70_world",
            "same_active_scalar_source": "S70 J=J L9, hence J^T S70^T=L9^T J^T; active9 and peripheral61 use the same original scalar70 source",
            "preserved_faces": {"active": 9, "peripheral": 61, "singlet": 25, "doublet": 36},
            "zero_momentum_scalar_frame": "I70", "focused_full70_consumer": scalar_consumer,
            "primal_readback_contract": {
                "source_green_input": "Verification/physics/low-energy-phenomenology/scalar-exchange/receipt.json#original_primal_readback_blocks",
                "source_rotation_input": "Verification/physics/low-energy-phenomenology/canonical-peripheral/rotation/receipt.json",
                "whole_euler_transport_consumer": "Verification/physics/low-energy-phenomenology/canonical-peripheral/rotation/transport.json#concrete_original_equation_consumers",
                "retained_contract": "same-source nonzero M intertwiner and full time/spatial primal-dual covariance; this checkpoint checks the complete scalar70 projected Green and does not claim a fresh1078-row field reconstruction"}},
        "classification": "same-root whole-carrier transporter; no new source occurrence",
        "multi_particle_spectral_status": "SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED",
        "elapsed_seconds": round(time.monotonic() - began, 3)}
    (HERE / "world-momentum.json").write_text(json.dumps(output, separators=(",", ":")) + "\n")
    print("PASS paired-frame all-three-momentum four-block source transporter", flush=True)


if __name__ == "__main__":
    main()
