"""Independent exact checks of complete fixed-law fiber endpoint certificates.

Geometry is reconstructed directly from primitive JSON. The numerical checker
imports no model, endpoint producer, optimizer, or primary square-root helper.
"""
from __future__ import annotations

from fractions import Fraction
import itertools
import json

GAP = Fraction(1, 100_000_000)
ROOT_BITS = 80
RUNS = ("2016-04-15", "2016-06-14")
VERSION = "stage10-munich-readout-fb0001"
PRIMARY_SCHEMA = "stage10-munich-readout-fiber-primary/v1"
SCHEMA = "stage10-munich-readout-fiber-independent/v1"
SCOPE = "complete_regular_fiber_of_one_frozen_generated_joint_law"
FILES = ("criterion-fb0001.md", "fiber_bounds.py", "test_fiber_bounds.py", "fiber_run.py",
         "fiber_independent.py", "test_fiber_independent.py", "FiberBoundsCertification.lean",
         "fiber_certify.py", "test_fiber_certify.py", "fiber-certification-first.json")
INPUTS = ("primitive-witness-c0002.json", "verification.json", "primary-first-c0002.json",
          "identification-verification.json", "identification-certification-first.json")


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def exact(value):
    require(type(value) in (str, int, Fraction), "exact_rational_required")
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError, TypeError) as error:
        raise ValueError("invalid_exact_rational") from error


def pair(value):
    require(type(value) in (list, tuple) and len(value) == 2, "two_rational_coordinates_required")
    return tuple(exact(entry) for entry in value)


def integer_square_root(number):
    require(type(number) is int and number >= 0, "natural_integer_square_root")
    if number == 0:
        return 0
    estimate = 1 << ((number.bit_length() + 1) // 2)
    while True:
        following = (estimate + number // estimate) // 2
        if following >= estimate:
            require(estimate * estimate <= number < (estimate + 1) ** 2, "integer_root_bracket_failed")
            return estimate
        estimate = following


def sqrt_bracket(value, bits=ROOT_BITS):
    value = exact(value)
    require(value >= 0 and type(bits) is int and bits >= 1, "nonnegative_root_and_positive_precision")
    numerator_root = integer_square_root(value.numerator)
    denominator_root = integer_square_root(value.denominator)
    if numerator_root ** 2 == value.numerator and denominator_root ** 2 == value.denominator:
        lower = upper = Fraction(numerator_root, denominator_root)
    else:
        unit = 1 << bits
        radicand = value.numerator * unit * unit // value.denominator
        lower = Fraction(integer_square_root(radicand), unit)
        upper = lower + Fraction(1, unit)
    require(0 <= lower <= upper and lower * lower <= value <= upper * upper, "rational_root_bracket_failed")
    return lower, upper


def primitive_coefficients(document):
    require(type(document) is dict and set(document) == {"alice", "bob"}, "primitive_two_side_shape")
    coefficients, biases = {}, {}
    for side in ("alice", "bob"):
        rows = document[side]
        require(type(rows) in (list, tuple) and len(rows) == 2, "two_own_setting_effects_required")
        coefficients[side], biases[side] = [], []
        for row in rows:
            require(type(row) is dict and set(row) == {"mu", "u", "z"}, "primitive_effect_fields_only")
            mu, u, z = (exact(row[key]) for key in ("mu", "u", "z"))
            require(-1 <= mu <= 1 and u * u + z * z <= (1 - abs(mu)) ** 2, "illegal_source_effect_cone")
            coefficients[side].append((u * u, z * z, (1 - abs(mu)) ** 2))
            biases[side].append(mu)
    # fb0001's generator uses the strict coefficient stratum, including both anchors.
    require(all(number > 0 for rows in coefficients.values() for row in rows for number in row),
            "strict_positive_fiber_coefficients_required")
    return coefficients, biases


def geometry(document, side):
    require(type(side) is str and side in ("alice", "bob"), "physical_side_required")
    coefficients, biases = primitive_coefficients(document)
    other = "bob" if side == "alice" else "alice"
    return coefficients[side], coefficients[other], biases[side]


def verify_endpoint(primitive, side, setting, kind, certificate):
    require(type(setting) is int and setting in (0, 1) and kind in ("minimum", "maximum"), "endpoint_role")
    require(type(certificate) is dict and set(certificate) == {"multipliers", "sqrt_lower", "primal_squared_scales"},
            "primitive_primal_dual_certificate_only")
    multipliers = certificate["multipliers"]
    require(type(multipliers) is dict and set(multipliers) == {"upper", "reciprocal"}, "dual_multiplier_roles")
    theta, lam = pair(multipliers["upper"]), pair(multipliers["reciprocal"])
    require(all(value >= 0 for value in theta + lam), "nonnegative_dual_multipliers")
    upper, reciprocal, _ = geometry(primitive, side)
    sign = 1 if kind == "minimum" else -1
    objective = upper[setting][:2]
    linear = tuple(sign * objective[k] + sum(theta[i] * upper[i][k] for i in (0, 1)) for k in (0, 1))
    inverse = tuple(sum(lam[j] * reciprocal[j][k] for j in (0, 1)) for k in (0, 1))
    constant = sum(theta[i] * upper[i][2] for i in (0, 1)) + sum(lam[j] * reciprocal[j][2] for j in (0, 1))
    roots = pair(certificate["sqrt_lower"])
    require(all(value >= 0 for value in linear + inverse + roots), "nonnegative_dual_root_data")
    require(all(roots[k] ** 2 <= linear[k] * inverse[k] for k in (0, 1)), "dual_root_lower_bound_failed")
    scales = pair(certificate["primal_squared_scales"])
    require(all(value > 0 for value in scales), "strict_positive_primal_scales")
    require(all(sum(upper[i][k] * scales[k] for k in (0, 1)) <= upper[i][2] for i in (0, 1)),
            "primal_upper_cone_failed")
    require(all(sum(reciprocal[j][k] / scales[k] for k in (0, 1)) <= reciprocal[j][2] for j in (0, 1)),
            "primal_reciprocal_cone_failed")
    attained = sum(objective[k] * scales[k] for k in (0, 1))
    bound = 2 * sum(roots) - constant
    gap = sign * attained - bound
    require(0 <= gap <= GAP, "uniform_dual_primal_gap_failed")
    brackets = [sqrt_bracket(linear[k] * inverse[k]) for k in (0, 1)]
    return {"gain_squared_bound": str(sign * bound), "attained_gain_squared": str(attained),
            "optimality_gap": str(gap), "all_continuous_members_covered": True,
            "coordinates": "alice_squared_scales" if side == "alice" else "bob_reciprocal_squared_scales",
            "primal_squared_scales": list(map(str, scales)),
            "dual_linear_coefficients": list(map(str, linear)),
            "dual_reciprocal_coefficients": list(map(str, inverse)), "dual_constant": str(constant),
            "sqrt_product_brackets": [list(map(str, bracket)) for bracket in brackets],
            "attained_gain_bracket": list(map(str, sqrt_bracket(attained)))}


def channel_ranges(primitive, side, setting, minimum, maximum):
    _, _, biases = geometry(primitive, side)
    mu = biases[setting]
    lower, upper = exact(minimum["gain_squared_bound"]), exact(maximum["gain_squared_bound"])
    require(0 < lower <= upper <= (1 - abs(mu)) ** 2, "positive_legal_gain_range")
    lo, hi = sqrt_bracket(lower)[0], sqrt_bracket(upper)[1]
    return {"canonical_gain": list(map(str, (lo, hi))),
            "canonical_e0": list(map(str, (max(Fraction(0), (1 - hi - mu) / 2), (1 - lo - mu) / 2))),
            "canonical_e1": list(map(str, (max(Fraction(0), (1 - hi + mu) / 2), (1 - lo + mu) / 2))),
            "scope": SCOPE,
            "coordinates": "alice_squared_scales" if side == "alice" else "bob_reciprocal_squared_scales",
            "actual_ideal_label_identity_selected": False, "whole_empirical_confidence_set_bounds": False}


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def verify_report(primary, witness):
    require(type(primary) is dict and primary.get("schema") == PRIMARY_SCHEMA and primary.get("version") == VERSION and
            primary.get("status") == "certified_complete_fiber_hardware_ranges", "primary_fiber_identity")
    require(primary.get("scope") == "complete_regular_fiber_of_each_frozen_generated_joint_law" and
            exact(primary["gain_squared_optimality_gap"]) == GAP, "primary_fiber_scope_or_gap")
    require(primary.get("uniform_fiber_coverage") is True and primary.get("geometric_optimizer_executed") is True,
            "primary_coverage_or_proposal_role")
    for flag in ("finite_grid_used_as_coverage", "new_confidence_budget_spent", "whole_empirical_confidence_set_bounds",
                 "actual_hardware_uniquely_identified", "new_statistical_fit_executed"):
        require(primary.get(flag) is False, "fiber_scope_promotion")
    require(type(primary.get("trial_event_files_read")) is int and primary["trial_event_files_read"] == 0, "fiber_event_access")
    for report in (primary, witness):
        require(type(report.get("runs")) is list and tuple(row.get("run") for row in report["runs"]) == RUNS,
                "ordered_complete_two_run_inventory")
    result = []
    endpoint_count = 0
    roles = tuple(itertools.product(("alice", "bob"), (0, 1)))
    for reported, original in zip(primary["runs"], witness["runs"]):
        require(canonical(reported["primitive"]) == canonical(original["primitive"]), "frozen_primitive_changed")
        primitive_coefficients(original["primitive"])
        supplied = reported["hardware_ranges"]
        require(type(supplied) is list and len(supplied) == 4 and
                tuple((row.get("side"), row.get("setting")) for row in supplied) == roles and
                all(type(row.get("setting")) is int for row in supplied), "ordered_complete_hardware_roles")
        ranges = []
        for row in supplied:
            checked = {}
            for kind in ("minimum", "maximum"):
                proposed = row[kind]
                require(type(proposed) is dict and set(proposed) == {"certificate", "checked", "proposal_solver_success", "proposal_iterations"},
                        "endpoint_proposal_shape")
                require(type(proposed["proposal_solver_success"]) is bool and type(proposed["proposal_iterations"]) is int and
                        proposed["proposal_iterations"] >= 0, "proposal_metadata_shape")
                checked[kind] = verify_endpoint(original["primitive"], row["side"], row["setting"], kind, proposed["certificate"])
                expected = {key: checked[kind][key] for key in
                            ("gain_squared_bound", "attained_gain_squared", "optimality_gap", "all_continuous_members_covered")}
                require(canonical(proposed["checked"]) == canonical(expected), "endpoint_numeric_claim_changed")
                endpoint_count += 1
            derived = channel_ranges(original["primitive"], row["side"], row["setting"], checked["minimum"], checked["maximum"])
            require(canonical(row["ranges"]) == canonical(derived), "canonical_channel_range_changed")
            ranges.append({"side": row["side"], "setting": row["setting"], "minimum": checked["minimum"],
                           "maximum": checked["maximum"], "ranges": derived})
        result.append({"run": original["run"], "primitive": original["primitive"], "hardware_ranges": ranges})
    require(endpoint_count == 16, "complete_endpoint_inventory")
    return {"schema": SCHEMA, "version": VERSION, "status": "certified_complete_fixed_law_fiber_ranges",
            "evidence_valid": True, "runs": result, "endpoints_checked": endpoint_count, "hardware_ranges_checked": 8,
            "gain_squared_optimality_gap": str(GAP), "integer_root_bits": ROOT_BITS, "uniform_fiber_coverage": True,
            "finite_grid_used_as_coverage": False, "whole_empirical_confidence_set_bounds": False,
            "actual_hardware_uniquely_identified": False, "source_optimizer_executed": False,
            "new_confidence_budget_spent": False, "trial_event_files_read": 0, "controller_advance": False}


def frozen_bindings(commit):
    import verify as parent
    module = parent.ROOT / "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutFiberBounds.lean"
    result = []
    for path in [*(parent.BASE / name for name in FILES + INPUTS), module]:
        raw = parent.frozen(path, commit)
        require(raw == parent.frozen(path), "fiber_science_not_at_execution_HEAD")
        result.append({"path": str(path.relative_to(parent.ROOT)), "sha256": parent.sha256(raw)})
    return result


def verify_primary_provenance(primary, attempt_raw, bindings, freeze_commit):
    import hashlib
    attempt = json.loads(attempt_raw)
    require(primary["freeze_commit"] == attempt["freeze_commit"] == freeze_commit and
            attempt["version"] == VERSION, "fiber_primary_scientific_freeze_changed")
    require(canonical(primary["source_bindings"]) == canonical(attempt["source_bindings"]) == canonical(bindings),
            "fiber_primary_scientific_bindings_changed")
    require(primary["attempt_sha256"] == hashlib.sha256(attempt_raw).hexdigest(), "fiber_primary_first_attempt_changed")
    require(type(attempt["event_files_read_at_reservation"]) is int and attempt["event_files_read_at_reservation"] == 0,
            "fiber_primary_event_scope_changed")
    require(primary["execution_head"] == attempt["execution_head"], "fiber_primary_execution_head_changed")


def main():
    import argparse
    from pathlib import Path
    import subprocess
    import verify as parent
    import identify_verify as identification
    import identification_certify
    import fiber_certify
    def exclusive_json(path, value):
        with path.open("x", encoding="utf-8") as output:
            output.write(canonical(value) + "\n")

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-commit", required=True)
    parser.add_argument("--primary-receipt", type=Path, default=parent.BASE / "fiber-first.json")
    args = parser.parse_args()
    attempt = parent.BASE / "fiber-independent-attempt.json"
    first = parent.BASE / "fiber-independent-first.json"
    try:
        require(not attempt.exists() and not first.exists(), "fiber_independent_first_already_reserved")
        def git(*arguments):
            result = subprocess.run(["git", *arguments], cwd=parent.ROOT, text=True, capture_output=True)
            require(result.returncode == 0, "fiber_freeze_not_execution_ancestor")
            return result.stdout.strip()
        commit = git("rev-parse", "--verify", args.freeze_commit + "^{commit}")
        head = git("rev-parse", "--verify", "HEAD^{commit}")
        git("merge-base", "--is-ancestor", commit, head)
        bindings = frozen_bindings(commit)
        # Geometry is admitted through the same fixed-source inverse before any endpoint intake.
        require(identification_certify.consume()["evidence_valid"] is True, "fixed_source_inverse_not_certified")
        require(fiber_certify.consume()["evidence_valid"] is True, "continuous_dual_bound_kernel_not_certified")
        require(identification.consume()["evidence_valid"] is True, "parent_identification_evidence_not_certified")
        primary_raw = parent.frozen(parent.BASE / "fiber-first.json")
        require(args.primary_receipt.read_bytes() == primary_raw, "fiber_primary_override_changed")
        primary_attempt_raw = parent.frozen(parent.BASE / "fiber-attempt.json")
        witness_raw = parent.frozen(parent.BASE / "primitive-witness-c0002.json")
        counts_raw = parent.frozen(parent.BASE / "primary-first-c0002.json")
        exclusive_json(attempt, {"schema": "stage10-munich-readout-fiber-independent-attempt/v1", "version": VERSION,
                                "freeze_commit": commit, "execution_head": head, "source_bindings": bindings,
                                "primary_receipt_sha256": parent.sha256(primary_raw), "trial_event_files_read": 0})
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(canonical({"schema": SCHEMA, "status": "not_started", "reason": str(error)}))
        return 2
    try:
        primary = parent.strict_json(primary_raw)
        verify_primary_provenance(primary, primary_attempt_raw, bindings, commit)
        require(primary["parent_identification_sha256"] == parent.sha256(parent.frozen(parent.BASE / "identification-verification.json")),
                "fiber_parent_identification_changed")
        require(primary["kernel_sha256"] == parent.sha256(parent.frozen(parent.BASE / "fiber-certification-first.json")),
                "fiber_kernel_receipt_changed")
        report = verify_report(primary, parent.strict_json(witness_raw))
        counts = parent.strict_json(counts_raw)
        require(tuple(row["run"] for row in counts["runs"]) == RUNS, "parent_prefix_run_inventory")
        for given, counted in zip(primary["runs"], counts["runs"]):
            require(type(given["parent_prefixes_inherited"]) is int and given["parent_prefixes_inherited"] == counted["trials"] and
                    given["parent_factor_sequence_sha256"] == counted["prefix_check"]["factor_sequence_sha256"],
                    "same_law_parent_prefix_identity_changed")
    except Exception as error:
        report = {"schema": SCHEMA, "version": VERSION, "status": "execution_failed", "evidence_valid": False,
                  "reason": str(error), "error_type": type(error).__name__}
    report.update({"freeze_commit": commit, "execution_head": head, "source_bindings": bindings,
                   "primary_receipt_sha256": parent.sha256(primary_raw),
                   "parent_identification_sha256": parent.sha256(parent.frozen(parent.BASE / "identification-verification.json")),
                   "kernel_sha256": parent.sha256(parent.frozen(parent.BASE / "fiber-certification-first.json")),
                   "attempt_sha256": parent.sha256(attempt.read_bytes())})
    exclusive_json(first, report)
    print(canonical({"schema": SCHEMA, "status": report["status"], "evidence_valid": report["evidence_valid"]}))
    return 0 if report["evidence_valid"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
