"""Integer checks for the source-coupled four-gain qualification domain.

Only the signed old full-component arithmetic is reused.  All eight product
caps and constrained parity maxima are constructed here, without importing
the new producer, finding endpoints, reading events or fitting a source.
"""
import argparse
from fractions import Fraction
import math
from pathlib import Path

import response_projection_independent as projection


source = projection.source
require, rational = source.require, source.rational
BASE, ROOT = projection.BASE, projection.ROOT
CONTEXTS, ROLES = projection.CONTEXTS, projection.ROLES
RAYS = ("uniform", "alice", "bob")
BRACKET = Fraction(1, 1 << 36)
VERSION = "stage10-munich-readout-cp0003"
PRIMARY_SCHEMA = "stage10-munich-joint-response-primary/v1"
SCHEMA = "stage10-munich-joint-response-independent/v1"
FILES = ("criterion-cp0003.md", "joint_response.py", "test_joint_response.py", "joint_response_run.py",
         "joint_response_independent.py", "test_joint_response_independent.py",
         "joint-response-audit.md", "joint-response-audit.json")
INPUTS = ("primary-first-c0002.json", "identification-first.json", "primitive-witness-c0002.json",
          "shared-response-first.json", "shared-response-verification.json", "response-bounds-certification-first.json",
          "response_projection.py", "response_projection_independent.py", "shared_response.py", "likelihood.py")
MODULE = ROOT / "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutResponseBounds.lean"


def caps(values):
    require(type(values) in (list, tuple) and len(values) == 4, "four_ordered_source_gain_caps")
    result = tuple(map(rational, values))
    require(all(0 <= value <= 1 for value in result), "legal_source_gain_caps")
    return result


def ray_caps(ray, parameter):
    parameter = rational(parameter)
    require(ray in RAYS and 0 <= parameter <= 1, "predeclared_source_gain_ray")
    if ray == "uniform":
        return (parameter,) * 4
    return (parameter, parameter, Fraction(1), Fraction(1)) if ray == "alice" else (Fraction(1), Fraction(1), parameter, parameter)


def bias_table(rows):
    require(type(rows) is list and len(rows) == 4, "whole_original_bias_projection_inventory")
    result = {}
    for row in rows:
        require(type(row) is dict and row["side"] in ("alice", "bob") and
                type(row["setting"]) is int and row["setting"] in (0, 1), "original_bias_role")
        key = row["side"], row["setting"]
        require(key not in result, "duplicate_original_bias_role")
        result[key] = projection.exact_interval(row["mu_outer_interval"], (Fraction(-1), Fraction(1)))
    require(set(result) == set(ROLES), "all_original_bias_roles")
    return result


class JointProfile:
    def __init__(self, rows, biases, bits=240):
        table = projection.counts_table(rows)
        self.full = projection.cached_profile(tuple((key, table[key]) for key in CONTEXTS), bits)
        self.arithmetic, self.biases = self.full.arithmetic, bias_table(biases)
        self.inputs = {}
        for key in CONTEXTS:
            grouped = self.full.parity_counts(key)
            require(all(n > 0 for n in grouped), "both_observed_parities_in_all_eight_contexts")
            corners = [a * b for a in self.biases["alice", key[1]] for b in self.biases["bob", key[2]]]
            self.inputs[key] = grouped, min(corners), max(corners), self.full.mle(key), self.full.mle_likelihood(grouped)

    def at(self, proposed):
        proposed = caps(proposed)
        value, records, likelihoods, infinite = self.full.mle_log, [], [], False
        for key in CONTEXTS:
            grouped, product_low, product_high, mle, mle_likelihood = self.inputs[key]
            radius = proposed[key[1]] * proposed[2 + key[2]]
            allowed_low = max(Fraction(0), (1 + product_low - radius) / 2)
            allowed_high = min(Fraction(1), (1 + product_high + radius) / 2)
            require(allowed_low <= allowed_high, "nonempty_joint_parity_domain")
            maximizing = allowed_low if mle < allowed_low else allowed_high if mle > allowed_high else mle
            derivative = grouped[0] - sum(grouped) * maximizing
            require((maximizing == mle and derivative == 0) or
                    (maximizing == allowed_low and derivative <= 0) or
                    (maximizing == allowed_high and derivative >= 0), "joint_clipped_MLE_not_a_likelihood_maximum")
            unsupported = (maximizing == 0 and grouped[0] > 0) or (maximizing == 1 and grouped[1] > 0)
            likelihood = None if unsupported else (self.arithmetic.log(maximizing).times(grouped[0]) +
                                                  self.arithmetic.log(1 - maximizing).times(grouped[1]))
            records.append({"context": list(key), "parity_counts": list(grouped), "gain_product_cap": str(radius),
                            "bias_product_outer_interval": list(map(str, (product_low, product_high))),
                            "allowed_even_probability": list(map(str, (allowed_low, allowed_high))),
                            "parity_mle": str(mle), "maximizing_even_probability": str(maximizing)})
            likelihoods.append({"context": list(key), "parity_MLE_log_likelihood": self.arithmetic.record(mle_likelihood),
                                "clipped_parity_log_likelihood": {"negative_infinite": True} if likelihood is None else
                                self.arithmetic.record(likelihood)})
            if unsupported:
                infinite = True
            elif maximizing != mle:
                value += mle_likelihood - likelihood
        return {"interval": None if infinite else value, "log_e": {"infinite": True} if infinite else self.arithmetic.record(value),
                "contexts": records, "context_likelihoods": likelihoods}


def cross_endpoint(profile, proposed, checked, excluded):
    require(type(proposed) is dict and set(proposed) == {"log_e", "contexts"}, "joint_profile_endpoint_record")
    require(source.canonical(proposed["contexts"]) == source.canonical(checked["contexts"]), "joint_product_caps_or_MLE_trace_changed")
    value = checked["interval"]
    if value is None:
        require(excluded and proposed["log_e"] == {"infinite": True} and proposed["log_e"].get("infinite") is True,
                "joint_zero_support_classification_changed")
        return
    threshold = profile.full.threshold
    require(value.lo >= threshold.hi if excluded else value.hi < threshold.lo, "joint_threshold_side_not_certified")
    exact_threshold = tuple(Fraction(v, profile.arithmetic.scale) for v in (threshold.lo, threshold.hi))
    projection.cross_logs(proposed["log_e"], checked["log_e"], exact_threshold, excluded)


def verify_ray(profile, entry, ray):
    require(type(entry) is dict and entry["ray"] == ray and ray in RAYS and entry["component_threshold"] == "80",
            "predeclared_joint_ray_identity")
    require(entry["entire_lower_orthant_excluded"] is True and entry["all_eight_contexts_used"] is True and
            entry["actual_gain_extremum_sharpness_claimed"] is False, "joint_ray_scope_changed")
    low, high = projection.exact_interval(entry["profile_threshold_bracket"], (Fraction(0), Fraction(1)))
    require(low < high and high - low <= BRACKET and entry["threshold_bracket_gap"] == str(high - low), "joint_ray_bracket_changed")
    lower_caps, upper_caps = ray_caps(ray, low), ray_caps(ray, high)
    require(caps(entry["lower_caps"]) == lower_caps and caps(entry["upper_caps"]) == upper_caps, "joint_ray_caps_changed")
    left, right = profile.at(lower_caps), profile.at(upper_caps)
    cross_endpoint(profile, entry["profile_lower_endpoint"], left, True)
    cross_endpoint(profile, entry["profile_upper_endpoint"], right, False)
    return {"ray": ray, "profile_threshold_bracket": [str(low), str(high)], "threshold_bracket_gap": str(high - low),
            "lower_caps": list(map(str, lower_caps)), "upper_caps": list(map(str, upper_caps)),
            "profile_lower_endpoint": {key: left[key] for key in ("log_e", "contexts")},
            "profile_upper_endpoint": {key: right[key] for key in ("log_e", "contexts")},
            "lower_context_likelihoods": left["context_likelihoods"], "upper_context_likelihoods": right["context_likelihoods"],
            "component_threshold": "80", "entire_lower_orthant_excluded": True, "all_eight_contexts_used": True,
            "actual_gain_extremum_sharpness_claimed": False, "coordinatewise_cap_domains_nested": True,
            "all_eight_likelihood_maxima_checked": True, "boundary_search_executed": False,
            "precision_bits": profile.arithmetic.bits}


def witness_caps(primitive):
    point, scale, result, squares = source.primitive(primitive), 1 << 48, [], []
    for side, setting in ROLES:
        effect = point[side][setting]
        square = effect.u ** 2 + effect.z ** 2
        # Determine a proposal in integers, then certify it by the adjacent exact grid squares.
        upper_integer = math.isqrt((square.numerator * scale ** 2) // square.denominator)
        upper_integer += int(Fraction(upper_integer ** 2, scale ** 2) < square)
        upper = Fraction(upper_integer, scale)
        require(0 <= upper <= 1 and square <= upper ** 2 and
                (upper == 0 and square == 0 or upper > 0 and (upper - Fraction(1, scale)) ** 2 < square),
                "lawful_primitive_sqrt_cap_not_minimal_outward_48bit")
        result.append(upper); squares.append(str(square))
    return tuple(result), squares


def individual_caps(envelopes):
    require(type(envelopes) is list and len(envelopes) == 4, "four_original_cp0002_response_projections")
    intervals = []
    for entry, (side, setting) in zip(envelopes, ROLES):
        require(type(entry) is dict and entry["side"] == side and type(entry["setting"]) is int and
                entry["setting"] == setting, "original_cp0002_response_role")
        intervals.append(projection.exact_interval(entry["canonical_gain"], (Fraction(0), Fraction(1))))
    lower = max(pair[0] for pair in intervals)
    integer = -((-lower.numerator * 1000000) // lower.denominator)
    upper = Fraction(integer, 1000000)
    require(all(low <= upper <= high for low, high in intervals), "lookalike_caps_outside_original_individual_gain_box")
    return (upper,) * 4


def verify_control(profile, entry, name, expected_caps):
    require(type(entry) is dict and entry["name"] == name and caps(entry["caps"]) == expected_caps, "joint_control_identity_or_caps_changed")
    checked = profile.at(expected_caps)
    value, threshold = checked["interval"], profile.full.threshold
    if value is None or value.lo >= threshold.hi:
        excluded, status = True, "entire_lower_orthant_excluded"
    elif value.hi < threshold.lo:
        excluded, status = False, "necessary_profile_not_excluded"
    else:
        raise ValueError("joint_control_threshold_unresolved")
    require(entry["status"] == status, "joint_control_classification_changed")
    cross_endpoint(profile, {key: entry[key] for key in ("log_e", "contexts")}, checked, excluded)
    require(name != "original_lawful_witness" or not excluded, "original_parent_source_witness_profile_conflict")
    return {"name": name, "caps": list(map(str, expected_caps)), "status": status,
            **{key: checked[key] for key in ("log_e", "contexts", "context_likelihoods")}}


def verify_report(primary, counts, biases, shared, primitive):
    require(type(primary) is dict and primary.get("schema") == PRIMARY_SCHEMA and primary.get("version") == VERSION and
            primary.get("status") == "generated_joint_response_parent_confidence_qualification", "joint_primary_identity")
    require(primary.get("joint_response_profile_certified") is True and primary.get("whole_empirical_confidence_set_bounds") is True and
            primary.get("parent_confidence_budget") == "1/20" and primary.get("full_component_threshold") == "80" and
            primary.get("profile_threshold_bracket_precision") == str(BRACKET), "joint_parent_confidence_contract_changed")
    for field in ("new_confidence_budget_spent", "fixed_law_point_used_as_confidence_bound", "hardware_parameter_uniqueness_certified",
                  "actual_ideal_label_identity_selected", "actual_gain_extremum_sharpness_claimed", "profile_pass_used_as_full_source_membership",
                  "source_theorem_changed", "optimizer_executed", "new_statistical_fit_executed"):
        require(primary.get(field) is False, "joint_profile_scope_promoted")
    require(type(primary.get("trial_event_files_read")) is int and primary["trial_event_files_read"] == 0, "joint_event_access_changed")
    identities = ((counts, "stage10-munich-readout-primary-point/v1", "stage10-munich-readout-rd0001"),
                  (biases, "stage10-munich-readout-identification-primary/v1", "stage10-munich-readout-id0001"),
                  (shared, "stage10-munich-shared-response-primary/v1", "stage10-munich-readout-cp0002"),
                  (primitive, "stage10-munich-readout-primitive-witness/v1", "stage10-munich-readout-rd0001"))
    for report, schema, version in identities:
        require(type(report) is dict and report.get("schema") == schema and report.get("version") == version, "original_parent_receipt_identity")
    for report in (primary, counts, biases, shared, primitive):
        require(type(report.get("runs")) is list and all(type(row) is dict for row in report["runs"]) and
                tuple(row.get("run") for row in report["runs"]) == source.RUNS, "whole_ordered_joint_run_family")
    results, lookalikes = [], 0
    for supplied, counted, biased, old, saved in zip(primary["runs"], counts["runs"], biases["runs"], shared["runs"], primitive["runs"]):
        rows = counted["four_outcomes"]
        total = sum(map(sum, projection.counts_table(rows).values()))
        require(type(counted["trials"]) is int and counted["trials"] == total and type(supplied["parent_trials"]) is int and
                supplied["parent_trials"] == total, "joint_original_trial_denominator_changed")
        factor = counted["prefix_check"]["factor_sequence_sha256"]
        require(type(factor) is str and len(factor) == 64 and all(c in "0123456789abcdef" for c in factor) and
                supplied["parent_factor_sequence_sha256"] == factor, "joint_original_factor_identity_changed")
        require(type(supplied["joint_response_rays"]) is list and len(supplied["joint_response_rays"]) == 3 and
                type(supplied["controls"]) is list and len(supplied["controls"]) == 2, "all_predeclared_joint_rays_and_controls")
        upper, squares = witness_caps(saved["primitive"])
        lookalike_caps = individual_caps(old["shared_response_envelopes"])
        failure = None
        for bits in (240, 320, 384):
            try:
                profile = JointProfile(rows, biased["bias_envelopes"], bits)
                rays = [verify_ray(profile, entry, ray) for entry, ray in zip(supplied["joint_response_rays"], RAYS)]
                controls = [verify_control(profile, supplied["controls"][0], "original_lawful_witness", upper),
                            verify_control(profile, supplied["controls"][1], "individual_projection_lookalike", lookalike_caps)]
                break
            except ValueError as error:
                failure = error
        else:
            raise failure
        lookalikes += int(controls[1]["status"] == "entire_lower_orthant_excluded")
        results.append({"run": counted["run"], "joint_response_rays": rays, "controls": controls,
                        "primitive_gain_squared": squares, "primitive_exactly_lawful": True, "witness_caps_rounding_bits": 48,
                        "parent_trials": total, "parent_factor_sequence_sha256": factor})
    return {"schema": SCHEMA, "version": VERSION, "status": "certified_joint_response_parent_confidence_qualification", "evidence_valid": True,
            "runs": results, "profile_brackets_checked": 6, "endpoints_checked": 12, "context_likelihood_checks": 96,
            "controls_checked": 4, "control_context_likelihood_checks": 32, "individual_projection_lookalikes_excluded": lookalikes,
            "lawful_witness_controls_not_excluded": 2, "joint_response_profile_certified": True,
            "whole_empirical_confidence_set_bounds": True, "parent_confidence_budget": "1/20", "full_component_threshold": "80",
            "profile_threshold_bracket_precision": str(BRACKET), "new_confidence_budget_spent": False,
            "fixed_law_point_used_as_confidence_bound": False, "hardware_parameter_uniqueness_certified": False,
            "actual_ideal_label_identity_selected": False, "actual_gain_extremum_sharpness_claimed": False,
            "profile_pass_used_as_full_source_membership": False, "parent_source_witness_membership_inherited": True,
            "source_theorem_changed": False, "controller_advance": False, "trial_event_files_read": 0,
            "optimizer_executed": False, "new_statistical_fit_executed": False, "boundary_search_executed": False,
            "primary_endpoint_numerics_used": False}


def frozen_bindings(commit):
    bindings = []
    for path in [*(BASE / name for name in (*FILES, *INPUTS)), MODULE]:
        raw = source.frozen_bytes(path, commit)
        require(raw == source.frozen_bytes(path), "joint_science_not_at_execution_HEAD")
        bindings.append({"path": str(path.relative_to(ROOT)), "sha256": source.digest(raw)})
    return bindings


def source_review():
    audit = source.strict_json(source.frozen_bytes(BASE / "joint-response-audit.json"))
    require(audit.get("schema") == "stage10-munich-readout-joint-response-audit/v1" and audit.get("version") == VERSION and
            audit.get("evidence_valid") is True and audit.get("status") == "accepted_joint_response_source_and_statistical_logic" and
            audit.get("substantive_defects") == [], "joint_source_review_rejected")
    contract = audit["confidence_contract"]
    require(contract["parent_confidence_budget"] == "1/20" and contract["new_confidence_budget_spent"] is False,
            "joint_audited_confidence_contract_changed")
    entries, seen = audit["source_bindings"], set()
    require(type(entries) is list and bool(entries), "joint_audit_source_inventory_empty")
    for entry in entries:
        require(type(entry) is dict and set(entry) == {"path", "sha256"} and type(entry["path"]) is str, "joint_audit_source_entry")
        relative = Path(entry["path"])
        require(not relative.is_absolute() and not {".", ".."}.intersection(relative.parts) and entry["path"] not in seen,
                "joint_audit_source_identity")
        seen.add(entry["path"])
        require(source.digest(source.frozen_bytes(ROOT / relative)) == entry["sha256"], "joint_audited_source_changed")
    return audit


def primary_provenance(primary, bindings, provenance):
    require(source.canonical(primary["source_bindings"]) == source.canonical(bindings) and
            primary["freeze_commit"] == provenance["freeze_commit"], "joint_primary_science_bindings_or_freeze_changed")
    inventory = {entry["path"]: entry["sha256"] for entry in bindings}
    for field, name in (("source_kernel_sha256", "response-bounds-certification-first.json"),
                        ("previous_shared_certificate_sha256", "shared-response-verification.json")):
        require(primary[field] == inventory[str((BASE / name).relative_to(ROOT))], "joint_source_or_previous_certificate_changed")
    raw = source.frozen_bytes(BASE / "joint-response-attempt.json")
    require(primary["attempt_sha256"] == source.digest(raw), "joint_primary_first_attempt_changed")
    attempt = source.strict_json(raw)
    require(attempt["version"] == VERSION and attempt["freeze_commit"] == primary["freeze_commit"] and
            attempt["execution_head"] == primary["execution_head"] and source.canonical(attempt["source_bindings"]) == source.canonical(bindings) and
            type(attempt["event_files_read_at_reservation"]) is int and attempt["event_files_read_at_reservation"] == 0,
            "joint_primary_attempt_provenance_changed")
    for older, newer in ((primary["freeze_commit"], primary["execution_head"]), (primary["execution_head"], provenance["execution_head"])):
        result = source.subprocess.run(["git", "merge-base", "--is-ancestor", older, newer], cwd=ROOT, capture_output=True, check=False)
        require(result.returncode == 0, "joint_source_not_frozen_before_science")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-commit", required=True)
    parser.add_argument("--primary-receipt", type=Path, default=BASE / "joint-response-first.json")
    args = parser.parse_args()
    attempt, first = BASE / "joint-response-independent-attempt.json", BASE / "joint-response-independent-first.json"
    try:
        require(not attempt.exists() and not first.exists(), "joint_independent_first_already_reserved")
        provenance = source.execution_provenance(args.freeze_commit)
        bindings = frozen_bindings(provenance["freeze_commit"])
        primary_raw = source.frozen_bytes(BASE / "joint-response-first.json")
        require(args.primary_receipt.read_bytes() == primary_raw, "joint_override_changes_primary_receipt")
        raws = [source.frozen_bytes(BASE / name) for name in ("primary-first-c0002.json", "identification-first.json",
                "shared-response-first.json", "primitive-witness-c0002.json")]
        source.exclusive_json(attempt, {"schema": "stage10-munich-joint-response-independent-attempt/v1", "version": VERSION,
                                       **provenance, "source_bindings": bindings, "primary_receipt_sha256": source.digest(primary_raw),
                                       "event_files_read_at_reservation": 0})
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(source.canonical({"schema": SCHEMA, "status": "not_started", "reason": str(error)})); return 2
    try:
        import shared_response_verify as previous
        admitted = previous.consume()
        require(admitted["evidence_valid"] is True and admitted["parent_joint_adjudication_preserved"] is True,
                "original_source_witness_or_joint_certificate_changed")
        source_review()
        primary = source.strict_json(primary_raw)
        primary_provenance(primary, bindings, provenance)
        report = verify_report(primary, *(source.strict_json(raw) for raw in raws))
    except Exception as error:
        report = {"schema": SCHEMA, "version": VERSION, "status": "execution_failed", "evidence_valid": False,
                  "reason": str(error), "error_type": type(error).__name__}
    inventory = {entry["path"]: entry["sha256"] for entry in bindings}
    report.update({**provenance, "source_bindings": bindings, "primary_receipt_sha256": source.digest(primary_raw),
                   "source_kernel_sha256": inventory[str((BASE / "response-bounds-certification-first.json").relative_to(ROOT))],
                   "previous_shared_certificate_sha256": inventory[str((BASE / "shared-response-verification.json").relative_to(ROOT))],
                   "attempt_sha256": source.digest(attempt.read_bytes())})
    source.exclusive_json(first, report)
    print(source.canonical({"schema": SCHEMA, "status": report["status"], "evidence_valid": report["evidence_valid"]}))
    return 0 if report["evidence_valid"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
