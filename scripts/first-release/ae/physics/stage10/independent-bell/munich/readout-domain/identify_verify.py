"""Consume frozen maximal-quotient, regular-fiber and confidence-projection certificates."""
from fractions import Fraction
from pathlib import Path
import argparse
import itertools
import subprocess

import identification as fiber
import verify as parent
from model import decode
from likelihood import Directed
from run import exclusive_json


BASE, ROOT = parent.BASE, parent.ROOT
SCHEMA = "stage10-munich-readout-identification-evidence/v1"
VERSION = "stage10-munich-readout-id0001"
FIRSTS = ("identification-first.json", "identification-independent-first.json")


def validate(primary, independent, witness, counts):
    parent.require(primary.get("schema") == "stage10-munich-readout-identification-primary/v1" and
                   independent.get("schema") == "stage10-munich-readout-identification-independent/v1", "identification_schema")
    parent.require(primary.get("version") == independent.get("version") == VERSION and independent.get("evidence_valid") is True,
                   "identification_not_certified")
    parent.require(primary.get("status") == "generated_parameter_fibers_and_parent_confidence_projections" and
                   independent.get("status") == "certified_source_fiber_and_parent_CS_projections", "identification_status")
    for report in (primary, independent):
        parent.require(report.get("parent_confidence_budget") == "1/20" and report.get("new_confidence_budget_spent") is False,
                       "parent_confidence_budget_changed")
        parent.require(report.get("actual_hardware_uniquely_identified") is False and report.get("optimizer_run") is False and
                       type(report.get("trial_event_files_read")) is int and report["trial_event_files_read"] == 0,
                       "identification_scope_promoted")
    for report in (primary, independent, witness, counts):
        parent.require(tuple(row["run"] for row in report["runs"]) == parent.RUNS, "complete_identification_family")
    parent.require(independent["source_probabilities_checked"] == 64 and independent["alternative_probabilities_checked"] == 128 and
                   independent["bias_envelopes_checked"] == 8 and independent["primary_endpoint_numerics_used"] is False,
                   "independent_identification_incomplete")
    threshold = Directed(80).logarithm(Fraction(240))
    output = []
    for p, i, w, c in zip(primary["runs"], independent["runs"], witness["runs"], counts["runs"]):
        point = decode(w["primitive"])
        parent.require(p["primitive"] == w["primitive"] and p["observable_quotient"] == i["observable_quotient"] == fiber.quotient(point),
                       "maximal_quotient_changed")
        parent.require(p["regular_fiber"] == fiber.fixed_law_fiber(point), "complete_regular_fiber_changed")
        parent.require(p["continuous_legal_rectangle"] == i["continuous_legal_rectangle"] == fiber.positive_rectangle(point),
                       "continuous_scale_coverage_changed")
        own = fiber.own_counts(c["four_outcomes"])
        parent.require(p["own_setting_counts"] == i["own_setting_counts"] == own, "original_counts_changed")
        parent.require(p["parent_factor_sequence_sha256"] == i["parent_factor_sequence_sha256"] == c["prefix_check"]["factor_sequence_sha256"],
                       "parent_prefix_identity_changed")
        parent.require(len(p["equivalent_hardware"]) == len(i["equivalent_hardware"]) == 2, "alternative_family_changed")
        for source, checked in zip(p["equivalent_hardware"], i["equivalent_hardware"]):
            parent.require(source["kind"] == checked["kind"] and source["gain_changes"] == checked["gain_changes"], "gain_nonuniqueness_changed")
            generated = fiber.scale(point, Fraction(source["s"]), Fraction(source["t"]))
            parent.require(decode(source["primitive"]) == generated and fiber.recover_scales(point, generated) ==
                           (Fraction(source["s"]), Fraction(source["t"])), "alternative_not_from_complete_fiber")
            parent.require(checked["all_8D_generated_probabilities_unchanged"] is True and
                           checked["same_statistical_factors_for_all_original_prefixes"] is True,
                           "source_or_prefix_gauge_inheritance_lost")
            parent.require(checked["changed_canonical_channel_settings"] and source["all_original_prefixes_inherited"] == c["trials"],
                           "hardware_changes_not_registered")
        parent.require(len(p["bias_envelopes"]) == len(i["bias_envelopes"]) == 4, "bias_projection_family_changed")
        envelopes = []
        for supplied, checked, role in zip(p["bias_envelopes"], i["bias_envelopes"], itertools.product(("alice", "bob"), (0, 1))):
            side, setting = role
            parent.require(supplied["side"] == checked["side"] == side and supplied["setting"] == checked["setting"] == setting and
                           supplied["counts"] == checked["counts"] == own[side], "projection_role_or_counts_changed")
            parent.require(supplied["p_outer_interval"] == checked["p_outer_interval"] and
                           supplied["mu_outer_interval"] == checked["mu_outer_interval"], "projection_endpoints_disagree")
            lo, hi = map(Fraction, supplied["p_outer_interval"])
            mle = Fraction(own[side][setting][0], sum(own[side][setting]))
            parent.require(0 < lo < mle < hi < 1 and supplied["p_mle"] == checked["p_mle"] == str(mle), "projection_mle_changed")
            parent.require(supplied["mu_outer_interval"] == list(map(str, (2 * lo - 1, 2 * hi - 1))), "bias_coordinates_changed")
            parent.require(checked["entire_outside_intervals_excluded"] is True and
                           checked["profile_convexity_from_exact_derivative"] is True and checked["new_confidence_budget_spent"] is False,
                           "entire_projection_not_certified")
            for original_name, checked_name in (("lower_endpoint_log_e", "left_log_profile"),
                                                 ("upper_endpoint_log_e", "right_log_profile")):
                parent.overlap(supplied[original_name], checked[checked_name])
                parent.require(parent.interval(supplied[original_name])[0] >= Fraction(threshold.upper) and
                               parent.interval(checked[checked_name])[0] >= Fraction(threshold.upper), "outside_threshold_not_certified")
            parent.overlap(supplied["mle_log_e"], checked["mle_log_profile"])
            parent.require(parent.interval(checked["mle_log_profile"])[1] < Fraction(threshold.lower), "profile_empty")
            envelopes.append({"side": side, "setting": setting, "mu_outer_interval": supplied["mu_outer_interval"],
                              "kind": "whole_parent_confidence_set_necessary_outer_projection"})
        output.append({"run": p["run"], "observable_quotient": p["observable_quotient"],
                       "complete_regular_fiber": p["regular_fiber"], "bias_envelopes": envelopes,
                       "scale_rectangle": p["continuous_legal_rectangle"],
                       "original_prefixes_inherited": c["trials"]})
    return output


def generate():
    import identification_certify
    kernel = identification_certify.consume()
    parent_result = parent.consume()
    p, i = [parent.strict_json(parent.frozen(BASE / name)) for name in FIRSTS]
    for role, report, attempt_name in (("primary", p, "identification-attempt.json"),
                                       ("independent", i, "identification-independent-attempt.json")):
        attempt_raw = parent.frozen(BASE / attempt_name)
        attempt = parent.strict_json(attempt_raw)
        parent.require(report["attempt_sha256"] == parent.sha256(attempt_raw), "identification_attempt_changed")
        parent.require(report["source_bindings"] == attempt["source_bindings"], "identification_binding_changed")
        provenance = report if role == "primary" else report["provenance"]
        commit = provenance["freeze_commit"]
        ancestor = subprocess.run(["git", "merge-base", "--is-ancestor", commit, provenance["execution_head"]],
                                  cwd=ROOT, capture_output=True, check=False)
        parent.require(ancestor.returncode == 0, "identification_not_frozen_before_execution")
        for entry in report["source_bindings"]:
            path = ROOT / entry["path"]
            parent.require(parent.sha256(parent.frozen(path, commit)) == entry["sha256"] == parent.sha256(parent.frozen(path)),
                           "identification_source_changed")
    parent.require(i["primary_receipt_sha256"] == parent.sha256(parent.frozen(BASE / FIRSTS[0])), "independent_primary_identity_changed")
    witness = parent.strict_json(parent.frozen(BASE / "primitive-witness-c0002.json"))
    counts = parent.strict_json(parent.frozen(BASE / "primary-first-c0002.json"))
    results = validate(p, i, witness, counts)
    return {"schema": SCHEMA, "criterion_version": VERSION, "evidence_valid": True,
            "status": "certified_maximal_observables_regular_fibers_and_bias_projections",
            "parameter_identification_completed": True, "maximal_observable_quotient_certified": True,
            "registered_regular_law_fibers_complete": True, "continuous_equivalent_hardware_certified": True,
            "parent_confidence_bias_envelopes_certified": True, "hardware_parameter_uniqueness_certified": False,
            "isotropic_nonuniqueness_preserves_axes": True, "parent_joint_adjudication_preserved": parent_result["evidence_valid"],
            "parent_confidence_budget": "1/20", "new_confidence_budget_spent": False,
            "trial_event_files_read_at_intake": 0, "new_science_executed_at_intake": 0,
            "controller_advance": False, "actual_hardware_identity_claimed": False, "runs": results,
            "source_bindings": [parent.binding(BASE / name) for name in ("criterion-id0001.md", "identify_verify.py",
                                      "identification-certification-first.json", *FIRSTS)],
            "explicit_declarations": len(kernel["explicit_declarations"])}


def consume(certificate=None):
    result = generate()
    supplied = parent.strict_json((BASE / "identification-verification.json" if certificate is None else Path(certificate)).read_bytes())
    parent.require(parent.canonical(result) == parent.canonical(supplied), "identification_certificate_changed")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    args = parser.parse_args()
    try:
        result = consume(args.certificate) if args.check_only else generate()
        if not args.check_only:
            parent.require(args.certificate is None, "identification_override_is_consume_only")
            exclusive_json(BASE / "identification-verification.json", result)
        print(parent.canonical(result))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(parent.canonical({"schema": SCHEMA, "evidence_valid": False, "reason": str(error)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
