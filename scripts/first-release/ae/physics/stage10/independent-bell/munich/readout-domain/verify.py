"""Consume frozen same-source primitive witnesses and two complete prefix checks."""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import itertools
import json
import math
from pathlib import Path
import subprocess

import kernel_certify
from likelihood import Directed, ORDER
from model import decode, encode, source_joint


BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[5]
PARENT = BASE.parent
VERSION = "stage10-munich-readout-rd0001"
SCHEMA = "stage10-munich-readout-domain-evidence/v1"
RUNS = ("2016-04-15", "2016-06-14")
CONTEXTS = tuple(itertools.product((0, 1), repeat=3))
RECEIPTS = ("primary-first-c0002.json", "independent-first-c0002.json", "primitive-witness-c0002.json",
            "primary-attempt-c0002.json", "independent-attempt-c0002.json")


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def strict_json(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "duplicate_json_key")
            result[key] = value
        return result
    def invalid(_):
        raise ValueError("nonfinite_json_constant")
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=invalid)


def sha256(raw):
    return hashlib.sha256(raw).hexdigest()


def frozen(path, commit="HEAD"):
    require(path.is_relative_to(ROOT), "binding_outside_repository")
    saved = subprocess.run(["git", "show", commit + ":" + path.relative_to(ROOT).as_posix()],
                           cwd=ROOT, capture_output=True, check=False)
    raw = path.read_bytes()
    require(saved.returncode == 0 and saved.stdout == raw, "unfrozen_or_changed_artifact")
    return raw


def binding(path):
    return {"path": path.relative_to(ROOT).as_posix(), "sha256": sha256(frozen(path))}


def exact(value):
    require(type(value) is str, "exact_rational_string_required")
    result = Fraction(value)
    require(str(result) == value, "noncanonical_rational")
    return result


def interval(value):
    require(type(value) is dict and set(value) == {"lower", "upper"}, "interval_shape")
    # Decimal strings and reduced rational strings both denote exact endpoints.
    require(all(type(value[k]) is str for k in value), "interval_endpoint_type")
    lo, hi = Fraction(value["lower"]), Fraction(value["upper"])
    require(lo <= hi, "inverted_interval")
    return lo, hi


def overlap(first, second):
    lo, hi = interval(first)
    other_lo, other_hi = interval(second)
    require(max(lo, other_lo) <= min(hi, other_hi), "independent_log_intervals_disagree")


def counts(rows):
    require(type(rows) is list and len(rows) == 8, "complete_joint_count_inventory")
    result = {}
    for row in rows:
        require(type(row) is dict and set(row) == {"h", "a", "b", "counts"}, "joint_count_shape")
        key = tuple(row[name] for name in ("h", "a", "b"))
        require(all(type(v) is int and v in (0, 1) for v in key) and key not in result, "joint_context_identity")
        values = row["counts"]
        require(type(values) is list and len(values) == 4 and
                all(type(v) is int and v >= 0 for v in values), "joint_count_type")
        result[key] = values
    require(set(result) == set(CONTEXTS), "joint_count_coverage")
    return result


def source_table(rows, primitive):
    instrument = decode(primitive)
    require(canonical(encode(instrument)) == canonical(primitive), "noncanonical_primitive")
    require(type(rows) is list and len(rows) == 32, "complete_source_probability_inventory")
    result = {}
    for row in rows:
        require(type(row) is dict and set(row) == {"h", "a", "b", "x", "y", "q"}, "source_probability_shape")
        key = tuple(row[name] for name in ("h", "a", "b", "x", "y"))
        require(all(type(v) is int and v in (0, 1) for v in key) and key not in result, "source_cell_identity")
        q = exact(row["q"])
        require(0 < q <= 1 and q == source_joint(instrument, *key), "positive_source_probability_changed")
        result[key] = q
    require(set(result) == set(itertools.product((0, 1), repeat=5)), "source_probability_coverage")
    return result


def terminal_components(joints, table):
    """Recompute the endpoint from counts; no event file or prefix recurrence."""
    arithmetic = Directed(80)
    zero = arithmetic.logarithm(Fraction(1))
    log_two = arithmetic.logarithm(Fraction(2))
    cache = {}
    def factorial(number):
        if number not in cache:
            cache[number] = arithmetic.logarithm(Fraction(math.factorial(number)))
        return cache[number]
    def predictor(values):
        result = zero
        for number in values:
            term = arithmetic.subtract(factorial(2 * number), factorial(number))
            term = arithmetic.subtract(term, arithmetic.scale(log_two, 2 * number))
            result = arithmetic.add(result, term)
        return arithmetic.subtract(result, factorial(sum(values) + int(len(values) == 4)))
    alice = [sum(values[2 * x] + values[2 * x + 1] for values in joints.values()) for x in (0, 1)]
    bob = [sum(values[y] + values[2 + y] for values in joints.values()) for y in (0, 1)]
    numerators = {"alice": predictor(alice), "bob": predictor(bob), "full": zero, "complement": zero}
    denominators = {name: zero for name in ORDER}
    for (h, a, b), values in joints.items():
        numerators["full"] = arithmetic.add(numerators["full"], predictor(values))
        for parity in (0, 1):
            projected = [values[parity], values[2 + (1 ^ parity)]]
            numerators["complement"] = arithmetic.add(numerators["complement"], predictor(projected))
        for event, number in enumerate(values):
            if number == 0:
                continue
            x, y = divmod(event, 2)
            q = table[h, a, b, x, y]
            require(q > 0, "observed_zero_source_probability")
            mass = sum(table[h, a, b, xx, xx ^ x ^ y] for xx in (0, 1))
            terms = {"full": q, "complement": q / mass,
                     "alice": sum(table[h, a, b, x, yy] for yy in (0, 1)),
                     "bob": sum(table[h, a, b, xx, y] for xx in (0, 1))}
            for name, term in terms.items():
                denominators[name] = arithmetic.add(denominators[name], arithmetic.scale(arithmetic.logarithm(term), number))
    components = {name: arithmetic.subtract(numerators[name], denominators[name]) for name in ORDER}
    mixture = arithmetic.mixture_log([components[name] for name in ORDER])
    return components, mixture, {"alice": alice, "bob": bob}


def provenance(first, attempt, required):
    require(first["version"] == attempt["version"] == VERSION, "scientific_version_changed")
    commit = attempt["freeze_commit"]
    require(type(commit) is str and 7 <= len(commit) <= 40 and
            all(c in "0123456789abcdef" for c in commit), "freeze_commit_shape")
    entries = first["program_bindings"]
    require(canonical(entries) == canonical(attempt["program_bindings"]), "attempt_program_binding_changed")
    paths = {entry["path"] for entry in entries}
    require(len(paths) == len(entries) and required <= paths, "incomplete_scientific_program_binding")
    for entry in entries:
        require(type(entry) is dict and "path" in entry and "sha256" in entry, "program_binding_shape")
        path = (ROOT / entry["path"]).resolve()
        require(sha256(frozen(path, commit)) == entry["sha256"], "frozen_program_bytes_changed")
        require(sha256(frozen(path)) == entry["sha256"], "execution_program_bytes_changed")
    head = first.get("execution_head", attempt.get("execution_head"))
    require(type(head) is str and head, "execution_head_missing")
    result = subprocess.run(["git", "merge-base", "--is-ancestor", commit, head], cwd=ROOT,
                            capture_output=True, check=False)
    require(result.returncode == 0, "science_not_frozen_before_execution")


def validate_runs(primary, independent, witness, legacy):
    require(primary.get("schema") == "stage10-munich-readout-primary-point/v1" and
            primary.get("status") == "certified_source_point" and primary.get("source_point_certified") is True,
            "primary_point_not_certified")
    require(independent.get("schema") == "stage10-munich-readout-independent-point/v1", "independent_point_schema")
    require(primary["version"] == independent["version"] == witness["version"] == VERSION, "version_changed")
    require(witness["schema"] == "stage10-munich-readout-primitive-witness/v1" and
            set(witness) == {"schema", "version", "runs"}, "witness_schema")
    require(primary.get("familywise_alpha") == independent.get("familywise_alpha") == "1/20", "confidence_budget_changed")
    for document in (primary, independent, witness, legacy):
        require(type(document.get("runs")) is list and len(document["runs"]) == 2 and
                tuple(run["run"] for run in document["runs"]) == RUNS, "complete_run_family_required")
    require(independent["source_point_certified"] is True and independent["status"] == "certified_source_point", "independent_point_not_certified")
    summaries = []
    threshold_lower = Fraction(Directed(80).logarithm(Fraction(40)).lower)
    for p, i, w, old in zip(primary["runs"], independent["runs"], witness["runs"], legacy["runs"]):
        require(set(w) == {"run", "primitive"} and canonical(p["primitive"]) == canonical(w["primitive"]), "primitive_witness_changed")
        table = source_table(p["source_probabilities"], w["primitive"])
        require(canonical(p["source_probabilities"]) == canonical(i["source_probabilities"]), "independent_full_Born_source_disagrees")
        check = p["prefix_check"]
        require(check["status"] == "all_prefix_witness_verified" and check["all_prefixes_checked"] is True and
                check["first_rejection"] is None and check["uncertain_prefixes"] == [], "primary_all_prefix_point_not_certified")
        require(i["status"] == "certified_all_prefix_point" and i["all_prefixes_below_threshold_certified"] is True and
                i["first_zero_model_probability_prefix"] is None and i["first_lower_bound_crossing_prefix"] is None and
                i["uncertain_prefixes"] == 0, "independent_all_prefix_point_not_certified")
        total = old["trials"]
        require(type(total) is int and total > 0 and check["trials"] == i["trials"] == i["prefixes_checked"] == i["factor_prefixes"] == total,
                "complete_prefix_denominator_changed")
        require(i["all_pair_records_scored"] is True, "independent_pair_selection_changed")
        for field in ("local_audit", "token_dictionaries", "four_outcomes", "pooled_counts"):
            require(canonical(p[field]) == canonical(i[field]) == canonical(old[field]), "original_archive_identity_changed")
        require(canonical(check["counts"]) == canonical(p["four_outcomes"]) and
                canonical(check["pooled_counts"]) == canonical(p["pooled_counts"]), "primary_count_projection_changed")
        require(i["factor_order"] == list(ORDER), "factor_order_changed")
        for field in ("factor_sequence_sha256", "trial_bit_sequence_sha256"):
            value = check[field]
            require(type(value) is str and len(value) == 64 and all(c in "0123456789abcdef" for c in value)
                    and value == i[field], "independent_complete_sequence_disagrees")
        for value in (check["maximum_log_e"], i["max_log_e"]):
            _, upper = interval(value)
            require(upper < threshold_lower, "prefix_threshold_not_strictly_certified")
        overlap(check["maximum_log_e"], i["max_log_e"])
        overlap(check["terminal_log_e"], i["terminal_log_e"])
        components, terminal, pooled = terminal_components(counts(p["four_outcomes"]), table)
        require(canonical(pooled) == canonical(p["pooled_counts"]), "endpoint_marginal_projection_changed")
        overlap(terminal.encode(), check["terminal_log_e"])
        for name in ORDER:
            overlap(components[name].encode(), check["component_terminal_log_e"][name])
        require(i["source_checks"] == {"dimension": 8, "probabilities": 32, "normalized_distributions": 8,
                                      "complete_effect_cone": True, "source_marginals_checked": True,
                                      "primary_probability_formula_used": False}, "independent_source_scope_changed")
        require(i["global_domain_rejection_claimed"] is False, "point_promoted_to_whole_domain_rejection")
        summaries.append({"run": p["run"], "trials": total, "verdict": "source_confidence_domain_nonempty",
                          "primary_maximum_log_e": check["maximum_log_e"], "independent_maximum_log_e": i["max_log_e"],
                          "maximum_prefix": i["max_prefix_upper"], "terminal_log_e": i["terminal_log_e"],
                          "factor_sequence_sha256": check["factor_sequence_sha256"],
                          "trial_bit_sequence_sha256": check["trial_bit_sequence_sha256"],
                          "primitive": w["primitive"]})
    return summaries


def generate():
    source = kernel_certify.consume()
    import likelihood_certify
    normalizer = likelihood_certify.consume()
    require(source["evidence_valid"] is True and normalizer["evidence_valid"] is True, "source_or_factor_kernel_not_certified")
    documents = {name: strict_json(frozen(BASE / name)) for name in RECEIPTS}
    primary, independent = (documents[name] for name in RECEIPTS[:2])
    witness = documents["primitive-witness-c0002.json"]
    for role, report in (("primary", primary), ("independent", independent)):
        attempt = documents[role + "-attempt-c0002.json"]
        require(report["candidate_revision"] == attempt["candidate_revision"] == "c0002", "candidate_revision_changed")
        require(report["attempt_sha256"] == sha256(frozen(BASE / (role + "-attempt-c0002.json"))), "attempt_identity_changed")
        require(report["witness_sha256"] == sha256(frozen(BASE / "primitive-witness-c0002.json")), "witness_bytes_changed")
        required_names = ("criterion.md", "sources.json", "method-constraints.md", "source-certification-first.json", role + ".py")
        if role == "primary":
            required_names = (*required_names, "run.py", "model.py", "likelihood.py", "criterion-c0002.md", "refine.py", "candidate.py")
        else:
            required_names = (*required_names, "criterion-c0002.md", "refine_independent.py")
        provenance(report, attempt, {str((BASE / name).relative_to(ROOT)) for name in required_names})
    legacy = strict_json(frozen(PARENT / "primary-first-mu0001.1.json"))
    other_legacy = strict_json(frozen(PARENT / "independent-first-mu0001.1.json"))
    archive_fields = ("run", "bytes", "sha256")
    source_archives = strict_json(frozen(PARENT / "sources.json"))["archives"]
    expected_archives = [{k: item[k] for k in archive_fields} for item in source_archives]
    expected_legacy = [binding(PARENT / name) for name in ("primary-first-mu0001.1.json", "independent-first-mu0001.1.json")]
    for report in (primary, independent):
        actual_archives = [{k: item[k] for k in archive_fields} for item in report["archive_bindings"]]
        require(canonical(actual_archives) == canonical(expected_archives), "archive_byte_binding_disagrees")
        require(canonical(report["legacy_first_bindings"]) == canonical(expected_legacy), "legacy_first_inventory_changed")
        for item in report["legacy_first_bindings"]:
            require(item == binding(ROOT / item["path"]), "legacy_first_identity_changed")
    require(canonical(legacy["runs"]) == canonical(other_legacy["runs"]), "legacy_independent_cross_changed")
    require(legacy["runs"][0]["status"] == "rejected", "original_ideal_rejection_lost")
    dyadic = legacy["runs"][0]["max_e"]["dyadic"]
    exponent = dyadic["exponent"]
    unit = Fraction(1 << exponent) if exponent >= 0 else Fraction(1, 1 << -exponent)
    require(dyadic["lower_mantissa"] * unit > 80, "original_zero_error_face_exclusion_not_paid")
    runs = validate_runs(primary, independent, witness, legacy)
    scope = independent["scope"]
    for name in ("independent_8D_Born_contraction", "all_original_prefixes_checked", "conditional_selected_fixed_run_source_contract_required"):
        require(scope[name] is True, "independent_execution_scope_lost")
    for name in ("primary_numeric_receipt_read", "optimizer_run", "global_domain_rejection_claimed",
                 "finite_grid_is_continuous_cover", "actual_hardware_identity_claimed", "controller_advance"):
        require(scope[name] is False, "independent_scope_promoted")
    return {"schema": SCHEMA, "criterion_version": VERSION, "candidate_revision": "c0002", "status": "certified_complete_joint_source_domain",
            "evidence_valid": True, "verdict": "source_confidence_domain_nonempty",
            "full_joint_source_model_certified": True, "public_readout_domain_adjudication_completed": True,
            "same_occurrence_source_bound": True, "independent_8D_Born_cross_certified": True,
            "all_original_prefixes_certified": True, "continuous_carrier_image_complete": True,
            "run_count": 2, "pair_records_scored": sum(run["trials"] for run in runs), "familywise_alpha": "1/20", "runs": runs,
            "source_theorem_changed": False, "actual_hardware_identity_claimed": False,
            "apparatus_optimum_verified": False, "controller_advance": False,
            "retrospective_public_data": True, "human_outcome_unexposed_claimed": False,
            "conditional_selected_fixed_run_source_contract_required": True,
            "original_zero_error_face_rejected": legacy["runs"][0]["status"] == "rejected",
            "trial_event_files_read_at_intake": 0, "new_science_executed_at_intake": 0,
            "source_bindings": [binding(BASE / name) for name in ("criterion.md", "criterion-c0002.md", "sources.json", "method-constraints.md",
                               "source-certification-first.json", "likelihood-certification-first.json", "model.py", "likelihood.py", "verify.py")],
            "first_receipts": [binding(BASE / name) for name in RECEIPTS]}


def consume(certificate=None):
    result = generate()
    receipt = strict_json((BASE / "verification.json" if certificate is None else Path(certificate)).read_bytes())
    require(canonical(receipt) == canonical(result), "certificate_does_not_match_fixed_consumer")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    args = parser.parse_args()
    try:
        result = consume(args.certificate) if args.check_only else generate()
        if not args.check_only:
            require(args.certificate is None, "receipt_override_is_consume_only")
            with (BASE / "verification.json").open("x", encoding="utf-8") as stream:
                json.dump(result, stream, indent=2, ensure_ascii=False)
                stream.write("\n")
        print(canonical(result))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(canonical({"schema": SCHEMA, "evidence_valid": False,
                         "public_readout_domain_adjudication_completed": False, "reason": str(error)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
