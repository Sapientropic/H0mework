"""Frozen, once-only search and all-prefix source-point certification of both runs."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
from itertools import product
import json
import math
from pathlib import Path
import subprocess
import sys

from likelihood import check_prefixes
from model import decode, encode, full_joint
from primary import TerminalCounts, search_terminal


BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[5]
PARENT = BASE.parent
VERSION = "stage10-munich-readout-rd0001"
SCHEMA = "stage10-munich-readout-primary-point/v1"
WITNESS_SCHEMA = "stage10-munich-readout-primitive-witness/v1"
RUNS = ("2016-04-15", "2016-06-14")
CONTEXTS = tuple(product(range(2), repeat=3))
PRECISIONS = (80, 160, 320)
MAX_ITERATIONS = 1500
PARENT_FREEZE = "b1247f063f"
LEGACY_FIRST_FREEZE = "e377420499"
SOURCE_CERTIFICATE_FREEZE = "0f1eac20c5"
PARSER_SHA256 = "af7932137128286d06ea4da2cb5d35236271b5e6a21eebf1993ee186f928397e"
PARENT_PRIMARY_SHA256 = "b748f5054914ff8ccf47774814be5dd3816be0503e085f3942d96f07f55ae6b2"
OLD_FIRSTS = ("primary-first-mu0001.1.json", "independent-first-mu0001.1.json")
OLD_ATTEMPTS = ("primary-attempt-mu0001.1.json", "independent-attempt-mu0001.1.json")
SCIENTIFIC_FILES = (
    "criterion.md", "method-constraints.md", "sources.json", "model.py", "primary.py",
    "likelihood.py", "run.py", "independent.py", "test_primary.py", "test_likelihood.py",
    "test_run.py", "test_independent.py", "kernel_certify.py", "test_kernel_certify.py",
    "Certification.lean", "source-certification-first.json", "likelihood_certify.py",
    "test_likelihood_certify.py", "LikelihoodCertification.lean", "likelihood-certification-first.json",
)
PARENT_FILES = (
    "schema.py", "primary.py", "criterion-mu0001.1.md", "sources.json", "source-methods.md",
    "format-repair-mu0001.1.json", *OLD_FIRSTS, *OLD_ATTEMPTS,
)
PROOF_FILES = tuple(ROOT / "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell" / name
                    for name in ("Readout.lean", "ReadoutEffects.lean", "ReadoutLikelihood.lean"))


class DriverError(ValueError):
    def __init__(self, code, **detail):
        self.detail = {"code": code, **detail}
        super().__init__(code)


def require(condition, code, **detail):
    if not condition:
        raise DriverError(code, **detail)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def canonical(document):
    return json.dumps(document, sort_keys=True, separators=(",", ":"), ensure_ascii=False)


def strict_json(raw):
    def pairs(entries):
        answer = {}
        for key, value in entries:
            require(key not in answer, "duplicate_json_key", field=key)
            answer[key] = value
        return answer
    def invalid(_):
        raise DriverError("nonfinite_json_constant")
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=invalid)


def load_module(path, name, expected_sha256=None):
    if expected_sha256 is not None:
        require(digest(path.read_bytes()) == expected_sha256, "fixed_program_bytes_changed", field=path.name)
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, "scientific_module_unavailable", field=path.name)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def git(*arguments):
    result = subprocess.run(["git", *arguments], cwd=ROOT, capture_output=True, check=False)
    require(result.returncode == 0, "scientific_git_guard", operation=arguments[0])
    return result.stdout


def frozen_bytes(path, revision="HEAD"):
    relative = path.resolve().relative_to(ROOT).as_posix()
    raw = path.read_bytes()
    require(git("show", f"{revision}:{relative}") == raw, "scientific_input_not_frozen", field=relative)
    return raw


def frozen_binding(path, revision="HEAD"):
    raw = frozen_bytes(path, revision)
    return {"path": path.resolve().relative_to(ROOT).as_posix(), "sha256": digest(raw)}


def committed_snapshot(freeze_commit):
    """Only the declared scientific corridor is required clean in this shared repo."""
    freeze = git("rev-parse", "--verify", freeze_commit + "^{commit}").decode("ascii").strip()
    head = git("rev-parse", "HEAD").decode("ascii").strip()
    paths = [BASE / name for name in SCIENTIFIC_FILES] + [PARENT / name for name in PARENT_FILES] + list(PROOF_FILES)
    relatives = [path.resolve().relative_to(ROOT).as_posix() for path in paths]
    dirty = git("status", "--porcelain", "--", *relatives)
    require(dirty == b"", "dirty_scientific_paths", paths=dirty.decode("utf-8", errors="replace").splitlines())
    bindings = []
    for path in paths:
        binding = frozen_binding(path)
        frozen_bytes(path, freeze)
        bindings.append(binding)
    for name in ("schema.py", "primary.py", "criterion-mu0001.1.md", "sources.json",
                 "source-methods.md", "format-repair-mu0001.1.json"):
        frozen_bytes(PARENT / name, PARENT_FREEZE)
    for name in OLD_FIRSTS + OLD_ATTEMPTS:
        frozen_bytes(PARENT / name, LEGACY_FIRST_FREEZE)
    frozen_bytes(BASE / "source-certification-first.json", SOURCE_CERTIFICATE_FREEZE)
    return {"freeze_commit": freeze, "execution_head": head, "program_bindings": bindings}


def radical_inverse(number, base):
    answer, scale = 0., 1. / base
    while number:
        number, digit = divmod(number, base)
        answer += digit * scale
        scale /= base
    return answer


def search_starts():
    nominal_angles = (0., math.pi / 2, math.pi / 4, -math.pi / 4)
    starts = [tuple(value for angle in nominal_angles for value in (0., radius, angle))
              for radius in (.95, .65)]
    starts.append((0., 0., 0.) * 4)
    primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for number in range(1, 33):
        values = [radical_inverse(number, prime) for prime in primes]
        starts.append(tuple(value for offset in range(0, 12, 3) for value in (
            .8 * (2 * values[offset] - 1), .15 + .8 * values[offset + 1],
            math.pi * (2 * values[offset + 2] - 1))))
    return tuple(starts)


SEARCH_DECLARATION = {
    "optimizer": "scipy.optimize.minimize/L-BFGS-B", "max_iterations_per_start": MAX_ITERATIONS,
    "required_scipy_version": "1.13.1",
    "ftol": "1e-12", "other_optimizer_options": "scipy_L-BFGS-B_defaults",
    "bounds_per_effect": [["-1", "1"], ["0", "1"], ["-pi", "pi"]],
    "parameter_order": "alice0/alice1/bob0/bob1;mu/radius/angle",
    "starts": [list(start) for start in search_starts()], "starts_count": len(search_starts()),
    "start_construction": "two_nominal_radii_0.95_0.65;zero_gain;Halton_indices_1_to_32_12_fixed_primes",
    "candidate_order": "declared_start_order_without_terminal_value_sorting",
    "primitive_rationalization": "coordinate_toward_zero_dyadic_40_bits_then_exact_cone_shrink",
    "precision_escalation": list(PRECISIONS), "terminal_objective_is_verdict": False,
    "search_failure_is_global_rejection": False,
}


def solver_environment():
    import numpy
    import scipy
    require(scipy.__version__ == SEARCH_DECLARATION["required_scipy_version"], "solver_version_mismatch")
    return {"python": sys.version.split()[0], "numpy": numpy.__version__, "scipy": scipy.__version__}


def load_frozen_inputs(snapshot):
    parser = load_module(PARENT / "schema.py", "_readout_fixed_parent_schema", PARSER_SHA256)
    previous = sys.modules.get("schema")
    sys.modules["schema"] = parser
    try:
        old_primary = load_module(PARENT / "primary.py", "_readout_fixed_parent_primary", PARENT_PRIMARY_SHA256)
    finally:
        if previous is None:
            sys.modules.pop("schema", None)
        else:
            sys.modules["schema"] = previous
    parent_bindings = old_primary.load_frozen_inputs()
    require(tuple(parser.RUNS) == RUNS, "fixed_run_inventory")
    criterion = (BASE / "criterion.md").read_text(encoding="utf-8")
    begin, end = "<!-- MUNICH-READOUT-RD0001-BEGIN -->", "<!-- MUNICH-READOUT-RD0001-END -->"
    require(criterion.count(begin) == criterion.count(end) == 1, "criterion_protocol_block")
    block = criterion.split(begin, 1)[1].split(end, 1)[0].strip()
    require(block.startswith("```json\n") and block.endswith("\n```"), "criterion_json_block")
    protocol = strict_json(block[8:-4])
    expected = {
        "version": VERSION, "source": "positiveSmoothUnifiedSource", "root_visit": 10,
        "current_tick": 16, "next_tick": 17, "controller_advance": False, "runs": list(RUNS),
        "real_parameters_per_run": 12, "shared_across_herald": True,
        "threshold": "40", "per_run_alpha": "1/40", "familywise_alpha": "1/20",
        "component_weights": {"full": "1/2", "alice": "1/6", "bob": "1/6", "complement": "1/6"},
        "selection": "all_original_official_pairs_mu0001.1_admission",
        "search_is_verdict": False, "retrospective_public_data": True,
    }
    require(all(protocol.get(key) == value for key, value in expected.items()), "criterion_protocol_mismatch")
    sources = strict_json((BASE / "sources.json").read_bytes())
    require(sources.get("schema") == "munich-readout-method-constraint-sources/v1" and
            sources.get("parent_method_bindings") == "../sources.json", "readout_source_identity")
    require(sources.get("original_source") == {
        "source": "positiveSmoothUnifiedSource", "visit": 10, "current_tick": 16, "next_tick": 17,
        "controller_advance": False, "original_source_theorem_changed": False}, "readout_root_identity")
    # The likelihood intake also consumes the exact frozen source115 and its paid base.
    likelihood_kernel = load_module(BASE / "likelihood_certify.py", "_readout_likelihood_kernel_intake")
    likelihood_kernel.consume()
    kernel_bindings = [frozen_binding(BASE / name) for name in
                       ("source-certification-first.json", "likelihood-certification-first.json")]
    legacy = [strict_json((PARENT / name).read_bytes()) for name in OLD_FIRSTS]
    for first, attempt_name in zip(legacy, OLD_ATTEMPTS):
        require(first.get("version") == "stage10-munich-mu0001.1" and
                first.get("admission") == "admitted" and
                first.get("scientific_adjudication_completed") is True and
                first.get("all_pair_records_scored", True) is True and
                tuple(entry["run"] for entry in first["runs"]) == RUNS,
                "legacy_complete_admission_required")
        require(canonical(first.get("source_bindings")) == canonical(parent_bindings), "legacy_source_bindings_changed")
        require(first.get("attempt_sha256") == digest((PARENT / attempt_name).read_bytes()), "legacy_attempt_bytes_changed")
    return {"parser": parser, "legacy_firsts": legacy,
            "bindings": {"parent": parent_bindings, "readout_sources_sha256": digest((BASE / "sources.json").read_bytes()),
                         "criterion_sha256": digest((BASE / "criterion.md").read_bytes()),
                         "method_constraints_sha256": digest((BASE / "method-constraints.md").read_bytes()),
                         "kernel_receipt_bindings": kernel_bindings,
                         "legacy_attempt_bindings": [frozen_binding(PARENT / name) for name in OLD_ATTEMPTS]},
            "legacy_first_bindings": [frozen_binding(PARENT / name) for name in OLD_FIRSTS]}


def summarize(admitted):
    counts = {key: [0, 0, 0, 0] for key in CONTEXTS}
    alice, bob = [0, 0], [0, 0]
    sequence, rows = hashlib.sha256(), hashlib.sha256()
    require(admitted.run in RUNS and bool(admitted.trials), "complete_nonempty_run_required")
    for prefix, trial in enumerate(admitted.trials, 1):
        bits = (trial.h, trial.a, trial.b, trial.x, trial.y)
        require(trial.row == prefix and all(type(bit) is int and bit in (0, 1) for bit in bits),
                "original_binary_trial_order", run=admitted.run, prefix=prefix)
        counts[bits[:3]][2 * trial.x + trial.y] += 1
        alice[trial.x] += 1
        bob[trial.y] += 1
        sequence.update(bytes(bits))
        rows.update(f"{prefix}|{trial.time_ms}|{','.join(map(str, bits))}|{trial.row_a}|{trial.row_b}\n".encode("ascii"))
    require(admitted.audit.get("pair_records") == len(admitted.trials) and
            admitted.audit.get("original_pair_order_preserved") is True and
            admitted.audit.get("all_pairs_joined") is True and
            admitted.audit.get("additional_outcome_selection") is False, "complete_original_pair_admission")
    return {"trials": len(admitted.trials),
            "four_outcomes": [dict(zip(("h", "a", "b"), key), counts=counts[key]) for key in CONTEXTS],
            "pooled_counts": {"alice": alice, "bob": bob},
            "trial_bit_sequence_sha256": sequence.hexdigest(),
            "trial_audit": {"row_time_local_refs_sha256": rows.hexdigest(),
                            "trial_bit_sequence_sha256": sequence.hexdigest(),
                            "original_pair_order_preserved": True, "pair_records": len(admitted.trials)}}


def legacy_cross(admitted, summary, firsts):
    hashes = []
    for first in firsts:
        old = next(entry for entry in first["runs"] if entry["run"] == admitted.run)
        require(old["trials"] == summary["trials"] and
                canonical(old["four_outcomes"]) == canonical(summary["four_outcomes"]) and
                canonical(old["pooled_counts"]) == canonical(summary["pooled_counts"]),
                "legacy_endpoint_counts_changed", run=admitted.run)
        require(canonical(old["local_audit"]) == canonical(admitted.audit) and
                canonical(old["token_dictionaries"]) == canonical(admitted.token_dictionaries),
                "legacy_full_data_identity_changed", run=admitted.run)
        require(old.get("all_pair_records_scored") is True, "legacy_all_pairs_required", run=admitted.run)
        hashes.append(old["prefix_e_sha256"])
    require(len(hashes) == 2 and hashes[0] == hashes[1], "legacy_prefix_cross_changed")
    return {"old_counts_and_original_pair_bytes_checked": True, "full_local_audit_checked": True,
            "original_token_dictionary_checked": True, "old_statistic_rescored": False,
            "legacy_balanced_prefix_sha256": hashes[0]}


def source_table(point):
    rows = full_joint(point)
    table = {(row["h"], row["a"], row["b"]): row["probabilities"] for row in rows}
    return table, [dict(zip(("h", "a", "b", "x", "y"), key + (x, y)), q=str(table[key][2 * x + y]))
                   for key in CONTEXTS for x, y in product(range(2), repeat=2)]


def validate_candidate(document):
    require(type(document) is dict and set(document) == {"alice", "bob"}, "primitive_shape")
    for side in ("alice", "bob"):
        require(type(document[side]) is list and len(document[side]) == 2, "primitive_setting_inventory")
        for entry in document[side]:
            require(type(entry) is dict and set(entry) == {"mu", "u", "z"} and
                    all(type(value) is str for value in entry.values()), "canonical_fraction_strings_required")
    point = decode(document)
    require(encode(point) == document, "noncanonical_primitive_rational")
    return point


def check_candidate(admitted, document):
    point = validate_candidate(document)
    table, probabilities = source_table(point)
    zero = next((trial.row for trial in admitted.trials
                 if table[trial.h, trial.a, trial.b][2 * trial.x + trial.y] == 0), None)
    if zero is not None:
        return {"primitive": document, "source_probabilities": probabilities, "precision_attempts": [],
                "prefix_precision_results": [], "prefix_check": {
                    "status": "zero_model_probability_observed", "trials": len(admitted.trials),
                    "all_prefixes_checked": False, "first_zero_model_probability_prefix": zero}}
    results = []
    for precision in PRECISIONS:
        result = check_prefixes(admitted.trials, table, precision=precision)
        require(result["trials"] == len(admitted.trials) and result.get("all_prefixes_checked") is True,
                "incomplete_prefix_check")
        results.append(result)
        if result["status"] != "numerical_boundary_unresolved":
            break
    return {"primitive": document, "source_probabilities": probabilities,
            "precision_attempts": [entry["numerical_precision"] for entry in results],
            "prefix_precision_results": results, "prefix_check": results[-1]}


def certify_run(admitted, summary):
    terminal = TerminalCounts(tuple(tuple(row["counts"]) for row in summary["four_outcomes"]))
    candidates, searches = [], []
    for number, start in enumerate(search_starts(), 1):
        try:
            emitted = search_terminal(terminal, (start,), max_iterations=MAX_ITERATIONS)
            require(len(emitted) <= 1, "single_start_candidate_inventory")
            for candidate in emitted:
                validate_candidate(candidate["primitive"])
                require(math.isfinite(candidate["approximate_terminal_log_e"]), "nonfinite_search_readout")
                candidates.append({**candidate, "search_start_index": number})
            searches.append({"search_start_index": number, "status": "candidate_generated" if emitted else "no_finite_candidate"})
        except Exception as error:
            searches.append({"search_start_index": number, "status": "search_failed", "error_type": type(error).__name__})
    checks, accepted = [], None
    for candidate in candidates:
        try:
            checked = check_candidate(admitted, candidate["primitive"])
            checked.update({key: value for key, value in candidate.items() if key != "primitive"})
        except Exception as error:
            checked = {"primitive": candidate["primitive"], "search_start_index": candidate["search_start_index"],
                       "prefix_check": {"status": "candidate_check_failed", "error_type": type(error).__name__}}
        checks.append(checked)
        if checked["prefix_check"]["status"] == "all_prefix_witness_verified":
            accepted = checked
            break
    result = {"run": admitted.run, **summary,
              "status": "all_prefix_witness_verified" if accepted is not None else "unresolved",
              "all_prefixes_below_threshold_certified": accepted is not None,
              "all_pair_records_scored": accepted is not None,
              "primitive": None if accepted is None else accepted["primitive"],
              "source_probabilities": None if accepted is None else accepted["source_probabilities"],
              "prefix_check": None if accepted is None else accepted["prefix_check"],
              "precision_attempts": [] if accepted is None else accepted["precision_attempts"],
              "searchcount": {"declared_starts": len(search_starts()), "finite_candidates": len(candidates),
                              "checked_candidates": len(checks)},
              "search_attempts": searches, "candidate_checks": checks,
              "threshold": "40", "per_run_alpha": "1/40",
              "local_audit": admitted.audit, "token_dictionaries": admitted.token_dictionaries,
              "global_domain_rejection_claimed": False}
    if accepted is not None:
        require(canonical(accepted["prefix_check"]["counts"]) == canonical(summary["four_outcomes"]) and
                canonical(accepted["prefix_check"]["pooled_counts"]) == canonical(summary["pooled_counts"]) and
                accepted["prefix_check"]["trial_bit_sequence_sha256"] == summary["trial_bit_sequence_sha256"],
                "accepted_prefix_accounting_changed")
    return result


def exclusive_json(path, document):
    with path.open("x", encoding="utf-8") as stream:
        json.dump(document, stream, indent=2, sort_keys=True, ensure_ascii=False, allow_nan=False)
        stream.write("\n")


def record_access(access):
    entries = [access[key] for key in sorted(access)]
    return {"members": entries,
            "event_record_lines_decoded": sum(entry["record_lines_decoded"] for entry in entries),
            "decoded_csv_members_in_full": sum(entry["fully_decoded"] for entry in entries),
            "decoded_pairs_members_in_full": sum(entry["fully_decoded"] and entry["role"] == "pairs" for entry in entries)}


def failed_report(error, status):
    detail = error.detail if hasattr(error, "detail") else {"code": "driver_error", "error_type": type(error).__name__}
    return {"schema": SCHEMA, "version": VERSION, "status": status, "failure": detail,
            "scientific_verdict": "unresolved" if status != "not_started" else "not_executed",
            "source_point_certified": False, "scientific_adjudication_completed": False,
            "global_domain_rejection_claimed": False, "real_instrument_empirical_verdict_executed": False}


def execute(archive_dir, freeze_commit, *, output_dir=BASE):
    attempt_path, first_path = output_dir / "primary-attempt.json", output_dir / "primary-first.json"
    witness_path = output_dir / "primitive-witness.json"
    if any(path.exists() for path in (attempt_path, first_path, witness_path)):
        return failed_report(DriverError("first_attempt_already_reserved"), "not_started"), 2
    snapshot, inputs, access = None, None, {}
    try:
        snapshot = committed_snapshot(freeze_commit)
        inputs = load_frozen_inputs(snapshot)
        runtime = solver_environment()
        attempt = {"schema": "stage10-munich-readout-primary-attempt/v1", "version": VERSION,
                   "started_utc": datetime.now(timezone.utc).isoformat(), **snapshot,
                   "source_bindings": inputs["bindings"], "legacy_first_bindings": inputs["legacy_first_bindings"],
                   "search_declaration": SEARCH_DECLARATION, "solver_environment": runtime,
                   "event_records_decoded_at_reservation": 0}
        exclusive_json(attempt_path, attempt)
    except FileExistsError:
        return failed_report(DriverError("first_attempt_already_reserved"), "not_started"), 2
    except Exception as error:
        report = failed_report(error, "not_started")
        report["record_access"] = record_access(access)
        if snapshot is not None:
            report.update(snapshot)
        exclusive_json(first_path, report)
        return report, 2
    results = []
    try:
        parser = inputs["parser"]
        admitted = {spec.run: parser.admit_archive(archive_dir, spec, access) for spec in parser.ARCHIVES}
        summaries = {run: summarize(admitted[run]) for run in RUNS}
        crosses = {run: legacy_cross(admitted[run], summaries[run], inputs["legacy_firsts"]) for run in RUNS}
        for run in RUNS:
            result = certify_run(admitted[run], summaries[run])
            result["legacy_cross"] = crosses[run]
            results.append(result)
        final_snapshot = committed_snapshot(freeze_commit)
        require(final_snapshot["program_bindings"] == snapshot["program_bindings"], "scientific_bytes_changed_during_execution")
        qualified = all(result["all_prefixes_below_threshold_certified"] for result in results)
        witness_sha256 = None
        if qualified:
            witness = {"schema": WITNESS_SCHEMA, "version": VERSION,
                       "runs": [{"run": result["run"], "primitive": result["primitive"]} for result in results]}
            exclusive_json(witness_path, witness)
            witness_sha256 = digest(witness_path.read_bytes())
        report = {"schema": SCHEMA, "version": VERSION,
                  "status": "certified_source_point" if qualified else "unresolved",
                  "scientific_verdict": "complete_joint_confidence_domain_nonempty" if qualified else "unresolved",
                  "source_point_certified": qualified, "scientific_adjudication_completed": qualified,
                  "real_instrument_empirical_verdict_executed": qualified,
                  "global_domain_rejection_claimed": False, "runs": results,
                  "familywise_alpha": "1/20", "pair_records_scored": sum(result["trials"] for result in results),
                  "archive_bindings": inputs["bindings"]["parent"]["archive_bindings"],
                  "witness_sha256": witness_sha256,
                  "scope": {"all_original_prefixes_checked": qualified, "full_joint_source_domain": True,
                            "fixed_run_conditional_source_contract_required": True,
                            "optimizer_is_verdict": False, "finite_grid_is_continuous_cover": False,
                            "actual_hardware_identity_claimed": False, "controller_advance": False,
                            "human_public_result_unexposed_claimed": False}}
    except Exception as error:
        report = failed_report(error, "execution_failed")
        report.update({"runs": results, "witness_sha256": None,
                       "archive_bindings": inputs["bindings"]["parent"]["archive_bindings"]})
    report.update({**snapshot, "source_bindings": inputs["bindings"],
                   "legacy_first_bindings": inputs["legacy_first_bindings"],
                   "attempt_sha256": digest(attempt_path.read_bytes()), "record_access": record_access(access),
                   "search_declaration": SEARCH_DECLARATION, "solver_environment": runtime})
    evidence_bindings = {"program_bindings_sha256": digest(canonical(snapshot["program_bindings"]).encode()),
                         "source_bindings_sha256": digest(canonical(inputs["bindings"]).encode()),
                         "kernel_receipt_bindings": inputs["bindings"]["kernel_receipt_bindings"],
                         "witness_sha256": report.get("witness_sha256"), "attempt_sha256": report["attempt_sha256"]}
    for result in report.get("runs", []):
        result["evidence_bindings"] = evidence_bindings
    exclusive_json(first_path, report)
    return report, 0 if report["source_point_certified"] else 1


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive-dir", type=Path, default=Path.home() / "Downloads",
                        help="Location override for both byte-identical fixed archives.")
    parser.add_argument("--freeze-commit", required=True, help="Commit freezing the entire declared scientific corridor.")
    args = parser.parse_args(argv)
    report, status = execute(args.archive_dir, args.freeze_commit)
    print(canonical({"schema": SCHEMA, "status": report["status"],
                     "source_point_certified": report["source_point_certified"],
                     "scientific_verdict": report["scientific_verdict"]}))
    return status


if __name__ == "__main__":
    raise SystemExit(main())
