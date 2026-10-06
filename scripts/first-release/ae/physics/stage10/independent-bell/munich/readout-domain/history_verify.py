"""Read-only intake of source-history recovery and the complete public record observer."""
import argparse
import hashlib
import json
import subprocess
from pathlib import Path

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[5]
SCHEMA = "stage10-munich-source-record-history-evidence/v1"
FIRST = BASE / "history-first-hr0001.1.json"
ATTEMPT = BASE / "history-first-hr0001.1-attempt.json"
PROOF = BASE / "source-history-certification-first.json"
PAID = BASE.parent / "primary-first-mu0001.1.json"
SCIENCE = tuple(BASE / name for name in (
    "criterion-hr0001.md", "criterion-hr0001.1.md", "history_feed.py",
    "history_feed_independent.py", "history_run.py", "test_history_feed.py"))
PARSERS = (BASE.parent / "schema.py", BASE.parent / "invariant_independent.py")
FIELDS = ["row", "time_raw", "setting", "result", "local_timestamp", "herald",
          "raw_flag", "comment", "raw_sha256"]


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def binding(path):
    return {"path": str(path.relative_to(ROOT)), "sha256": digest(path)}


def frozen(path, commit="HEAD"):
    raw = path.read_bytes()
    bound = subprocess.check_output(["git", "show", f"{commit}:{path.relative_to(ROOT)}"], cwd=ROOT)
    require(raw == bound, "changed frozen history source: " + str(path.relative_to(ROOT)))
    return raw


def generate():
    first = json.loads(frozen(FIRST))
    attempt = json.loads(frozen(ATTEMPT))
    proof = json.loads(frozen(PROOF))
    paid = json.loads(frozen(PAID))
    require(first.get("schema") == "bell-public-record-history/v1" and
            first.get("version") == "hr0001.1" and
            first.get("status") == "complete_public_record_history_connected", "history receipt identity")
    require(attempt.get("schema") == "bell-history-consumption-attempt/v1" and
            attempt.get("version") == first["version"] and
            attempt.get("execution_head") == first.get("execution_head"), "history attempt identity")
    expected = [binding(path) for path in (*SCIENCE, PAID, *PARSERS)]
    require(first.get("source_bindings") == attempt.get("source_bindings") == expected, "history source bindings")
    for path in (*SCIENCE, PAID, *PARSERS):
        frozen(path, first["execution_head"])
    require(subprocess.run(["git", "merge-base", "--is-ancestor", first["execution_head"], "HEAD"],
                           cwd=ROOT, capture_output=True).returncode == 0, "history freeze ancestry")
    require(first.get("source") == "positiveSmoothUnifiedSource" and
            first.get("root_visit") == 10 and first.get("current_tick") == 16 and
            first.get("next_tick") == 17, "history source root identity")
    for key in ("controller_advance", "pair_csv_decoded", "statistics_replayed",
                "physical_action_inferred_from_record_order", "full_history_nonrecoverability_certified",
                "actual_hardware_parameters_uniquely_recovered"):
        require(first.get(key) is False, "history scope promoted: " + key)
    require(first.get("all_available_local_record_fields_preserved") is True and
            first.get("primary") == first.get("independent"), "history observer cross mismatch")
    expected_locals = {}
    for run in paid["runs"]:
        audit = run["local_audit"]
        require(audit["admissible_row_offset_pairs"] == [[1, 1]], "history original selection changed")
        for role in ("local1", "local2"):
            expected_locals[run["run"], role] = audit["join_candidates"][0][role]
    actual = first["primary"]
    require(len(actual) == 4 and {(item["run"], item["role"]) for item in actual} == set(expected_locals),
            "history observer inventory")
    for item in actual:
        local = expected_locals[item["run"], item["role"]]
        require(item["fields"] == FIELDS and item["every_record_recovered"] is True and
                item["records"] == local["total_records"] and
                item["paired_records"] == local["paired_records"] and
                item["unpaired_records"] == local["unpaired_records"] and
                item["record_sequence_sha256"] == local["all_original_row_sequence_sha256"],
                "history record field or source identity")
    require(proof.get("schema") == "stage10-bell-source-history-certification/v1" and
            proof.get("candidate_module") == "SaturationMonoid.PhysicsCore.Stage10.Bell.SourceHistory" and
            proof.get("evidence_valid") is True and proof.get("focused_trust_level") == 0,
            "source history proof identity")
    for key in ("all_owned_declarations_audited", "same_original_occurrence", "full_field_recovery",
                "native_action_and_joint_fibre", "whole_history_retained", "original_ledger_and_macro_next",
                "current_next_born_commutes"):
        require(proof.get(key) is True, "source history proof absent: " + key)
    for key in ("actual_hardware_parameter_mapping_certified", "controller_advance"):
        require(proof.get(key) is False, "source history proof scope promoted")
    require(set(proof["axiom_union"]) <= {"propext", "Classical.choice", "Quot.sound"}, "source history trust escape")
    expected_proof_paths = {
        "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/SourceHistory.lean",
        str((BASE / "SourceHistoryCertification.lean").relative_to(ROOT)),
    }
    require({item["path"] for item in proof["source_bindings"]} == expected_proof_paths, "source history proof owner")
    for item in proof["source_bindings"]:
        path = ROOT / item["path"]
        require(digest(path) == item["sha256"], "source history proof source changed")
        frozen(path)
    return {"schema": SCHEMA, "version": "hr0001.1", "evidence_valid": True,
            "status": "certified_original_source_and_complete_public_record_history",
            "full_original_source_history_recovery_certified": True,
            "complete_public_record_history_connected": True,
            "original_native_action_and_joint_fibre_consumed": True,
            "source": "positiveSmoothUnifiedSource", "root_visit": 10, "current_tick": 16, "next_tick": 17,
            "public_records": sum(item["records"] for item in actual),
            "unpaired_public_records_preserved": sum(item["unpaired_records"] for item in actual),
            "actual_field_control_record_binding_certified": False,
            "actual_hardware_uniquely_identified": False, "full_history_nonrecoverability_certified": False,
            "controller_advance": False, "trial_events_read_at_intake": 0,
            "new_lean_compilations_at_intake": 0, "new_statistical_executions_at_intake": 0,
            "source_bindings": [binding(path) for path in (Path(__file__).resolve(), FIRST, ATTEMPT, PROOF, PAID)]}


def consume(certificate=None):
    expected = generate()
    path = BASE / "history-verification.json" if certificate is None else Path(certificate)
    require(expected == json.loads(path.read_text(encoding="utf-8")), "history certificate changed")
    return expected


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    args = parser.parse_args()
    try:
        result = consume(args.certificate) if args.check_only else generate()
        if not args.check_only:
            require(args.certificate is None, "history override is intake only")
            with (BASE / "history-verification.json").open("x", encoding="utf-8") as output:
                json.dump(result, output, indent=2, sort_keys=True)
                output.write("\n")
        print(json.dumps(result, sort_keys=True))
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(json.dumps({"schema": SCHEMA, "evidence_valid": False, "reason": str(error)}))
        raise SystemExit(1)
