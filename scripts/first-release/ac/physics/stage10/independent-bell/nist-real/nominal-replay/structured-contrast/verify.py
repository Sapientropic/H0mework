#!/usr/bin/env python3
"""Source-bound certification and intake of the aligned scalar-source contrast."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
VERSION = "p23-structured-contrast-sc0001.1"
SCHEMA = "p23-structured-contrast-verification/v1"
FREEZE = "b4114c8e818d788bfb3df8b804b086b651b259fd"
CANDIDATE_FREEZE = "3d7e88bc26e934d4af22ee2b9163e1c91a056f19"
FLAGS = ("source_mapping_identified", "publication_configuration_identified", "production_admitted",
         "calibration_protocol_identified", "actual_source_failure_claimed")
CHAIN = (
    HERE.parent / "gaussian-window/GaussianSource.lean",
    HERE.parent / "gaussian-window/native-effects/DetectorGamma.lean",
    HERE.parent / "calibration-readout/CalibrationLaw.lean",
    HERE / "AlignedSingles.lean", HERE / "SinglesConsumer.lean", HERE / "SinglesCertification.lean",
)
LSP_HELPER = HERE.parent / "investigation/collected-source/certify.py"
LSP_HELPER_INPUT = LSP_HELPER.parent / "verify.py"
TRUTH = {
    "raw_kernel_actual_ports_and_occupation_to_Gamma": True,
    "all_number_sectors_scalar_click_dominance": True,
    "mirror_paired_local_effect_identity": True,
    "phase_only_local_fullBorn_invariance": True,
    "original_fullBorn_summability_and_single_dominance": True,
    "same_N_and_local_OR_background_dominance": True,
    "printed_probability_box_ratio": True,
    "named_matched_calibration_ratio_and_order": True,
    "one_step_null_factor_readout": True,
    "fullBorn_source_dominance_kernel": True,
    "kernel_closed_form_Born_identity": False,
    "sequential_supermartingale_Ville_kernel": False,
}
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def canonical(value: object) -> str:
    return json.dumps(value, sort_keys=True, ensure_ascii=False, allow_nan=False, separators=(",", ":"))


def load_owned(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, "owned module cannot be loaded")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def committed(path: Path, *, after_contract: bool = False) -> dict:
    name = relative(path)
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", name], cwd=ROOT, text=True).strip()
    require(bool(commit), "execution source is not committed: " + name)
    require(subprocess.check_output(["git", "show", commit + ":" + name], cwd=ROOT) == path.read_bytes(), "execution source differs from its freeze: " + name)
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    if after_contract:
        subprocess.run(["git", "merge-base", "--is-ancestor", FREEZE, commit], cwd=ROOT, check=True)
    return {"commit": commit, "sha256": digest(path)}


def inputs() -> tuple[dict, dict]:
    subprocess.run(["git", "merge-base", "--is-ancestor", FREEZE, "HEAD"], cwd=ROOT, check=True)
    for name in ("criterion-sc0001.1.md", "sources-sc0001.1.json"):
        path = HERE / name
        require(subprocess.check_output(["git", "show", FREEZE + ":" + relative(path)], cwd=ROOT) == path.read_bytes(), "scientific criterion or sources changed")
    for path in CHAIN[3:5]:
        require(subprocess.check_output(["git", "show", CANDIDATE_FREEZE + ":" + relative(path)], cwd=ROOT) == path.read_bytes(), "audited candidate differs from the strike capsule")
    independent = load_owned("p23_structured_intake_independent", HERE / "independent.py")
    spec, manifest = independent.specification()
    require(spec["version"] == manifest["version"] == VERSION, "source criterion version differs")
    bindings = {row["path"]: row["sha256"] for row in manifest["inputs"]}
    owned = (HERE / "criterion-sc0001.1.md", HERE / "sources-sc0001.1.json", *CHAIN,
             HERE / "contrast.py", HERE / "independent.py", HERE / "comparison.py", Path(__file__),
             LSP_HELPER, LSP_HELPER_INPUT)
    freezes = {}
    for path in owned:
        bindings[relative(path)] = digest(path)
        if path not in (HERE / "criterion-sc0001.1.md", HERE / "sources-sc0001.1.json"):
            freezes[relative(path)] = committed(path, after_contract=path.parent == HERE)
    return bindings, freezes


def parse_closure(log: str) -> dict:
    match = re.search(r"STRUCTURED_SOURCE_CERTIFIED declarations=(\d+) nodes=(\d+) required=(\d+) primitive=(\d+)", log)
    independent = re.search(r"STRUCTURED_SOURCE_INDEPENDENT_AXIOMS declarations=(\d+)", log)
    require(match is not None and independent is not None, "missing independent source closure or axiom audit")
    names = ("candidate_declarations", "dependency_nodes", "required_nodes", "primitive_nodes")
    result = dict(zip(names, map(int, match.groups())))
    result["independent_declarations"] = int(independent.group(1))
    require(result["required_nodes"] > 40 and result["independent_declarations"] >= 10, "source audit does not cover its advertised chain")
    return result


def compile_sources(*, lsp: bool) -> dict:
    bindings, freezes = inputs()
    project = ROOT / "Lean"
    env = json.loads(subprocess.check_output(
        ["lake", "env", "python3", "-c", "import json,os; print(json.dumps(dict(os.environ)))"], cwd=project, text=True))
    fresh = Path(tempfile.mkdtemp(prefix="p23-structured-contrast-certify-"))
    env["LEAN_PATH"] = str(fresh) + os.pathsep + env.get("LEAN_PATH", "")
    checks = []
    for path in CHAIN:
        argv = ["lean", "--trust=0", "-DwarningAsError=true", "--root=" + os.path.relpath(path.parent, project),
                "-o", str(fresh / (path.stem + ".olean")), os.path.relpath(path, project)]
        run = subprocess.run(argv, cwd=project, env=env, text=True, capture_output=True, timeout=240)
        (fresh / (path.stem + ".log")).write_text(run.stdout + run.stderr)
        shown = argv.copy()
        shown[5] = "${fresh_olean}/" + path.stem + ".olean"
        checks.append({"source": relative(path), "command": shown, "exit_code": run.returncode,
                       "stdout": run.stdout, "stderr": run.stderr})
        (fresh / "state.json").write_text(json.dumps({"source_bindings": bindings, "commands": checks}, indent=2))
        print(path.name + " fresh trust0/werror exit=" + str(run.returncode), file=sys.stderr, flush=True)
        require(run.returncode == 0, "focused source compile failed: " + path.name + ":" + run.stdout + run.stderr)
    diagnostics = []
    if lsp:
        old_verify = sys.modules.pop("verify", None)
        sys.path.insert(0, str(LSP_HELPER.parent))
        try:
            helper = load_owned("p23_structured_owned_lsp_helper", LSP_HELPER)
            diagnostics = helper.lsp_check(project, env, list(CHAIN))
        finally:
            sys.path.remove(str(LSP_HELPER.parent))
            sys.modules.pop("verify", None)
            if old_verify is not None:
                sys.modules["verify"] = old_verify
    for name, expected in bindings.items():
        require(digest(ROOT / name) == expected, "source changed during fresh compilation: " + name)
    return {"bindings": bindings, "execution_source_freezes": freezes, "commands": checks, "lsp": diagnostics,
            "closure_counts": parse_closure(checks[-1]["stdout"])}


def certify() -> dict:
    fresh = compile_sources(lsp=True)
    return {
        "schema": "p23-structured-contrast-lean-certification/v1", "version": VERSION, "status": "certified",
        "criterion_freeze": {"commit": FREEZE, "criterion_sha256": digest(HERE / "criterion-sc0001.1.md"),
                             "sources_sha256": digest(HERE / "sources-sc0001.1.json")},
        "candidate_freeze": CANDIDATE_FREEZE,
        "bindings": fresh["bindings"], "execution_source_freezes": fresh["execution_source_freezes"],
        "authorized_axioms": AXIOMS, "kernel_claims": TRUTH,
        "source_audit": {**fresh["closure_counts"], "actual_Gamma_paired_local_summability_original_fullBorn_in_closure": True,
                         "target_singles_relation_in_primitive": False, "operational_root_in_closure": False,
                         "primitive_raw_source_and_transmissions_only": True},
        "focused_verification": {"fresh_source_compilation": True, "trust_level": 0, "warning_as_error": True,
                                 "commands": fresh["commands"], "lsp": fresh["lsp"]},
        "declaration_classification": {
            "actual_source_single_contrast": "subordinate optical producer from raw source and actual scalar ports",
            "phase_only_local_source_contract": "same-source local readout invariance",
            "printed_box_source_contrast": "generated scalar-efficiency-domain consumer",
            "matched_calibration_source_contrast": "named matched-calibration consumer",
            "one_step_readout": "conditional statistical readout; its null is a premise",
        },
        "known_assumptions": ["paired HH/VV RawKernel", "scalar H/V transmission per side", "mirror analyzer angles",
                              "one common pulse law repeated N times", "Alice local OR background at least Bob",
                              "named matched single-pulse signal-only calibration for the calibrated branch"],
        "root_effect": "bounded subordinate producer/readout; no root, whole-ledger or tick installation",
        "kernel_closed_form_Born_identity": False, "nominal_optimum_verdict_changed": False,
        "retrospective": True, "bell_event_files_read": 0, **{flag: False for flag in FLAGS},
    }


def certificate_check(directory: Path, *, fresh: bool) -> dict:
    bindings, freezes = inputs()
    path = directory / "certification.json"
    receipt = json.loads(path.read_text(encoding="utf-8"))
    require(canonical(receipt) == canonical(json.loads((HERE / "certification.json").read_text(encoding="utf-8"))), "untrusted certificate differs from the owned fresh certificate")
    require(receipt["schema"] == "p23-structured-contrast-lean-certification/v1" and receipt["version"] == VERSION and receipt["status"] == "certified", "certificate schema, version or status differs")
    require(receipt["criterion_freeze"] == {"commit": FREEZE, "criterion_sha256": digest(HERE / "criterion-sc0001.1.md"), "sources_sha256": digest(HERE / "sources-sc0001.1.json")}, "certificate criterion binding differs")
    require(receipt["candidate_freeze"] == CANDIDATE_FREEZE and receipt["bindings"] == bindings and receipt["execution_source_freezes"] == freezes, "certificate source bindings differ")
    require(receipt["authorized_axioms"] == AXIOMS and set(receipt["kernel_claims"]) == set(TRUTH) and all(receipt["kernel_claims"][key] is value for key, value in TRUTH.items()), "certificate axiom or kernel scope differs")
    require(all(receipt.get(flag) is False for flag in FLAGS) and receipt["kernel_closed_form_Born_identity"] is False and receipt["nominal_optimum_verdict_changed"] is False, "certificate grants actual apparatus or closed-form identity")
    require(receipt["retrospective"] is True and type(receipt["bell_event_files_read"]) is int and receipt["bell_event_files_read"] == 0, "certificate access scope differs")
    audit = receipt["source_audit"]
    require(audit["actual_Gamma_paired_local_summability_original_fullBorn_in_closure"] is True and audit["primitive_raw_source_and_transmissions_only"] is True and audit["target_singles_relation_in_primitive"] is False and audit["operational_root_in_closure"] is False, "certificate source primitive or dependency scope differs")
    focused = receipt["focused_verification"]
    require(focused["fresh_source_compilation"] is True and type(focused["trust_level"]) is int and focused["trust_level"] == 0 and focused["warning_as_error"] is True, "certificate does not record fresh strict kernel compilation")
    require([row["source"] for row in focused["commands"]] == [relative(path) for path in CHAIN], "certificate misses a source layer")
    for row in focused["commands"]:
        require(type(row["exit_code"]) is int and row["exit_code"] == 0 and row["command"][1:3] == ["--trust=0", "-DwarningAsError=true"], "certificate compilation failed or uses a different trust policy")
    require([row["file"] for row in focused["lsp"]] == [path.name for path in CHAIN] and all(type(row["errors"]) is int and type(row["warnings"]) is int and row["errors"] == row["warnings"] == 0 for row in focused["lsp"]), "certificate lacks completed LSP diagnostics")
    counts = parse_closure(focused["commands"][-1]["stdout"])
    require(all(type(audit[key]) is int and audit[key] == value for key, value in counts.items()), "certificate closure counts differ from the kernel audit")
    if fresh:
        repeated = compile_sources(lsp=False)
        require(repeated["closure_counts"] == counts, "fresh source closure differs from the certified candidate")
    return receipt


def generated_report(directory: Path, *, fresh: bool = False) -> dict:
    receipt = certificate_check(directory, fresh=fresh)
    comparison = load_owned("p23_structured_intake_comparison", HERE / "comparison.py")
    paired = comparison.compare(directory)
    stored_comparison = json.loads((directory / "independent-comparison.json").read_text(encoding="utf-8"))
    require(canonical(paired) == canonical(stored_comparison), "stored posterior comparison differs from fresh 120-row intake")
    all_rejected = paired["all_named_mappings_rejected"]
    require(type(all_rejected) is bool, "named-model decision is not a Boolean")
    bindings, freezes = inputs()
    for name in ("certification.json", "contrast.json", "independent.json", "independent-comparison.json"):
        bindings[name] = digest(directory / name)
    return {
        "schema": SCHEMA, "version": VERSION, "status": "verified", "evidence_valid": True,
        "criterion_freeze": receipt["criterion_freeze"], "candidate_freeze": CANDIDATE_FREEZE,
        "fullBorn_source_dominance_kernel": True, "kernel_closed_form_Born_identity": False,
        "all_named_mappings_rejected": all_rejected,
        "outcome": "ALIGNED_SCALAR_MAPPING_REJECTED" if all_rejected else "NOT_ALL_NAMED_MAPPINGS_REJECTED",
        "complete_trial_count_grid": paired["full_grid_size"], "full_family_size": paired["full_family_size"],
        "all_120_exact_log_intervals_compatible": True, "all_120_threshold_decisions_agree": True,
        "consumed_fresh_source_certificate": True, "fresh_source_compilation": fresh,
        "kernel_claims": TRUTH, "source_audit": receipt["source_audit"],
        "authorized_axioms": AXIOMS, "execution_source_freezes": freezes, "bindings": bindings,
        "by_model": paired["by_model"], "information_access": paired["information_access"],
        "scope": "named aligned scalar loss and mirror paired local count law; actual NIST identity is not supplied",
        "nominal_optimum_verdict_changed": False, "combined_with_po0003_alpha": False,
        "retrospective": True, "bell_event_files_read": 0, **{flag: False for flag in FLAGS},
    }


def assess(report_dir=None, *, enabled: bool = True, fresh: bool = False) -> dict:
    base = {"schema": SCHEMA, "version": VERSION, "evidence_valid": False,
            "fullBorn_source_dominance_kernel": False, "kernel_closed_form_Born_identity": False,
            "all_named_mappings_rejected": False, "nominal_optimum_verdict_changed": False,
            **{flag: False for flag in FLAGS}}
    if not enabled:
        return {**base, "status": "disabled_by_override"}
    directory = HERE if report_dir is None else Path(report_dir).resolve()
    try:
        stored = json.loads((directory / "verification.json").read_text(encoding="utf-8"))
        require(stored.get("schema") == SCHEMA and stored.get("version") == VERSION and stored.get("status") == "verified" and stored.get("evidence_valid") is True, "stored verification does not have the structured contrast schema")
        require(type(stored.get("all_named_mappings_rejected")) is bool, "stored named-model decision is not a Boolean")
        require(stored.get("fullBorn_source_dominance_kernel") is True and stored.get("kernel_closed_form_Born_identity") is False and stored.get("nominal_optimum_verdict_changed") is False and all(stored.get(flag) is False for flag in FLAGS), "stored verification grants an unbound claim")
        generated = generated_report(directory, fresh=fresh)
        comparable = dict(generated)
        comparable["fresh_source_compilation"] = False
        require(canonical(stored) == canonical(comparable), "stored verification differs from source-derived fresh intake")
        return generated
    except FileNotFoundError as error:
        return {**base, "status": "missing_structured_contrast_evidence", "reason": str(error)}
    except (ValueError, KeyError, TypeError, AttributeError, ArithmeticError, ImportError, OSError, RuntimeError, subprocess.SubprocessError) as error:
        return {**base, "status": "invalid_structured_contrast_evidence", "reason": str(error)}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--disabled", action="store_true")
    parser.add_argument("--fresh", action="store_true")
    parser.add_argument("--certify", action="store_true", help="compile the owned six-layer source chain and emit its certificate")
    parser.add_argument("--generate", action="store_true", help="emit the first verification after source certification")
    args = parser.parse_args()
    require(not (args.certify and args.generate), "certificate and verification generation are separate steps")
    if args.certify:
        result = certify()
        (HERE / "certification.json").write_text(json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False) + "\n")
        print(json.dumps({"status": result["status"], "source_audit": result["source_audit"]}))
        return 0
    if args.generate:
        result = generated_report(HERE if args.directory is None else args.directory)
        (HERE / "verification.json").write_text(json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False) + "\n")
    else:
        result = assess(args.directory, enabled=not args.disabled, fresh=args.fresh)
    print(json.dumps(result, ensure_ascii=False, indent=2, allow_nan=False))
    return 0 if result["status"] == "verified" else 1


if __name__ == "__main__":
    raise SystemExit(main())
