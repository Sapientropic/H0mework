#!/usr/bin/env python3
"""Independent hash-bound, fresh Lean certification of the pf0001 phase fibre."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / ".git").exists())
PROJECT = ROOT / "Lean"
NOMINAL = HERE.parents[1]
CRITERION_FREEZE = "6bc572139a93512e9f1ed7dbcae71dcd72cec6ef"
CHAIN = [NOMINAL / "gaussian-window/GaussianSource.lean",
         HERE.parent / "ObservableClosure.lean", HERE.parent / "ClosureConsumer.lean",
         HERE / "PhaseFiber.lean", HERE / "PhaseConsumer.lean", HERE / "PhaseCertification.lean"]
EXPECTED = {
    "GaussianSource.lean": "1dee783a0976a497139e64d4ef7278b203d56a0b119c84eea942bbb7846a10af",
    "ObservableClosure.lean": "10bd6d3abc3fa23d5a6672e3b7ecd2249624b29396d41e84ea2ebb39b2770c2f",
    "ClosureConsumer.lean": "aeab3e4a50fc884e3dbdd6bb6a6d91711879a3b045fcbf54b9e315dd1580f9d2",
    "PhaseFiber.lean": "08faf200fbb20f5e9b91d92ef00fa03b2cfdd8e23ef85f7625130a6e1732eec7",
    "PhaseConsumer.lean": "89d43b95430673850657a2c6c636edb7ba983185bd1526f6dad99a218c96ffc6",
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(?:sorry|admit|axiom|native_decide|unsafe)\b")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def frozen(path: Path) -> dict:
    revision = git("log", "-1", "--format=%H", "--", rel(path))
    if not revision:
        raise ValueError("uncommitted audit source: " + rel(path))
    original = subprocess.check_output(["git", "show", revision + ":" + rel(path)], cwd=ROOT)
    if original != path.read_bytes():
        raise ValueError("source differs from owned preexecution commit: " + rel(path))
    return {"commit": revision, "sha256": digest(path)}


def imports(path: Path) -> list[str]:
    source = path.read_text()
    clean = []
    index = 0
    depth = 0
    while index < len(source):
        if source.startswith("/-", index):
            depth += 1
            index += 2
        elif depth and source.startswith("-/", index):
            depth -= 1
            index += 2
        elif not depth and source.startswith("--", index):
            newline = source.find("\n", index)
            index = len(source) if newline < 0 else newline
        else:
            if not depth or source[index] == "\n":
                clean.append(source[index])
            index += 1
    modules = []
    for line in "".join(clean).splitlines():
        line = line.strip()
        if not line or line in {"prelude", "module"}:
            continue
        match = re.match(r"^(?:(?:public|private|meta)\s+)*import(?:\s+all)?\s+(.+)$", line)
        if match:
            modules.extend(match.group(1).split())
        else:
            break
    return modules


def import_closure(env: dict) -> dict:
    prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=PROJECT, env=env,
                                     text=True).strip()
    search = [HERE, HERE.parent, NOMINAL / "gaussian-window", PROJECT,
              *sorted((PROJECT / ".lake/packages").glob("*")),
              Path(prefix) / "src/lean", Path(prefix) / "src/lean/lake"]
    pending = [module for path in CHAIN for module in imports(path)]
    seen = {}
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        suffix = Path(*module.split(".")).with_suffix(".lean")
        path = next((p / suffix for p in search if (p / suffix).is_file()), None)
        if path is None:
            raise ValueError("unresolved import source: " + module)
        seen[module] = digest(path)
        pending.extend(imports(path))
    payload = json.dumps(seen, sort_keys=True, separators=(",", ":")).encode()
    return {"modules": len(seen), "source_binding_sha256": hashlib.sha256(payload).hexdigest(),
            "local_modules": sorted(m for m in seen if m in {p.stem for p in CHAIN}),
            "unresolved": []}


def audit_log(log: str) -> dict:
    match = re.search(r"PHASE_FIBER_CERTIFIED declarations=(\d+) source_declarations=(\d+) "
                      r"mouth_nodes=(\d+) consumer_nodes=(\d+) primitive_nodes=(\d+) body_nodes=(\d+) "
                      r"bundle_nodes=(\d+) required_mouth=(\d+) required_consumer=(\d+)", log)
    controls = re.search(r"PHASE_FIBER_INDEPENDENT_CERTIFIED declarations=(\d+)", log)
    if match is None or controls is None:
        raise ValueError("complete phase certification sentinel missing")
    labels = ["candidate_declarations", "source_declarations", "mouth_nodes", "consumer_nodes",
              "primitive_nodes", "body_nodes", "bundle_nodes", "required_mouth", "required_consumer"]
    result = dict(zip(labels, map(int, match.groups())))
    result["independent_declarations"] = int(controls.group(1))
    graphs = {}
    for role in ("mouth", "consumer", "primitive", "body", "bundle"):
        nodes = sorted(set(re.findall(r"PHASE_FIBER_DEP " + role + r"\|([^\s]+)", log)))
        if len(nodes) != result[role + "_nodes"]:
            raise ValueError("incomplete declaration dependency inventory: " + role)
        graphs[role] = {"nodes": len(nodes),
                        "sha256": hashlib.sha256("\n".join(nodes).encode()).hexdigest(),
                        "project_declarations": [n for n in nodes if n.startswith("P23.")]}
    axiom_rows = re.findall(r"PHASE_FIBER_(?:INDEPENDENT_)?AXIOMS ([^|\s]+)\|(?:#)?\[(.*?)\]",
                           log, re.DOTALL)
    expected_count = result["source_declarations"] + result["independent_declarations"]
    if len(axiom_rows) != expected_count:
        raise ValueError("incomplete all-declaration axiom audit: " + str(len(axiom_rows))
                         + " rows, expected " + str(expected_count))
    axiom_sets = {}
    for name, row in axiom_rows:
        values = sorted(n.strip() for n in row.split(",") if n.strip())
        if not set(values) <= ALLOWED:
            raise ValueError("unauthorized axiom: " + name + ": " + str(values))
        axiom_sets[name] = values
    result["dependency_closure"] = graphs
    result["axiom_declarations_checked"] = len(axiom_rows)
    result["all_axiom_sets_sha256"] = hashlib.sha256(
        json.dumps(axiom_sets, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    result["public_axioms"] = {n: a for n, a in axiom_sets.items()
        if n in {"P23.ObservableClosure.PhaseFiber.complete_phase_fiber",
                 "P23.ObservableClosure.PhaseFiber.generatedSnapshot",
                 "P23.ObservableClosure.PhaseFiber.generated_all_cells",
                 "P23.ObservableClosure.PhaseFiber.Consumer.generates_training_and_all_windows",
                 "P23.ObservableClosure.PhaseFiber.Consumer.shared_phase_relation",
                 "P23.ObservableClosure.PhaseFiber.Consumer.no_signaling_restrictions",
                 "P23.ObservableClosure.PhaseFiber.covariance_pulse_readback"}}
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lsp-record", type=Path, required=True)
    args = parser.parse_args()
    owned = [HERE / "criterion-lean.md", HERE / "sources-lean.json", *CHAIN,
             Path(__file__).resolve(), PROJECT / "lean-toolchain", PROJECT / "lake-manifest.json"]
    bindings = {rel(p): frozen(p) for p in owned}
    for p in CHAIN[:-1]:
        if digest(p) != EXPECTED[p.name]:
            raise ValueError("candidate/source epoch hash differs: " + p.name)
    for name in ("criterion-lean.md", "sources-lean.json"):
        if subprocess.check_output(["git", "show", CRITERION_FREEZE + ":" + rel(HERE / name)],
                                   cwd=ROOT) != (HERE / name).read_bytes():
            raise ValueError("phase criterion differs from its precompile freeze")
    source_manifest = json.loads((HERE / "sources-lean.json").read_text())
    for row in source_manifest["inputs"]:
        p = ROOT / row["path"]
        if p.name != "lakefile.toml" and digest(p) != row["sha256"]:
            raise ValueError("source context differs: " + row["path"])
    criterion = (HERE / "criterion-lean.md").read_text()
    frozen_block = criterion.split("<!-- PHASE-FIBER-FROZEN-BEGIN -->")[1].split(
        "<!-- PHASE-FIBER-FROZEN-END -->")[0].split("```json")[1].split("```")[0]
    contract = json.loads(frozen_block)
    for name in ("new_full_Born_kernel_claim", "new_statistical_coverage_kernel_claim", "controller_advance"):
        if contract[name] is not False:
            raise ValueError("phase scope changed: " + name)
    for p in CHAIN:
        if FORBIDDEN.search(p.read_text()):
            raise ValueError("unauthorized local trust escape: " + rel(p))
        if any("scratch" in m for m in imports(p)):
            raise ValueError("production imports scratch: " + rel(p))
    lsp_record = json.loads(args.lsp_record.read_text())
    if lsp_record["candidate_sha256"] != EXPECTED["PhaseFiber.lean"]:
        raise ValueError("LSP metadata belongs to another candidate")
    lake_config = {"sha256": digest(PROJECT / "lakefile.toml"),
                   "frozen_sha256": next(r["sha256"] for r in source_manifest["inputs"]
                                         if r["path"] == "Lean/lakefile.toml"),
                   "diff": git("diff", "--", "Lean/lakefile.toml")}
    env = json.loads(subprocess.check_output(
        ["lake", "env", "python3", "-c", "import json,os;print(json.dumps(dict(os.environ)))"],
        cwd=PROJECT, text=True))
    module_bindings = import_closure(env)
    checks = []
    with tempfile.TemporaryDirectory(prefix="p23-pf-independent-certify-") as fresh:
        env["LEAN_PATH"] = fresh + os.pathsep + env.get("LEAN_PATH", "")
        for p in CHAIN:
            command = ["lean", "--trust=0", "-DwarningAsError=true", "--root=" + str(p.parent),
                       "-o", str(Path(fresh) / (p.stem + ".olean")), str(p)]
            run = subprocess.run(command, cwd=PROJECT, env=env, capture_output=True, text=True, timeout=240)
            normalized = [part.replace(fresh, "${fresh_olean}") for part in command]
            log = run.stdout + run.stderr
            checks.append({"source": rel(p), "command": normalized, "exit_code": run.returncode,
                           "log_sha256": hashlib.sha256(log.encode()).hexdigest(),
                           "warnings_or_errors": run.stderr,
                           "stdout": run.stdout if p.name != "PhaseCertification.lean" else "dependency/axiom inventory parsed below"})
            print(p.name + " fresh trust0/werror exit=" + str(run.returncode), flush=True)
            if run.returncode:
                print(log, flush=True)
                raise RuntimeError("focused phase certification failed: " + p.name)
            if p.name == "PhaseCertification.lean":
                Path("/tmp/p23-pf-last-audit.log").write_text(log)
                audit = audit_log(log)
    for name, binding in bindings.items():
        if digest(ROOT / name) != binding["sha256"]:
            raise ValueError("source changed during certification: " + name)
    if digest(PROJECT / "lakefile.toml") != lake_config["sha256"]:
        raise ValueError("live Lake config changed during focused checks")
    module_bindings_after = import_closure(env)
    if module_bindings_after != module_bindings:
        raise ValueError("actual transitive import source changed during certification")
    lint = subprocess.run(["python3", str(ROOT / ".agents/skills/lean-agent/scripts/theorem_mouth_lint.py"),
                           *map(str, CHAIN[3:5]), "--fail-on", "never"], cwd=ROOT,
                          capture_output=True, text=True, check=True)
    report = {
        "schema": "p23-phase-fiber-lean-certification/v1", "version": contract["version"],
        "status": "certified", "classification": "bounded subordinate optical producer and direct readout",
        "criterion_precompile_freeze": CRITERION_FREEZE,
        "candidate_precompile_freeze": bindings[rel(HERE / "PhaseFiber.lean")]["commit"],
        "audit_preexecution_freeze": bindings[rel(HERE / "PhaseCertification.lean")]["commit"],
        "public_mouth": "P23.ObservableClosure.PhaseFiber.complete_phase_fiber",
        "direct_consumer": "P23.ObservableClosure.PhaseFiber.Consumer.generates_training_and_all_windows",
        "bindings": bindings, "actual_import_closure": module_bindings,
        "live_lake_configuration": lake_config,
        "authorized_axioms": sorted(ALLOWED), "source_audit": audit,
        "focused_verification": {"fresh_source_compilation": True, "trust_level": 0,
                                 "warning_as_error": True, "commands": checks, "lsp": lsp_record,
                                 "mouth_lint": lint.stdout},
        "kernel_claims": {"raw_source_legality_and_generated_phase_bounds": True,
                          "all_legal_lambda_two_training_qualification_iff_physical_k_and_slabs": True,
                          "same_generated_snapshot_all_cells": True,
                          "zero_T_retains_all_legal_phase_readout_equivalence": True,
                          "pure_mode_and_zero_g_preserved": True,
                          "same_source_N5_independent_OR_four_outcome_recipe": True,
                          "shared_phase_identity_and_no_signaling_restrictions": True,
                          "same_snapshot_covariance_ell_gamma_and_nonzero_R2_pulse_chart": True,
                          "new_infinite_Born_or_detector_determinant_identity": False,
                          "new_statistical_coverage_kernel": False,
                          "actual_hardware_or_source_epoch_identification": False,
                          "all_four_outcome_nonnegativity_kernel": False,
                          "controller_advance": False},
        "mouth_scope": {"primitive": "nH,nV,etaA,etaB,delta with elementary source bounds",
                        "qualification": "complete fibre characterization; interval feasibility is generated characterization, not a fitted training claim",
                        "consumer_input": "PhaseQualified pays declared interval membership; shared source and all-window laws are generated",
                        "window": "N5/independent-OR algebraic recipes for arbitrary real backgrounds; physical background legality and probability positivity are outside this exact mouth",
                        "covariance": "ell/gamma identities hold on every Snapshot; pulse chart uses its nonzero generated R2",
                        "controller": "original visit10/tick16-to17, same whole ledger and source epoch unchanged"},
        "source_access": {"new_science_implementations_read": False,
                          "new_numerical_outputs_read": False, "raw_event_files_read": 0,
                          "external_or_hardware_contact": False},
    }
    output = HERE / "phase-certification.json"
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False, allow_nan=False) + "\n")
    capsule = {"schema": "p23-phase-fiber-certify-capsule/v1", "phase": "certify", "verdict": "certified",
               "classification": report["classification"], "public_mouth": report["public_mouth"],
               "direct_consumer": report["direct_consumer"], "candidate_precompile_freeze": report["candidate_precompile_freeze"],
               "audit_preexecution_freeze": report["audit_preexecution_freeze"],
               "certification_sha256": digest(output), "source_audit": audit,
               "kernel_claims": report["kernel_claims"], "mouth_scope": report["mouth_scope"],
               "lsp": lsp_record, "bindings": bindings}
    (HERE / "phase-audit-capsule.json").write_text(json.dumps(capsule, indent=2, ensure_ascii=False) + "\n")
    Path("/tmp/p23-pf-certify-capsule.json").write_text(json.dumps(capsule, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"status": "certified", "candidate_declarations": audit["candidate_declarations"],
                      "source_declarations": audit["source_declarations"],
                      "independent_declarations": audit["independent_declarations"],
                      "axiom_declarations_checked": audit["axiom_declarations_checked"],
                      "actual_import_modules": module_bindings["modules"],
                      "certification_sha256": digest(output)}, indent=2), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
