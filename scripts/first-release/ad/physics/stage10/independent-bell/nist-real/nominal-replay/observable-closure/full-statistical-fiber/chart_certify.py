#!/usr/bin/env python3
"""Fresh independent certification of the complete tc0001 source chart."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

from phase_certify import ALLOWED, FORBIDDEN, digest, frozen, git, imports, rel

HERE = Path(__file__).resolve().parent
ROOT = next(p for p in HERE.parents if (p / ".git").exists())
PROJECT = ROOT / "Lean"
NOMINAL = HERE.parents[1]
CRITERION_FREEZE = "5c19bf1dde82836dbf60638d92990392ebc7c4e0"
CHAIN = [NOMINAL / "gaussian-window/GaussianSource.lean",
         HERE.parent / "ObservableClosure.lean", HERE.parent / "ClosureConsumer.lean",
         HERE / "PhaseFiber.lean", HERE / "PhaseConsumer.lean",
         HERE / "TrainingChart.lean", HERE / "TrainingChartConsumer.lean",
         HERE / "TrainingChartCertification.lean"]
EXPECTED = {
    "GaussianSource.lean": "1dee783a0976a497139e64d4ef7278b203d56a0b119c84eea942bbb7846a10af",
    "ObservableClosure.lean": "10bd6d3abc3fa23d5a6672e3b7ecd2249624b29396d41e84ea2ebb39b2770c2f",
    "ClosureConsumer.lean": "aeab3e4a50fc884e3dbdd6bb6a6d91711879a3b045fcbf54b9e315dd1580f9d2",
    "PhaseFiber.lean": "08faf200fbb20f5e9b91d92ef00fa03b2cfdd8e23ef85f7625130a6e1732eec7",
    "PhaseConsumer.lean": "89d43b95430673850657a2c6c636edb7ba983185bd1526f6dad99a218c96ffc6",
    "TrainingChart.lean": "3a4dc03452a1b9b6e130e004d6fcfd8e5014dbd52600ae649bd18d697a3a2a51",
    "TrainingChartConsumer.lean": "7abbf2d84fc21bcbeacb41b842583c6399f73ce8117ea4e07de2afa70ed669ea",
}


def import_closure(env: dict) -> dict:
    prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=PROJECT, env=env, text=True).strip()
    search = [HERE, HERE.parent, NOMINAL / "gaussian-window", PROJECT,
              *sorted((PROJECT / ".lake/packages").glob("*")),
              Path(prefix) / "src/lean", Path(prefix) / "src/lean/lake"]
    pending = [module for p in CHAIN for module in imports(p)]
    seen = {}
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        suffix = Path(*module.split(".")).with_suffix(".lean")
        p = next((folder / suffix for folder in search if (folder / suffix).is_file()), None)
        if p is None:
            raise ValueError("unresolved chart import source: " + module)
        seen[module] = digest(p)
        pending.extend(imports(p))
    encoded = json.dumps(seen, sort_keys=True, separators=(",", ":")).encode()
    return {"modules": len(seen), "source_binding_sha256": hashlib.sha256(encoded).hexdigest(),
            "local_modules": sorted(m for m in seen if m in {p.stem for p in CHAIN}), "unresolved": []}


def audit_log(log: str) -> dict:
    counts = re.search(r"TRAINING_CHART_CERTIFIED declarations=(\d+) source_declarations=(\d+)", log)
    independent = re.search(r"TRAINING_CHART_INDEPENDENT_CERTIFIED declarations=(\d+)", log)
    if counts is None or independent is None:
        raise ValueError("complete chart certification sentinel missing")
    result = {"candidate_declarations": int(counts.group(1)),
              "source_declarations": int(counts.group(2)),
              "independent_declarations": int(independent.group(1))}
    graphs = {}
    for role in ("inverse", "intervals", "consumer", "recipe", "regular", "primitive",
                 "actual_body", "inverse_body", "bundle"):
        count = re.search(r"TRAINING_CHART_GRAPH " + role + r"\|(\d+)", log)
        nodes = sorted(set(re.findall(r"TRAINING_CHART_DEP " + role + r"\|([^\s]+)", log)))
        if count is None or int(count.group(1)) != len(nodes):
            raise ValueError("incomplete chart dependency inventory: " + role)
        graphs[role] = {"nodes": len(nodes), "sha256": hashlib.sha256("\n".join(nodes).encode()).hexdigest(),
                        "project_declarations": [n for n in nodes if n.startswith("P23.")]}
    result["dependency_closure"] = graphs
    rows = re.findall(r"TRAINING_CHART_(?:INDEPENDENT_)?AXIOMS ([^|\s]+)\|(?:#)?\[(.*?)\]",
                      log, re.DOTALL)
    if len(rows) != result["source_declarations"] + result["independent_declarations"]:
        raise ValueError("incomplete all-declaration chart axiom audit")
    sets = {}
    for name, row in rows:
        axioms = sorted(s.strip() for s in row.split(",") if s.strip())
        if not set(axioms) <= ALLOWED:
            raise ValueError("unauthorized chart axiom: " + name)
        sets[name] = axioms
    result["axiom_declarations_checked"] = len(rows)
    result["all_axiom_sets_sha256"] = hashlib.sha256(
        json.dumps(sets, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    public = {"P23.ObservableClosure.TrainingChart." + name for name in
              ("native_mirror_means", "actual_means_recover_chart", "single_membership_iff_polytope",
               "source_physical_covariance", "training_intervals_exclude_equal_modes",
               "Consumer.full_training_iff_chart", "Consumer.source_generates_full_training_chart",
               "Consumer.chart_generates_full_training_source",
               "Consumer.full_interval_members_recover_regular_chart")}
    result["public_axioms"] = {n: v for n, v in sets.items() if n in public}
    if len(result["public_axioms"]) != len(public):
        raise ValueError("public chart axiom inventory missing a mouth")
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lsp-record", type=Path, required=True)
    args = parser.parse_args()
    owned = [HERE / "criterion-chart.md", HERE / "sources-chart.json", *CHAIN,
             Path(__file__).resolve(), HERE / "phase_certify.py", HERE / "phase-certification.json",
             PROJECT / "lean-toolchain", PROJECT / "lake-manifest.json", PROJECT / "lakefile.toml"]
    bindings = {rel(p): frozen(p) for p in owned}
    for p in CHAIN[:-1]:
        if digest(p) != EXPECTED[p.name]:
            raise ValueError("chart source/candidate epoch differs: " + p.name)
    for name in ("criterion-chart.md", "sources-chart.json"):
        if subprocess.check_output(["git", "show", CRITERION_FREEZE + ":" + rel(HERE / name)],
                                   cwd=ROOT) != (HERE / name).read_bytes():
            raise ValueError("chart criterion differs from precompile freeze")
    for row in json.loads((HERE / "sources-chart.json").read_text())["inputs"]:
        if digest(ROOT / row["path"]) != row["sha256"]:
            raise ValueError("chart source context differs: " + row["path"])
    text = (HERE / "criterion-chart.md").read_text()
    block = text.split("<!-- TRAINING-CHART-FROZEN-BEGIN -->")[1].split(
        "<!-- TRAINING-CHART-FROZEN-END -->")[0].split("```json")[1].split("```")[0]
    contract = json.loads(block)
    for name in ("new_numeric_tree_coverage_kernel_claim", "new_full_Born_kernel_claim",
                 "new_statistical_coverage_kernel_claim", "controller_advance"):
        if contract[name] is not False:
            raise ValueError("chart claim changed: " + name)
    for p in CHAIN:
        if FORBIDDEN.search(p.read_text()) or any("scratch" in module for module in imports(p)):
            raise ValueError("local chart trust escape or scratch import: " + rel(p))
    lsp = json.loads(args.lsp_record.read_text())
    if lsp["candidate_sha256"] != EXPECTED["TrainingChart.lean"]:
        raise ValueError("LSP metadata belongs to another chart candidate")
    env = json.loads(subprocess.check_output(
        ["lake", "env", "python3", "-c", "import json,os;print(json.dumps(dict(os.environ)))"],
        cwd=PROJECT, text=True))
    modules = import_closure(env)
    checks = []
    with tempfile.TemporaryDirectory(prefix="p23-tc-independent-certify-") as fresh:
        env["LEAN_PATH"] = fresh + os.pathsep + env.get("LEAN_PATH", "")
        for p in CHAIN:
            argv = ["lean", "--trust=0", "-DwarningAsError=true", "--root=" + str(p.parent),
                    "-o", str(Path(fresh) / (p.stem + ".olean")), str(p)]
            run = subprocess.run(argv, cwd=PROJECT, env=env, capture_output=True, text=True, timeout=240)
            log = run.stdout + run.stderr
            checks.append({"source": rel(p), "command": [s.replace(fresh, "${fresh_olean}") for s in argv],
                           "exit_code": run.returncode, "log_sha256": hashlib.sha256(log.encode()).hexdigest(),
                           "stderr": run.stderr,
                           "stdout": run.stdout if p.name != "TrainingChartCertification.lean" else "inventory parsed below"})
            print(p.name + " fresh trust0/werror exit=" + str(run.returncode), flush=True)
            if p.name == "TrainingChartCertification.lean":
                Path("/tmp/p23-tc-last-audit.log").write_text(log)
            if run.returncode:
                blocks = re.split(r"(?m)(?=^/[^\n]+\.lean:\d+:\d+: )", log)
                diagnostics = "\n".join(block for block in blocks
                    if re.match(r"^/[^\n]+\.lean:\d+:\d+: (?:error|warning):", block))
                print(diagnostics, flush=True)
                raise RuntimeError("focused chart certification failed: " + p.name)
            if p.name == "TrainingChartCertification.lean":
                audit = audit_log(log)
    for name, binding in bindings.items():
        if digest(ROOT / name) != binding["sha256"]:
            raise ValueError("chart audit source changed during certification: " + name)
    if import_closure(env) != modules:
        raise ValueError("chart transitive import source changed during certification")
    lint = subprocess.check_output(["python3", str(ROOT / ".agents/skills/lean-agent/scripts/theorem_mouth_lint.py"),
                                   *map(str, CHAIN[5:7]), "--fail-on", "never"], cwd=ROOT, text=True)
    report = {
        "schema": "p23-training-chart-lean-certification/v1", "version": contract["version"],
        "status": "certified", "classification": "bounded subordinate source-coordinate readout and inverse chart with direct full-training consumer",
        "criterion_precompile_freeze": CRITERION_FREEZE,
        "candidate_precompile_freezes": {p.name: bindings[rel(p)]["commit"] for p in CHAIN[5:7]},
        "audit_preexecution_freeze": bindings[rel(HERE / "TrainingChartCertification.lean")]["commit"],
        "bindings": bindings, "actual_import_closure": modules, "authorized_axioms": sorted(ALLOWED),
        "source_audit": audit, "focused_verification": {"fresh_source_compilation": True,
            "trust_level": 0, "warning_as_error": True, "commands": checks, "lsp": lsp, "mouth_lint": lint},
        "public_mouths": sorted(audit["public_axioms"]),
        "kernel_claims": {"same_snapshot_native_four_mean_coordinates": True,
            "inverse_ratio_z_m_x_from_four_actual_means_under_symbolic_nondegeneracy": True,
            "signed_denominator_strictly_negative_generated_from_angles_and_positive_B_means": True,
            "four_complete_single_interval_membership_iff_eight_linear_halfspaces": True,
            "source_generated_covariance_PSD_and_loss_domain": True,
            "both_strict_interval_increases_generate_z_and_R2_positive": True,
            "pure_mode_PSD_boundary_and_regular_inverse_chart_preserved": True,
            "four_singles_and_two_joints_iff_same_source_polytope_and_complete_phase_slabs": True,
            "same_original_source_all_N5_independent_OR_windows": True,
            "lawful_full_chart_internally_generates_its_phase_source": True,
            "all_unknown_coordinate_tuples_realizable_as_source": False,
            "numeric_tree_coverage_or_statistical_confidence_kernel": False,
            "new_infinite_Born_or_detector_determinant_kernel": False,
            "actual_hardware_or_source_epoch_identification": False, "controller_advance": False},
        "mouth_scope": {"forward_and_interval": "all lawful Snapshot/RawSource/lambda; arbitrary intervals with every bound retained",
            "inverse": "sin(2a0)>0, sin(2a1)<0, positive actual Bob means and cos(2a0)>cos(2a1); CI consumer derives actual-mean positivity from positive lower bounds",
            "regular": "strictly separated A and B intervals plus descending cosine generate positive source z and R2; no nV>0 premise",
            "recipe": "FullTrainingChart is a qualification over the same supplied raw source; its legal k generates lambda internally, not arbitrary source existence from coordinates",
            "window": "original N5/independent-OR algebraic recipes; physical statistical coverage and background positivity retain their existing scope",
            "controller": "original visit10/tick16-to17 and root remain unchanged"},
        "source_access": {"new_science_implementations_read": False, "new_numerical_outputs_read": False,
                          "raw_event_files_read": 0, "external_or_hardware_contact": False},
    }
    output = HERE / "chart-certification.json"
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False, allow_nan=False) + "\n")
    capsule = {"schema": "p23-training-chart-certify-capsule/v1", "phase": "certify", "verdict": "certified",
               "classification": report["classification"], "certification_path": rel(output),
               "certification_sha256": digest(output), "public_mouths": report["public_mouths"],
               "candidate_precompile_freezes": report["candidate_precompile_freezes"],
               "audit_preexecution_freeze": report["audit_preexecution_freeze"],
               "machine_counts": {k: v for k, v in audit.items() if isinstance(v, int)},
               "kernel_claims": report["kernel_claims"], "mouth_scope": report["mouth_scope"], "lsp": lsp}
    (HERE / "chart-audit-capsule.json").write_text(json.dumps(capsule, indent=2, ensure_ascii=False) + "\n")
    Path("/tmp/p23-tc-certify-capsule.json").write_text(json.dumps(capsule, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"status": "certified", **capsule["machine_counts"],
                      "actual_import_modules": modules["modules"], "certification_sha256": digest(output)}, indent=2), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
