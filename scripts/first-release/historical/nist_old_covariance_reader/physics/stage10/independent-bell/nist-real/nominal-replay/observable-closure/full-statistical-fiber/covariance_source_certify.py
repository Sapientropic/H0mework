#!/usr/bin/env python3
"""Fresh independent exact-source producer certification of cs0001."""
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
CRITERION_FREEZE = "a8f7ff307c2834523d177b9f4d0aa200541ac967"
CHAIN = [NOMINAL / "gaussian-window/GaussianSource.lean",
         HERE.parent / "ObservableClosure.lean", HERE.parent / "ClosureConsumer.lean",
         HERE / "PhaseFiber.lean", HERE / "PhaseConsumer.lean", HERE / "TrainingChart.lean",
         HERE / "CovarianceSource.lean", HERE / "CovarianceSourceConsumer.lean",
         HERE / "CovarianceSourceCertification.lean"]
EXPECTED = {
    "GaussianSource.lean": "1dee783a0976a497139e64d4ef7278b203d56a0b119c84eea942bbb7846a10af",
    "ObservableClosure.lean": "10bd6d3abc3fa23d5a6672e3b7ecd2249624b29396d41e84ea2ebb39b2770c2f",
    "ClosureConsumer.lean": "aeab3e4a50fc884e3dbdd6bb6a6d91711879a3b045fcbf54b9e315dd1580f9d2",
    "PhaseFiber.lean": "08faf200fbb20f5e9b91d92ef00fa03b2cfdd8e23ef85f7625130a6e1732eec7",
    "PhaseConsumer.lean": "89d43b95430673850657a2c6c636edb7ba983185bd1526f6dad99a218c96ffc6",
    "TrainingChart.lean": "3a4dc03452a1b9b6e130e004d6fcfd8e5014dbd52600ae649bd18d697a3a2a51",
    "CovarianceSource.lean": "4f9679384b1c284d2102614da793ff855c1ea20f7525fa32546c26f143fe300d",
    "CovarianceSourceConsumer.lean": "eb851e78f9cf35330888b556be4af61e101d539f273a64914d1c5fc5028bc82a",
}
KERNEL_CLAIMS = {
    "all_legal_regular_z_positive_coordinate_tuples_generate_original_RawSource": True,
    "primitive_has_only_five_coordinates_and_elementary_physical_inequalities": True,
    "arctan_axis_and_original_loss_occupation_fields_generated_internally": True,
    "exact_same_tuple_five_coordinate_and_original_T2_readback": True,
    "every_lawful_signed_k_generates_phase_lambda_and_original_Snapshot": True,
    "pure_nV_zero_T_zero_and_every_lawful_lambda_readout_equivalence_preserved": True,
    "complete_tuple_eight_halfspaces_iff_generated_source_four_single_intervals": True,
    "same_generated_source_all_original_pulse_cells_shared_phase_and_N5_OR_windows": True,
    "numeric_tree_or_statistical_confidence_coverage_kernel": False,
    "new_infinite_Born_or_detector_determinant_kernel": False,
    "actual_hardware_or_source_epoch_identification": False,
    "controller_advance": False,
}
MOUTH_SCOPE = {
    "producer_domain": "m>=0, z^2+x^2<=m^2, z>0, r>0, 0<loss<=1, loss<=r; arbitrary real x",
    "raw_source": "nH=(m+sqrt(z^2+x^2))/loss, nV=(m-sqrt(z^2+x^2))/loss, etaA=loss, etaB=loss/r, delta=arctan(x/z)/2",
    "phase": "k^2<=(m^2-z^2-x^2)((m+loss)^2-z^2-x^2); internal same-source PF phase recipe",
    "CI": "all eight tuple bounds correspond to all four actual generated local intervals; no tree or confidence premise",
    "window": "original Gaussian pulse and N5/independent-OR algebraic readouts from that generated source",
    "controller": "original visit10/tick16-to17 and root remain unchanged",
}
PUBLIC_MOUTHS = {"P23.ObservableClosure.CovarianceSource." + name for name in
    ("Primitive", "rawSource", "generatedSnapshot", "axis_readback", "baseline_coordinates",
     "generated_coordinates", "baseline_T2", "generated_phase_physical", "generated_interference",
     "generated_all_cells", "boundary_pure_mode", "boundary_zero_T", "boundary_preserves_all_phases",
     "Consumer.primitive_generates_source_and_readouts", "Consumer.generated_single_intervals_iff_tuple",
     "Consumer.generated_shared_phase")}


def header_imports(path: Path) -> list[str]:
    modules = []
    depth = 0
    with path.open() as source:
        for line in source:
            clean = []
            index = 0
            while index < len(line):
                if line.startswith("/-", index):
                    depth += 1
                    index += 2
                elif depth and line.startswith("-/", index):
                    depth -= 1
                    index += 2
                elif not depth and line.startswith("--", index):
                    break
                else:
                    if not depth:
                        clean.append(line[index])
                    index += 1
            text = "".join(clean).strip()
            if not text or text in {"module", "prelude"}:
                continue
            match = re.match(r"^(?:(?:public|private|meta)\s+)*import(?:\s+all)?\s+(.+)$", text)
            if match is None:
                break
            modules.extend(match.group(1).split())
    return modules


def import_closure(env: dict | None = None, source_root: str | None = None) -> dict:
    if source_root is None:
        if env is None:
            raise ValueError("pinned toolchain source root required for read-only import validation")
        prefix = subprocess.check_output(["lean", "--print-prefix"], cwd=PROJECT, env=env, text=True).strip()
        source_root = str(Path(prefix) / "src/lean")
    search = [HERE, HERE.parent, NOMINAL / "gaussian-window", PROJECT,
              *sorted((PROJECT / ".lake/packages").glob("*")),
              Path(source_root), Path(source_root) / "lake"]
    pending = [module for p in CHAIN for module in header_imports(p)]
    seen = {}
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        suffix = Path(*module.split(".")).with_suffix(".lean")
        p = next((folder / suffix for folder in search if (folder / suffix).is_file()), None)
        if p is None:
            raise ValueError("unresolved covariance source import: " + module)
        seen[module] = digest(p)
        pending.extend(header_imports(p))
    encoded = json.dumps(seen, sort_keys=True, separators=(",", ":")).encode()
    return {"modules": len(seen), "source_binding_sha256": hashlib.sha256(encoded).hexdigest(),
            "local_modules": sorted(m for m in seen if m in {p.stem for p in CHAIN}), "unresolved": [],
            "toolchain_source_root": source_root}


def audit_log(log: str) -> dict:
    counts = re.search(r"COVARIANCE_SOURCE_CERTIFIED declarations=(\d+) source_declarations=(\d+)", log)
    independent = re.search(r"COVARIANCE_SOURCE_INDEPENDENT_CERTIFIED declarations=(\d+)", log)
    if counts is None or independent is None:
        raise ValueError("complete covariance source audit sentinel missing")
    result = {"candidate_declarations": int(counts.group(1)),
              "source_declarations": int(counts.group(2)),
              "independent_declarations": int(independent.group(1))}
    graphs = {}
    for role in ("primitive", "axis_body", "raw_body", "phase_body", "baseline", "consumer",
                 "intervals", "shared", "boundary", "bundle"):
        count = re.search(r"COVARIANCE_SOURCE_GRAPH " + role + r"\|(\d+)", log)
        nodes = sorted(set(re.findall(r"COVARIANCE_SOURCE_DEP " + role + r"\|([^\s]+)", log)))
        if count is None or int(count.group(1)) != len(nodes):
            raise ValueError("incomplete covariance source dependency inventory: " + role)
        graphs[role] = {"nodes": len(nodes), "sha256": hashlib.sha256("\n".join(nodes).encode()).hexdigest(),
                        "project_declarations": [n for n in nodes if n.startswith("P23.")]}
    result["dependency_closure"] = graphs
    rows = re.findall(r"COVARIANCE_SOURCE_(?:INDEPENDENT_)?AXIOMS ([^|\s]+)\|(?:#)?\[(.*?)\]",
                      log, re.DOTALL)
    if len(rows) != result["source_declarations"] + result["independent_declarations"]:
        raise ValueError("incomplete all-declaration covariance source axiom audit")
    sets = {}
    for name, row in rows:
        axioms = sorted(s.strip() for s in row.split(",") if s.strip())
        if not set(axioms) <= ALLOWED:
            raise ValueError("unauthorized covariance source axiom: " + name)
        sets[name] = axioms
    result["axiom_declarations_checked"] = len(rows)
    result["all_axiom_sets_sha256"] = hashlib.sha256(
        json.dumps(sets, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
    result["public_axioms"] = {n: v for n, v in sets.items() if n in PUBLIC_MOUTHS}
    if len(result["public_axioms"]) != len(PUBLIC_MOUTHS):
        raise ValueError("public covariance source axiom inventory missing a mouth")
    return result


def consume(certificate_path: str | Path | None = None, disabled: bool = False) -> dict:
    """Validate the committed receipt and all bound sources without running Lean."""
    result = {
        "schema": "p23-covariance-source-evidence/v1", "disabled": disabled,
        "evidence_valid": False, "source_realization_kernel_certified": False,
        "all_legal_regular_coordinate_tuples_realizable_as_source": False,
        "five_covariance_coordinates_read_back": False, "source_generated_all_cells_and_N5": False,
        "actual_source_or_hardware_identified": False, "source_epoch_identified": False,
        "nominal_optimum_verified": False, "controller_advance": False,
        "new_full_Born_kernel_claim": False, "new_statistical_coverage_kernel_claim": False,
    }
    if disabled:
        return result
    canonical = HERE / "covariance-source-certification.json"
    canonical_binding = frozen(canonical)
    given = canonical if certificate_path is None else Path(certificate_path)
    original = canonical.read_bytes()
    if given.read_bytes() != original:
        raise ValueError("covariance certificate override is not an immutable original-byte copy")
    cert = json.loads(original)
    if (cert.get("schema") != "p23-covariance-source-lean-certification/v1"
        or cert.get("version") != "p23-covariance-source-realization-cs0001"
        or cert.get("status") != "certified"
        or cert.get("classification") != "bounded subordinate optical source producer over every lawful regular z>0 coordinate tuple"
        or cert.get("kernel_claims") != KERNEL_CLAIMS or cert.get("mouth_scope") != MOUTH_SCOPE
        or cert.get("authorized_axioms") != sorted(ALLOWED)
        or set(cert.get("public_mouths", [])) != PUBLIC_MOUTHS):
        raise ValueError("covariance producer receipt schema or exact scope changed")
    bindings = cert["bindings"]
    required = [*CHAIN, HERE / "criterion-source-realization.md", HERE / "sources-source-realization.json",
                Path(__file__).resolve(), HERE / "phase_certify.py", HERE / "phase-certification.json",
                HERE / "chart-certification.json", HERE / "TrainingChartConsumer.lean",
                PROJECT / "lean-toolchain", PROJECT / "lake-manifest.json", PROJECT / "lakefile.toml"]
    if set(bindings) != {rel(p) for p in required}:
        raise ValueError("covariance receipt source-binding inventory changed")
    for name, row in bindings.items():
        path = (ROOT / name).resolve()
        if not path.is_relative_to(ROOT) or digest(path) != row["sha256"]:
            raise ValueError("covariance producer bound source changed: " + name)
        committed = subprocess.check_output(["git", "show", row["commit"] + ":" + name], cwd=ROOT)
        if committed != path.read_bytes():
            raise ValueError("covariance producer precompile source binding differs: " + name)
    for row in json.loads((HERE / "sources-source-realization.json").read_text())["inputs"]:
        if digest(ROOT / row["path"]) != row["sha256"]:
            raise ValueError("covariance context source binding changed: " + row["path"])
    source = cert["source_audit"]
    if (source["axiom_declarations_checked"] != source["source_declarations"] + source["independent_declarations"]
        or source["candidate_declarations"] <= 0 or source["independent_declarations"] <= 0
        or set(source["public_axioms"]) != PUBLIC_MOUTHS
        or any(not set(values) <= ALLOWED for values in source["public_axioms"].values())):
        raise ValueError("covariance producer Std3 summary changed")
    focus = cert["focused_verification"]
    if (focus["fresh_source_compilation"] is not True or focus["trust_level"] != 0
        or focus["warning_as_error"] is not True
        or [row["source"] for row in focus["commands"]] != [rel(p) for p in CHAIN]
        or any(row["exit_code"] != 0 for row in focus["commands"])):
        raise ValueError("covariance fresh-kernel receipt is incomplete")
    closure = cert["actual_import_closure"]
    if import_closure(source_root=closure["toolchain_source_root"]) != closure:
        raise ValueError("covariance actual import source binding changed")
    result.update({"evidence_valid": True, "source_realization_kernel_certified": True,
                   "all_legal_regular_coordinate_tuples_realizable_as_source": True,
                   "five_covariance_coordinates_read_back": True, "source_generated_all_cells_and_N5": True,
                   "certificate_schema": cert["schema"], "certificate_sha256": canonical_binding["sha256"],
                   "certificate_commit": canonical_binding["commit"],
                   "candidate_precompile_freezes": cert["candidate_precompile_freezes"],
                   "authorized_axioms": cert["authorized_axioms"],
                   "axiom_declarations_checked": source["axiom_declarations_checked"],
                   "producer_domain": MOUTH_SCOPE["producer_domain"]})
    return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--lsp-record", type=Path)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    parser.add_argument("--disabled", action="store_true")
    args = parser.parse_args()
    if args.check_only or args.disabled:
        print(json.dumps(consume(args.certificate, args.disabled), indent=2, ensure_ascii=False))
        return 0
    if args.certificate is not None or args.lsp_record is None:
        parser.error("generation requires --lsp-record; receipt consumption uses --check-only")
    owned = [HERE / "criterion-source-realization.md", HERE / "sources-source-realization.json", *CHAIN,
             Path(__file__).resolve(), HERE / "phase_certify.py", HERE / "phase-certification.json",
             HERE / "chart-certification.json", HERE / "TrainingChartConsumer.lean",
             PROJECT / "lean-toolchain", PROJECT / "lake-manifest.json", PROJECT / "lakefile.toml"]
    bindings = {rel(p): frozen(p) for p in owned}
    for p in CHAIN[:-1]:
        if digest(p) != EXPECTED[p.name]:
            raise ValueError("covariance source/candidate epoch differs: " + p.name)
    for name in ("criterion-source-realization.md", "sources-source-realization.json"):
        if subprocess.check_output(["git", "show", CRITERION_FREEZE + ":" + rel(HERE / name)],
                                   cwd=ROOT) != (HERE / name).read_bytes():
            raise ValueError("covariance source criterion differs from precompile freeze")
    source_manifest = json.loads((HERE / "sources-source-realization.json").read_text())
    for row in source_manifest["inputs"]:
        if digest(ROOT / row["path"]) != row["sha256"]:
            raise ValueError("covariance source context differs: " + row["path"])
    text = (HERE / "criterion-source-realization.md").read_text()
    block = text.split("<!-- COVARIANCE-SOURCE-FROZEN-BEGIN -->")[1].split(
        "<!-- COVARIANCE-SOURCE-FROZEN-END -->")[0].split("```json")[1].split("```")[0]
    contract = json.loads(block)
    for name in ("caller_angle_witness", "caller_source_endpoint", "z_zero_chart_claim",
                 "new_full_Born_kernel_claim", "new_statistical_coverage_kernel_claim",
                 "actual_hardware_identity", "controller_advance"):
        if contract[name] is not False:
            raise ValueError("covariance source claim changed: " + name)
    if contract["all_legal_regular_coordinate_tuples_generate_source"] is not True:
        raise ValueError("regular-coordinate producer contract weakened")
    for p in CHAIN:
        if FORBIDDEN.search(p.read_text()) or any("scratch" in module for module in imports(p)):
            raise ValueError("local covariance trust escape or scratch import: " + rel(p))
    lsp = json.loads(args.lsp_record.read_text())
    if lsp["candidate_sha256"] != EXPECTED["CovarianceSource.lean"]:
        raise ValueError("LSP metadata belongs to another covariance source candidate")
    env = json.loads(subprocess.check_output(
        ["lake", "env", "python3", "-c", "import json,os;print(json.dumps(dict(os.environ)))"],
        cwd=PROJECT, text=True))
    modules = import_closure(env)
    checks = []
    with tempfile.TemporaryDirectory(prefix="p23-cs-independent-certify-") as fresh:
        env["LEAN_PATH"] = fresh + os.pathsep + env.get("LEAN_PATH", "")
        for p in CHAIN:
            argv = ["lean", "--trust=0", "-DwarningAsError=true", "--root=" + str(p.parent),
                    "-o", str(Path(fresh) / (p.stem + ".olean")), str(p)]
            run = subprocess.run(argv, cwd=PROJECT, env=env, capture_output=True, text=True, timeout=240)
            log = run.stdout + run.stderr
            checks.append({"source": rel(p), "command": [s.replace(fresh, "${fresh_olean}") for s in argv],
                           "exit_code": run.returncode, "log_sha256": hashlib.sha256(log.encode()).hexdigest(),
                           "stderr": run.stderr,
                           "stdout": run.stdout if p.name != "CovarianceSourceCertification.lean" else "inventory parsed below"})
            print(p.name + " fresh trust0/werror exit=" + str(run.returncode), flush=True)
            if p.name == "CovarianceSourceCertification.lean":
                Path("/tmp/p23-cs-last-audit.log").write_text(log)
            if run.returncode:
                blocks = re.split(r"(?m)(?=^/[^\n]+\.lean:\d+:\d+: )", log)
                diagnostics = "\n".join(b for b in blocks
                    if re.match(r"^/[^\n]+\.lean:\d+:\d+: (?:error|warning):", b))
                print(diagnostics, flush=True)
                raise RuntimeError("focused covariance source certification failed: " + p.name)
            if p.name == "CovarianceSourceCertification.lean":
                audit = audit_log(log)
    for name, binding in bindings.items():
        if digest(ROOT / name) != binding["sha256"]:
            raise ValueError("source changed during covariance producer audit: " + name)
    for row in source_manifest["inputs"]:
        if digest(ROOT / row["path"]) != row["sha256"]:
            raise ValueError("source manifest context changed during covariance audit")
    if import_closure(env) != modules:
        raise ValueError("covariance transitive import source changed during certification")
    lint = subprocess.check_output(["python3", str(ROOT / ".agents/skills/lean-agent/scripts/theorem_mouth_lint.py"),
                                   *map(str, CHAIN[6:8]), "--fail-on", "never"], cwd=ROOT, text=True)
    report = {
        "schema": "p23-covariance-source-lean-certification/v1", "version": contract["version"],
        "status": "certified", "classification": "bounded subordinate optical source producer over every lawful regular z>0 coordinate tuple",
        "criterion_precompile_freeze": CRITERION_FREEZE,
        "candidate_precompile_freezes": {p.name: bindings[rel(p)]["commit"] for p in CHAIN[6:8]},
        "audit_preexecution_freeze": bindings[rel(HERE / "CovarianceSourceCertification.lean")]["commit"],
        "bindings": bindings, "actual_import_closure": modules, "authorized_axioms": sorted(ALLOWED),
        "source_audit": audit, "focused_verification": {"fresh_source_compilation": True,
            "trust_level": 0, "warning_as_error": True, "commands": checks, "lsp": lsp, "mouth_lint": lint},
        "public_mouths": sorted(audit["public_axioms"]),
        "kernel_claims": KERNEL_CLAIMS, "mouth_scope": MOUTH_SCOPE,
        "source_access": {"new_science_implementations_or_AST_read": False, "new_numerical_outputs_read": False,
                          "raw_event_files_read": 0, "external_or_hardware_contact": False},
    }
    output = HERE / "covariance-source-certification.json"
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False, allow_nan=False) + "\n")
    capsule = {"schema": "p23-covariance-source-certify-capsule/v1", "phase": "certify", "verdict": "certified",
               "classification": report["classification"], "certification_path": rel(output),
               "certification_sha256": digest(output), "public_mouths": report["public_mouths"],
               "candidate_precompile_freezes": report["candidate_precompile_freezes"],
               "audit_preexecution_freeze": report["audit_preexecution_freeze"],
               "machine_counts": {k: v for k, v in audit.items() if isinstance(v, int)},
               "kernel_claims": report["kernel_claims"], "mouth_scope": report["mouth_scope"], "lsp": lsp}
    (HERE / "covariance-source-audit-capsule.json").write_text(json.dumps(capsule, indent=2, ensure_ascii=False) + "\n")
    Path("/tmp/p23-cs-certify-capsule.json").write_text(json.dumps(capsule, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps({"status": "certified", **capsule["machine_counts"],
                      "actual_import_modules": modules["modules"], "certification_sha256": digest(output)}, indent=2), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
