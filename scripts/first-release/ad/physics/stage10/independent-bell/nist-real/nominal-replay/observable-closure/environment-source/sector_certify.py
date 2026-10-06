#!/usr/bin/env python3
"""Certify actual all-number paired sectors and internally generated symmetric image."""
from __future__ import annotations

import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

import env_certify as base

HERE = Path(__file__).resolve().parent
ROOT = base.ROOT
CRITERION_FREEZE = "d316af87ec22bc0b7bfad7d1d0669fee850e2db1"
CANDIDATE_FREEZE = "d9d396539b43fd0ff92171248ad9b56492e293f6"
CHAIN = [base.NOMINAL/"gaussian-window/GaussianSource.lean",
         base.NOMINAL/"gaussian-window/native-effects/DetectorGamma.lean",
         *[HERE/name for name in ("EnvironmentSource.lean", "SectorSource.lean", "SectorConsumer.lean", "SectorCertification.lean")]]


def main() -> int:
    for name in ("sector-criterion.md", "sector-sources.json"):
        base.frozen(HERE/name, CRITERION_FREEZE)
    for name in ("SectorSource.lean", "SectorConsumer.lean"):
        base.frozen(HERE/name, CANDIDATE_FREEZE)
    text = (HERE/"sector-criterion.md").read_text()
    block = text.split("<!-- SECTOR-FROZEN-BEGIN -->")[1].split("<!-- SECTOR-FROZEN-END -->")[0]
    config = json.loads(block.split("```json")[1].split("```")[0])
    if config["version"] != "p23-environment-sector-sp0001" or config["bob_transpose"] != "ordinary" or config["all_n_actual_sector_trace_identity_required"] is not True:
        raise ValueError("unexpected all-sector source contract")
    for name in ("completed_sector_trace_as_primitive", "completed_normalizer_as_primitive", "recurrence_claim",
                 "new_infinite_Born_or_determinant_claim", "controller_advance", "numeric_count_programs_or_outputs_read"):
        if config[name] is not False:
            raise ValueError("sector source scope changed: "+name)
    source = json.loads((HERE/"sector-sources.json").read_text())
    if source["schema"] != "p23-environment-sector-sources/v1" or source["version"] != config["version"]:
        raise ValueError("unexpected sector source manifest")
    if source["numeric_count_programs_or_outputs_read"] is not False or source["controller_advance"] is not False:
        raise ValueError("sector source access or authority changed")
    bindings = {row["path"]: row["sha256"] for row in source["inputs"]}
    for name, expected in bindings.items():
        path = (ROOT/name).resolve()
        if not path.is_relative_to(ROOT) or base.digest(path) != expected:
            raise ValueError("sector source upstream binding differs: "+name)
    owned = [*CHAIN, Path(__file__).resolve(), HERE/"env_certify.py", HERE/"sector-criterion.md", HERE/"sector-sources.json",
             ROOT/"Lean/lean-toolchain", ROOT/"Lean/lake-manifest.json", base.LSP_HELPER, base.LSP_INPUT]
    freezes = {base.relative(path): base.committed(path) for path in owned}
    bindings.update({name: row["sha256"] for name, row in freezes.items()})
    project = ROOT/"Lean"
    env = json.loads(subprocess.check_output(
        ["lake", "env", "python3", "-c", "import json,os;print(json.dumps(dict(os.environ)))"], cwd=project, text=True))
    checks = []
    with tempfile.TemporaryDirectory(prefix="p23-sp-independent-certify-") as fresh:
        env["LEAN_PATH"] = fresh+os.pathsep+env.get("LEAN_PATH", "")
        for path in CHAIN:
            argv = ["lean", "--trust=0", "-DwarningAsError=true", "--root="+os.path.relpath(path.parent, project),
                    "-o", str(Path(fresh)/(path.stem+".olean")), os.path.relpath(path, project)]
            run = subprocess.run(argv, cwd=project, env=env, capture_output=True, text=True, timeout=180)
            shown = argv.copy()
            shown[5] = "${fresh_olean}/"+path.stem+".olean"
            checks.append({"source": base.relative(path), "command": shown, "exit_code": run.returncode,
                           "stdout": run.stdout, "stderr": run.stderr})
            print(path.name+" fresh trust0/werror exit="+str(run.returncode), flush=True)
            if run.returncode:
                print(run.stdout+run.stderr, flush=True)
                raise RuntimeError("focused paired sector certification failed")
        base.CHAIN = CHAIN
        diagnostics = base.lsp(project, env)
    for name, expected in bindings.items():
        if base.digest(ROOT/name) != expected:
            raise ValueError("source changed during sector certification: "+name)
    log = checks[-1]["stdout"]
    match = re.search(r"PAIRED_SECTOR_CERTIFIED declarations=(\d+) main_nodes=(\d+) bundle_nodes=(\d+) required=(\d+) primitive=(\d+) source_body=(\d+)", log)
    independent = re.search(r"PAIRED_SECTOR_INDEPENDENT_AXIOMS declarations=(\d+)", log)
    if match is None or independent is None:
        raise ValueError("sector source primitive or independent axiom audit missing")
    counts = dict(zip(("candidate_declarations", "main_dependency_nodes", "bundle_dependency_nodes",
                       "required_main_nodes", "primitive_nodes", "source_body_nodes"), map(int, match.groups())))
    counts["independent_declarations"] = int(independent.group(1))
    report = {
        "schema": "p23-environment-sector-lean-certification/v1", "version": "p23-environment-sector-sp0001",
        "status": "certified", "criterion_preexecution_freeze": CRITERION_FREEZE,
        "candidate_precompile_freeze": CANDIDATE_FREEZE,
        "public_mouth": "P23.EnvironmentSource.Sector.Consumer.actual_ports_sector_consumer",
        "bindings": bindings, "execution_source_freezes": freezes,
        "authorized_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "focused_verification": {"fresh_source_compilation": True, "trust_level": 0, "warning_as_error": True,
                                 "commands": checks, "lsp": diagnostics},
        "source_audit": {**counts, "primitive": "original legal RawKernel, two EnvironmentPrim and real analyzer angles",
            "sector_trace_normalizer_or_symmetric_image_certificate_in_primitive": False,
            "symmetric_image_generated_by_matching_permutation_word_action_and_occupation": True,
            "SP_multiplication_ordinary_transpose_and_adjoint_in_main_closure": True,
            "same_original_sectorVector_phase_and_generated_sourceRoot_Z_in_main_closure": True,
            "actual_EV_number_port_Grams_and_sectorMass_budget_in_main_closure": True,
            "infinite_sum_or_Gaussian_determinant_in_main_closure": False,
            "root_or_statistical_authority_in_bundle": False},
        "kernel_claims": {"source_generated_symmetric_word_image": True,
            "internally_generated_symmetricPower_product_and_transpose_naturality": True,
            "original_normalized_RawKernel_sectorVector_factors_into_pairMatrix": True,
            "all_n_actual_pairedBlock_sectorBorn_equals_real_Z_symmetricTrace_product": True,
            "ordinary_Bob_transpose_complex_phase_preserved": True,
            "actual_number_port_Gram_and_original_sectorMass_bounds": True,
            "zero_one_symmetric_trace_readback": True,
            "complex_i_transpose_vacuum_zero_loss_and_same_product_controls": True,
            "symmetricTrace_recurrence": False, "new_infinite_Born_or_determinant_sum": False,
            "Gaussian_determinant_identity": False, "calibration_inverse": False,
            "actual_hardware_or_source_identity": False, "argmax_or_original_gate_pass": False, "root_activation": False},
        "declaration_classification": {
            "producer": ["matchingPerm", "word_action_same_count", "occupation_projection", "occupation_intertwines", "symmetricPower_mul", "sectorVector_factored", "paired_sector_trace", "environmentJointNoClick"],
            "readout": ["symmetricTrace_zero", "symmetricTrace_one", "environment_sector_identity"],
            "transporter": ["symmetricPower_transpose", "symmetricPower_conjTranspose"],
            "direct_consumer": ["actual_ports_sector_consumer", "sector_source_consumer"]},
        "scope": {"source": "same original RawKernel amplitudes and EV generated local no-click port Grams",
            "identity": "for every finite n, sectorBorn is Re(Z trace SP_n(D-adjoint XA D XB-transpose))",
            "normalization": "Z from tH/tV; original sectorMass budget retained; no completed normalizer premise",
            "symmetric_image": "occupation invariance is internally generated; no caller-supplied projection endpoint",
            "Bob": "ordinary transpose, separately controlled against the false adjoint replacement",
            "same_product_control": "transporter for equal generated products with the same RawKernel; does not generate product equality",
            "recurrence_claim": False, "new_infinite_Born_or_determinant_sum": False, "Gaussian_determinant_claim": False,
            "calibration_inverse_verified": False, "actual_hardware_verified": False, "actual_NIST_source_identified": False,
            "production_admitted": False, "apparatus_optimum_verified": False, "controller_advance": False},
        "numeric_count_programs_or_outputs_read": False,
    }
    output = HERE/"sector-certification.json"
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False, allow_nan=False)+"\n")
    capsule = {"schema": "p23-environment-sector-certify-capsule/v1", "phase": "certify", "verdict": "certified",
               "public_mouth": report["public_mouth"], "candidate_precompile_freeze": CANDIDATE_FREEZE,
               "certification_sha256": base.digest(output), "source_audit": report["source_audit"],
               "kernel_claims": report["kernel_claims"], "scope": report["scope"], "bindings": bindings}
    Path("/tmp/p23-sp-certify-capsule.json").write_text(json.dumps(capsule, indent=2, ensure_ascii=False))
    print(json.dumps({"status": report["status"], "source_audit": report["source_audit"],
                      "certification_sha256": capsule["certification_sha256"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
