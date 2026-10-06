#!/usr/bin/env python3
"""Independent nominal PC-off waveplate source and original detector-feed audit."""
from __future__ import annotations

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
ROOT = HERE.parents[7]
NOMINAL = HERE.parents[1]
CRITERION_FREEZE = "b806a5e095f178d57e2a7786cb34f6bfbbfa4278"
SOURCE_CONTEXT_FREEZE = "0919a10e64b2616358d7d26b83422f650f727406"
CANDIDATE_FREEZE = "1d77d45a0348571b1374fef83758cbf18bca37a6"
CHAIN = [NOMINAL/"gaussian-window/GaussianSource.lean",
         NOMINAL/"gaussian-window/native-effects/DetectorGamma.lean",
         *[HERE/name for name in ("WaveplateSource.lean", "WaveplateConsumer.lean", "Certification.lean")]]
LSP_HELPER = NOMINAL/"investigation/collected-source/certify.py"
LSP_INPUT = LSP_HELPER.parent/"verify.py"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def frozen(path: Path, commit: str) -> None:
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    original = subprocess.check_output(["git", "show", commit+":"+relative(path)], cwd=ROOT)
    if original != path.read_bytes():
        raise ValueError("waveplate source differs from its preexecution freeze: "+relative(path))


def committed(path: Path) -> dict:
    commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative(path)],
                                     cwd=ROOT, text=True).strip()
    if not commit:
        raise ValueError("waveplate audit source has no precompile freeze")
    frozen(path, commit)
    return {"commit": commit, "sha256": digest(path)}


def lsp(project: Path, env: dict) -> list:
    old_verify = sys.modules.pop("verify", None)
    sys.path.insert(0, str(LSP_HELPER.parent))
    try:
        spec = importlib.util.spec_from_file_location("p23_rc_independent_LSP", LSP_HELPER)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module.lsp_check(project, env, CHAIN)
    finally:
        sys.path.remove(str(LSP_HELPER.parent))
        sys.modules.pop("verify", None)
        if old_verify is not None:
            sys.modules["verify"] = old_verify


def main() -> int:
    frozen(HERE/"criterion.md", CRITERION_FREEZE)
    frozen(HERE/"sources.json", SOURCE_CONTEXT_FREEZE)
    for name in ("WaveplateSource.lean", "WaveplateConsumer.lean"):
        frozen(HERE/name, CANDIDATE_FREEZE)
    text = (HERE/"criterion.md").read_text()
    block = text.split("<!-- RC-FROZEN-BEGIN -->")[1].split("<!-- RC-FROZEN-END -->")[0]
    config = json.loads(block.split("```json")[1].split("```")[0])
    if config["version"] != "p23-receiver-control-source-rc0001" or config["measurement_scope"] != "ideal_nominal_PCoff_static_waveplate_recipe":
        raise ValueError("unexpected waveplate source scope")
    for name in ("recipe_controls_prove_argmax", "actual_source_or_hardware_identity_verified",
                 "PC_on_retarder_identified", "apparatus_optimum_verified", "controller_advance"):
        if config[name] is not False:
            raise ValueError("waveplate criterion claim changed: "+name)
    if config["retrospective"] is not True or any(type(config[name]) is not int or config[name] != 0
        for name in ("raw_event_archives_read", "archive_programs_executed")):
        raise ValueError("waveplate source access contract changed")
    source = json.loads((HERE/"sources.json").read_text())
    if source["schema"] != "p23-public-receiver-control-source-review/v1":
        raise ValueError("unexpected DAQ text source manifest")
    for name in ("actual_motor_config_in_these_archives", "actual_xor3_execution_record_identified",
                 "pc_axis_or_voltage_to_retardance_numeric_calibration_identified", "same_design_optimizer_executable_identified",
                 "generic_field_values_are_final_xor3_snapshot", "source_scripts_imported_or_executed",
                 "internal_network_endpoints_contacted", "new_model_calculations_executed",
                 "published_five_controls_used_for_fit_or_admission", "source_mapping_identified",
                 "apparatus_optimum_verified", "controller_advance"):
        if source[name] is not False:
            raise ValueError("public text source qualification changed: "+name)
    if type(source["trial_event_files_read"]) is not int or source["trial_event_files_read"] != 0:
        raise ValueError("event archive access changed")
    archives = {row["name"]: row for row in source["archives"]}
    if archives["bell_client.zip"]["sha256"] != config["source_archive_sha256"]:
        raise ValueError("waveplate archive descriptor binding differs")
    excerpts = []
    bindings = {}
    for row in [*source["extracts"], source["notice"]]:
        path = (HERE/row["path"]).resolve()
        if not path.is_relative_to(HERE) or digest(path) != row["sha256"] or path.stat().st_size != row["bytes"]:
            raise ValueError("source excerpt or notice binding differs: "+row["path"])
        excerpts.append(path)
        bindings[relative(path)] = row["sha256"]
    owned = [*CHAIN, Path(__file__).resolve(), HERE/"criterion.md", HERE/"sources.json", HERE/"sources.md", *excerpts,
             ROOT/"Lean/lean-toolchain", ROOT/"Lean/lake-manifest.json", LSP_HELPER, LSP_INPUT]
    freezes = {relative(path): committed(path) for path in owned}
    bindings.update({name: row["sha256"] for name, row in freezes.items()})
    project = ROOT/"Lean"
    env = json.loads(subprocess.check_output(
        ["lake", "env", "python3", "-c", "import json,os;print(json.dumps(dict(os.environ)))"], cwd=project, text=True))
    checks = []
    with tempfile.TemporaryDirectory(prefix="p23-rc-independent-certify-") as fresh:
        env["LEAN_PATH"] = fresh+os.pathsep+env.get("LEAN_PATH", "")
        for path in CHAIN:
            argv = ["lean", "--trust=0", "-DwarningAsError=true", "--root="+os.path.relpath(path.parent, project),
                    "-o", str(Path(fresh)/(path.stem+".olean")), os.path.relpath(path, project)]
            run = subprocess.run(argv, cwd=project, env=env, capture_output=True, text=True, timeout=180)
            shown = argv.copy()
            shown[5] = "${fresh_olean}/"+path.stem+".olean"
            checks.append({"source": relative(path), "command": shown, "exit_code": run.returncode,
                           "stdout": run.stdout, "stderr": run.stderr})
            print(path.name+" fresh trust0/werror exit="+str(run.returncode), flush=True)
            if run.returncode:
                print(run.stdout+run.stderr, flush=True)
                raise RuntimeError("focused waveplate source certification failed")
        diagnostics = lsp(project, env)
    for name, expected in bindings.items():
        if digest(ROOT/name) != expected:
            raise ValueError("source changed during waveplate certification: "+name)
    log = checks[-1]["stdout"]
    match = re.search(r"WAVEPLATE_SOURCE_CERTIFIED declarations=(\d+) main_nodes=(\d+) bundle_nodes=(\d+) required=(\d+) primitive=(\d+) source_body=(\d+)", log)
    independent = re.search(r"WAVEPLATE_SOURCE_INDEPENDENT_AXIOMS declarations=(\d+)", log)
    if match is None or independent is None:
        raise ValueError("waveplate primitive, source body or independent axiom audit missing")
    counts = dict(zip(("candidate_declarations", "main_dependency_nodes", "bundle_dependency_nodes",
                       "required_main_nodes", "primitive_nodes", "source_body_nodes"), map(int, match.groups())))
    counts["independent_declarations"] = int(independent.group(1))
    report = {
        "schema": "p23-receiver-control-lean-certification/v1", "version": "p23-receiver-control-source-rc0001",
        "status": "certified", "criterion_preexecution_freeze": CRITERION_FREEZE,
        "source_context_preexecution_freeze": SOURCE_CONTEXT_FREEZE, "candidate_precompile_freeze": CANDIDATE_FREEZE,
        "public_mouth": "P23.ReceiverControl.Consumer.waveplate_source_effect_consumer",
        "bindings": bindings, "execution_source_freezes": freezes,
        "source_archive_descriptors": {name: {key: row[key] for key in ("url", "sha256", "bytes")} for name, row in archives.items()},
        "authorized_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "focused_verification": {"fresh_source_compilation": True, "trust_level": 0, "warning_as_error": True,
                                 "commands": checks, "lsp": diagnostics},
        "source_audit": {**counts, "primitive": "two real mechanical HWP parameters and aligned/orthogonal QWP recipe enumeration",
            "effective_angle_or_completed_projector_in_primitive_or_Jones_body": False,
            "same_physical_Jones_pulled_port_unit_phase_projector_in_main_closure": True,
            "both_basis_source_effect_product_trace_transport_in_bundle": True,
            "original_onePhotonEffect_wordTensor_occupation_gamma_in_main_closure": True,
            "fullBorn_or_source_normalization_in_main_closure": False, "root_or_statistical_authority_in_bundle": False},
        "kernel_claims": {"physical_waveplate_recipe_generates_effective_angle_and_rank_one_effect": True,
            "quarter_global_phase_unit_modulus_generated": True,
            "arbitrary_complex_matrix_Born_equality": True, "arbitrary_finite_complex_source_vector_Born_equality": True,
            "same_signed_basis_source_effect_operator_product_and_trace_transport": True,
            "direct_original_no_click_one_photon_feed": True, "direct_original_gamma_feed_for_every_number_sector": True,
            "both_QWP_recipes_offset_half_angle_and_only_state_controls": True,
            "new_full_Fock_Born_kernel_identity": False, "PC_on_retarder_identity": False,
            "actual_motor_zero_or_hardware_identity": False, "receiver_or_pump_argmax_proved": False,
            "statistical_or_stationary_model_qualification": False, "root_activation": False},
        "declaration_classification": {
            "producer": ["quarterAxis", "nativeJones", "native_pulled_port", "native_effective_projector"],
            "readout": ["effectiveAngle", "actual_pose_born", "finite_source_born"],
            "transporter": ["transport_product", "transport_trace", "transport_born", "actual_one_photon_feed", "actual_all_sector_feed"],
            "direct_consumer": ["waveplate_source_effect_consumer"]},
        "scope": {"source": "ideal nominal PC-off static HWP-QWP-HWP chain in the physical H,V basis and final V port",
            "quarter_recipe": "axis 2*lastHWP or 2*lastHWP+pi/2; all real first/last HWP parameters",
            "effective_angle": "2*(lastHWP-firstHWP), generated before the projector comparison",
            "Born": "same matrix effect algebra for arbitrary complex rho and finite vectors; no new density or infinite-state probability law",
            "basis": "unitary signed quarter-turn applied to source, effect and products together",
            "all_sectors": "existing DetectorGamma is directly fed the generated real projector for every n",
            "public_text": "frozen excerpt/source descriptor binding only; no execution or independent certification of a historical apparatus snapshot",
            "actual_XOR3_execution_identified": False, "actual_hardware_verified": False, "PC_on_retarder_identified": False,
            "new_full_Fock_Born_kernel": False, "pump_or_receiver_controls_prove_argmax": False,
            "production_admitted": False, "apparatus_optimum_verified": False, "controller_advance": False},
        "source_access": {"archive_programs_imported_or_executed": False, "hardware_or_network_contacted": False,
                          "decoder_or_independent_decoder_executed_by_certification": False, "event_files_read": 0},
        "retrospective": True,
    }
    output = HERE/"certification.json"
    output.write_text(json.dumps(report, indent=2, ensure_ascii=False, allow_nan=False)+"\n")
    capsule = {"schema": "p23-native-waveplate-certify-capsule/v1", "phase": "certify", "verdict": "certified",
               "public_mouth": report["public_mouth"], "candidate_precompile_freeze": CANDIDATE_FREEZE,
               "certification_sha256": digest(output), "source_audit": report["source_audit"],
               "kernel_claims": report["kernel_claims"], "scope": report["scope"], "bindings": bindings}
    Path("/tmp/p23-rc-certify-capsule.json").write_text(json.dumps(capsule, indent=2, ensure_ascii=False))
    print(json.dumps({"status": report["status"], "source_audit": report["source_audit"],
                      "certification_sha256": capsule["certification_sha256"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
