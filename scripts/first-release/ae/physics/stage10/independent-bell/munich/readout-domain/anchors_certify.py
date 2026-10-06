"""Independent calibrated inverse-anchor certification and read-only receipt intake."""
from __future__ import annotations

import argparse
from collections import defaultdict, deque
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("frozen_readout_source_certificate", HERE / "kernel_certify.py")
source = importlib.util.module_from_spec(spec)
spec.loader.exec_module(source)
ROOT, LEAN_ROOT = source.ROOT, source.LEAN_ROOT
MODULE = "SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutAnchors"
CANDIDATE = source.candidate_path(MODULE)
AUDIT = HERE / "AnchorsCertification.lean"
DEFAULT_REPORT = HERE / "anchors-certification-first.json"
SCHEMA = "stage10-munich-readout-anchors-certification/v1"
MARKER = "BELL_ANCHORS_KERNEL_AUDIT|"
PUBLIC_MOUTH = MODULE + ".reconstruct_split_eq"
FLAGS = source.FLAGS
require = source.require


def validate_inventory(inventory: dict, paid: dict, accepted_source: dict) -> dict:
    require(inventory["candidate_modules"] == [MODULE], "wrong anchor candidate")
    own, consumers = inventory["owned_declarations"], inventory["independent_consumers"]
    require(bool(own) and bool(consumers), "empty anchor or independent consumer")
    require(len(set(own)) == len(own) and len(set(consumers)) == len(consumers), "duplicate anchor audit")
    accepted = {x["name"]: x["axioms"] for x in accepted_source["owned_declarations"]}
    require(not set(own).intersection(accepted), "anchor audit changes frozen source scope")
    delta, boundaries = inventory["dependency_delta"], inventory["paid_boundary"]
    require(len({x["name"] for x in delta}) == len(delta), "duplicate anchor dependency")
    graph = dict(paid)
    source_boundaries = []
    base_boundaries = []
    for entry in boundaries:
        if entry["name"] in accepted:
            require(entry["module"] in source.CANDIDATE_MODULES + ["SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutIdentification"], "source boundary ownership changed")
            require(entry["kind"] not in {"axiom", "unsafe-definition"}, "source boundary trust changed")
            graph[entry["name"]] = dict(entry, dependencies=accepted[entry["name"]])
            source_boundaries.append(entry)
        else:
            require(entry["name"] in paid and source.normalized_entry(entry) == source.normalized_entry(paid[entry["name"]]),
                    "paid base dependency identity changed")
            base_boundaries.append(entry)
    require(not set(x["name"] for x in delta).intersection(graph), "new audit overwrites paid declarations")
    graph.update({x["name"]: x for x in delta})
    require(set(own + consumers).issubset(graph), "missing anchor or consumer declaration")
    require(all(d in graph for x in graph.values() for d in x["dependencies"]), "open anchor dependency edge")
    require(MODULE in inventory["imported_modules"], "anchor import inventory incomplete")
    for module in inventory["imported_modules"]:
        require(not module.startswith(source.FORBIDDEN_MODULES), "empirical or scratch anchor import")
    for entry in delta:
        require(not entry["module"].startswith(source.FORBIDDEN_MODULES), "empirical anchor dependency")
        require(not entry["name"].startswith(source.FORBIDDEN_NAMES), "anchor kernel trust escape")
        require(entry["kind"] != "axiom" or entry["name"] in source.ALLOWED_AXIOMS, "unauthorized anchor axiom")
        require(not (entry["module"] == MODULE and entry["kind"] == "unsafe-definition"), "unsafe anchor primitive")
    declarations = source.explicit_declarations(CANDIDATE)
    require(len(declarations) == 40, "anchor 40 declaration scope changed")
    require(set(x["name"] for x in declarations).issubset(own), "anchor explicit declaration missed")
    for entry in declarations:
        expected = {"structure": "inductive", "def": "definition", "theorem": "theorem"}[entry["kind"]]
        require(graph[entry["name"]]["kind"] == expected, "anchor declaration kind changed")
    mouths = {x["name"]: x["type"] for x in inventory["public_mouths"]}
    require(PUBLIC_MOUTH in mouths and
            "SaturationMonoid.PhysicsCore.Stage10.Bell.AnchorsCertification.generalSourceSplitRecovery" in mouths,
            "generic or source-coupled anchor public mouth absent")
    parents = defaultdict(set)
    for entry in graph.values():
        for dependency in entry["dependencies"]:
            parents[dependency].add(entry["name"])
    axiom_map = defaultdict(set)
    for axiom in (n for n, entry in graph.items() if entry["kind"] == "axiom"):
        seen, queue = set(), deque([axiom])
        while queue:
            name = queue.popleft()
            if name not in seen:
                seen.add(name)
                axiom_map[name].add(axiom)
                queue.extend(parents[name])
    audited = lambda names: [{"name": n, "axioms": sorted(axiom_map[n])} for n in sorted(names)]
    return {"explicit_declarations": [dict(x, axioms=sorted(axiom_map[x["name"]])) for x in declarations],
            "owned_declarations": audited(own), "independent_consumers": audited(consumers),
            "axiom_union": sorted(set(a for n in own + consumers for a in axiom_map[n])),
            "public_mouths": inventory["public_mouths"],
            "compiler_only_module_symbols": sorted(inventory["compiler_only_module_symbols"]),
            "new_dependency_declaration_count": len(delta),
            "delegated_source_boundary_count": len(source_boundaries),
            "checked_base_boundary_count": len(base_boundaries),
            "dependency_delta_sha256": source.digest(source.json_bytes(sorted(delta, key=lambda x: x["name"]))),
            "source_boundary_sha256": source.digest(source.json_bytes(sorted(source_boundaries, key=lambda x: x["name"]))),
            "dependency_closure_method": "fresh new type/value graph; frozen source-owned axiom boundaries; exact-edge accepted base graph",
            "source_only_import_module_count": len(inventory["imported_modules"])}


def generate(checked_overlay: Path | None = None) -> dict:
    started = time.monotonic()
    accepted = source.consume()
    from identification_certify import consume as consume_id
    identification = consume_id()
    accepted = dict(accepted, owned_declarations=accepted["owned_declarations"] + identification["owned_declarations"])
    paid = source.base_graph(source.base_receipt())
    inputs = [source.binding(p) for p in (CANDIDATE, AUDIT, Path(__file__).resolve())]
    version = source.run(["lake", "env", "lean", "--version"]).strip()
    require(version == accepted["toolchain_version"], "anchor toolchain differs from frozen source")
    executable = source.run(["lake", "env", "which", "lean"]).strip()
    search = source.run(["lake", "env", "printenv", "LEAN_PATH"]).strip()
    old = None
    with tempfile.TemporaryDirectory(prefix="bell-anchor-certify-") as temporary:
        out = Path(temporary)
        source.proof_overlay(out, search)
        for module in source.CANDIDATE_MODULES:
            target = out / Path(*module.split(".")).with_suffix(".olean")
            artifact = checked_overlay / Path(*module.split(".")).with_suffix(".olean") if checked_overlay else None
            require(artifact is not None and artifact.is_file(), "frozen source export unavailable; supply its checked overlay")
            record = next(x for x in accepted["producer_compilation_evidence"] if x["module"] == module)
            require(source.digest(artifact.read_bytes()) == record["object_sha256"], "frozen source object identity changed")
            shutil.copyfile(artifact, target)
        id_module = "SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutIdentification"
        id_artifact = checked_overlay / Path(*id_module.split(".")).with_suffix(".olean")
        require(source.digest(id_artifact.read_bytes()) == identification["producer_compilation_evidence"]["compiled_object_sha256"],
                "paid ID source object identity changed")
        id_target = out / Path(*id_module.split(".")).with_suffix(".olean")
        if id_target.is_symlink():
            id_target.unlink()
        shutil.copyfile(id_artifact, id_target)
        candidate_object = out / Path(*MODULE.split(".")).with_suffix(".olean")
        if candidate_object.is_symlink():
            candidate_object.unlink()
        require(checked_overlay is not None, "fresh anchor certification needs a checked candidate capsule")
        capsule = json.loads((checked_overlay / "capsule.json").read_text())
        artifact = checked_overlay / Path(*MODULE.split(".")).with_suffix(".olean")
        require(capsule["candidate"] == source.relative(CANDIDATE) and capsule["phase"] == "strike", "wrong candidate capsule")
        require(capsule["candidate_sha256"] == source.digest(CANDIDATE.read_bytes()) and
                type(capsule["focused_exit_code"]) is int and capsule["focused_exit_code"] == 0,
                "focused anchor source or exit changed")
        require(capsule["focused_command"][0] == executable and all(x in capsule["focused_command"] for x in FLAGS),
                "focused anchor trust settings changed")
        require(source.digest(artifact.read_bytes()) == capsule["compiled_object_sha256"], "focused anchor object changed")
        stdout = (checked_overlay / "anchor-compile.log").read_text()
        require(source.digest(stdout.encode()) == capsule["compile_log_sha256"], "focused anchor diagnostics changed")
        require(capsule["actual_anchor_availability_asserted"] is False and
                capsule["actual_hardware_uniqueness_asserted"] is False, "candidate capsule promotes actual identity")
        shutil.copyfile(artifact, candidate_object)
        old = capsule
        boundary_file = out / "paid-names.json"
        boundary_file.write_bytes(source.json_bytes(sorted(set(paid) | {x['name'] for x in accepted['owned_declarations']})))
        env = dict(os.environ, LEAN_PATH=temporary + os.pathsep + search,
                   BELL_ANCHORS_PAID_NAMES=str(boundary_file))
        audit_stdout = source.run([executable, *FLAGS, "-DmaxHeartbeats=0", "-DmaxRecDepth=100000", str(AUDIT)], env=env)
    lines = [line[len(MARKER):] for line in audit_stdout.splitlines() if line.startswith(MARKER)]
    require(len(lines) == 1, "anchor dependency inventory missing or duplicated")
    inventory = validate_inventory(json.loads(lines[0]), paid, accepted)
    require(inputs == [source.binding(p) for p in (CANDIDATE, AUDIT, Path(__file__).resolve())], "anchor source changed during audit")
    require(accepted["source_bindings"] == source.consume()["source_bindings"] and identification == consume_id(),
            "frozen source or ID changed during anchor audit")
    return {"schema": SCHEMA, "evidence_valid": True,
            "status": "certified_law_derived_split_probe_inverse_and_conditional_uniqueness",
            "candidate_module": MODULE, "source_bindings": inputs, "toolchain_version": version,
            "focused_trust_level": 0, "warning_as_error": True, "asynchronous_elaboration": False, "lean_threads": 1,
            "fresh_candidate_and_general_consumer_checked": True, "all_owned_declarations_audited": True,
            "complete_new_dependency_closure_certified": True, "same_original_source_current_next_certified": True,
            "law_readouts_generate_inverse_coefficients_certified": True,
            "two_known_normalized_probes_required": True,
            "two_actual_signed_response_means_required": True,
            "nonzero_law_derived_determinant_required": True,
            "different_setting_nonzero_product_anchors_certified": True,
            "all_four_effects_reconstructed_from_law_and_means_certified": True,
            "all_nonzero_signed_scale_branches_covered": True,
            "split_pole_domain_nonempty_certified": True,
            "singular_opposite_probe_control_certified": True,
            "probe_probabilities_physical_and_normalized_certified": True,
            "original_source_ledger_and_next_certified": True,
            "actual_independent_anchor_inputs_available": False,
            "actual_hardware_uniquely_identified": False,
            "atomic_response_forward_model_kernel_proved": False,
            "atomic_detector_self_calibration_kernel_proved": False,
            "new_statistical_interval_coverage_kernel_proved": False,
            "controller_advance": False, "empirical_fit_executed": False,
            "trial_event_files_read": 0, "new_statistical_tables_read": 0,
            "frozen_source_receipt": {"path": source.relative(source.DEFAULT_REPORT),
                                      "sha256": source.digest(source.DEFAULT_REPORT.read_bytes()),
                                      "explicit_declarations": 115, "source_recompiled": False},
            "frozen_identification_receipt": {"path": source.relative(HERE / "identification-certification-first.json"),
                                              "sha256": source.digest((HERE / "identification-certification-first.json").read_bytes())},
            "producer_compilation_evidence": old, "independent_audit_stdout_sha256": source.digest(audit_stdout.encode()),
            "elapsed_seconds": round(time.monotonic() - started, 3), **inventory}


def validate_payload(report: dict) -> None:
    require(report.get("schema") == SCHEMA and report.get("candidate_module") == MODULE, "wrong anchor receipt")
    true_fields = ("evidence_valid", "warning_as_error", "fresh_candidate_and_general_consumer_checked", "all_owned_declarations_audited",
                   "complete_new_dependency_closure_certified", "same_original_source_current_next_certified",
                   "law_readouts_generate_inverse_coefficients_certified", "two_known_normalized_probes_required",
                   "two_actual_signed_response_means_required", "nonzero_law_derived_determinant_required",
                   "different_setting_nonzero_product_anchors_certified", "all_four_effects_reconstructed_from_law_and_means_certified",
                   "all_nonzero_signed_scale_branches_covered", "split_pole_domain_nonempty_certified",
                   "singular_opposite_probe_control_certified", "probe_probabilities_physical_and_normalized_certified",
                   "original_source_ledger_and_next_certified")
    require(all(report.get(k) is True for k in true_fields), "anchor receipt lost an obligation")
    false_fields = ("asynchronous_elaboration", "actual_independent_anchor_inputs_available", "actual_hardware_uniquely_identified",
                    "atomic_response_forward_model_kernel_proved", "atomic_detector_self_calibration_kernel_proved",
                    "new_statistical_interval_coverage_kernel_proved", "controller_advance", "empirical_fit_executed")
    require(all(report.get(k) is False for k in false_fields), "anchor receipt scope was promoted")
    for key, value in (("focused_trust_level", 0), ("lean_threads", 1), ("trial_event_files_read", 0), ("new_statistical_tables_read", 0)):
        require(type(report.get(key)) is int and report[key] == value, "anchor receipt invalid literal")
    require(len(report["explicit_declarations"]) == 40 and bool(report["owned_declarations"]) and bool(report["independent_consumers"]),
            "anchor receipt declaration scope changed")
    require(set(report["axiom_union"]).issubset(source.ALLOWED_AXIOMS), "anchor receipt unauthorized axioms")


def consume(certificate: Path | None = None, *, require_frozen: bool = True) -> dict:
    canonical = DEFAULT_REPORT.read_bytes()
    require(certificate is None or certificate.read_bytes() == canonical, "anchor override changes canonical receipt")
    if require_frozen:
        committed = subprocess.run(["git", "show", f"HEAD:{source.relative(DEFAULT_REPORT)}"], cwd=ROOT,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        require(committed.returncode == 0 and committed.stdout == canonical, "anchor receipt is not frozen at HEAD")
    report = json.loads(canonical)
    validate_payload(report)
    accepted = source.consume()
    from identification_certify import consume as consume_id
    consume_id()
    require(report["frozen_identification_receipt"]["sha256"] == source.digest((HERE / "identification-certification-first.json").read_bytes()),
            "frozen ID receipt changed")
    require(report["toolchain_version"] == accepted["toolchain_version"], "anchor source toolchain changed")
    require(report["frozen_source_receipt"]["sha256"] == source.digest(source.DEFAULT_REPORT.read_bytes()), "frozen source receipt changed")
    for item in report["source_bindings"]:
        require(source.digest((ROOT / item["path"]).read_bytes()) == item["sha256"], "anchor certified source changed")
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=DEFAULT_REPORT)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    parser.add_argument("--checked-overlay", type=Path)
    args = parser.parse_args()
    if args.check_only:
        report = consume(args.certificate)
    else:
        require(args.certificate is None, "anchor overrides are intake-only")
        report = generate(args.checked_overlay)
        with args.out.open("x") as output:
            json.dump(report, output, indent=2, ensure_ascii=False)
            output.write("\n")
    print(json.dumps({"evidence_valid": report["evidence_valid"], "status": report["status"],
                      "explicit_declarations": len(report["explicit_declarations"]),
                      "owned_declarations": len(report["owned_declarations"])}))


if __name__ == "__main__":
    main()
