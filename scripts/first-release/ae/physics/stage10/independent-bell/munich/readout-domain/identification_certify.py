"""Independent generated-law identification certification and read-only receipt intake."""
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
MODULE = "SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutIdentification"
CANDIDATE = source.candidate_path(MODULE)
AUDIT = HERE / "IdentificationCertification.lean"
DEFAULT_REPORT = HERE / "identification-certification-first.json"
SCHEMA = "stage10-munich-readout-identification-certification/v1"
MARKER = "BELL_IDENTIFICATION_KERNEL_AUDIT|"
PUBLIC_MOUTH = MODULE + ".sameOccurrenceIdentification"
FLAGS = source.FLAGS
require = source.require


def validate_inventory(inventory: dict, paid: dict, accepted_source: dict) -> dict:
    require(inventory["candidate_modules"] == [MODULE], "wrong identification candidate")
    own, consumers = inventory["owned_declarations"], inventory["independent_consumers"]
    require(bool(own) and bool(consumers), "empty identification or independent consumer")
    require(len(set(own)) == len(own) and len(set(consumers)) == len(consumers), "duplicate identification audit")
    accepted = {x["name"]: x["axioms"] for x in accepted_source["owned_declarations"]}
    require(not set(own).intersection(accepted), "identification audit changes frozen source scope")
    delta, boundaries = inventory["dependency_delta"], inventory["paid_boundary"]
    require(len({x["name"] for x in delta}) == len(delta), "duplicate identification dependency")
    graph = dict(paid)
    source_boundaries = []
    base_boundaries = []
    for entry in boundaries:
        if entry["name"] in accepted:
            require(entry["module"] in source.CANDIDATE_MODULES, "source boundary ownership changed")
            require(entry["kind"] not in {"axiom", "unsafe-definition"}, "source boundary trust changed")
            graph[entry["name"]] = dict(entry, dependencies=accepted[entry["name"]])
            source_boundaries.append(entry)
        else:
            require(entry["name"] in paid and source.normalized_entry(entry) == source.normalized_entry(paid[entry["name"]]),
                    "paid base dependency identity changed")
            base_boundaries.append(entry)
    require(not set(x["name"] for x in delta).intersection(graph), "new audit overwrites paid declarations")
    graph.update({x["name"]: x for x in delta})
    require(set(own + consumers).issubset(graph), "missing identification or consumer declaration")
    require(all(d in graph for x in graph.values() for d in x["dependencies"]), "open identification dependency edge")
    require(MODULE in inventory["imported_modules"], "identification import inventory incomplete")
    for module in inventory["imported_modules"]:
        require(not module.startswith(source.FORBIDDEN_MODULES), "empirical or scratch identification import")
    for entry in delta:
        require(not entry["module"].startswith(source.FORBIDDEN_MODULES), "empirical identification dependency")
        require(not entry["name"].startswith(source.FORBIDDEN_NAMES), "identification kernel trust escape")
        require(entry["kind"] != "axiom" or entry["name"] in source.ALLOWED_AXIOMS, "unauthorized identification axiom")
        require(not (entry["module"] == MODULE and entry["kind"] == "unsafe-definition"), "unsafe identification primitive")
    declarations = source.explicit_declarations(CANDIDATE)
    require(len(declarations) == 46, "identification 46 declaration scope changed")
    require(set(x["name"] for x in declarations).issubset(own), "identification explicit declaration missed")
    for entry in declarations:
        expected = {"structure": "inductive", "def": "definition", "theorem": "theorem"}[entry["kind"]]
        require(graph[entry["name"]]["kind"] == expected, "identification declaration kind changed")
    mouths = {x["name"]: x["type"] for x in inventory["public_mouths"]}
    require(inventory.get("closed_public_mouth") is True, "identification public mouth is conditional")
    require(mouths.get(PUBLIC_MOUTH) == "SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutIdentification.SameOccurrenceIdentification",
            "identification public mouth changed")
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
    paid = source.base_graph(source.base_receipt())
    inputs = [source.binding(p) for p in (CANDIDATE, AUDIT, Path(__file__).resolve())]
    version = source.run(["lake", "env", "lean", "--version"]).strip()
    require(version == accepted["toolchain_version"], "identification toolchain differs from frozen source")
    executable = source.run(["lake", "env", "which", "lean"]).strip()
    search = source.run(["lake", "env", "printenv", "LEAN_PATH"]).strip()
    old = None
    with tempfile.TemporaryDirectory(prefix="bell-identification-certify-") as temporary:
        out = Path(temporary)
        source.proof_overlay(out, search)
        for module in source.CANDIDATE_MODULES:
            target = out / Path(*module.split(".")).with_suffix(".olean")
            artifact = checked_overlay / Path(*module.split(".")).with_suffix(".olean") if checked_overlay else None
            require(artifact is not None and artifact.is_file(), "frozen source export unavailable; supply its checked overlay")
            record = next(x for x in accepted["producer_compilation_evidence"] if x["module"] == module)
            require(source.digest(artifact.read_bytes()) == record["object_sha256"], "frozen source object identity changed")
            shutil.copyfile(artifact, target)
        candidate_object = out / Path(*MODULE.split(".")).with_suffix(".olean")
        if candidate_object.is_symlink():
            candidate_object.unlink()
        if checked_overlay is not None:
            evidence = json.loads((checked_overlay / "environment.json").read_text())
            old = evidence["identification_compile"]
            artifact = checked_overlay / Path(*MODULE.split(".")).with_suffix(".olean")
            require(old["candidate_sha256"] == source.digest(CANDIDATE.read_bytes()) and old["exit_code"] == 0,
                    "focused identification source or exit changed")
            require(old["command"][0] == executable and all(x in old["command"] for x in FLAGS),
                    "focused identification trust settings changed")
            require(source.digest(artifact.read_bytes()) == old["compiled_object_sha256"], "focused identification object changed")
            stdout = (checked_overlay / "identification-compile.log").read_text()
            require(source.digest(stdout.encode()) == old["output_sha256"], "focused identification diagnostics changed")
            shutil.copyfile(artifact, candidate_object)
        else:
            raise ValueError("fresh identification certification requires its independently checked source overlay")
        boundary_file = out / "paid-names.json"
        boundary_file.write_bytes(source.json_bytes(sorted(set(paid) | {x['name'] for x in accepted['owned_declarations']})))
        env = dict(os.environ, LEAN_PATH=temporary + os.pathsep + search,
                   BELL_IDENTIFICATION_PAID_NAMES=str(boundary_file))
        audit_stdout = source.run([executable, *FLAGS, "-DmaxHeartbeats=0", "-DmaxRecDepth=100000", str(AUDIT)], env=env)
    lines = [line[len(MARKER):] for line in audit_stdout.splitlines() if line.startswith(MARKER)]
    require(len(lines) == 1, "identification dependency inventory missing or duplicated")
    inventory = validate_inventory(json.loads(lines[0]), paid, accepted)
    require(inputs == [source.binding(p) for p in (CANDIDATE, AUDIT, Path(__file__).resolve())], "identification source changed during audit")
    require(accepted == source.consume(), "frozen source changed during identification audit")
    return {"schema": SCHEMA, "evidence_valid": True, "status": "certified_same_occurrence_maximal_quotient_and_complete_regular_fiber",
            "candidate_module": MODULE, "source_bindings": inputs, "toolchain_version": version,
            "focused_trust_level": 0, "warning_as_error": True, "asynchronous_elaboration": False, "lean_threads": 1,
            "fresh_candidate_and_general_consumer_checked": True, "all_owned_declarations_audited": True,
            "complete_new_dependency_closure_certified": True, "same_original_source_current_next_certified": True,
            "closed_public_mouth_certified": True,
            "global_full_law_iff_identified_quotient_certified": True,
            "all_generated_law_quotient_recovery_certified": True,
            "primitive_cone_scales_construct_legal_family_certified": True,
            "all_nonzero_signed_scale_branches_source_current_next_preserved": True,
            "regular_fiber_complete_constructor_and_unique_scales_certified": True,
            "uniform_rank_one_all_indices_certified": True,
            "regular_source_domain_nonempty_certified": True,
            "regular_anchor_required_for_complete_scale_fiber": True,
            "inverse_input_requires_two_legal_generated_families": True,
            "arbitrary_target_probability_table_used": False,
            "actual_empirical_probability_identified": False,
            "actual_hardware_uniquely_identified": False,
            "new_confidence_or_statistical_projection_kernel_proved": False,
            "controller_advance": False, "empirical_fit_executed": False,
            "trial_event_files_read": 0, "new_statistical_tables_read": 0,
            "frozen_source_receipt": {"path": source.relative(source.DEFAULT_REPORT),
                                      "sha256": source.digest(source.DEFAULT_REPORT.read_bytes()),
                                      "explicit_declarations": 115, "source_recompiled": False},
            "producer_compilation_evidence": old, "independent_audit_stdout_sha256": source.digest(audit_stdout.encode()),
            "elapsed_seconds": round(time.monotonic() - started, 3), **inventory}


def validate_payload(report: dict) -> None:
    require(report.get("schema") == SCHEMA and report.get("candidate_module") == MODULE, "wrong identification receipt")
    true_fields = ("evidence_valid", "warning_as_error", "fresh_candidate_and_general_consumer_checked", "all_owned_declarations_audited",
                   "complete_new_dependency_closure_certified", "same_original_source_current_next_certified",
                   "closed_public_mouth_certified", "global_full_law_iff_identified_quotient_certified",
                   "all_generated_law_quotient_recovery_certified", "primitive_cone_scales_construct_legal_family_certified",
                   "all_nonzero_signed_scale_branches_source_current_next_preserved",
                   "regular_fiber_complete_constructor_and_unique_scales_certified", "uniform_rank_one_all_indices_certified",
                   "regular_source_domain_nonempty_certified", "regular_anchor_required_for_complete_scale_fiber",
                   "inverse_input_requires_two_legal_generated_families")
    require(all(report.get(k) is True for k in true_fields), "identification receipt lost an obligation")
    false_fields = ("asynchronous_elaboration", "arbitrary_target_probability_table_used", "actual_empirical_probability_identified",
                    "actual_hardware_uniquely_identified", "new_confidence_or_statistical_projection_kernel_proved",
                    "controller_advance", "empirical_fit_executed")
    require(all(report.get(k) is False for k in false_fields), "identification receipt scope was promoted")
    for key, value in (("focused_trust_level", 0), ("lean_threads", 1), ("trial_event_files_read", 0), ("new_statistical_tables_read", 0)):
        require(type(report.get(key)) is int and report[key] == value, "identification receipt invalid literal")
    require(len(report["explicit_declarations"]) == 46 and bool(report["owned_declarations"]) and bool(report["independent_consumers"]),
            "identification receipt declaration scope changed")
    require(set(report["axiom_union"]).issubset(source.ALLOWED_AXIOMS), "identification receipt unauthorized axioms")


def consume(certificate: Path | None = None, *, require_frozen: bool = True) -> dict:
    canonical = DEFAULT_REPORT.read_bytes()
    require(certificate is None or certificate.read_bytes() == canonical, "identification override changes canonical receipt")
    if require_frozen:
        committed = subprocess.run(["git", "show", f"HEAD:{source.relative(DEFAULT_REPORT)}"], cwd=ROOT,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        require(committed.returncode == 0 and committed.stdout == canonical, "identification receipt is not frozen at HEAD")
    report = json.loads(canonical)
    validate_payload(report)
    accepted = source.consume()
    require(report["toolchain_version"] == accepted["toolchain_version"], "identification source toolchain changed")
    require(report["frozen_source_receipt"]["sha256"] == source.digest(source.DEFAULT_REPORT.read_bytes()), "frozen source receipt changed")
    for item in report["source_bindings"]:
        require(source.digest((ROOT / item["path"]).read_bytes()) == item["sha256"], "identification certified source changed")
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
        require(args.certificate is None, "identification overrides are intake-only")
        report = generate(args.checked_overlay)
        with args.out.open("x") as output:
            json.dump(report, output, indent=2, ensure_ascii=False)
            output.write("\n")
    print(json.dumps({"evidence_valid": report["evidence_valid"], "status": report["status"],
                      "explicit_declarations": len(report["explicit_declarations"]),
                      "owned_declarations": len(report["owned_declarations"])}))


if __name__ == "__main__":
    main()
