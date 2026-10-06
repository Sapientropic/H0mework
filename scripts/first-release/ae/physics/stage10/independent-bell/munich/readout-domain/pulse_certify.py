"""Independent primitive-response realizer certification and read-only receipt intake."""
from __future__ import annotations

import argparse
from collections import defaultdict, deque
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("frozen_readout_source_certificate", HERE / "kernel_certify.py")
source = importlib.util.module_from_spec(spec)
spec.loader.exec_module(source)
ROOT, LEAN_ROOT = source.ROOT, source.LEAN_ROOT
MODULE = "SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutPulseRealization"
CANDIDATE = source.candidate_path(MODULE)
AUDIT = HERE / "PulseCertification.lean"
DEFAULT_REPORT = HERE / "pulse-certification-first.json"
SCHEMA = "stage10-munich-readout-pulse-certification/v1"
MARKER = "BELL_PULSE_KERNEL_AUDIT|"
PUBLIC_MOUTH = MODULE + ".realized_effect_eq"
FLAGS = source.FLAGS
PAID_MODULE = "SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutDetectorFiber"
REQUIRED_MOUTHS = (PUBLIC_MOUTH, MODULE + ".feasible_iff_rates", MODULE + ".feasible_iff_squared",
                   MODULE + ".feasible_monotone", MODULE + ".pulse_realizes",
                   MODULE + ".atomic_effect_injective", MODULE + ".two_spectra_same_effect",
                   "SaturationMonoid.PhysicsCore.Stage10.Bell.PulseCertification.generalSameSourceCurrentNext",
                   "SaturationMonoid.PhysicsCore.Stage10.Bell.PulseCertification.nonemptyDistinctRealizers")

require = source.require


def validate_inventory(inventory: dict, paid: dict, accepted_source: dict) -> dict:
    require(inventory["candidate_modules"] == [MODULE], "wrong pulse candidate")
    own, consumers = inventory["owned_declarations"], inventory["independent_consumers"]
    require(bool(own) and bool(consumers), "empty pulse or independent consumer")
    require(len(set(own)) == len(own) and len(set(consumers)) == len(consumers), "duplicate pulse audit")
    accepted = {x["name"]: x["axioms"] for x in accepted_source["owned_declarations"]}
    require(not set(own).intersection(accepted), "pulse audit changes frozen source scope")
    delta, boundaries = inventory["dependency_delta"], inventory["paid_boundary"]
    require(len({x["name"] for x in delta}) == len(delta), "duplicate pulse dependency")
    require(len({x["name"] for x in boundaries}) == len(boundaries), "duplicate pulse paid boundary")
    graph = dict(paid)
    source_boundaries = []
    base_boundaries = []
    for entry in boundaries:
        if entry["name"] in accepted:
            require(entry["module"] in source.CANDIDATE_MODULES + [PAID_MODULE], "source boundary ownership changed")
            require(entry["kind"] not in {"axiom", "unsafe-definition"}, "source boundary trust changed")
            graph[entry["name"]] = dict(entry, dependencies=accepted[entry["name"]])
            source_boundaries.append(entry)
        else:
            require(entry["name"] in paid and source.normalized_entry(entry) == source.normalized_entry(paid[entry["name"]]),
                    "paid base dependency identity changed")
            base_boundaries.append(entry)
    require(not set(x["name"] for x in delta).intersection(graph), "new audit overwrites paid declarations")
    graph.update({x["name"]: x for x in delta})
    require(set(own + consumers).issubset(graph), "missing pulse or consumer declaration")
    require(all(d in graph for x in graph.values() for d in x["dependencies"]), "open pulse dependency edge")
    require(MODULE in inventory["imported_modules"], "pulse import inventory incomplete")
    for module in inventory["imported_modules"]:
        require(not module.startswith(source.FORBIDDEN_MODULES), "empirical or scratch pulse import")
    for entry in delta:
        require(not entry["module"].startswith(source.FORBIDDEN_MODULES), "empirical pulse dependency")
        require(not entry["name"].startswith(source.FORBIDDEN_NAMES), "pulse kernel trust escape")
        require(entry["kind"] != "axiom" or entry["name"] in source.ALLOWED_AXIOMS, "unauthorized pulse axiom")
        require(not (entry["module"] == MODULE and entry["kind"] == "unsafe-definition"), "unsafe pulse primitive")
    declarations = source.explicit_declarations(CANDIDATE)
    require(set(x["name"] for x in declarations).issubset(own), "pulse explicit declaration missed")
    for entry in declarations:
        expected = {"structure": "inductive", "def": "definition", "theorem": "theorem"}[entry["kind"]]
        require(graph[entry["name"]]["kind"] == expected, "pulse declaration kind changed")
    mouths = {x["name"]: x["type"] for x in inventory["public_mouths"]}
    require(set(REQUIRED_MOUTHS).issubset(mouths), "generic or source-coupled pulse public mouth absent")
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
    from detector_certify import consume as consume_df
    df = consume_df()
    accepted = dict(accepted, owned_declarations=accepted["owned_declarations"] + df["owned_declarations"])
    paid = source.base_graph(source.base_receipt())
    inputs = [source.binding(p) for p in (CANDIDATE, AUDIT, Path(__file__).resolve())]
    version = source.run(["lake", "env", "lean", "--version"]).strip()
    require(version == accepted["toolchain_version"], "pulse toolchain differs from frozen source")
    executable = source.run(["lake", "env", "which", "lean"]).strip()
    search = source.run(["lake", "env", "printenv", "LEAN_PATH"]).strip()
    old = None
    with tempfile.TemporaryDirectory(prefix="bell-pulse-certify-") as temporary:
        out = Path(temporary)
        source.proof_overlay(out, search)
        for module in source.CANDIDATE_MODULES:
            target = out / Path(*module.split(".")).with_suffix(".olean")
            artifact = checked_overlay / Path(*module.split(".")).with_suffix(".olean") if checked_overlay else None
            require(artifact is not None and artifact.is_file(), "frozen source export unavailable; supply its checked overlay")
            record = next(x for x in accepted["producer_compilation_evidence"] if x["module"] == module)
            require(source.digest(artifact.read_bytes()) == record["object_sha256"], "frozen source object identity changed")
            shutil.copyfile(artifact, target)
        df_object = checked_overlay / Path(*PAID_MODULE.split(".")).with_suffix(".olean")
        require(source.digest(df_object.read_bytes()) == df["producer_compilation_evidence"]["compiled_object_sha256"],
                "frozen detector object identity changed")
        df_target = out / Path(*PAID_MODULE.split(".")).with_suffix(".olean")
        if df_target.is_symlink():
            df_target.unlink()
        shutil.copyfile(df_object, df_target)
        candidate_object = out / Path(*MODULE.split(".")).with_suffix(".olean")
        if candidate_object.is_symlink():
            candidate_object.unlink()
        require(checked_overlay is not None, "fresh pulse certification needs a checked candidate capsule")
        capsule = json.loads((checked_overlay / "capsule.json").read_text())
        artifact = checked_overlay / Path(*MODULE.split(".")).with_suffix(".olean")
        require(capsule["candidate"] == source.relative(CANDIDATE) and capsule["phase"] == "strike", "wrong candidate capsule")
        require(capsule["candidate_sha256"] == source.digest(CANDIDATE.read_bytes()) and
                type(capsule["focused_exit_code"]) is int and capsule["focused_exit_code"] == 0,
                "focused pulse source or exit changed")
        require(capsule["focused_command"][0] == executable and capsule["focused_command"][1:1+len(FLAGS)] == FLAGS,
                "focused pulse trust settings changed")
        require(source.digest(artifact.read_bytes()) == capsule["compiled_object_sha256"], "focused pulse object changed")
        stdout = (checked_overlay / "realization-compile.log").read_text()
        require(source.digest(stdout.encode()) == capsule["compile_log_sha256"], "focused pulse diagnostics changed")
        require(capsule["controller_advance"] is False and
                capsule["actual_hardware_uniqueness_asserted"] is False, "candidate capsule promotes actual identity")
        shutil.copyfile(artifact, candidate_object)
        old = capsule
        boundary_file = out / "paid-names.json"
        boundary_file.write_bytes(source.json_bytes(sorted(set(paid) | {x['name'] for x in accepted['owned_declarations']})))
        env = dict(os.environ, LEAN_PATH=temporary + os.pathsep + search,
                   BELL_PULSE_PAID_NAMES=str(boundary_file))
        result = subprocess.run([executable, *FLAGS, "-DmaxHeartbeats=0", "-DmaxRecDepth=100000", str(AUDIT)],
                                cwd=LEAN_ROOT, env=env, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=600)
        audit_stdout = result.stdout
        audit_log = Path(tempfile.gettempdir()) / ("bell-pulse-audit-" + source.digest(AUDIT.read_bytes()) + ".log")
        audit_log.write_text(audit_stdout)
        diagnostics = "\n".join(line for line in audit_stdout.splitlines() if not line.startswith(MARKER))
        require(result.returncode == 0, "focused pulse consumer failed: " + diagnostics[:10000])
        require(not re.search(r"(?m)\b(?:error|warning):", audit_stdout), "focused pulse consumer diagnostic")
    lines = [line[len(MARKER):] for line in audit_stdout.splitlines() if line.startswith(MARKER)]
    require(len(lines) == 1, "pulse dependency inventory missing or duplicated")
    inventory = validate_inventory(json.loads(lines[0]), paid, accepted)
    require(inputs == [source.binding(p) for p in (CANDIDATE, AUDIT, Path(__file__).resolve())], "pulse source changed during audit")
    require(accepted["source_bindings"] == source.consume()["source_bindings"] and df == consume_df(),
            "frozen source or detector changed during pulse audit")
    return {"schema": SCHEMA, "evidence_valid": True,
            "status": "certified_primitive_response_realizer_and_complete_native_feasibility",
            "candidate_module": MODULE, "source_bindings": inputs, "toolchain_version": version,
            "focused_trust_level": 0, "warning_as_error": True, "asynchronous_elaboration": False, "lean_threads": 1,
            "fresh_candidate_and_general_consumer_checked": True, "all_owned_declarations_audited": True,
            "complete_new_dependency_closure_certified": True, "same_original_source_current_next_certified": True,
            "primitive_bright_dark_response_required": True,
            "positive_source_gain_required": True,
            "native_feasibility_iff_generated_legal_detector_rates": True,
            "squared_source_coordinates_feasibility_certified": True,
            "whole_response_box_worst_corner_transport_certified": True,
            "faithful_same_source_effect_realization_certified": True,
            "distinct_feasible_response_realizers_certified": True,
            "nonempty_math_response_realizer_certified": True,
            "original_source_ledger_and_next_certified": True,
            "detector_factors_scoped_per_role": True,
            "actual_hardware_uniquely_identified": False,
            "actual_raw_pulse_inputs_available": False,
            "shared_detector_factors_between_settings_certified": False,
            "atomic_response_forward_model_kernel_proved": False,
            "new_statistical_interval_coverage_kernel_proved": False,
            "controller_advance": False, "empirical_fit_executed": False,
            "trial_event_files_read": 0, "new_statistical_tables_read": 0,
            "frozen_source_receipt": {"path": source.relative(source.DEFAULT_REPORT),
                                      "sha256": source.digest(source.DEFAULT_REPORT.read_bytes()),
                                      "explicit_declarations": 115, "source_recompiled": False},
            "frozen_detector_receipt": {"path": source.relative(HERE / "detector-certification-first.json"),
                                        "sha256": source.digest((HERE / "detector-certification-first.json").read_bytes()),
                                        "owned_declarations": len(df["owned_declarations"]), "source_recompiled": False},
            "producer_compilation_evidence": old, "independent_audit_stdout_sha256": source.digest(audit_stdout.encode()),
            "elapsed_seconds": round(time.monotonic() - started, 3), **inventory}



TRUE_FIELDS = ("evidence_valid", "warning_as_error", "fresh_candidate_and_general_consumer_checked",
               "all_owned_declarations_audited", "complete_new_dependency_closure_certified",
               "same_original_source_current_next_certified", "primitive_bright_dark_response_required",
               "positive_source_gain_required",
               "native_feasibility_iff_generated_legal_detector_rates", "squared_source_coordinates_feasibility_certified",
               "whole_response_box_worst_corner_transport_certified", "faithful_same_source_effect_realization_certified",
               "distinct_feasible_response_realizers_certified", "nonempty_math_response_realizer_certified",
               "original_source_ledger_and_next_certified", "detector_factors_scoped_per_role")
FALSE_FIELDS = ("asynchronous_elaboration", "actual_raw_pulse_inputs_available", "actual_hardware_uniquely_identified",
                "shared_detector_factors_between_settings_certified", "atomic_response_forward_model_kernel_proved",
                "new_statistical_interval_coverage_kernel_proved", "controller_advance", "empirical_fit_executed")


def validate_payload(report: dict) -> None:
    require(report.get("schema") == SCHEMA and report.get("candidate_module") == MODULE, "wrong pulse receipt")
    require(all(report.get(k) is True for k in TRUE_FIELDS), "pulse receipt lost an obligation")
    require(all(report.get(k) is False for k in FALSE_FIELDS), "pulse receipt scope was promoted")
    for key, value in (("focused_trust_level", 0), ("lean_threads", 1), ("trial_event_files_read", 0), ("new_statistical_tables_read", 0)):
        require(type(report.get(key)) is int and report[key] == value, "pulse receipt invalid literal")
    explicit = source.explicit_declarations(CANDIDATE)
    require([{k: row[k] for k in ("name", "kind")} for row in report["explicit_declarations"]] == explicit and
            bool(report["owned_declarations"]) and bool(report["independent_consumers"]),
            "pulse receipt declaration scope changed")
    require(set(report["axiom_union"]).issubset(source.ALLOWED_AXIOMS), "pulse receipt unauthorized axioms")


def consume(certificate: Path | None = None, *, require_frozen: bool = True) -> dict:
    canonical = DEFAULT_REPORT.read_bytes()
    require(certificate is None or certificate.read_bytes() == canonical, "pulse override changes canonical receipt")
    if require_frozen:
        committed = subprocess.run(["git", "show", f"HEAD:{source.relative(DEFAULT_REPORT)}"], cwd=ROOT,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        require(committed.returncode == 0 and committed.stdout == canonical, "pulse receipt is not frozen at HEAD")
    report = json.loads(canonical)
    validate_payload(report)
    accepted = source.consume()
    from detector_certify import consume as consume_df
    consume_df()
    require(report["frozen_detector_receipt"]["sha256"] == source.digest((HERE / "detector-certification-first.json").read_bytes()),
            "frozen detector receipt changed")
    require(report["toolchain_version"] == accepted["toolchain_version"], "pulse source toolchain changed")
    require(report["frozen_source_receipt"]["sha256"] == source.digest(source.DEFAULT_REPORT.read_bytes()), "frozen source receipt changed")
    for item in report["source_bindings"]:
        require(source.digest((ROOT / item["path"]).read_bytes()) == item["sha256"], "pulse certified source changed")
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
        require(args.certificate is None, "pulse overrides are intake-only")
        report = generate(args.checked_overlay)
        with args.out.open("x") as output:
            json.dump(report, output, indent=2, ensure_ascii=False)
            output.write("\n")
    print(json.dumps({"evidence_valid": report["evidence_valid"], "status": report["status"],
                      "explicit_declarations": len(report["explicit_declarations"]),
                      "owned_declarations": len(report["owned_declarations"])}))


if __name__ == "__main__":
    main()
