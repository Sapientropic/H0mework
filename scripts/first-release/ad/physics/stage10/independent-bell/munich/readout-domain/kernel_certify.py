"""Source-only kernel certification; receipt intake never reruns a data producer."""

from __future__ import annotations

import argparse
from collections import defaultdict, deque
import hashlib
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
ROOT = HERE.parents[5]
LEAN_ROOT = ROOT / "Lean"
BASE_DIR = HERE.parents[1] / "theory-blind"
BASE_REPORT = BASE_DIR / "kernel-certification-first.json"
DEFAULT_REPORT = HERE / "source-certification-first.json"
SCHEMA = "stage10-munich-readout-source-certification/v1"
MARKER = "BELL_READOUT_KERNEL_AUDIT|"
READOUT_MODULE = "SaturationMonoid.PhysicsCore.Stage10.Bell.Readout"
EFFECT_MODULE = "SaturationMonoid.PhysicsCore.Stage10.Bell.ReadoutEffects"
CANDIDATE_MODULES = [READOUT_MODULE, EFFECT_MODULE]
AUDIT = HERE / "Certification.lean"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_MODULES = ("SaturationMonoid.PhysicsCore.Stage10.Empirical", "SaturationMonoid.PhysicsCore.Stage10.Bell.Delft", "Verification", "scratch")
FORBIDDEN_NAMES = ("sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler")
FLAGS = ["--trust=0", "-DwarningAsError=true", "-DElab.async=false", "-j1"]
PUBLIC_MOUTH = "SaturationMonoid.PhysicsCore.Stage10.Bell.sameOccurrenceReadoutPrediction"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def json_bytes(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def binding(path: Path) -> dict:
    return {"path": relative(path), "sha256": digest(path.read_bytes())}


def candidate_path(module: str) -> Path:
    return LEAN_ROOT / Path(*module.split(".")).with_suffix(".lean")


def run(command: list[str], *, env: dict | None = None, timeout: int = 600) -> str:
    result = subprocess.run(command, cwd=LEAN_ROOT, env=env, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=timeout)
    require(result.returncode == 0, f"focused kernel command failed: {result.stdout[-10000:]}")
    require(not re.search(r"(?m)\b(?:error|warning):", result.stdout), "focused kernel diagnostic")
    return result.stdout


def base_receipt() -> dict:
    spec = importlib.util.spec_from_file_location("paid_bell_theory_certificate", BASE_DIR / "kernel_certify.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.consume()


def base_graph(receipt: dict, explicit_log: Path | None = None) -> dict[str, dict]:
    source = next(x for x in receipt["source_bindings"] if x["path"].endswith("/TheoryBlind.lean"))
    log = explicit_log or Path(tempfile.gettempdir()) / f"tb0001-paid-proof-{source['sha256']}" / "audit-stdout.txt"
    raw = log.read_bytes()
    require(digest(raw) == receipt["independent_audit_stdout_sha256"], "paid base graph log changed")
    marker = "THEORY_BLIND_KERNEL_AUDIT|"
    lines = [line[len(marker):] for line in raw.decode().splitlines() if line.startswith(marker)]
    require(len(lines) == 1, "paid base graph marker missing or duplicated")
    entries = json.loads(lines[0])["dependency_closure"]
    require(len(entries) == receipt["dependency_declaration_count"], "paid base graph count changed")
    require(digest(json_bytes(sorted(entries, key=lambda x: x["name"]))) == receipt["dependency_inventory_sha256"],
            "paid base declaration graph differs from accepted receipt")
    return {x["name"]: x for x in entries}


def explicit_declarations(path: Path) -> list[dict]:
    text = re.sub(r"/-.*?-/", "", path.read_text(), flags=re.S)
    frames: list[tuple[str, str]] = []
    declarations = []
    for number, line in enumerate(text.splitlines(), 1):
        namespace = re.match(r"\s*namespace\s+([\w.]+)", line)
        if namespace:
            frames.append(("namespace", namespace[1]))
        elif re.match(r"\s*(?:noncomputable\s+)?section(?:\s|$)", line):
            frames.append(("section", ""))
        elif re.match(r"\s*end(?:\s|$)", line):
            if frames:
                frames.pop()
        declaration = re.match(r"\s*(?:@\[[^\]]+\]\s*)*(?:noncomputable\s+)?(structure|def|theorem)\s+([\w.]+)", line)
        if declaration:
            prefix = ".".join(name for kind, name in frames if kind == "namespace")
            declarations.append({"name": prefix + "." + declaration[2], "kind": declaration[1]})
    require(bool(declarations), f"no explicit declarations: {path}")
    return declarations


def normalized_entry(entry: dict) -> dict:
    return {"name": entry["name"], "module": entry["module"], "kind": entry["kind"],
            "dependencies": sorted(entry["dependencies"])}


def validate_inventory(inventory: dict, paid: dict[str, dict]) -> dict:
    require(inventory.get("candidate_modules") == CANDIDATE_MODULES, "wrong candidate modules")
    require(inventory.get("closed_public_mouth") is True, "public mouth is not the registered closed Prop")
    require(inventory.get("closed_effect_mouth") is True, "effect mouth is not the registered closed Prop")
    own, consumers = inventory["owned_declarations"], inventory["independent_consumers"]
    require(bool(own) and bool(consumers), "empty candidate or consumer inventory")
    require(len(set(own)) == len(own) and len(set(consumers)) == len(consumers), "duplicate audited declaration")
    delta, boundary = inventory["dependency_delta"], inventory["paid_boundary"]
    require(len({x['name'] for x in delta}) == len(delta), "duplicate delta declaration")
    require(len({x['name'] for x in boundary}) == len(boundary), "duplicate paid boundary")
    require(not set(x['name'] for x in delta).intersection(paid), "delta reclassifies paid base")
    for entry in boundary:
        require(entry["name"] in paid and normalized_entry(entry) == normalized_entry(paid[entry["name"]]),
                f"imported base dependency identity changed: {entry['name']}")
    graph = dict(paid)
    graph.update({x["name"]: x for x in delta})
    require(set(own + consumers).issubset(graph), "missing owned declaration or consumer")
    require(all(d in graph for x in graph.values() for d in x["dependencies"]), "dependency closure has an open edge")
    require(set(CANDIDATE_MODULES).issubset(inventory["imported_modules"]), "candidate import inventory incomplete")
    for module in inventory["imported_modules"]:
        require(not module.startswith(FORBIDDEN_MODULES), f"empirical or scratch import: {module}")
    for name, entry in graph.items():
        require(not entry["module"].startswith(FORBIDDEN_MODULES), f"empirical declaration dependency: {name}")
        require(not name.startswith(FORBIDDEN_NAMES), f"kernel trust escape: {name}")
        require(entry["kind"] != "axiom" or name in ALLOWED_AXIOMS, f"unauthorized axiom: {name}")
        require(not (entry["module"] in CANDIDATE_MODULES and entry["kind"] == "unsafe-definition"),
                f"unsafe owned definition: {name}")
    explicit = []
    for module in CANDIDATE_MODULES:
        definitions = explicit_declarations(candidate_path(module))
        require(set(x["name"] for x in definitions).issubset(own), f"explicit declaration not audited: {module}")
        for declaration in definitions:
            expected = {"structure": "inductive", "def": "definition", "theorem": "theorem"}[declaration["kind"]]
            require(graph[declaration["name"]]["kind"] == expected, "explicit declaration kind changed")
        explicit.extend(dict(x, module=module) for x in definitions)
    require(sum(x["module"] == READOUT_MODULE for x in explicit) == 67, "original readout 67 declaration scope changed")
    require(sum(x["module"] == EFFECT_MODULE for x in explicit) == 48, "effect 48 declaration scope changed")
    mouths = {x["name"]: x["type"] for x in inventory["public_mouths"]}
    require(mouths.get(PUBLIC_MOUTH) == "SaturationMonoid.PhysicsCore.Stage10.Bell.SameOccurrenceReadoutPrediction",
            "public source mouth type changed")
    require(mouths.get("SaturationMonoid.PhysicsCore.Stage10.Bell.sameOccurrenceReadoutEffectPrediction") ==
            "SaturationMonoid.PhysicsCore.Stage10.Bell.SameOccurrenceReadoutEffectPrediction",
            "public effect source mouth type changed")
    parents = defaultdict(set)
    for entry in graph.values():
        for dependency in entry["dependencies"]:
            parents[dependency].add(entry["name"])
    axiom_map = defaultdict(set)
    for axiom in (n for n, x in graph.items() if x["kind"] == "axiom"):
        seen, queue = set(), deque([axiom])
        while queue:
            name = queue.popleft()
            if name not in seen:
                seen.add(name)
                axiom_map[name].add(axiom)
                queue.extend(parents[name])
    reachable, queue = set(), deque(own + consumers)
    while queue:
        name = queue.popleft()
        if name not in reachable:
            reachable.add(name)
            queue.extend(graph[name]["dependencies"])
    additional = []
    for module in sorted(set(graph[name]["module"] for name in reachable)):
        if module.startswith("SaturationMonoid."):
            additional.append(dict(binding(candidate_path(module)), module=module))
    audited = lambda names: [{"name": n, "axioms": sorted(axiom_map[n])} for n in sorted(names)]
    return {"explicit_declarations": [dict(x, axioms=sorted(axiom_map[x["name"]])) for x in explicit],
            "owned_declarations": audited(own), "independent_consumers": audited(consumers),
            "compiler_only_module_symbols": sorted(inventory["compiler_only_module_symbols"]),
            "public_mouths": inventory["public_mouths"],
            "axiom_union": sorted(set(a for n in own + consumers for a in axiom_map[n])),
            "dependency_declaration_count": len(reachable), "new_dependency_declaration_count": len(delta),
            "reused_base_declaration_count": len(paid), "checked_base_boundary_count": len(boundary),
            "dependency_delta_sha256": digest(json_bytes(sorted(delta, key=lambda x: x["name"]))),
            "checked_base_boundary_sha256": digest(json_bytes(sorted(boundary, key=lambda x: x["name"]))),
            "project_dependency_source_bindings": additional,
            "project_import_modules": sorted(module for module in inventory["imported_modules"] if module.startswith("SaturationMonoid.")),
            "dependency_closure_method": "fresh type/value constant delta; exact-edge paid boundary; accepted complete base graph"}


def proof_overlay(destination: Path, search_path: str) -> None:
    roots = [Path(p) if Path(p).is_absolute() else LEAN_ROOT / p for p in search_path.split(os.pathsep) if p]
    cache = next(p for p in roots if (p / "SaturationMonoid/PhysicsCore/Stage10/Bell/Runtime.olean").is_file())
    names = tuple(m.split(".")[-1] + "." for m in CANDIDATE_MODULES)
    def link(source: Path, target: Path, corridor: list[str]) -> None:
        target.mkdir(parents=True, exist_ok=True)
        for entry in source.iterdir():
            if corridor and entry.name == corridor[0]:
                link(entry, target / entry.name, corridor[1:])
            elif not corridor and entry.name.startswith(names):
                continue
            else:
                (target / entry.name).symlink_to(entry.resolve(), target_is_directory=entry.is_dir())
    link(cache / "SaturationMonoid", destination / "SaturationMonoid", ["PhysicsCore", "Stage10", "Bell"])


def generate(*, paid_log: Path | None = None, checked_readout: Path | None = None) -> dict:
    started = time.monotonic()
    base = base_receipt()
    paid = base_graph(base, paid_log)
    sources = [candidate_path(m) for m in CANDIDATE_MODULES] + [AUDIT, Path(__file__).resolve(),
              LEAN_ROOT / "lean-toolchain", LEAN_ROOT / "lake-manifest.json"]
    initial = [binding(path) for path in sources]
    version = run(["lake", "env", "lean", "--version"]).strip()
    require(version == base["toolchain_version"], "paid base toolchain changed")
    executable = run(["lake", "env", "which", "lean"]).strip()
    search = run(["lake", "env", "printenv", "LEAN_PATH"]).strip()
    records = []
    with tempfile.TemporaryDirectory(prefix="bell-readout-source-certification-") as directory:
        out = Path(directory)
        proof_overlay(out, search)
        boundary_file = out / "paid-base-names.json"
        boundary_file.write_bytes(json_bytes(sorted(paid)))
        env = dict(os.environ, LEAN_PATH=directory + os.pathsep + search,
                   BELL_READOUT_PAID_NAMES=str(boundary_file))
        for module in CANDIDATE_MODULES:
            target = out / Path(*module.split(".")).with_suffix(".olean")
            reused = False
            source = candidate_path(module)
            command = [executable, *FLAGS, "-o", str(target), str(source.relative_to(LEAN_ROOT))]
            if checked_readout is not None:
                evidence = json.loads((checked_readout / "environment.json").read_text())
                old = evidence["readout_compile" if module == READOUT_MODULE else "effects_compile"]
                artifact = checked_readout / Path(*module.split(".")).with_suffix(".olean")
                source_sha = evidence["candidate_sha256"] if module == READOUT_MODULE else old["candidate_sha256"]
                require(source_sha == digest(source.read_bytes()) and old["exit_code"] == 0,
                        "focused paid readout source identity changed")
                require(old["command"][0] == executable and all(flag in old["command"] for flag in FLAGS),
                        "focused paid readout trust settings changed")
                require(digest(artifact.read_bytes()) == old["compiled_object_sha256"], "focused paid readout artifact changed")
                stdout = (checked_readout / ("readout-compile.log" if module == READOUT_MODULE else "effects-compile.log")).read_text()
                require(digest(stdout.encode()) == old["output_sha256"], "focused paid readout diagnostic log changed")
                shutil.copyfile(artifact, target)
                reused = True
            else:
                stdout = run(command, env=env)
            records.append({"module": module, "source_sha256": digest(source.read_bytes()),
                            "flags": FLAGS, "exit_code": 0, "stdout_sha256": digest(stdout.encode()),
                            "object_sha256": digest(target.read_bytes()), "same_session_focused_check_reused": reused})
            print("focused producer checked: " + module, flush=True)
        stdout = run([executable, *FLAGS, "-DmaxHeartbeats=0", "-DmaxRecDepth=100000", str(AUDIT)], env=env)
    lines = [line[len(MARKER):] for line in stdout.splitlines() if line.startswith(MARKER)]
    require(len(lines) == 1, "missing complete dependency delta")
    inventory = validate_inventory(json.loads(lines[0]), paid)
    require(initial == [binding(path) for path in sources], "source changed during certification")
    require(base_receipt() == base, "paid base changed during certification")
    return {"schema": SCHEMA, "evidence_valid": True,
            "status": "certified_same_occurrence_full_joint_local_binary_readout",
            "candidate_modules": CANDIDATE_MODULES, "source_bindings": initial,
            "toolchain_version": version, "focused_trust_level": 0, "warning_as_error": True,
            "asynchronous_elaboration": False, "lean_threads": 1,
            "fresh_candidate_and_general_consumer_checked": True, "all_owned_declarations_audited": True,
            "complete_source_dependency_closure_certified": True,
            "same_original_source_visit_current_next_certified": True,
            "general_legal_binary_channels_and_XZ_axes_certified": True,
            "full_four_outcome_distribution_certified": True,
            "source_current_next_joint_law_transport_certified": True,
            "own_setting_and_cross_herald_shared_marginals_certified": True,
            "zero_error_identity_certified": True, "optional_visibility_mathematics_certified": True,
            "complete_compact_effect_domain_certified": True,
            "all_original_channels_and_axes_image_covered": True,
            "negative_and_zero_gain_covered": True,
            "exact_rational_primitive_source_current_next_readback_certified": True,
            "empirical_visibility_parameter_used": False, "empirical_fit_executed": False,
            "real_instrument_verdict_executed": False, "controller_advance": False,
            "human_public_result_unexposed_claimed": False, "empirical_argument_count": 0,
            "trial_event_files_read": 0, "new_statistical_tables_read": 0,
            "paid_base_receipt": {"path": relative(BASE_REPORT), "sha256": digest(BASE_REPORT.read_bytes()),
                                  "dependency_inventory_sha256": base["dependency_inventory_sha256"],
                                  "source_binding_count": len(base["project_dependency_source_bindings"]),
                                  "base_recompiled": False},
            "producer_compilation_evidence": records,
            "independent_audit_stdout_sha256": digest(stdout.encode()),
            "elapsed_seconds": round(time.monotonic() - started, 3), **inventory}


def validate_payload(report: dict) -> None:
    require(report.get("schema") == SCHEMA, "wrong source certificate schema")
    require(report.get("candidate_modules") == CANDIDATE_MODULES, "wrong certified candidates")
    true_fields = ("evidence_valid", "warning_as_error", "fresh_candidate_and_general_consumer_checked",
                   "all_owned_declarations_audited", "complete_source_dependency_closure_certified",
                   "same_original_source_visit_current_next_certified", "general_legal_binary_channels_and_XZ_axes_certified",
                   "full_four_outcome_distribution_certified", "source_current_next_joint_law_transport_certified",
                   "own_setting_and_cross_herald_shared_marginals_certified", "zero_error_identity_certified",
                   "optional_visibility_mathematics_certified", "complete_compact_effect_domain_certified",
                   "all_original_channels_and_axes_image_covered", "negative_and_zero_gain_covered",
                   "exact_rational_primitive_source_current_next_readback_certified")
    require(all(report.get(k) is True for k in true_fields), "source certificate lost an obligation")
    false_fields = ("asynchronous_elaboration", "empirical_visibility_parameter_used", "empirical_fit_executed",
                    "real_instrument_verdict_executed", "controller_advance", "human_public_result_unexposed_claimed")
    require(all(report.get(k) is False for k in false_fields), "source certificate scope was promoted")
    for key, value in (("focused_trust_level", 0), ("lean_threads", 1), ("empirical_argument_count", 0),
                       ("trial_event_files_read", 0), ("new_statistical_tables_read", 0)):
        require(type(report.get(key)) is int and report[key] == value, "invalid source certificate literal")
    require(set(report["axiom_union"]).issubset(ALLOWED_AXIOMS), "source certificate unauthorized axioms")
    require(len([x for x in report["explicit_declarations"] if x["module"] == READOUT_MODULE]) == 67,
            "source certificate changed explicit readout scope")
    require(len([x for x in report["explicit_declarations"] if x["module"] == EFFECT_MODULE]) == 48,
            "source certificate changed effect scope")
    require(bool(report["independent_consumers"]) and bool(report["owned_declarations"]), "empty source certificate")


def consume(certificate: Path | None = None, *, require_frozen: bool = True) -> dict:
    canonical = DEFAULT_REPORT.read_bytes()
    supplied = canonical if certificate is None else certificate.read_bytes()
    require(supplied == canonical, "source certificate override changes canonical evidence")
    if require_frozen:
        committed = subprocess.run(["git", "show", f"HEAD:{relative(DEFAULT_REPORT)}"], cwd=ROOT,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        require(committed.returncode == 0 and committed.stdout == canonical, "source certificate is not frozen at HEAD")
    report = json.loads(supplied)
    validate_payload(report)
    require(report["paid_base_receipt"]["sha256"] == digest(BASE_REPORT.read_bytes()), "paid base receipt changed")
    require(report["toolchain_version"] == base_receipt()["toolchain_version"], "paid base toolchain identity changed")
    for item in report["source_bindings"] + report["project_dependency_source_bindings"]:
        require(digest((ROOT / item["path"]).read_bytes()) == item["sha256"], f"certified source changed: {item['path']}")
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=DEFAULT_REPORT)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    parser.add_argument("--base-inventory-log", type=Path)
    parser.add_argument("--checked-readout", type=Path)
    args = parser.parse_args()
    if args.check_only:
        report = consume(args.certificate)
    else:
        require(args.certificate is None, "certificate overrides are intake-only")
        report = generate(paid_log=args.base_inventory_log, checked_readout=args.checked_readout)
        with args.out.open("x") as output:
            json.dump(report, output, indent=2, ensure_ascii=False)
            output.write("\n")
    print(json.dumps({"evidence_valid": report["evidence_valid"], "status": report["status"],
                      "explicit_declarations": len(report["explicit_declarations"]),
                      "owned_declarations": len(report["owned_declarations"]),
                      "dependency_declarations": report["dependency_declaration_count"]}))


if __name__ == "__main__":
    main()
