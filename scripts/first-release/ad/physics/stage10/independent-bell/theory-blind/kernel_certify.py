"""Independent focused kernel/declaration certification of tb0001's theory lock.

The driver reads only this revision's proof sources and proof-tool metadata. Its
output certifies a theoretical producer; it cannot issue an instrument verdict.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
LEAN_ROOT = ROOT / "Lean"
CRITERION_COMMIT = "130c2c24cfb244ce50e0f87e8ad8a9c3e3e3fa12"
CANDIDATE_MODULE = "SaturationMonoid.PhysicsCore.Stage10.Bell.TheoryBlind"
CANDIDATE = LEAN_ROOT / Path(*CANDIDATE_MODULE.split(".")).with_suffix(".lean")
AUDIT = HERE / "Certification.lean"
DEFAULT_REPORT = HERE / "kernel-certification-first.json"
MARKER = "THEORY_BLIND_KERNEL_AUDIT|"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_MODULE_PREFIXES = (
    "SaturationMonoid.PhysicsCore.Stage10.Empirical.",
    "SaturationMonoid.PhysicsCore.Stage10.Bell.Delft",
    "Verification.",
)
FORBIDDEN_DECLARATION_PREFIXES = ("sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler")
FORBIDDEN_EMPIRICAL_NAMES = re.compile(
    r"(?:^|\.)(?:releasedContact|Released|Statistic|NIST|nist|replayJson|"
    r"frozenNumericalResidual|observedCounts|observedStatistics)(?:\.|$)"
)


def _digest(payload: bytes) -> str:
    return hashlib.sha256(payload).hexdigest()


def _json_bytes(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def _run(command: list[str], *, cwd: Path = ROOT, env: dict[str, str] | None = None,
         timeout: int = 600, log_path: Path | None = None) -> subprocess.CompletedProcess[str]:
    if log_path is None:
        result = subprocess.run(command, cwd=cwd, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    else:
        with log_path.open("w") as log:
            process = subprocess.run(command, cwd=cwd, env=env, text=True,
                                     stdout=log, stderr=subprocess.STDOUT, timeout=timeout)
        result = subprocess.CompletedProcess(command, process.returncode, log_path.read_text())
    if result.returncode:
        raise ValueError(f"proof command failed ({result.returncode}): {result.stdout[-12000:]}")
    return result


def _relative(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def _frozen_binding(path: Path) -> dict[str, str]:
    relative = _relative(path)
    payload = path.read_bytes()
    frozen = subprocess.run(["git", "show", f"HEAD:{relative}"], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True).stdout
    if frozen != payload:
        raise ValueError(f"scientific source is not frozen at HEAD: {relative}")
    commit = _run(["git", "log", "-1", "--format=%H", "--", relative]).stdout.strip()
    return {"path": relative, "sha256": _digest(payload), "commit": commit}


def _inputs() -> list[dict[str, str]]:
    sources_path = HERE / "sources.json"
    criterion_path = HERE / "criterion.md"
    for path in (sources_path, criterion_path):
        relative = _relative(path)
        original = subprocess.run(["git", "show", f"{CRITERION_COMMIT}:{relative}"],
                                  cwd=ROOT, stdout=subprocess.PIPE,
                                  stderr=subprocess.PIPE, check=True).stdout
        if original != path.read_bytes():
            raise ValueError(f"tb0001 input revision changed: {relative}")
    sources = json.loads(sources_path.read_text())
    if sources["schema"] != "stage10-theory-blind-sources/v1":
        raise ValueError("wrong theoretical source schema")
    if sources["criterion_sha256"] != _digest(criterion_path.read_bytes()):
        raise ValueError("criterion identity mismatch")
    bindings = [_frozen_binding(path) for path in
                (criterion_path, sources_path, CANDIDATE, AUDIT, Path(__file__).resolve())]
    for item in sources["sources"]:
        path = ROOT / item["path"]
        if path.suffix != ".lean" or not path.is_relative_to(LEAN_ROOT):
            raise ValueError("source binding is not a Lean theory source")
        if _digest(path.read_bytes()) != item["sha256"]:
            raise ValueError(f"original theoretical source changed: {item['path']}")
        bindings.append(_frozen_binding(path))
    return bindings


def validate_inventory(inventory: dict) -> dict:
    if inventory.get("candidate_module") != CANDIDATE_MODULE:
        raise ValueError("wrong candidate module")
    own_names = inventory["owned_declarations"]
    consumer_names = inventory["independent_consumers"]
    closure = inventory["dependency_closure"]
    if not own_names or not consumer_names or not closure:
        raise ValueError("empty declaration audit")
    for names in (own_names, consumer_names):
        if len(names) != len(set(names)):
            raise ValueError("duplicate declaration audit")
    names = [entry["name"] for entry in closure]
    if len(names) != len(set(names)) or not set(own_names + consumer_names).issubset(names):
        raise ValueError("incomplete or duplicate dependency closure")
    graph = {entry["name"]: entry for entry in closure}
    if any(dependency not in graph for entry in closure for dependency in entry["dependencies"]):
        raise ValueError("dependency edge leaves the complete inventory")
    for entry in closure:
        name, module, kind = entry["name"], entry["module"], entry["kind"]
        if module.startswith(FORBIDDEN_MODULE_PREFIXES) or FORBIDDEN_EMPIRICAL_NAMES.search(name):
            raise ValueError(f"empirical declaration dependency: {module}: {name}")
        if name.startswith(FORBIDDEN_DECLARATION_PREFIXES):
            raise ValueError(f"kernel trust escape: {name}")
        if kind == "axiom" and name not in ALLOWED_AXIOMS:
            raise ValueError(f"unauthorized dependency axiom: {name}")
        if kind == "unsafe-definition" and module == CANDIDATE_MODULE:
            raise ValueError(f"unsafe owned definition: {name}")

    def axioms_of(start: str) -> list[str]:
        pending, seen, axioms = [start], set(), set()
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            entry = graph[name]
            if entry["kind"] == "axiom":
                axioms.add(name)
            pending.extend(entry["dependencies"])
        return sorted(axioms)

    own = [{"name": name, "axioms": axioms_of(name)} for name in own_names]
    consumers = [{"name": name, "axioms": axioms_of(name)} for name in consumer_names]
    mouths = {item["name"]: item["type"] for item in inventory["public_mouths"]}
    if (inventory.get("closed_public_mouth") is not True or
            f"{CANDIDATE_MODULE}.predictionLock" not in mouths):
        raise ValueError("public lock is not closed at its exact registered mouth")
    modules = sorted(set(entry["module"] for entry in closure))
    project_modules = [name for name in modules if name.startswith("SaturationMonoid.")]
    bindings = []
    for module in project_modules:
        path = LEAN_ROOT / Path(*module.split(".")).with_suffix(".lean")
        if not path.is_file():
            raise ValueError(f"missing dependency source: {module}")
        bindings.append({"module": module, "path": _relative(path),
                         "sha256": _digest(path.read_bytes())})
    return {
        "owned_declarations": sorted(own, key=lambda item: item["name"]),
        "compiler_only_module_symbols": sorted(inventory["compiler_only_module_symbols"]),
        "independent_consumers": sorted(consumers, key=lambda item: item["name"]),
        "public_mouths": inventory["public_mouths"],
        "dependency_declaration_count": len(closure),
        "dependency_closure_method": "single type/value fold per declaration; shared directed graph",
        "dependency_inventory_sha256": _digest(_json_bytes(sorted(closure,
                                                    key=lambda item: item["name"]))),
        "dependency_module_count": len(modules),
        "project_dependency_source_bindings": bindings,
        "axiom_union": sorted(set(axiom for entry in own + consumers for axiom in entry["axioms"])),
    }


def _proof_cache_overlay(destination: Path, search_path: str) -> None:
    runtime_module = Path("SaturationMonoid/PhysicsCore/Stage10/Bell/Runtime.olean")
    candidates = [Path(part) if Path(part).is_absolute() else LEAN_ROOT / part
                  for part in search_path.split(os.pathsep) if part]
    cache = next((path for path in candidates if (path / runtime_module).is_file()), None)
    if cache is None:
        raise ValueError("original proof-cache root was not found")
    corridor = CANDIDATE_MODULE.split(".")[:-1]

    def link_layer(source: Path, target: Path, remaining: list[str]) -> None:
        target.mkdir(parents=True, exist_ok=True)
        for entry in source.iterdir():
            if remaining and entry.name == remaining[0]:
                link_layer(entry, target / entry.name, remaining[1:])
            elif not remaining and entry.name.startswith("TheoryBlind."):
                continue
            else:
                (target / entry.name).symlink_to(entry.resolve(), target_is_directory=entry.is_dir())

    # Lean resolves the first matching namespace directory, so the fresh module
    # needs a read-only overlay of its siblings rather than an empty prefix.
    link_layer(cache / corridor[0], destination / corridor[0], corridor[1:])


def generate() -> dict:
    started = time.monotonic()
    inputs = _inputs()
    version = _run(["lake", "env", "lean", "--version"], cwd=LEAN_ROOT).stdout.strip()
    if "version 4.33.0" not in version:
        raise ValueError(f"unexpected toolchain: {version}")
    lean_path = _run(["lake", "env", "printenv", "LEAN_PATH"], cwd=LEAN_ROOT).stdout.strip()
    executable = _run(["lake", "env", "which", "lean"], cwd=LEAN_ROOT).stdout.strip()
    checkpoint = Path(tempfile.gettempdir()) / f"tb0001-paid-proof-{_digest(CANDIDATE.read_bytes())}"
    checkpoint.mkdir(exist_ok=True)
    artifact = checkpoint / "TheoryBlind.olean"
    paid_path = checkpoint / "candidate-paid.json"
    proof_inputs = [{"path": item["path"], "sha256": item["sha256"]} for item in inputs
                    if item["path"] not in {_relative(AUDIT), _relative(Path(__file__).resolve())}]
    candidate_reused = False
    with tempfile.TemporaryDirectory(prefix="tb0001-kernel-") as temporary:
        temporary_path = Path(temporary)
        _proof_cache_overlay(temporary_path, lean_path)
        output = temporary_path / Path(*CANDIDATE_MODULE.split(".")).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        env = dict(os.environ, LEAN_PATH=f"{temporary}:{lean_path}")
        common = [executable, "--trust=0", "-DwarningAsError=true", "-DmaxHeartbeats=0"]
        if paid_path.is_file() and artifact.is_file():
            paid = json.loads(paid_path.read_text())
            if (paid["proof_inputs"] != proof_inputs or paid["toolchain_version"] != version or
                    paid["trust_level"] != 0 or paid["warning_as_error"] is not True or
                    paid["artifact_sha256"] != _digest(artifact.read_bytes())):
                raise ValueError("paid candidate export no longer matches its compiled proof scope")
            shutil.copyfile(artifact, output)
            candidate_result = subprocess.CompletedProcess([], 0, paid["stdout"])
            candidate_reused = True
        else:
            candidate_result = _run(common + ["-o", str(output),
                                             str(CANDIDATE.relative_to(LEAN_ROOT))],
                                    cwd=LEAN_ROOT, env=env)
            shutil.copyfile(output, artifact)
            paid = {"proof_inputs": proof_inputs, "toolchain_version": version,
                    "trust_level": 0, "warning_as_error": True,
                    "artifact_sha256": _digest(artifact.read_bytes()), "stdout": candidate_result.stdout}
            paid_path.write_text(json.dumps(paid, indent=2) + "\n")
        print("candidate export reused" if candidate_reused else "candidate export checked", flush=True)
        print(f"metadata progress log: {checkpoint / 'audit-stdout.txt'}", flush=True)
        audit_result = _run(common + ["-DmaxRecDepth=100000", str(AUDIT)],
                            cwd=LEAN_ROOT, env=env, log_path=checkpoint / "audit-stdout.txt")
    for result in (candidate_result, audit_result):
        if re.search(r"(?m)\b(?:error|warning):", result.stdout):
            raise ValueError("focused check contains a required diagnostic")
    lines = [line[len(MARKER):] for line in audit_result.stdout.splitlines()
             if line.startswith(MARKER)]
    if len(lines) != 1:
        raise ValueError("one complete kernel audit inventory was not emitted")
    inventory = validate_inventory(json.loads(lines[0]))
    if inputs != _inputs():
        raise ValueError("theoretical source changed during certification")
    return {
        "schema": "stage10-theory-blind-kernel-certification/v1",
        "criterion_commit": CRITERION_COMMIT,
        "evidence_valid": True,
        "status": "certified_source_native_theory_blind_prediction",
        "candidate_module": CANDIDATE_MODULE,
        "focused_trust_level": 0,
        "warning_as_error": True,
        "fresh_candidate_and_independent_consumer_checked": True,
        "all_owned_declarations_audited": True,
        "declaration_dependency_closure_certified": True,
        "same_original_source_visit_current_next_certified": True,
        "complete_Born_probability_family_certified": True,
        "uniform_XZ_Tsirelson_bound_certified": True,
        "fixed_theory_settings_saturate_Tsirelson": True,
        "exact_Qsqrt2_export_bridge_certified": True,
        "point_independence_certified": True,
        "empirical_argument_count": 0,
        "public_statistical_dependency_count": 0,
        "new_public_statistical_tables_read": 0,
        "trial_event_files_read": 0,
        "human_outcome_unexposed_claimed": False,
        "real_instrument_empirical_verdict_executed": False,
        "controller_advance": False,
        "source_bindings": inputs,
        "toolchain_version": version,
        "focused_command_contract": ["lean --trust=0 -DwarningAsError=true -DmaxHeartbeats=0",
                                       _relative(CANDIDATE), _relative(AUDIT)],
        "candidate_stdout_sha256": _digest(candidate_result.stdout.encode()),
        "paid_candidate_export_reused": candidate_reused,
        "paid_candidate_export_sha256": _digest(artifact.read_bytes()),
        "independent_audit_stdout_sha256": _digest(audit_result.stdout.encode()),
        "elapsed_seconds": round(time.monotonic() - started, 3),
        **inventory,
    }


def consume(certificate_path: Path | None = None) -> dict:
    canonical_bytes = DEFAULT_REPORT.read_bytes()
    frozen = subprocess.run(["git", "show", f"HEAD:{_relative(DEFAULT_REPORT)}"], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True).stdout
    if frozen != canonical_bytes:
        raise ValueError("kernel receipt is not the frozen canonical bytes")
    supplied = canonical_bytes if certificate_path is None else certificate_path.read_bytes()
    if supplied != canonical_bytes:
        raise ValueError("kernel receipt override does not preserve the certified bytes")
    report = json.loads(supplied)
    if report["schema"] != "stage10-theory-blind-kernel-certification/v1":
        raise ValueError("wrong kernel receipt schema")
    if report["source_bindings"] != _inputs():
        raise ValueError("kernel source bindings changed")
    for binding in report["project_dependency_source_bindings"]:
        path = ROOT / binding["path"]
        if _digest(path.read_bytes()) != binding["sha256"]:
            raise ValueError(f"mathematical dependency source changed: {binding['path']}")
    true_fields = ("evidence_valid", "warning_as_error", "fresh_candidate_and_independent_consumer_checked",
                   "all_owned_declarations_audited", "declaration_dependency_closure_certified",
                   "same_original_source_visit_current_next_certified", "complete_Born_probability_family_certified",
                   "uniform_XZ_Tsirelson_bound_certified", "fixed_theory_settings_saturate_Tsirelson",
                   "exact_Qsqrt2_export_bridge_certified",
                   "point_independence_certified")
    if any(report.get(field) is not True for field in true_fields):
        raise ValueError("kernel receipt lost a certified obligation")
    if any(report.get(field) is not False for field in
           ("human_outcome_unexposed_claimed", "real_instrument_empirical_verdict_executed", "controller_advance")):
        raise ValueError("kernel receipt scope was promoted")
    if any(type(report.get(field)) is not int or report[field] != 0 for field in
           ("focused_trust_level", "empirical_argument_count", "public_statistical_dependency_count",
            "new_public_statistical_tables_read", "trial_event_files_read")):
        raise ValueError("kernel receipt has invalid literal counts")
    if not set(report["axiom_union"]).issubset(ALLOWED_AXIOMS):
        raise ValueError("kernel receipt changed its axiom scope")
    return report


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path, default=DEFAULT_REPORT)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    args = parser.parse_args()
    if args.check_only:
        report = consume(args.certificate)
    else:
        if args.certificate is not None:
            parser.error("certificate overrides are intake-only")
        report = generate()
        with args.out.open("x", encoding="utf-8") as output:
            json.dump(report, output, indent=2, ensure_ascii=False)
            output.write("\n")
    print(json.dumps({"evidence_valid": report["evidence_valid"], "status": report["status"],
                      "owned_declaration_count": len(report["owned_declarations"]),
                      "dependency_declaration_count": report["dependency_declaration_count"]}))


if __name__ == "__main__":
    main()
