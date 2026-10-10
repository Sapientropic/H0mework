from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
BASE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "tools"))
import first_release as fr


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n")


def main():
    plan_path = BASE / "plan.json"
    plan = json.loads(plan_path.read_bytes())
    source_plan_path = BASE.parent / "physics-runtime-overlap-plan-c762e780.json"
    source_plan = json.loads(source_plan_path.read_bytes())
    graph = source_plan["physics_graph"]
    selected = next(p for p in source_plan["packages"] if p["id"] == "v2-9c73-charged-transfer")
    rows = {r["target"]: r for r in plan["rows"]}
    prefix = next(iter(rows)).rsplit(".", 1)[0] + "."
    joint = prefix + "MixedSpectatorJointFacts"
    ancestors = set()

    def descend(module):
        if module in ancestors:
            return
        ancestors.add(module)
        for dep in graph.get(module, []):
            descend(dep)

    for module in [*rows, joint]:
        descend(module)
    changed = set(rows)
    while True:
        more = changed | {m for m in ancestors if any(d in changed for d in graph.get(m, []))}
        if more == changed:
            break
        changed = more
    assert len(changed) == 11
    ordered, done = [], set()

    def order(module):
        if module in done:
            return
        done.add(module)
        for dep in graph.get(module, []):
            if dep in changed:
                order(dep)
        ordered.append(module)

    for module in sorted(changed):
        order(module)
    out = fr.new_output(ROOT, BASE / "environment-verification-c762e780")
    src, lib = out / "src", out / "lib"
    src.mkdir()
    lib.mkdir()
    settings = fr.settings(ROOT)
    flags = list(dict.fromkeys(settings["package_moreLeanArgs"] + settings["package_weakLeanArgs"] +
                               ["--trust=0", "-DwarningAsError=true"]))
    freeze_path = ROOT / ".local/acceptance-execution-20261010/cohort-freeze.json"
    freeze = json.loads(freeze_path.read_bytes())
    input_paths = set(freeze["files"]) | set(selected["source_files"])
    input_paths.update(r["candidate_path"] for r in rows.values())
    input_paths.update(p.relative_to(ROOT).as_posix() for p in (plan_path, source_plan_path, Path(__file__)))

    def capture():
        return {"head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                "files": {p: sha(ROOT / p) for p in sorted(input_paths)},
                "cohort_freeze_sha256": sha(freeze_path)}

    before = capture()
    assert before["head"] == plan["head"] == freeze["head"]
    assert all(before["files"][p] == digest for p, digest in freeze["files"].items())
    assert all(before["files"][p] == digest for p, digest in selected["source_files"].items())
    write(out / "input-before.json", before)
    (out / "invocation-source.py").write_bytes(Path(__file__).read_bytes())
    original_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                            cwd=ROOT / "Lean", text=True).strip()
    environment = fr.build_environment()
    assert environment["LEAN_NUM_THREADS"] == "2"
    environment["LEAN_PATH"] = original_path
    steps = []

    def execute(name, source, output, expected_owners=None):
        command = ["lean", "--root=" + str(src), *flags, str(source), "-o", str(output)]
        started, begin = datetime.now(timezone.utc).isoformat(), time.monotonic()
        write(out / (name + "-command.json"), {"command": command, "cwd": "Lean", "LEAN_NUM_THREADS": "2",
                                             "LEAN_PATH": environment["LEAN_PATH"], "settings": settings})
        log = out / (name + ".log")
        with log.open("x") as stream:
            process = subprocess.Popen(command, cwd=ROOT / "Lean", env=environment,
                                       stdout=stream, stderr=subprocess.STDOUT)
            write(out / "handle.json", {"controller_pid": os.getpid(), "lean_pid": process.pid,
                                         "current_step": name, "started_at": started})
            code = process.wait()
        text = log.read_text()
        owners_ok = all("OWNER " + declaration + " = " + owner in text
                        for declaration, owner in (expected_owners or {}).items())
        step = {"name": name, "command": command, "exit_code": code, "started_at": started,
                "elapsed_seconds": round(time.monotonic() - begin, 3), "source_sha256": sha(source),
                "object_sha256": sha(output) if output.exists() else None, "log_sha256": sha(log),
                "expected_owners": expected_owners, "owner_verified": owners_ok}
        steps.append(step)
        write(out / "steps.json", steps)
        print(json.dumps({k: step[k] for k in ("name", "exit_code", "elapsed_seconds", "owner_verified")}), flush=True)
        return code == 0 and owners_ok

    def owner_driver(name, imports, expected):
        source = src / (name + ".lean")
        source.write_text("".join("import " + m + "\n" for m in imports) + "import Lean\n" +
                          "set_option autoImplicit false\nopen Lean Elab Command\nrun_cmd do\n" +
                          "  let env ← getEnv\n  for text in " + json.dumps(list(expected)) + " do\n" +
                          "    let name := (text.splitOn \".\").foldl Name.str .anonymous\n" +
                          "    let some info := env.checked.get.find? name | throwError \"Missing checked constant {name}\"\n" +
                          "    let some index := env.getModuleIdxFor? name | throwError \"Missing owner {name}\"\n" +
                          "    unless (info.value? true).isSome do throwError \"Missing value {name}\"\n" +
                          "    logInfo m!\"OWNER {name} = {env.header.moduleNames[index]!}\"\n" +
                          "    logInfo m!\"TYPE {name} = {info.type}\"\n")
        return source

    ok = True
    original_name = "LowEnergy.MixedSpectatorCandidate.instDecidableEqIndex"
    for stem in ("MixedSpectatorColorMatrix", "MixedSpectatorSpin"):
        expected = {original_name: prefix + stem}
        source = owner_driver("Original" + stem + "Owner", [prefix + stem], expected)
        ok = execute("original-" + stem, source, out / (stem + "-owner.olean"), expected)
        if not ok:
            break
    if ok:
        reserved = {Path(*m.split(".")).with_suffix(".olean") for m in changed}
        ancestors = {a for path in reserved for a in path.parents}

        def link_cache(public, private, relative=Path(".")):
            private.mkdir(exist_ok=True)
            for child in public.iterdir():
                rel = relative / child.name
                if any(rel.parent == p.parent and child.name.startswith(p.stem + ".") for p in reserved):
                    continue
                destination = private / child.name
                if rel in ancestors:
                    link_cache(child, destination, rel)
                elif not destination.exists():
                    destination.symlink_to(child, target_is_directory=child.is_dir())

        link_cache(ROOT / "Lean/.lake/build/lib/lean", lib)
        environment["LEAN_PATH"] = str(lib) + ":" + original_path
        for module in ordered:
            path = Path(*module.split(".")).with_suffix(".lean")
            source = src / path
            source.parent.mkdir(parents=True, exist_ok=True)
            source.write_bytes((ROOT / rows[module]["candidate_path"]).read_bytes() if module in rows
                               else (ROOT / "Lean" / path).read_bytes())
            output = lib / path.with_suffix(".olean")
            output.parent.mkdir(parents=True, exist_ok=True)
            ok = execute("canonical-" + path.stem, source, output)
            if not ok:
                break
    if ok:
        expected = {"LowEnergy.MixedSpectatorCandidate." + rule["target_name"]: row["target"]
                    for row in rows.values() for rule in row["local_instance_names"]}
        source = owner_driver("IndependentChargedConsumer", [joint, prefix + "MixedSpectatorExchangeSelection"], expected)
        joint_raw = (ROOT / "Lean" / Path(*joint.split(".")).with_suffix(".lean")).read_text()
        opening = joint_raw.split("namespace LowEnergy.MixedSpectatorCandidate\n", 1)[1].split("theorem", 1)[0]
        statement = joint_raw.split("theorem actual_charged_color_singlet_spin_half", 1)[1].split(" :=", 1)[0]
        with source.open("a") as stream:
            stream.write("namespace LowEnergy.MixedSpectatorCandidate\n" + opening + "example" + statement +
                         " := actual_charged_color_singlet_spin_half dual\nend LowEnergy.MixedSpectatorCandidate\n" +
                         "#print axioms LowEnergy.MixedSpectatorCandidate.actual_charged_color_singlet_spin_half\n")
        ok = execute("independent-charged-consumer", source, out / "consumer.olean", expected)
    after = capture()
    write(out / "input-after.json", after)
    result = {"schema": "h0mework/private-new9-mixed-spectator-environment-verification@1",
              "formal_acceptance": False, "ok": ok and before == after, "inputs_unchanged": before == after,
              "candidate_plan_path": plan_path.relative_to(ROOT).as_posix(), "candidate_plan_sha256": sha(plan_path),
              "canonical_candidate_modules": list(rows), "unchanged_direct_modules_recompiled": sorted(changed - set(rows)),
              "settings": settings, "input_before": before, "input_after": after, "steps": steps,
              "input_source_scope_sha256": selected["source_scope_sha256"]}
    write(out / "result.json", result)
    print(json.dumps({"ok": result["ok"], "inputs_unchanged": result["inputs_unchanged"], "steps": len(steps)}), flush=True)
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
