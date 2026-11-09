"""Replay the retained peace journal and original local controls without node calls."""

from __future__ import annotations

from contextlib import contextmanager
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

import first_release as release
import generated_society as finite
import source_view


BACKEND = ("Lean/SaturationMonoid/ProcessGame/Society/Institutions/Conflict/"
           "Constitution/TerminalPeace/Deployment/Main.lean")
TRACK = "SaturationMonoid.Tracks.LivingLawTerminalPeaceInstance"
REPLICATION = "scripts/verification/terminal-peace-replication-check.py"
DISPOSITION = "scripts/verification/terminal-peace-handoff-resolution-check.py"


def native_command(root, backend):
    lean_root = root / "Lean"
    environment = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                          cwd=lean_root, text=True).strip()
    compiler = subprocess.check_output(["lake", "env", "which", "lean"],
                                       cwd=lean_root, text=True).strip()
    return ["env", "LEAN_PATH=" + environment, compiler, "--trust=0", "-j1",
            "-DwarningAsError=true", "-DElab.async=false", "--root=" + str(lean_root),
            "--run", str(release.repo_file(root, backend))]


def runtime_view(state, inverse, directory):
    """Restore original paths and Lean bytes for the original source-version check."""
    for path, row in state["modules"].items():
        _, original = source_view.module_views(row, inverse)
        output = directory / path
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(original)
    for path, row in state["artifacts"].items():
        if path.startswith(("Lean/", "Verification/")):
            public, original = source_view.artifact_views(row)
            output = directory / path
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(public if original is None else original)
    return directory / "Lean"


def activation_files(root, data, state):
    """Bind the archived activation to the signed receipt and the fixed Git inputs."""
    reference = data["activation_extraction"]
    inventory = finite.artifact(root, reference)
    handoff = finite.artifact(root, data["online_evidence"]["handoff"])
    base = Path(reference["path"]).parent
    members = inventory["members"]
    manifest_bytes = release.repo_file(root, (base / "release.json").as_posix()).read_bytes()
    manifest = json.loads(manifest_bytes)
    finite.require(inventory["archive_sha256"] == handoff["activation_archive_sha256"]
                   and inventory["activation_release"] == manifest["hash"] == handoff["activation_release"]
                   and release.sha(manifest_bytes) == members["release.json"]["sha256"]
                   and set(members) == {"release.json"} | {"scripts/" + name for name in manifest["scripts"]},
                   "The extracted release manifest does not match the original activation")
    overrides = {}
    for name, digest in manifest["scripts"].items():
        path = release.relative_path("scripts/" + name)
        member = members[path]
        if "archive_member" in member:
            finite.require(member["archive_member"] == path, "Activation member path differs")
            raw = release.repo_file(root, (base / path).as_posix()).read_bytes()
            overrides[path] = raw
        else:
            finite.require(member["fixed_git_path"] == "Lean/" + path, "Activation source path differs")
            row = state["artifacts"][member["fixed_git_path"]]
            finite.require(row["source_sha256"] == digest, "Activation Git identity differs: " + path)
            raw = release.repo_file(root, row["path"]).read_bytes()
        finite.require(member["sha256"] == digest == release.sha(raw),
                       "Activation script bytes differ: " + path)
    return manifest["hash"], overrides


@contextmanager
def runtime_imports(lean_root):
    # The original modules use top-level imports resolved beside their restored files.
    saved = sys.path[:]
    sys.path.insert(0, str(lean_root / "scripts"))
    try:
        yield
    finally:
        sys.path[:] = saved


def signed_history(root, data, policy_path, command, lean_root):
    from proposition_dependency_inventory import active_lake_roots
    from terminal_peace_admission import Admission
    from terminal_peace_replication.protocol import Timeline
    from terminal_peace_worker import VERSION, _Committed, _digest, _open_native, _source_version

    evidence = {name: finite.artifact(root, ref) for name, ref in data["online_evidence"].items()
                if name in {"legacy", "recovery", "handoff", "policy", "journal"}}
    legacy, recovery, handoff = (evidence[key] for key in ("legacy", "recovery", "handoff"))
    policy, bundle = evidence["policy"], evidence["journal"]
    refs = data["online_evidence"]
    finite.require(_digest(policy) == legacy["policy"]
                   and recovery["previous_acceptance_sha256"] == refs["legacy"]["sha256"]
                   and handoff["previous_acceptance_sha256"] == refs["recovery"]["sha256"],
                   "Original peace evidence has a different policy or prior receipt")
    finite.require(any(module == TRACK for _, module in active_lake_roots(lean_root)),
                   "The fixed deployment is absent from LivingLawActive")
    version = _source_version(lean_root, Path(BACKEND).relative_to("Lean"))
    admission = Admission(policy_path, version, policy["compiler"])
    genesis = dict(bundle["prefix"]["genesis"])
    genesis_head = genesis.pop("head")
    finite.require(_digest([VERSION, version, genesis]) == genesis_head,
                   "The original initial source address differs")
    origin = _Committed(genesis, genesis_head)
    signed = Timeline(bundle, admission, version, origin)
    rows = bundle["prefix"]["rows"]
    finite.require([row[0] for row in rows] == list(range(1, 28))
                   and len({row[1] for row in rows}) == len(rows),
                   "Original signed history is not consecutive and uniquely addressed")
    by_cursor = {row[0]: (dict(json.loads(row[4]), head=row[5]), row[6]) for row in rows}
    by_id = {row[1]: row for row in rows}
    admissions = [legacy["before"], *legacy["after"]]
    finite.require([record["clock"] for record in admissions] == ["12", "13", "14", "15", "16"]
                   and all(by_cursor[record["cursor"]][0] == record for record in admissions)
                   and [json.loads(by_cursor[record["cursor"]][1]) for record in legacy["after"]]
                   == legacy["certificates"],
                   "The original four-machine admission suffix differs from the signed journal")
    handoff_certificate = recovery["handoff_certificate"]
    handoff_request = handoff_certificate["intent"]["owner"]["body"]["request"]["id"]
    handoff_row = by_id[handoff_request]
    finite.require(bundle["bootstrap"] == recovery["bootstrap"]
                   and recovery["original_prefix"] == admissions[-1]
                   and handoff_certificate == json.loads(handoff_row[6])
                   and json.loads(handoff_row[4])["clock"] == "18"
                   and recovery["current"]["clock"] == "20"
                   and recovery["current"] == by_cursor[recovery["current"]["cursor"]][0],
                   "Cold recovery or the first signed roster handoff differs")
    finite.require(len(handoff["proofs"]) == 8 and all(
        json.loads(by_id[request][6]) == proof for request, proof in handoff["proofs"].items()
    ) and signed.current.reply() == handoff["current"] == by_cursor[27][0]
                   and signed.current.record["clock"] == "28"
                   and set(signed.members) == set(handoff["active_members"]),
                   "Ordered handoff proofs differ from the final certified history")
    quorum = lean_root / Path(BACKEND).relative_to("Lean").parent / "Recovery/Quorum.lean"
    disposition = quorum.with_name("HandoffDisposition.lean")
    finite.require(release.sha(quorum.read_bytes()) == recovery["kernel"]["source_sha256"]
                   == handoff["kernel"]["prior_quorum_source_sha256"]
                   and release.sha(disposition.read_bytes()) == handoff["kernel"]["source_sha256"],
                   "Original runtime evidence names different quorum or disposition proofs")

    with _open_native(command + ["--live"], root / "Lean", version, 180) as (native, actual):
        finite.require(actual == origin, "The local Lean backend generates a different genesis")
        replayed = Timeline(bundle, admission, version, actual, native)
    finite.require(replayed.current.reply() == signed.current.reply()
                   and replayed.current.record["remaining"] == "0",
                   "Local Lean replay did not generate the same signed tip")
    return {"signed_rows": len(rows), "native_rows": replayed.current.cursor,
            "final_clock": replayed.current.record["clock"],
            "final_address": replayed.current.record["address"],
            "final_remaining": replayed.current.record["remaining"],
            "active_roles": sorted(signed.members),
            "original_source_version": version,
            "legacy_clocks": ["12", "13", "14", "15", "16"],
            "first_recovery_clock": recovery["current"]["clock"],
            "ordered_proofs": len(handoff["proofs"])}


def worker_control(command, cwd):
    def run(mode, requests=None):
        result = subprocess.run(command + mode, cwd=cwd, input=requests,
                                text=True, capture_output=True, timeout=180)
        finite.require(result.returncode == 0, "Lean deployment control failed")
        return [json.loads(line) for line in result.stdout.splitlines() if line.strip()]

    batch = run(["--fuel", "12"])
    requests = [{"op": "inspect"}] + [{"op": "advance", "cursor": index} for index in range(12)]
    worker = run(["--worker"], "".join(json.dumps(row) + "\n" for row in requests))
    finite.require(batch == worker and len(batch) == 13 and batch[-1]["clock"] == "13",
                   "Default batch and streamed Lean readouts differ")
    return len(batch)


def fixture(root, view, backend, output):
    """Run the fixed recovery check with its original native callback bound to H0."""
    command = native_command(root, backend)
    script = view / REPLICATION
    spec = importlib.util.spec_from_file_location("original_peace_replication_check", script)
    if spec is None or spec.loader is None:
        raise RuntimeError("Original replication control is unavailable")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    module.terminal_peace_command = lambda *_args: command
    sys.argv = [str(script)]
    module.check(output)
    print("Original recovery and fully disjoint signed handoff passed")


def run_fixture(command, cwd, logfile):
    with logfile.open("w") as stream:
        result = subprocess.run(command, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
    finite.require(result.returncode == 0, "Original local fixture failed: " + logfile.name)


def replay(root, map_path, selection_path, output):
    data = release.read_json(root / map_path)
    receipt = release.new_output(root, output)
    _, _, epochs = finite.selected_views(root, selection_path=selection_path)
    with tempfile.TemporaryDirectory(prefix="enforceable-peace-replay-") as temporary, finite.source_root(root):
        directory = Path(temporary)
        _, _, _, inverse = source_view.load_map()
        latest, recovery = (data["deployment_epochs"][name] for name in ("handoff", "recovery"))
        current_state, recovery_state = epochs[latest], epochs[recovery]
        current_view = runtime_view(current_state, inverse, directory / "current")
        recovery_view = runtime_view(recovery_state, inverse, directory / "recovery")
        activation, overrides = activation_files(root, data, current_state)
        active_view = directory / "activation" / "Lean"
        shutil.copytree(current_view / "scripts", active_view / "scripts")
        (active_view.parent / "Verification").symlink_to(current_view.parent / "Verification", target_is_directory=True)
        for path, body in overrides.items():
            (active_view / path).write_bytes(body)
        current_backend = current_state["modules"][BACKEND]["path"]
        recovery_backend = recovery_state["modules"][BACKEND]["path"]
        command = native_command(root, current_backend)
        with runtime_imports(active_view):
            result = signed_history(root, data, release.repo_file(root, data["online_evidence"]["policy"]["path"]),
                                    command, current_view)
        result["batch_worker_observations"] = worker_control(command, root / "Lean")
        run_fixture([sys.executable, str(current_view / DISPOSITION)], current_view,
                    receipt / "disposition-fixture.log")
        fixture_output = directory / "replication-fixture"
        fixture_output.mkdir()
        run_fixture([sys.executable, str(Path(__file__).resolve()), str(root), str(recovery_view),
                     recovery_backend, str(fixture_output)], recovery_view, receipt / "replication-fixture.log")
    result.update(schema="h0mework/enforceable-peace-offline-replay@1", status="passed",
                  production_node_calls=0, native_backend=current_backend,
                  activation_release=activation, activation_inventory_sha256=data["activation_extraction"]["sha256"],
                  inputs={key: reference["sha256"] for key, reference in data["online_evidence"].items()},
                  fixtures={"original_recovery_disjoint_rosters": "passed",
                            "original_ordered_handoff_disposition": "passed"},
                  receipt=(receipt / "result.json").relative_to(root).as_posix())
    (receipt / "result.json").write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    return result


if __name__ == "__main__":
    repo, source, backend, output = sys.argv[1:]
    fixture(Path(repo), Path(source), backend, Path(output))
