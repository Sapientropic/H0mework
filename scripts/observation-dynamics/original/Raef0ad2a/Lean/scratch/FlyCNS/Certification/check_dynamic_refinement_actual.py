"""Independent actual-source audit; snapshots are comparisons, never inputs.

Run after the owning complete root has actually emitted through visit 58.
The frozen consumer separately materializes its complete packet and executes
the captured source. This checker independently reads its before-state basis,
literal comparisons, source guards, event indices and command dataflow.
"""

from __future__ import annotations

import argparse
import ast
from hashlib import sha256
import json
from pathlib import Path
import subprocess


HERE = Path(__file__).resolve().parent
OWNED = HERE.parent
REPOSITORY = OWNED.parents[2]
PYTHON = REPOSITORY / "Biomedical/Connectomics/.venv/bin/python"
SOURCE = OWNED / "full_dynamic_refinement.py"
EXPECTED = "e695cf792da4d216060f2264efee0d28b7fa8f57b428d562a5492d597aa69a29"
NAMES = tuple(f"{index}.npy" for index in range(52)) + (
    "neural.npz", "body.npz", "source-state.npz", "source.json", "words.json")
IDENTITY = {
    "instance_id": "male-cns-393a1613-ddc6-49c0-9226-9640883d0ec3",
    "occurrence_id": "fly-occurrence-6f3385a3-7f70-4ddb-8c80-d89661a7e42e",
    "installation_sha256": "5f91ca446b90b79ebcf8b77680976cf5378b6111392cbb2e1a236bb666192c4e",
}


def require(condition, reason):
    if not condition:
        raise AssertionError(reason)


def digest(path):
    result = sha256()
    with Path(path).open("rb") as source:
        while block := source.read(1 << 20):
            result.update(block)
    return result.hexdigest()


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def compare(left, right, names=NAMES):
    hashes = {}
    for name in names:
        raw = (left / name).read_bytes()
        require(raw == (right / name).read_bytes(), f"literal mismatch {left.name}/{right.name}/{name}")
        hashes[name] = sha256(raw).hexdigest()
    return sha256(canonical(hashes)).hexdigest()


def verify_dataflow():
    require(digest(SOURCE) == EXPECTED, "frozen Python consumer changed")
    tree = ast.parse(SOURCE.read_text())
    advance = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == "advance_representation")
    invocations = [node for node in ast.walk(advance) if isinstance(node, ast.Call) and
                   isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name) and
                   node.func.value.id == "subprocess" and node.func.attr == "run"]
    require(len(invocations) == 1, "source action is not the single fixed invocation")
    command = ast.unparse(invocations[0].args[0])
    require(command == "[str(PYTHON), str(Path(binding['root']) / 'primitive.py'), 'step', binding['root'], str(output / 'decoded'), str(generated)]",
            "unexpected source action arguments: " + command)
    require(not any(isinstance(node, ast.Constant) and isinstance(node.value, str) and
                    any(word in node.value for word in ("observed-", "independent-", "expected", "fixture"))
                    for node in ast.walk(advance)), "an expected snapshot entered source execution")
    detector = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == "detect_escape")
    added = next(node for node in detector.body if isinstance(node, ast.Assign) and
                 any(isinstance(target, ast.Name) and target.id == "added" for target in node.targets))
    require(not any(isinstance(node, ast.Name) and node.id in {"left_future", "right_future"}
                    for node in ast.walk(added.value)), "future output selected a refinement coordinate")
    return {"single_fixed_source_command": command, "expected_state_absent_from_source_call": True,
            "added_coordinates_use_original_states_only": True}


def audit(root, output, evidence_path):
    import numpy as np

    root, output = root.resolve(), output.resolve()
    flow = verify_dataflow()
    initial = json.loads((root / "initial/words.json").read_text())
    require(all(initial[key] == value for key, value in IDENTITY.items()), "another born root")
    fields = [row["name"] for row in initial["fields"]]
    require(len(fields) == len(set(fields)) == 52 and fields[35] == "body.controller_enabled", "another source inventory")
    installation = json.loads((root / "installation.json").read_text())
    require(installation["operations"] == [{"operation": "damage", "visit": 55}, {"operation": "repair", "visit": 58}],
            "the source operation law changed")
    admission = json.loads((REPOSITORY / "Biomedical/Connectomics/evidence/joint-memory-causality.json").read_text())["graph"]
    manifest_path = root / "raw/graph/manifest.json"
    require(digest(manifest_path) == admission["graph_manifest_sha256"], "original admitted graph differs")
    manifest = json.loads(manifest_path.read_text())
    raw_guards = []
    for row in manifest["source_files"]:
        expected = admission["source_files"][row["role"]]
        require(row["sha256"] == expected["sha256"] and row["size_bytes"] == expected["size_bytes"], "raw admission reference differs")
        path = root / "raw" / row["path"]
        require(path.stat().st_size == row["size_bytes"] and digest(path) == row["sha256"], "full original source changed")
        raw_guards.append({"role": row["role"], "bytes": row["size_bytes"], "sha256": row["sha256"]})
    for row in manifest["artifacts"].values():
        path = root / "raw" / row["path"]
        require(path.stat().st_size == row["size_bytes"] and digest(path) == row["sha256"], "complete admitted graph array differs")
    for row in installation["files"]:
        require(digest(row["path"]) == digest(root / row["relative"]), "prebirth installed source file changed")
    require(digest(REPOSITORY / "Biomedical/Connectomics/src/flycns/state_codec.py") ==
            digest(root / "programme/flycns/state_codec.py"), "consumer codec differs from captured source codec")
    activation_path = root / "activation-58.json"
    activation = json.loads(activation_path.read_text())
    require(len(activation["steps"]) == 58 and activation["field_count"] == 52, "actual source has not frozen the finite 58-visit prefix")
    require(activation["instance_id"] == IDENTITY["instance_id"] and activation["birth_occurrence"] == IDENTITY["occurrence_id"],
            "activation belongs to another root")
    for visit in range(55, 59):
        row = activation["steps"][visit - 1]
        require(row["before_visit"] == visit - 1 and row["after_visit"] == visit and row["complete_ledger_rows"] == 6,
                "actual operation is detached from original whole-ledger occurrence")
    images = [root / f"observed-{visit}" for visit in (55, 56, 57)]
    headers = [json.loads((image / "words.json").read_text()) for image in images]
    require([header["operation"] for header in headers] == ["neural", "damage", "neural"], "unexpected actual branches")
    gate = fields.index("body.controller_enabled")
    differing_before = [index for index in range(52) if
                        (images[0] / f"{index}.npy").read_bytes() != (images[1] / f"{index}.npy").read_bytes()]
    require(differing_before == [gate] and headers[0]["root_visit"] == 55 and headers[1]["root_visit"] == 56,
            "the original source-state attaching span differs")
    require(all(headers[0][key] == headers[1][key] for key in ("tick", "body_tick", "physics_tick")),
            "damage invented a microtick")
    future_different = [fields[index] for index in range(52) if index != gate and
                        (images[1] / f"{index}.npy").read_bytes() != (images[2] / f"{index}.npy").read_bytes()]
    require("body.integration" in future_different and "neural.tick" in future_different, "no actual autonomous future kernel escape")
    require(not output.exists(), "use a fresh independent consumer directory")
    command = [str(PYTHON), str(SOURCE), str(root), str(output)]
    run = subprocess.run(command, cwd=REPOSITORY, capture_output=True, text=True)
    evidence_path.parent.mkdir(parents=True, exist_ok=True)
    (output.parent / (output.name + ".log")).write_text(run.stdout + run.stderr)
    require(run.returncode == 0, "frozen actual consumer failed: " + run.stderr[-2500:])
    evidence = json.loads((output / "evidence.json").read_text())
    binding = json.loads((output / "source-binding.json").read_text())
    for row in binding["files"]:
        require(digest(row["path"]) == row["sha256"], "source guard changed during independent execution")
    refinement = evidence["source_state_refinement"]
    require(refinement["added_source_coordinates"] == ["word:body.controller_enabled", "visit"], "actual source coordinates differ")
    require(len(refinement["old_plan"]) == 51 and len(refinement["next_plan"]) == 53,
            "refinement did not preserve the complete old coordinate plan")
    require(refinement["next_plan"][:51] == refinement["old_plan"], "old projection changed")
    require(refinement["future_different_coordinates"] == ["word:" + name for name in future_different],
            "consumer future difference does not match independently read literal words")
    reopened = compare(images[1], output / "reopened")
    steps = []
    for index, visit in enumerate((57, 58), start=1):
        generated, actual = output / f"step-{index}/generated", root / f"observed-{visit}"
        fingerprint = compare(generated, actual, NAMES + ("generated-events.npz",))
        microtrace = compare(generated, actual, ("learning-trace.npz", "physics-trace.npz"))
        header = json.loads((generated / "words.json").read_text())
        require(header["root_visit"] == visit and header["operation"] == "neural", "packet selected another native letter")
        for key, value in IDENTITY.items():
            require(header[key] == value, "packet continuation changed source identity")
        with np.load(generated / "generated-events.npz", allow_pickle=False) as events:
            require(int(events["before_visit"]) == visit - 1 and int(events["after_visit"]) == visit,
                    "generated events have another support/next")
        steps.append({"after_visit": visit, "neural_tick": header["tick"], "physics_tick": header["physics_tick"],
                      "literal_58_sha256": fingerprint, "microtrace_sha256": microtrace})
    require([row["case"] for row in evidence["negative_controls"]] == ["descriptor", "visit", "missing-gate"] and
            all(row["rejected_before_source_event"] for row in evidence["negative_controls"]), "negative complete-packet controls differ")
    result = {"schema": "flycns-independent-dynamic-refinement-actual-audit/v1", "frozen_python_sha256": EXPECTED,
              "source_directory": str(root.relative_to(REPOSITORY)), "identity": IDENTITY, "source_command_dataflow": flow,
              "activation_prefix": str(activation_path.relative_to(REPOSITORY)), "activation_sha256": digest(activation_path),
              "raw_original_source_guards": raw_guards, "source_guarded_files": len(binding["files"]),
              "actual_before_visits": [55, 56], "actual_future_visits": [56, 57],
              "old_plan_words": 51, "source_origin_added": refinement["added_source_coordinates"],
              "future_different_words": future_different, "complete_current_files": 57,
              "complete_reopen_sha256": reopened, "packet_only_actual_successors": steps,
              "initial_codec": {key: value for key, value in evidence["initial_codec"].items() if key != "plan"},
              "negative_controls": evidence["negative_controls"],
              "evidence_sha256": digest(output / "evidence.json"), "consumer_sha256": digest(output / "consumer.py"),
              "basis_scope": "gate plus visit are actual original-state directions; different macro operation letters remain part of the fixed source",
              "activation_scope": "fresh captured fixed foreign primitive consumer; not late installation into the already-born Lean cap",
              "quotient_scope": "complete exact residual execution and local source-derived refinement; minimum behavioral partition not computed"}
    evidence_path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ("schema", "source_origin_added", "source_guarded_files", "complete_current_files")}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--evidence", type=Path, required=True)
    args = parser.parse_args()
    audit(args.root, args.output, args.evidence)


if __name__ == "__main__":
    main()
