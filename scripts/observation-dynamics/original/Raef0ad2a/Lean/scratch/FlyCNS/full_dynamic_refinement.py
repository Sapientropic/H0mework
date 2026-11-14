"""Actual source-kernel escape and exact residual execution consumer.

An old view can omit source state while the complete materialized packet
continues to retain it.  Actual completed successors diagnose that failure;
the refined coordinates are read from the original states.  This consumer
does not replace the fixed primitive, its source law or its operation schedule.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import zipfile

HERE = Path(__file__).resolve().parent
REPOSITORY = HERE.parents[2]
PYTHON = REPOSITORY / "Biomedical/Connectomics/.venv/bin/python"
sys.path.insert(0, str(REPOSITORY / "Biomedical/Connectomics/src"))

import numpy as np
from flycns.state_codec import _decode_file, _zero64_encode

FILES = tuple(f"{index}.npy" for index in range(52)) + (
    "neural.npz", "body.npz", "source-state.npz", "source.json", "words.json")
PRIMITIVE_SHA = "a3706e1153a32de182831ff81c11101434bba3fc4b2888d1db205db8408d3a17"
CONTENT_SHA = "68fb9d631a181a55de9297e05121859c426d251d4d353f9b34841389e31c746b"
PACKET_SCHEMA = "flycns-full-dynamic-residual-packet/v1"
IDENTITY = ("instance_id", "occurrence_id", "installation_sha256")


class RefinementRejected(ValueError):
    pass


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


def file_digest(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as source:
        while block := source.read(1 << 20):
            result.update(block)
    return result.hexdigest()


def require(condition, reason):
    if not condition:
        raise RefinementRejected(reason)


def descriptor(raw):
    stream = io.BytesIO(raw)
    version = np.lib.format.read_magic(stream)
    if version == (1, 0):
        shape, order, dtype = np.lib.format.read_array_header_1_0(stream)
    elif version == (2, 0):
        shape, order, dtype = np.lib.format.read_array_header_2_0(stream)
    else:
        raise RefinementRejected("unsupported literal word version")
    require(not order and len(shape) == 1 and not dtype.hasobject,
            "source word is not a literal flat primitive array")
    result = {"dataStart": stream.tell(), "width": dtype.itemsize, "count": shape[0]}
    require(len(raw) == result["dataStart"] + result["width"] * result["count"],
            "source word extent differs from its interpretation")
    return result


def source_binding(root):
    root = Path(root).resolve()
    installation = json.loads((root / "installation.json").read_bytes())
    initial = json.loads((root / "initial/words.json").read_bytes())
    require(file_digest(root / "primitive.py") == PRIMITIVE_SHA, "another fixed source primitive")
    require(file_digest(root / "programme/flycns/content_driver.py") == CONTENT_SHA,
            "another prebirth executed content programme")
    paths = {root / name for name in ("primitive.py", "installation.json", "parameters.json", "body.mjb")}
    for row in installation["files"]:
        paths.update((Path(row["path"]).resolve(), (root / row["relative"]).resolve()))
    paths.update(path for path in (root / "raw").rglob("*")
                 if path.is_file() and path.suffix not in (".pyc", ".nbi", ".nbc"))
    binding = {"schema": "flycns-fixed-full-dynamic-source/v1", "root": str(root),
               **{key: initial[key] for key in IDENTITY},
               "fields": [row["name"] for row in initial["fields"]],
               "files": [{"path": str(path), "sha256": file_digest(path)} for path in sorted(paths)]}
    require(len(binding["fields"]) == 52 and len(set(binding["fields"])) == 52,
            "source field inventory is incomplete or aliased")
    binding["binding_sha256"] = digest(canonical(binding))
    return binding


def guard_source(binding):
    raw = {key: value for key, value in binding.items() if key != "binding_sha256"}
    require(digest(canonical(raw)) == binding["binding_sha256"], "fixed source binding was rewritten")
    for row in binding["files"]:
        require(file_digest(row["path"]) == row["sha256"], "fixed source material changed: " + row["path"])


def identity_matches(document, binding):
    require(all(document[key] == binding[key] for key in IDENTITY), "another source occurrence")


def read_current(directory, binding):
    directory = Path(directory)
    files = {name: (directory / name).read_bytes() for name in FILES}
    header = json.loads(files["words.json"])
    identity_matches(header, binding)
    require([row["name"] for row in header["fields"]] == binding["fields"], "another complete field order")
    require(type(header["root_visit"]) is int and header["root_visit"] >= 0, "invalid registered root visit")
    descriptions = [descriptor(files[f"{index}.npy"]) for index in range(52)]
    return files, header, descriptions


def basis(binding):
    return ["word:" + name for name in binding["fields"]] + ["visit"]


def checked_plan(plan, binding):
    require(isinstance(plan, list) and all(isinstance(key, str) for key in plan), "nonmaterial coordinate inventory")
    require(len(set(plan)) == len(plan) and set(plan) <= set(basis(binding)), "unknown or repeated source coordinate")
    return plan


def coordinate(key, image, binding):
    files, header, descriptions = image
    if key == "visit":
        return ("visit", header["root_visit"])
    require(key in basis(binding), "coordinate does not belong to the independent source basis")
    index = binding["fields"].index(key.removeprefix("word:"))
    # Literal NPY plus its whole interpretation; no float averaging/tolerance.
    return (files[f"{index}.npy"], canonical(descriptions[index]))


def view(plan, image, binding):
    return [coordinate(key, image, binding) for key in checked_plan(plan, binding)]


def detect_escape(plan, left, right, left_future, right_future, binding):
    old_left, old_right = view(plan, left, binding), view(plan, right, binding)
    if old_left != old_right:
        return None
    if view(plan, left_future, binding) == view(plan, right_future, binding):
        return None
    # Only original before-state data generate the attaching directions.
    added = [key for key in basis(binding) if key not in plan and
             coordinate(key, left, binding) != coordinate(key, right, binding)]
    require(added, "a different actual successor has no original source-state direction")
    next_plan = plan + added
    require(view(next_plan, left, binding) != view(next_plan, right, binding), "refinement did not split the old fibre")
    require(view(next_plan, left, binding)[:len(plan)] == old_left and
            view(next_plan, right, binding)[:len(plan)] == old_right, "refinement changed the old projection")
    return {"added_source_coordinates": added, "old_plan": plan, "next_plan": next_plan,
            "future_different_coordinates": [key for key in plan if
                coordinate(key, left_future, binding) != coordinate(key, right_future, binding)]}


def encode_representation(directory, plan, destination, binding):
    started = time.perf_counter()
    files, header, descriptions = read_current(directory, binding)
    checked_plan(plan, binding)
    destination = Path(destination)
    destination.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(dir=destination.parent, prefix=destination.name + ".")
    os.close(fd)
    try:
        rows = []
        with zipfile.ZipFile(temporary, "w", compression=zipfile.ZIP_STORED) as archive:
            for name, raw in files.items():
                encoded = _zero64_encode(raw)
                rows.append({"name": name, "size_bytes": len(raw), "stored_bytes": len(encoded), "sha256": digest(raw)})
                archive.writestr(name + ".zero64", encoded)
            manifest = {"schema": PACKET_SCHEMA, "binding_sha256": binding["binding_sha256"],
                        **{key: header[key] for key in IDENTITY}, "plan": plan,
                        "root_visit": header["root_visit"], "files": rows,
                        "word_descriptors": descriptions, "raw_bytes": sum(len(raw) for raw in files.values())}
            archive.writestr("representation.json", canonical(manifest))
        os.replace(temporary, destination)
        return {"raw_bytes": manifest["raw_bytes"], "packet_bytes": destination.stat().st_size,
                "packet_sha256": file_digest(destination), "encode_seconds": time.perf_counter() - started}
    finally:
        Path(temporary).unlink(missing_ok=True)


def decode_representation(packet, destination, binding, *, max_bytes=128 << 20):
    started = time.perf_counter()
    destination = Path(destination)
    if destination.exists():
        raise FileExistsError(destination)
    destination.parent.mkdir(parents=True, exist_ok=True)
    temporary = Path(tempfile.mkdtemp(dir=destination.parent, prefix=destination.name + "."))
    try:
        with zipfile.ZipFile(packet) as archive:
            expected = {name + ".zero64" for name in FILES} | {"representation.json"}
            require(len(archive.namelist()) == len(expected) and set(archive.namelist()) == expected,
                    "representation omits or aliases a complete source file")
            require(archive.getinfo("representation.json").file_size <= 1 << 20, "oversized material manifest")
            manifest = json.loads(archive.read("representation.json"))
            require(manifest["schema"] == PACKET_SCHEMA and manifest["binding_sha256"] == binding["binding_sha256"],
                    "representation uses another fixed source")
            identity_matches(manifest, binding)
            checked_plan(manifest["plan"], binding)
            rows = manifest["files"]
            require([row["name"] for row in rows] == list(FILES), "incomplete ordered literal inventory")
            sizes = [row["size_bytes"] for row in rows]
            require(all(type(size) is int and size >= 0 for size in sizes) and
                    sum(sizes) == manifest["raw_bytes"] and sum(sizes) <= max_bytes, "invalid decoded byte budget")
            require(len(manifest["word_descriptors"]) == 52, "interpretation inventory is incomplete")
            for row in rows:
                name = row["name"]
                require(type(row["stored_bytes"]) is int and row["stored_bytes"] >= 0 and
                        archive.getinfo(name + ".zero64").file_size == row["stored_bytes"], "packed extent differs")
                with archive.open(name + ".zero64") as source, (temporary / name).open("wb") as target:
                    _decode_file(source, target, row, "zero64")
        _, header, descriptions = read_current(temporary, binding)
        require(descriptions == manifest["word_descriptors"], "packet and parsed original word interpretations differ")
        require(type(manifest["root_visit"]) is int and header["root_visit"] == manifest["root_visit"],
                "packet lost the source-owned autonomous visit")
        os.rename(temporary, destination)
        return {"plan": manifest["plan"], "root_visit": manifest["root_visit"],
                "decode_seconds": time.perf_counter() - started}
    finally:
        shutil.rmtree(temporary, ignore_errors=True)


def advance_representation(binding, packet, output):
    """The only mutable source input is the decoded complete residual."""
    guard_source(binding)
    output = Path(output)
    if output.exists():
        raise FileExistsError(output)
    output.mkdir(parents=True)
    decoded = decode_representation(packet, output / "decoded", binding)
    generated = output / "generated"
    started = time.perf_counter()
    result = subprocess.run([str(PYTHON), str(Path(binding["root"]) / "primitive.py"), "step", binding["root"],
                             str(output / "decoded"), str(generated)], cwd=REPOSITORY, capture_output=True, text=True)
    (output / "source-execution.log").write_text(result.stdout + result.stderr)
    require(result.returncode == 0, "the fixed source rejected the complete materialized residual")
    execution_seconds = time.perf_counter() - started
    encoded = encode_representation(generated, decoded["plan"], output / "next.packet", binding)
    _, header, _ = read_current(generated, binding)
    require(header["root_visit"] == decoded["root_visit"] + 1, "native next visit did not advance")
    return {**encoded, **decoded, "after_visit": header["root_visit"], "operation": header["operation"],
            "neural_tick": header["tick"], "body_tick": header["body_tick"], "physics_tick": header["physics_tick"],
            "source_execution_seconds": execution_seconds, "packet": str(output / "next.packet")}


def same_files(left, right, names=FILES):
    rows = {}
    for name in names:
        first = (Path(left) / name).read_bytes()
        require(first == (Path(right) / name).read_bytes(), "literal source difference: " + name)
        rows[name] = digest(first)
    return digest(canonical(rows))


def malformed_controls(packet, binding, output):
    output.mkdir()
    with zipfile.ZipFile(packet) as source:
        contents = {name: source.read(name) for name in source.namelist()}
    results = []
    for case in ("descriptor", "visit", "missing-gate"):
        damaged = dict(contents)
        manifest = json.loads(damaged["representation.json"])
        if case == "descriptor":
            manifest["word_descriptors"][0]["width"] *= 2
        elif case == "visit":
            manifest["root_visit"] += 1
        else:
            gate = binding["fields"].index("body.controller_enabled")
            del damaged[f"{gate}.npy.zero64"]
        damaged["representation.json"] = canonical(manifest)
        candidate = output / (case + ".packet")
        with zipfile.ZipFile(candidate, "w", compression=zipfile.ZIP_STORED) as archive:
            for name, raw in damaged.items():
                archive.writestr(name, raw)
        target = output / (case + "-decoded")
        try:
            decode_representation(candidate, target, binding)
        except RefinementRejected as error:
            require(not target.exists(), "a rejected partial decode was exposed as a complete state")
            results.append({"case": case, "rejected_before_source_event": True, "reason": str(error)})
        else:
            raise RefinementRejected("a malformed complete residual was accepted: " + case)
    return results


def consume(root, output, *, left_visit=55, right_visit=56, advances=2):
    root, output = Path(root).resolve(), Path(output).resolve()
    require(not output.exists(), "use a fresh actual-consumer output directory")
    output.mkdir(parents=True)
    shutil.copyfile(__file__, output / "consumer.py")
    shutil.copyfile(HERE / "BodyFullDynamicRefinement.lean", output / "BodyFullDynamicRefinement.lean")
    binding = source_binding(root)
    (output / "source-binding.json").write_bytes(canonical(binding))
    activation = json.loads((root / "activation.json").read_bytes())
    require(activation["instance_id"] == binding["instance_id"] and
            activation["birth_occurrence"] == binding["occurrence_id"] and activation["field_count"] == 52,
            "actual source activation has another identity or inventory")
    visits = (left_visit, right_visit, left_visit + 1, right_visit + 1)
    for visit in visits:
        require(0 < visit <= len(activation["steps"]), "required actual source occurrence has not been emitted")
        row = activation["steps"][visit - 1]
        require(row["after_visit"] == visit and row["complete_ledger_rows"] == 6,
                "the coordinate consumer detached from the actual complete root patch")
    left, right, left_future, right_future = [read_current(root / f"observed-{visit}", binding) for visit in visits]
    plan = ["word:" + name for name in binding["fields"] if name != "body.controller_enabled"]
    escape = detect_escape(plan, left, right, left_future, right_future, binding)
    require(escape is not None, "the actual pair does not escape this old source view")
    require(escape["added_source_coordinates"] == ["word:body.controller_enabled", "visit"],
            "this actual original-state pair has a different attaching span")
    require(detect_escape(plan, left, left, left_future, left_future, binding) is None,
            "equal actual branches were reported as a refinement demand")
    next_plan = escape["next_plan"]
    require(detect_escape(next_plan, left, right, left_future, right_future, binding) is None,
            "an already separated before-state pair still counted as a kernel escape")
    body_index = binding["fields"].index("body.integration")
    require(left_future[0][f"{body_index}.npy"] != right_future[0][f"{body_index}.npy"],
            "no actual future physical integration difference")
    encoded = encode_representation(root / f"observed-{right_visit}", next_plan, output / "initial.packet", binding)
    decoded = decode_representation(output / "initial.packet", output / "reopened", binding)
    reopened_sha = same_files(root / f"observed-{right_visit}", output / "reopened")
    negative = malformed_controls(output / "initial.packet", binding, output / "negative-controls")
    packet = output / "initial.packet"
    steps = []
    for index in range(advances):
        step_output = output / f"step-{index + 1}"
        result = advance_representation(binding, packet, step_output)
        actual = root / f"observed-{result['after_visit']}"
        require(actual.exists(), "execute comparisons only after the owning root emitted the finite successor")
        result["same_58_literal_sha256"] = same_files(step_output / "generated", actual, FILES + ("generated-events.npz",))
        if result["operation"] == "neural":
            result["same_microtrace_sha256"] = same_files(step_output / "generated", actual,
                                                           ("learning-trace.npz", "physics-trace.npz"))
        result["coordinate_plan_preserved"] = result.pop("plan") == next_plan
        steps.append(result)
        packet = Path(result["packet"])
    guard_source(binding)
    evidence = {"schema": "flycns-full-source-dynamic-refinement-actual/v1", "instance_id": binding["instance_id"],
                "birth_occurrence": binding["occurrence_id"], "installation_sha256": binding["installation_sha256"],
                "source_directory": str(root.relative_to(REPOSITORY)), "binding_sha256": binding["binding_sha256"],
                "source_guarded_files": len(binding["files"]), "basis": "52 literal words/interpretations + original root visit",
                "actual_branches": {"left_before_visit": left_visit, "right_before_visit": right_visit,
                                    "left_after_visit": left_visit + 1, "right_after_visit": right_visit + 1},
                "old_kernel_exact_equal": True, "actual_future_physical_difference": True,
                "source_state_refinement": escape, "old_projection_preserved": True,
                "complete_residual_files": len(FILES), "complete_reopen_sha256": reopened_sha,
                "initial_codec": {**encoded, **decoded, "raw_reduction_percent":
                    100 * (1 - encoded["packet_bytes"] / encoded["raw_bytes"])},
                "actual_autonomous_steps": steps, "negative_controls": negative,
                "consumer_sha256": file_digest(output / "consumer.py"),
                "lean_candidate_sha256": file_digest(output / "BodyFullDynamicRefinement.lean"),
                "scope": "actual source-derived refinement and complete residual execution; no computed minimum behavioral quotient",
                "activation_scope": "new consumer executes captured fixed foreign primitive; frozen Lean cap retains its own actual history"}
    (output / "evidence.json").write_bytes(canonical(evidence))
    return evidence


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--left-visit", type=int, default=55)
    parser.add_argument("--right-visit", type=int, default=56)
    parser.add_argument("--advances", type=int, default=2)
    args = parser.parse_args()
    require(args.advances >= 1, "consume at least one actual autonomous continuation")
    evidence = consume(args.root, args.output, left_visit=args.left_visit, right_visit=args.right_visit, advances=args.advances)
    print(json.dumps({"schema": evidence["schema"], "new_coordinates": evidence["source_state_refinement"]["added_source_coordinates"],
                      "steps": len(evidence["actual_autonomous_steps"]), "report": str(args.output / "evidence.json")}, ensure_ascii=False))


if __name__ == "__main__":
    main()
