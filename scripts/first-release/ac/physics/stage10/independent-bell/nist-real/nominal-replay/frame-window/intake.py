#!/usr/bin/env python3
"""Lossless source intake and compact indexes of reproducible fringe coefficients."""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

HERE = Path(__file__).resolve().parent
FULL_SHA = "15ee9b8dba95a45fcc8d1775a412e27a5107fce026c3fc97815069e5ce3bb8d1"
SCIENCE_FREEZE = "4af1a446b0"
FIRST = Path("/tmp/p23-fw-primary-first.json")


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def coefficient_hash(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def compact_probe(probe, prefix, omitted):
    result = copy.deepcopy(probe)
    for key in ("U", "A", "B", "derivative_polynomial"):
        values = result.pop(key)
        result[key+"_coefficients"] = {"degree": len(values)-1, "sha256": coefficient_hash(values),
                                      "rebuild_from_frozen_generator": True}
        omitted.append(prefix+"/"+key)
    inventory = result["root_inventory"]
    square_free = inventory.pop("square_free_polynomial")
    inventory["square_free_coefficients"] = {"degree": len(square_free)-1, "sha256": coefficient_hash(square_free)}
    inventory["gcd_degree"] = result["derivative_polynomial_coefficients"]["degree"]-(len(square_free)-1)
    omitted.append(prefix+"/root_inventory/square_free_polynomial")
    chains = inventory["chains"]
    for identity, row in chains.items():
        polynomial, sequence = row.pop("polynomial"), row.pop("sequence")
        row.update({"polynomial_degree": len(polynomial)-1, "polynomial_sha256": coefficient_hash(polynomial),
                    "sequence_degrees": [len(p)-1 for p in sequence], "sequence_sha256": coefficient_hash(sequence)})
        omitted.extend((prefix+"/root_inventory/chains/"+identity+"/polynomial",
                        prefix+"/root_inventory/chains/"+identity+"/sequence"))
    return result


def compact(full):
    result = copy.deepcopy(full)
    omitted = []
    for i, point in enumerate(result["points"]):
        if "calibration_readouts" not in point:
            continue
        calibration = point["calibration_readouts"]
        prefix = "/points/"+str(i)+"/calibration_readouts"
        calibration["threshold_probes"] = [compact_probe(probe, prefix+"/threshold_probes/"+str(j), omitted)
                                            for j, probe in enumerate(calibration["threshold_probes"])]
        for name in ("HV_full_fringe", "DA_full_fringe"):
            for side in ("left_probe", "right_probe"):
                calibration[name][side] = compact_probe(calibration[name][side], prefix+"/"+name+"/"+side, omitted)
    result["scientific_schema"] = result["schema"]
    result["schema"] = "p23-frame-window-primary-intake/v1"
    result["derivative_intake"] = {"full_scientific_json_sha256": FULL_SHA,
                                    "scientific_generator_freeze": SCIENCE_FREEZE,
                                    "coefficient_fields_omitted": omitted,
                                    "all_source_calibration_probability_and_root_fields_preserved": True,
                                    "intake_is_original_first_scientific_json": False}
    return result


def source_snapshot(full):
    rows = []
    for point in full["points"]:
        row = {key: copy.deepcopy(point[key]) for key in
               ("point", "outcome", "failure_reason", "partial_point_discarded", "source_parameters",
                "phase_flip_probability_enclosure", "source_construction") if key in point}
        if "calibration_readouts" in point:
            row["calibration_root_descriptor"] = copy.deepcopy(point["calibration_readouts"]["lambda_root"])
        rows.append(row)
    return {"schema": "p23-frame-window-source-snapshot/v1", "scientific_schema": full["schema"],
            "version": full["version"], "full_scientific_json_sha256": FULL_SHA,
            "criterion_freeze": full["criterion_freeze"], "executable_freeze": full["executable_freeze"],
            "bindings": full["bindings"], "point_count": full["point_count"], "points": rows,
            **{key: value for key, value in full.items() if key.endswith("_identified") or
               key in ("production_admitted", "bell_event_files_read", "retrospective")}}


def recompute_checkpoints(full, fw):
    config, _, _, _, gaussian, _, _ = fw.inputs()
    checks = []
    for i, row in enumerate(full["points"]):
        if "calibration_readouts" not in row:
            continue
        for j in (0, 1):
            probe = row["calibration_readouts"]["threshold_probes"][j]
            _, rebuilt = fw.fringe_extrema(row["source_parameters"], fw.F(probe["lambda"]), probe["axis"],
                                           config, gaussian, probe["refinement_depth"])
            rebuilt = fw.serial(rebuilt)
            require(canonical(rebuilt) == canonical(probe), "FROZEN_FRINGE_CHECKPOINT_CHANGED")
            checks.append({"point_index": i, "probe_index": j, "byte_canonical_equal": True,
                           "full_probe_sha256": coefficient_hash(probe)})
    return checks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--recompute-checkpoints", action="store_true")
    parser.add_argument("--recompute-full", action="store_true")
    args = parser.parse_args()
    import forward as fw
    fw.committed(Path(__file__).resolve())
    relative = fw.relative(HERE/"forward.py")
    require(subprocess.check_output(["git", "show", SCIENCE_FREEZE+":"+relative], cwd=fw.ROOT) ==
            (HERE/"forward.py").read_bytes(), "SCIENTIFIC_GENERATOR_CHANGED")
    original = FIRST.read_bytes()
    require(hashlib.sha256(original).hexdigest() == FULL_SHA, "FIRST_SCIENTIFIC_JSON_CHANGED")
    full = json.loads(original)
    if args.recompute_full:
        rebuilt = (json.dumps(fw.generate(), indent=2, allow_nan=False)+"\n").encode()
        require(rebuilt == original, "FROZEN_FULL_SCIENTIFIC_REGENERATION_CHANGED")
    checks = recompute_checkpoints(full, fw) if args.recompute_checkpoints else []
    derived, snapshot = compact(full), source_snapshot(full)
    require(source_snapshot(derived)["points"] == snapshot["points"], "SOURCE_SNAPSHOT_LOST_CONTENT")
    prior = HERE/"forward.json"
    if prior.exists() and hashlib.sha256(prior.read_bytes()).hexdigest() == FULL_SHA:
        backup = Path("/tmp/p23-fw-primary-first-directory-copy.json")
        shutil.copyfile(prior, backup)
        require(backup.read_bytes() == original, "FIRST_DIRECTORY_COPY_CHANGED")
    for path, value in ((prior, derived), (HERE/"forward-source.json", snapshot)):
        path.write_text(json.dumps(value, indent=2, allow_nan=False)+"\n")
    receipt = {"schema": "p23-frame-window-storage-intake/v1", "full_scientific_json_sha256": FULL_SHA,
               "frozen_scientific_generator": SCIENCE_FREEZE, "compact_sha256": fw.digest(prior),
               "source_snapshot_sha256": fw.digest(HERE/"forward-source.json"),
               "omitted_coefficient_field_count": len(derived["derivative_intake"]["coefficient_fields_omitted"]),
               "recompute_checkpoints": checks, "source_and_probability_values_changed": False,
               "first_scientific_json_changed": False}
    (HERE/"storage-intake.json").write_text(json.dumps(receipt, indent=2)+"\n")
    print(json.dumps({"storage_adapter_completed": True, "compact_bytes": prior.stat().st_size,
                      "source_snapshot_bytes": (HERE/"forward-source.json").stat().st_size,
                      "full_scientific_json_sha256": FULL_SHA, "compact_sha256": receipt["compact_sha256"],
                      "source_snapshot_sha256": receipt["source_snapshot_sha256"],
                      "recomputed_checkpoint_count": len(checks)}, indent=2))


if __name__ == "__main__":
    main()
