"""Original all-prefix processes consume independently checked raw-model q boxes."""
import argparse
from fractions import Fraction as Q
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

import atomic_full_forward as full
import atomic_modes as mode_checker
import hardware_inverse as inverse
import mode_forward_run as forward
import raw_command_family as commands
from interval_prefix import IntervalPrefixChecker
from interval_prefix_independent import IntervalPrefixes

BASE, ROOT = inverse.BASE, full.ROOT
FILES = (*forward.FILES, "mode_prefix_run.py", "criterion-mp0001.md", "interval_prefix_independent.py",
         "test_interval_prefix_independent.py", "mode-forward-mi0001.json.gz", "likelihood.py", "independent.py")
PARENT_FILES = ("schema.py", "invariant_independent.py", "sources.json")


def bindings(commit):
    def git(*args):
        return subprocess.check_output(["git", "-C", str(ROOT), *args])
    revision = git("rev-parse", "--verify", commit + "^{commit}").decode().strip()
    result = []
    paths = (*[BASE / name for name in FILES], *[BASE.parent / name for name in PARENT_FILES],
             BASE / "primary-first-c0002.json", BASE.parents[1] / "theory-blind" / "independent_born.py")
    for path in paths:
        relative = path.relative_to(ROOT).as_posix()
        raw = git("show", revision + ":" + relative)
        if raw != path.read_bytes():
            raise ValueError("prefix science differs from freeze: " + relative)
        result.append({"path": relative, "sha256": hashlib.sha256(raw).hexdigest()})
    return revision, result


def load_parser(name, filename):
    spec = importlib.util.spec_from_file_location(name, BASE.parent / filename)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def source_tables(document):
    candidate = json.loads((BASE / "hardware-inverse-first-hi0002.json").read_text())
    tables = {}
    for run, raw_row in zip(document["runs"], candidate["runs"]):
        if run["run"] != raw_row["run"]:
            raise ValueError("original run order changed")
        sides = []
        for index, side in enumerate(("alice", "bob")):
            transfer = [[(Q.from_float(real), Q.from_float(imag)) for real, imag in row]
                        for row in raw_row["raw_transfers"][index]]
            d, eta = map(Q.from_float, raw_row["raw_parameters"][8 + 2 * index:10 + 2 * index])
            effects = []
            for setting, angle in enumerate(commands.SIDE_ANGLES[side]):
                saved = next(row for row in run["settings"] if row["side"] == side and row["setting"] == setting)
                entry = saved["witness"]
                path = BASE / entry["path"]
                if path.parent != BASE or path.name != entry["path"]:
                    raise ValueError("mode witness path outside registered corridor")
                packed = path.read_bytes()
                if len(packed) != entry["bytes"] or hashlib.sha256(packed).hexdigest() != entry["sha256"]:
                    raise ValueError("mode witness bytes changed")
                decoded = gzip.decompress(packed)
                if hashlib.sha256(decoded).hexdigest() != entry["decoded_sha256"]:
                    raise ValueError("mode decoded witness changed")
                witness = json.loads(decoded)
                program = commands.compile_commands(transfer, [inverse.raw_template()], angle, 240)
                if witness["raw_program"] != program.segments[0].record() or witness["mode_bits"] != 60:
                    raise ValueError("mode witness belongs to a different raw programme")
                certificate = mode_checker.certify(program.segments[0], witness["modes"], mode_bits=60,
                                                   coefficient_bits=160, exponential_bits=160)
                if str(Q(certificate["operator_error_bound"]) + program.command_trace_norm_error) != saved["combined_operator_error"]:
                    raise ValueError("mode source certificate differs from first")
                effects.append(forward.detector(forward.qubit_ion_effect(certificate, program.command_trace_norm_error), d, eta))
                print(json.dumps({"source_checked": run["run"], "side": side, "setting": setting}), flush=True)
            sides.append(effects)
        rows = [{"h": h, "a": a, "b": b, "x": x, "y": y,
                 **commands.tensor_born(sides[0][a], sides[1][b], h, x, y)}
                for h in (0, 1) for a in (0, 1) for b in (0, 1) for x in (0, 1) for y in (0, 1)]
        if rows != run["source_probability_enclosures"]:
            raise ValueError("source probability enclosures changed")
        tables[run["run"]] = {(h, a, b): [tuple(map(Q, row["probability_interval"])) for row in rows
                                          if (row["h"], row["a"], row["b"]) == (h, a, b)]
                                    for h in (0, 1) for a in (0, 1) for b in (0, 1)}
    return tables


def execute(commit, directory):
    document = json.loads(gzip.decompress((BASE / "mode-forward-mi0001.json.gz").read_bytes()))
    if document["schema"] != "stage10-raw-hardware-mode-forward-mi0001/v1" or document["status"] != "source_probability_enclosures_generated":
        raise ValueError("registered complete mode forward required")
    tables = source_tables(document)
    primary_parser = load_parser("_mp0001_original_schema", "schema.py")
    independent_parser = load_parser("_mp0001_independent_schema", "invariant_independent.py")
    old = json.loads((BASE / "primary-first-c0002.json").read_text())
    results = []
    for spec, independent_spec, previous in zip(primary_parser.ARCHIVES, independent_parser.ARCHIVE_IDENTITIES, old["runs"]):
        admitted = primary_parser.admit_archive(directory, spec)
        checked = independent_parser.archive_run((directory / spec.name).read_bytes(), independent_spec)
        bits = lambda trial: (trial.row, trial.h, trial.a, trial.b, trial.x, trial.y)
        if [bits(t) for t in admitted.trials] != [bits(t) for t in checked.trials]:
            raise ValueError("original complete trials disagree across parsers")
        first, second = IntervalPrefixChecker(tables[spec.run], 80), IntervalPrefixes(tables[spec.run], 240)
        cross = hashlib.sha256()
        for p, q in zip(admitted.trials, checked.trials):
            a, b = first.step(p.h, p.a, p.b, p.x, p.y), second.step(q)
            if max(Q(a.lower), Q(b.lo, second.arithmetic.scale)) > min(Q(a.upper), Q(b.hi, second.arithmetic.scale)):
                raise ValueError("prefix numerical enclosures do not intersect")
            cross.update(bytes((p.h, p.a, p.b, p.x, p.y)))
        primary, independent = first.result(), second.result()
        if (primary["trials"] != previous["trials"] or primary["trial_bit_sequence_sha256"] != previous["trial_bit_sequence_sha256"]
                or primary["trial_bit_sequence_sha256"] != independent["trial_bit_sequence_sha256"]
                or primary["counts"] != independent["counts"] or primary["pooled_counts"] != independent["pooled_counts"]
                or primary["all_prefixes_below_threshold_certified"] != independent["all_prefixes_below_threshold_certified"]):
            raise ValueError("complete original counts/prefix verdict changed across implementations")
        independent.pop("prefix_log_e")
        results.append({"run": spec.run, "primary": primary, "independent": independent,
                        "all_prefix_intersections_checked": True, "all_original_trial_bits_sha256": cross.hexdigest(),
                        "raw_source_membership_verified": True,
                        "raw_model_joint_witness_verified": primary["all_prefixes_below_threshold_certified"]})
        print(json.dumps({"run": spec.run, "status": primary["status"], "trials": primary["trials"]}), flush=True)
    bindings(commit)
    return {"schema": "stage10-raw-hardware-joint-prefix-mp0001/v1", "status": "all_original_prefixes_scored",
            "runs": results, "familywise_alpha": "1/20", "new_confidence_budget_spent": False,
            "actual_hardware_uniquely_identified": False, "controller_advance": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-commit", required=True)
    parser.add_argument("--directory", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    commit, sources = bindings(args.freeze_commit)
    if args.output.exists():
        raise FileExistsError(args.output)
    with args.output.with_name(args.output.stem + "-attempt.json").open("x") as stream:
        json.dump({"freeze_commit": commit, "source_bindings": sources}, stream, indent=2); stream.write("\n")
    try:
        result = execute(commit, args.directory)
    except Exception as error:
        result = {"schema": "stage10-raw-hardware-joint-prefix-mp0001/v1", "status": "failed",
                  "error_type": type(error).__name__, "error": str(error)}
        with args.output.open("x") as stream:
            json.dump({**result, "freeze_commit": commit, "source_bindings": sources}, stream, indent=2); stream.write("\n")
        raise
    with args.output.open("x") as stream:
        json.dump({**result, "freeze_commit": commit, "source_bindings": sources}, stream, indent=2, sort_keys=True); stream.write("\n")


if __name__ == "__main__":
    main()
