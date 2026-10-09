"""Frozen raw inverse candidates to checked full-atom effect enclosures."""
import argparse
from fractions import Fraction as Q
import gzip
import hashlib
import json
from pathlib import Path
import subprocess

import atomic_dipole as dipole
import atomic_full_forward as full
import atomic_modes as checker
import atomic_modes_search as producer
import hardware_inverse as inverse
import raw_command_family as commands

BASE, ROOT = inverse.BASE, full.ROOT
FILES = ("criterion-mi0001.md", "mode_forward_run.py", "atomic_modes.py", "atomic_modes_search.py",
         "test_atomic_modes.py", "raw_command_family.py", "test_raw_command_family.py",
         "atomic_qutrit_channel.py", "test_atomic_qutrit_channel.py", "atom_photon_source.py",
         "test_atom_photon_source.py", "interval_prefix.py", "test_interval_prefix.py",
         "atomic_search.py", "hardware_inverse.py", "atomic_full_forward.py", "atomic_dipole.py",
         "hardware-inverse-first-hi0002.json", "hardware-forward-sources.json")


def bindings(commit):
    def git(*args):
        return subprocess.check_output(["git", "-C", str(ROOT), *args])
    revision = git("rev-parse", "--verify", commit + "^{commit}").decode().strip()
    result = []
    for name in FILES:
        path = BASE / name
        relative = path.relative_to(ROOT).as_posix()
        raw = git("show", revision + ":" + relative)
        if raw != path.read_bytes():
            raise ValueError("mode science differs from freeze: " + relative)
        result.append({"path": relative, "sha256": hashlib.sha256(raw).hexdigest()})
    return revision, result


def qubit_ion_effect(report, extra_error=Q(0)):
    operator = {(i, j): (Q(real), Q(imag)) for i, j, real, imag in report["observable_center"]}
    bridge = dipole.source_qubit_bridge()
    vectors = [bridge[name] for name in ("u_x", "d_x")]
    matrix, error = [], Q(report["operator_error_bound"]) + extra_error
    for left in vectors:
        row = []
        for right in vectors:
            value = dipole.ComplexRadical()
            for i, a in left.items():
                for j, b in right.items():
                    real, imag = operator.get((i, j), (0, 0))
                    value += a.conjugate() * dipole.ComplexRadical(real, imag) * b
            row.append((value.real.as_rational(), value.imag.as_rational()))
        matrix.append(row)
    return {"00": [str(matrix[0][0][0] - error), str(matrix[0][0][0] + error)],
            "11": [str(matrix[1][1][0] - error), str(matrix[1][1][0] + error)],
            "01": {"real": [str(matrix[0][1][0] - error), str(matrix[0][1][0] + error)],
                   "imag": [str(matrix[0][1][1] - error), str(matrix[0][1][1] + error)]},
            "10": {"real": [str(matrix[1][0][0] - error), str(matrix[1][0][0] + error)],
                   "imag": [str(matrix[1][0][1] - error), str(matrix[1][0][1] + error)]}}


def detector(ion, d, eta):
    d, eta = commands.probability(d), commands.probability(eta)
    k = (1 - d) * eta
    a, b = commands.Interval.read(ion["00"]), commands.Interval.read(ion["11"])
    real, imag = commands.Interval.read(ion["01"]["real"]), commands.Interval.read(ion["01"]["imag"])
    zero = commands.Interval(0, 0)
    off = commands.ComplexInterval(-2 * k * real, -2 * k * imag)
    operator = ((commands.ComplexInterval((1 - 2 * d) - 2 * k * a, zero), off),
                (off.conjugate(), commands.ComplexInterval((1 - 2 * d) - 2 * k * b, zero)))
    return commands.DetectorEffect(operator, {"mu": (1 - 2 * d) - k * (a + b), "u": -2 * k * real,
                                            "v": 2 * k * imag, "z": -k * (a - b)}, ion)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-commit", required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    commit, sources = bindings(args.freeze_commit)
    if args.output.exists():
        raise FileExistsError(args.output)
    with args.output.with_name(args.output.stem + "-attempt.json").open("x") as stream:
        json.dump({"freeze_commit": commit, "source_bindings": sources}, stream, indent=2); stream.write("\n")
    candidate = json.loads((BASE / "hardware-inverse-first-hi0002.json").read_text())
    reports = []
    try:
        for run in candidate["runs"]:
            side_effects, settings = [], []
            for index, side in enumerate(("alice", "bob")):
                raw_transfer = [[(Q.from_float(real), Q.from_float(imag)) for real, imag in row]
                                for row in run["raw_transfers"][index]]
                d, eta = map(Q.from_float, run["raw_parameters"][8 + 2 * index:10 + 2 * index])
                effects = []
                for setting, angle in enumerate(commands.SIDE_ANGLES[side]):
                    program = commands.compile_commands(raw_transfer, [inverse.raw_template()], angle, 240)
                    raw = program.segments[0]
                    modes = producer.generate(raw, mode_bits=60, threshold=1e-13)
                    report = checker.certify(raw, modes, mode_bits=60, coefficient_bits=160, exponential_bits=160)
                    error = Q(report["operator_error_bound"]) + program.command_trace_norm_error
                    if error > Q(1, 10 ** 6):
                        raise ValueError("mode operator enclosure exceeds registered width")
                    ion = qubit_ion_effect(report, program.command_trace_norm_error)
                    effect = detector(ion, d, eta)
                    effects.append(effect)
                    raw_witness = json.dumps({"raw_program": raw.record(), "mode_bits": 60, "modes": modes},
                                             sort_keys=True, separators=(",", ":")).encode()
                    witness = gzip.compress(raw_witness, compresslevel=9, mtime=0)
                    name = args.output.stem + "-" + run["run"] + "-" + side + str(setting) + ".json.gz"
                    path = args.output.with_name(name)
                    with path.open("xb") as stream:
                        stream.write(witness)
                    settings.append({"side": side, "setting": setting, "program": program.record(),
                                     "mode_certificate": report, "combined_operator_error": str(error),
                                     "dark_effect": effect.record(),
                                     "witness": {"path": name, "sha256": hashlib.sha256(witness).hexdigest(),
                                                 "bytes": len(witness), "decoded_sha256": hashlib.sha256(raw_witness).hexdigest()}})
                    print(json.dumps({"run": run["run"], "side": side, "setting": setting,
                                      "mode_count": len(modes), "operator_error": float(error)}), flush=True)
                side_effects.append(effects)
            table = [{"h": h, "a": a, "b": b, "x": x, "y": y,
                      **commands.tensor_born(side_effects[0][a], side_effects[1][b], h, x, y)}
                     for h in (0, 1) for a in (0, 1) for b in (0, 1) for x in (0, 1) for y in (0, 1)]
            reports.append({"run": run["run"], "settings": settings, "source_probability_enclosures": table})
        bindings(commit)
        result = {"schema": "stage10-raw-hardware-mode-forward-mi0001/v1", "status": "source_probability_enclosures_generated",
                  "freeze_commit": commit, "source_bindings": sources, "runs": reports,
                  "new_empirical_record_files_read": 0, "actual_parameter_identity_asserted": False, "controller_advance": False}
    except Exception as error:
        result = {"schema": "stage10-raw-hardware-mode-forward-mi0001/v1", "status": "failed",
                  "freeze_commit": commit, "source_bindings": sources, "completed_runs": reports,
                  "error_type": type(error).__name__, "error": str(error)}
        with args.output.open("x") as stream:
            json.dump(result, stream, indent=2, sort_keys=True); stream.write("\n")
        raise
    with args.output.open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True); stream.write("\n")


if __name__ == "__main__":
    main()
