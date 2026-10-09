"""Inverse search over raw fields and detector variables of one shared device.

Interpolation guides the search. Candidates are re-evaluated with the full
atom; probability and history certificates are separate consumers.
"""
import argparse
from dataclasses import replace
from fractions import Fraction as Q
import json
from math import cos, sin, pi
from pathlib import Path

import numpy as np
import scipy
from scipy.interpolate import PchipInterpolator
from scipy.optimize import least_squares

import atomic_dipole as dipole
import atomic_full_forward as full
import atomic_search as search
import atomic_covariance as covariance

BASE = Path(__file__).resolve().parent
RATES = (12, 16, 20, 24, 28, 32)
ANGLES = (0, pi / 4, -pi / 8, pi / 8)


def raw_template():
    """Table-5 reference constants, with chosen raw pulse variables explicitly retained."""
    gamma_mhz = Q(23, 4)
    ground_split = 2 * Q("3417.341305452145") / gamma_mhz
    d1_split = 2 * Q("407.25") / gamma_mhz
    a, b = Q("84.7185"), Q("12.4965")
    energies = {}
    for f in (0, 1, 2, 3):
        k = Q(f * (f + 1)) - Q(15, 2)
        energies[f] = a * k / 2 + b * (Q(3, 4) * k * (k + 1) - Q(225, 16)) / 18
    diagonal = {("ground", 1): Q(0), ("ground", 2): ground_split,
                ("D1", 1): Q(0), ("D1", 2): d1_split, ("ion", None): Q(0)}
    diagonal.update({("D2", f): ground_split + (energies[f] - energies[3]) / gamma_mhz
                     for f in (0, 1, 2, 3)})
    return full.Segment(5, dict.fromkeys(dipole.Q_COMPONENTS, 0), {-1: 0, 0: 0, 1: 1}, 1, 50,
                        {key: -diagonal[key] for key in dipole.MANIFOLDS},
                        {key: Q(1) if key[0] == "D1" else Q(30333, 28750) for key in full.WIDTHS},
                        dict.fromkeys(full.EXCITED, Q(83, 25)), field_convention="absorption_amplitudes")


def field(rate, angle):
    return {-1: 1j * rate * complex(cos(angle), sin(angle)), 0: 0,
            1: 1j * rate * complex(cos(angle), -sin(angle))}


def transfer_from_fields(side, rates, angles):
    if side not in ("alice", "bob") or len(rates) != 2 or len(angles) != 2:
        raise ValueError("two registered same-side raw fields required")
    nominal = ANGLES[:2] if side == "alice" else ANGLES[2:]
    commands = np.array([[cos(angle), -sin(angle)] for angle in nominal]).T
    outputs = np.array([[field(rate, angle)[q] for rate, angle in zip(rates, angles)]
                        for q in dipole.Q_COMPONENTS])
    return outputs @ np.linalg.inv(commands)


class ResponseCurve:
    def __init__(self, template, rates=RATES):
        self.template, self.kernel = template, search.Kernel(template)
        covariance.verify_covariance(replace(template, fields_r={-1: (0, 1), 0: 0, 1: (0, 1)}),
                                     Q(3, 5), Q(4, 5))
        self.rates, values = np.asarray(rates, dtype=float), []
        cycling = {q: search.complex_value(template.fields_c[q]) for q in dipole.Q_COMPONENTS}
        for rate in self.rates:
            effect = self.kernel.ion_effect(field(rate, 0), cycling, r=search.complex_value(template.r),
                                           c=search.complex_value(template.c))
            values.append([effect[0, 0].real, effect[1, 1].real, effect[0, 1].real, effect[0, 1].imag])
        self.values = np.asarray(values)
        self.guide = PchipInterpolator(self.rates, self.values, axis=0, extrapolate=False)

    def effect(self, rate, angle, *, recheck=False):
        if recheck:
            cycling = {q: search.complex_value(self.template.fields_c[q]) for q in dipole.Q_COMPONENTS}
            return self.kernel.ion_effect(field(rate, angle), cycling, r=search.complex_value(self.template.r),
                                         c=search.complex_value(self.template.c))
        a, b, real, imag = self.guide(rate)
        effect = np.array([[a, real + 1j * imag], [real - 1j * imag, b]])
        rotation = np.array([[cos(angle), sin(angle)], [-sin(angle), cos(angle)]])
        return rotation @ effect @ rotation.T

    def probabilities(self, parameters, *, recheck=False):
        if np.shape(parameters) != (12,):
            raise ValueError("four field amplitudes/phases and two detector pairs required")
        effects = [self.effect(rate, angle, recheck=recheck) for rate, angle in zip(parameters[:4], parameters[4:8])]
        aa = [search.observable_coordinates(effect, parameters[8], parameters[9]) for effect in effects[:2]]
        bb = [search.observable_coordinates(effect, parameters[10], parameters[11]) for effect in effects[2:]]
        return search.joint_table(aa, bb)

    def fit(self, target):
        target = np.asarray(target)
        if target.shape != (8, 4) or not np.all(np.isfinite(target)) or np.min(target) < 0 or not np.allclose(target.sum(axis=1), 1):
            raise ValueError("eight normalized observed-law rows required by inverse objective")
        lower = [self.rates[0]] * 4 + [a - .35 for a in ANGLES] + [0, .8, 0, .8]
        upper = [self.rates[-1]] * 4 + [a + .35 for a in ANGLES] + [.2, 1, .2, 1]
        starts = ([17, 22, 22, 24, *ANGLES, .02, .97, .04, .98],
                  [22, 26, 17, 22, *ANGLES, .04, .99, .02, .95])
        answers = []
        for start in starts:
            solved = least_squares(lambda p: (self.probabilities(p) - target).reshape(-1), start,
                                   bounds=(lower, upper), max_nfev=300, ftol=1e-11, xtol=1e-11, gtol=1e-11)
            if not np.all(np.isfinite(solved.x)):
                raise ArithmeticError("inverse search returned nonfinite raw variables")
            actual = self.probabilities(solved.x, recheck=True)
            transfers = [transfer_from_fields(side, solved.x[offset:offset + 2], solved.x[4 + offset:6 + offset])
                         for side, offset in (("alice", 0), ("bob", 2))]
            answers.append({"raw_parameters": solved.x.tolist(), "residual_norm": float(np.linalg.norm(actual - target)),
                            "search_evaluations": solved.nfev, "interpolation_used_only_as_search_guide": True,
                            "full_atom_rechecked_probabilities": actual.tolist(),
                            "raw_transfers": [[[[float(value.real), float(value.imag)] for value in row]
                                               for row in transfer] for transfer in transfers],
                            "actual_hardware_identity_asserted": False, "numerical_certificate_produced": False})
        return min(answers, key=lambda row: row["residual_norm"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--point-receipt", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--freeze-commit", required=True)
    args = parser.parse_args()
    # The execution guard is shared with the additive inverse corridor, not hf0001.
    from hardware_inverse_run import frozen_inputs
    commit, bindings = frozen_inputs(args.freeze_commit, args.point_receipt)
    if np.__version__ != "2.2.6" or scipy.__version__ != "1.15.3":
        raise ValueError("registered search library versions required")
    if args.output.exists():
        raise FileExistsError(args.output)
    with args.output.with_name(args.output.stem + "-attempt.json").open("x") as stream:
        json.dump({"freeze_commit": commit, "source_bindings": bindings}, stream, indent=2)
        stream.write("\n")
    try:
        target = json.loads(args.point_receipt.read_text())
        curve, reports = ResponseCurve(raw_template()), []
        for run in target["runs"]:
            table = np.zeros((8, 4))
            for row in run["source_probabilities"]:
                table[4 * row["h"] + 2 * row["a"] + row["b"], 2 * row["x"] + row["y"]] = float(Q(row["q"]))
            reports.append({"run": run["run"], **curve.fit(table)})
        frozen_inputs(commit, args.point_receipt)
    except Exception as error:
        with args.output.open("x") as stream:
            json.dump({"schema": "stage10-raw-hardware-inverse-search-hi0001/v1", "status": "failed",
                       "freeze_commit": commit, "source_bindings": bindings,
                       "error_type": type(error).__name__, "error": str(error)}, stream, indent=2)
            stream.write("\n")
        raise
    report = {"schema": "stage10-raw-hardware-inverse-search-hi0001/v1", "status": "raw_parameter_candidates_generated",
              "freeze_commit": commit,
              "source_bindings": bindings, "raw_template": curve.template.record(),
              "raw_response_guide": {"rates": list(RATES), "J_coordinates": curve.values.tolist()},
              "runs": reports, "new_empirical_record_files_read": 0,
              "actual_parameter_identification_completed": False, "controller_advance": False}
    with args.output.open("x") as stream:
        json.dump(report, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"runs": [{"run": r["run"], "residual_norm": r["residual_norm"]} for r in reports]}))


if __name__ == "__main__":
    main()
