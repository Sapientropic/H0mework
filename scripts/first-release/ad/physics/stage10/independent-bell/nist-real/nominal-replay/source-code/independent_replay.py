"""Independent finite-Fock NIST design replay; never reads experimental events."""
from __future__ import annotations

import argparse
import functools
import hashlib
import itertools
import json
import math
import re
import subprocess
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
CRITERION = HERE / "criterion.md"
OUTPUT = HERE / "independent_replay.json"
PRIMARY = HERE / "replay.json"
FREEZE_COMMIT = "7756ce61784f8e705444450c03b12996340090f5"
N = 4


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def criterion_freeze():
    relative = str(CRITERION.relative_to(ROOT))
    committed = subprocess.check_output(
        ["git", "show", f"{FREEZE_COMMIT}:{relative}"], cwd=ROOT)
    if committed != CRITERION.read_bytes():
        raise ValueError("criterion differs from its pre-replay frozen commit")
    return {"commit": FREEZE_COMMIT, "sha256": sha256(CRITERION), "path": relative}


def load_frozen(path=None):
    path = CRITERION if path is None else Path(path)
    text = path.read_text(encoding="utf-8")
    match = re.search(
        r"<!-- FROZEN-SOURCE-STUDY-BEGIN -->\s*```json\s*(.*?)\s*```\s*"
        r"<!-- FROZEN-SOURCE-STUDY-END -->", text, re.S)
    if match is None:
        raise ValueError("missing unique frozen source study block")
    if len(re.findall(r"<!-- FROZEN-SOURCE-STUDY-BEGIN -->", text)) != 1:
        raise ValueError("ambiguous frozen source study block")
    study = json.loads(match.group(1))
    found = re.findall(r"(74\.7|75\.6)\s*±\s*([0-9.]+)\s*%", text)
    for side, percentage in (("eta_A", "74.7"), ("eta_B", "75.6")):
        widths = [float(width) / 100 for centre, width in found if centre == percentage]
        entry = study["published"][side]
        if not widths or any(width != entry["half_width"] for width in widths):
            raise ValueError(f"efficiency text/probability unit mismatch: {side}")
        if not math.isclose(entry["center"], float(percentage) / 100, rel_tol=0, abs_tol=1e-15):
            raise ValueError(f"efficiency text/centre mismatch: {side}")
    if study["source"] != {"N": 4, "relative_phase_rad": 0.0, "detector_noise": "additive"}:
        raise ValueError("unsupported source or detector contract")
    if len(input_points(study)) != 19:
        raise ValueError("frozen 19-point input contract mismatch")
    if path.resolve() == CRITERION:
        criterion_freeze()
    return study


def input_points(study):
    points = []
    for case in study["cases"]:
        if case == "author_defaults":
            cfg = study[case]
            points.append({
                "case": case, "point_id": case + ":center",
                "eta_A": cfg["eta_A"], "eta_B": cfg["eta_B"],
                "background_A": cfg["darks_A_per_second"] * cfg["coincidence_window_seconds"],
                "background_B": cfg["darks_B_per_second"] * cfg["coincidence_window_seconds"],
                "epsilon_squared": cfg["balanced_HH_coincidences_per_second"] /
                    (cfg["eta_A"] * cfg["eta_B"] * cfg["rep_rate_per_second"]),
                "pair_scale": None,
            })
            continue
        if case not in ("published_gain_half", "published_native_strength"):
            raise ValueError(f"unknown frozen case {case}")
        cfg = study["published"]
        divisor = 2 if case == "published_gain_half" else 1

        def point(label, eta_a, eta_b, q):
            return {"case": case, "point_id": case + ":" + label,
                    "eta_A": eta_a, "eta_B": eta_b,
                    "background_A": cfg["background_A_per_trial"],
                    "background_B": cfg["background_B_per_trial"],
                    "epsilon_squared": q / divisor, "pair_scale": q}

        points.append(point("center", cfg["eta_A"]["center"], cfg["eta_B"]["center"],
                            cfg["pair_scale"]["center"]))
        for bits in itertools.product((0, 1), repeat=3):
            eta_a = cfg["eta_A"]["center"] + (2 * bits[0] - 1) * cfg["eta_A"]["half_width"]
            eta_b = cfg["eta_B"]["center"] + (2 * bits[1] - 1) * cfg["eta_B"]["half_width"]
            q = cfg["pair_scale"]["box_high" if bits[2] else "box_low"]
            points.append(point("corner_" + "".join(map(str, bits)), eta_a, eta_b, q))
    return points


@functools.lru_cache(maxsize=1)
def spectra():
    annihilate = np.zeros((N, N), dtype=complex)
    for number in range(1, N):
        annihilate[number - 1, number] = math.sqrt(number)
    create = annihilate.conj().T
    pair = np.kron(create, create) + np.kron(annihilate, annihilate)
    rotation = 1j * (np.kron(annihilate, create) - np.kron(create, annihilate))
    pair_values, pair_vectors = np.linalg.eigh(pair)
    rotation_values, rotation_vectors = np.linalg.eigh(rotation)
    return pair_values, pair_vectors, rotation_values, rotation_vectors


@functools.lru_cache(maxsize=4096)
def source_matrix(epsilon_squared, gamma_deg):
    values, vectors, _, _ = spectra()
    gamma = math.radians(gamma_deg)
    strength = math.sqrt(2 * epsilon_squared)
    vacuum_coordinates = vectors[0].conj()
    hh = vectors @ (np.exp(-1j * strength * math.sin(gamma) * values) * vacuum_coordinates)
    vv = vectors @ (np.exp(-1j * strength * math.cos(gamma) * values) * vacuum_coordinates)
    # Pair order is (Ha,Hb,Va,Vb); explicitly rearrange the complete tensor basis.
    return np.kron(hh, vv).reshape(N, N, N, N).transpose(0, 2, 1, 3).reshape(N*N, N*N)


@functools.lru_cache(maxsize=8192)
def hwp(angle_deg):
    _, _, values, vectors = spectra()
    phase = np.exp(-1j * math.radians(angle_deg) * values)
    return (vectors * phase) @ vectors.conj().T


def bucket_click(eta, background, cutoff=N):
    if not 0 <= eta <= 1 or not 0 <= background <= 1:
        raise ValueError("detector input outside probability domain")
    values = np.array([1 - (1 - eta) ** n + background for n in range(cutoff)])
    if np.any(values < 0) or np.any(values > 1):
        raise ValueError("finite additive detector effect outside [0,1]")
    return values


class Model:
    def __init__(self, point):
        self.point = dict(point)
        self.epsilon_squared = float(point["epsilon_squared"])
        if not math.isfinite(self.epsilon_squared) or self.epsilon_squared < 0:
            raise ValueError("invalid source strength")
        self.detector_A = np.repeat(bucket_click(point["eta_A"], point["background_A"]), N)
        self.detector_B = np.repeat(bucket_click(point["eta_B"], point["background_B"]), N)
        self.joint_weights = self.detector_A[:, None] * self.detector_B[None, :]

    def source(self, gamma_deg):
        return source_matrix(self.epsilon_squared, float(gamma_deg))

    def source_norm(self, gamma_deg):
        matrix = self.source(gamma_deg)
        return float(np.vdot(matrix, matrix).real)

    def r_one_pair(self, gamma_deg):
        full = self.source(gamma_deg).reshape(N, N, N, N)
        denominator = full[0, 1, 0, 1]
        if abs(denominator) == 0:
            raise ValueError("undefined empty one-pair coefficient ratio")
        return float(abs(full[1, 0, 1, 0] / denominator))

    def single(self, gamma_deg, angle_deg, side):
        source = self.source(gamma_deg)
        if side == "alice":
            amplitudes = hwp(float(angle_deg)) @ source
            probabilities = np.abs(amplitudes) ** 2
            return float(self.detector_A @ probabilities.sum(axis=1))
        if side == "bob":
            amplitudes = source @ hwp(float(angle_deg)).T
            probabilities = np.abs(amplitudes) ** 2
            return float(probabilities.sum(axis=0) @ self.detector_B)
        raise ValueError("side must be alice or bob")

    def joint(self, gamma_deg, angle_a_deg, angle_b_deg):
        amplitudes = hwp(float(angle_a_deg)) @ self.source(gamma_deg) @ hwp(float(angle_b_deg)).T
        return float(np.sum(np.abs(amplitudes) ** 2 * self.joint_weights))

    def score(self, coordinates):
        gamma, a0, a1 = map(float, coordinates)
        source = self.source(gamma)
        ua0, ua1 = hwp(a0), hwp(a1)
        ub0, ub1 = hwp(-a0), hwp(-a1)
        left0, left1 = ua0 @ source, ua1 @ source
        joint00 = np.sum(np.abs(left0 @ ub0.T) ** 2 * self.joint_weights)
        joint01 = np.sum(np.abs(left0 @ ub1.T) ** 2 * self.joint_weights)
        joint10 = np.sum(np.abs(left1 @ ub0.T) ** 2 * self.joint_weights)
        joint11 = np.sum(np.abs(left1 @ ub1.T) ** 2 * self.joint_weights)
        single_a = self.detector_A @ (np.abs(left0) ** 2).sum(axis=1)
        single_b = (np.abs(source @ ub0.T) ** 2).sum(axis=0) @ self.detector_B
        return float(joint00 + joint01 + joint10 - joint11 - single_a - single_b)


def nelder_mead(model, start, study):
    cfg = study["independent_optimizer"]
    bounds = np.array([study["domains"]["gamma_deg"], study["domains"]["angle_deg"],
                       study["domains"]["angle_deg"]], dtype=float)

    def constrain(x):
        return np.minimum(np.maximum(np.asarray(x, dtype=float), bounds[:, 0]), bounds[:, 1])

    def objective(x):
        return -model.score(x) * cfg["objective_scale"]

    first = constrain(start)
    vertices = [first]
    for axis in range(3):
        vertex = first.copy()
        step = cfg["simplex_step_deg"]
        if vertex[axis] + step > bounds[axis, 1]:
            step = -step
        vertex[axis] += step
        vertices.append(constrain(vertex))
    simplex = np.array(vertices)
    values = np.array([objective(x) for x in simplex])
    for _ in range(cfg["iterations"]):
        order = np.argsort(values, kind="stable")
        simplex, values = simplex[order], values[order]
        if (np.max(np.abs(simplex[1:] - simplex[0])) <= cfg["coordinate_stop"] and
                np.max(np.abs(values[1:] - values[0])) <= cfg["scaled_objective_stop"]):
            break
        centre = simplex[:-1].mean(axis=0)
        reflected = constrain(centre + (centre - simplex[-1]))
        reflected_value = objective(reflected)
        if reflected_value < values[0]:
            expanded = constrain(centre + 2 * (reflected - centre))
            expanded_value = objective(expanded)
            simplex[-1], values[-1] = (expanded, expanded_value) if expanded_value < reflected_value else (reflected, reflected_value)
        elif reflected_value < values[-2]:
            simplex[-1], values[-1] = reflected, reflected_value
        else:
            outside = reflected_value < values[-1]
            contracted = constrain(centre + 0.5 * ((reflected if outside else simplex[-1]) - centre))
            contracted_value = objective(contracted)
            if contracted_value < (reflected_value if outside else values[-1]):
                simplex[-1], values[-1] = contracted, contracted_value
            else:
                simplex[1:] = [constrain(simplex[0] + 0.5 * (x - simplex[0])) for x in simplex[1:]]
                values[1:] = [objective(x) for x in simplex[1:]]
    best = simplex[int(np.argmin(values))]
    gamma, a0, a1 = map(float, best)
    if a0 < 0 or (a0 == 0 and a1 < 0):
        a0, a1 = -a0, -a1
    return {"gamma_deg": gamma, "r_one_pair": model.r_one_pair(gamma),
            "weak_r": math.tan(math.radians(gamma)),
            "a0_deg": a0, "a1_deg": a1, "b0_deg": -a0, "b1_deg": -a1,
            "CH": model.score((gamma, a0, a1))}


def optimise(model, study, own_centre=None):
    cfg = study["independent_optimizer"]
    if own_centre is None:
        coarse = [(model.score(x), x) for x in itertools.product(
            cfg["grid_gamma_deg"], cfg["grid_angle0_deg"], cfg["grid_angle1_deg"])]
        coarse.sort(key=lambda item: (-item[0], item[1]))
        starts = [list(x) for _, x in coarse[:cfg["keep"]]] + [study["author_start_deg"]]
    else:
        starts = [[own_centre[key] for key in ("gamma_deg", "a0_deg", "a1_deg")]]
        starts += study["corner_starts_deg"]
    candidates = [nelder_mead(model, start, study) for start in starts]
    return max(candidates, key=lambda item: item["CH"])


def controls(study):
    errors = []
    norms = []
    rows = []
    expected = np.array([0.001, 0.601, 0.841, 0.937])
    if np.max(np.abs(bucket_click(0.6, 0.001) - expected)) > 1e-15:
        errors.append("author additive detector control")
    or_values = np.array([1 - (1 - 0.6)**n * (1 - 0.001) for n in range(N)])
    if np.max(np.abs(or_values - expected)) <= 1e-15:
        errors.append("OR detector look-alike was not distinguished")
    for point in input_points(study):
        model = Model(point)
        if not point["point_id"].endswith(":center"):
            continue
        for gamma, a, b in study["operator_controls_deg"]:
            norm = model.source_norm(gamma)
            norms.append(abs(norm - 1))
            sa = model.single(gamma, a, "alice")
            sb = model.single(gamma, b, "bob")
            joint = model.joint(gamma, a, b)
            outcomes = [joint, sa-joint, sb-joint, norm-sa-sb+joint]
            if min(outcomes) < -1e-12 or max(outcomes) > 1+1e-12:
                errors.append(f"invalid complete outcomes {point['point_id']}")
            rows.append({"case": point["case"], "gamma_deg": gamma, "a_deg": a,
                         "b_deg": b, "source_norm": norm, "single_A": sa,
                         "single_B": sb, "joint": joint, "outcomes": outcomes})
    vacuum_point = dict(input_points(study)[0], epsilon_squared=0)
    vacuum = Model(vacuum_point)
    gamma, a, b = study["operator_controls_deg"][0]
    if (abs(vacuum.single(gamma, a, "alice") - vacuum_point["background_A"]) > 1e-14 or
            abs(vacuum.single(gamma, b, "bob") - vacuum_point["background_B"]) > 1e-14 or
            abs(vacuum.joint(gamma, a, b) - vacuum_point["background_A"]*vacuum_point["background_B"]) > 1e-14):
        errors.append("vacuum dark-count control")
    weak = Model(dict(vacuum_point, epsilon_squared=1e-12, eta_A=1, eta_B=1,
                      background_A=0, background_B=0))
    low_gain_worst = 0.0
    for gamma, a, b in study["operator_controls_deg"]:
        g, aa, bb = map(math.radians, (gamma, a, b))
        born = (math.sin(g)*math.cos(aa)*math.cos(bb) +
                math.cos(g)*math.sin(aa)*math.sin(bb))**2
        error = abs(weak.joint(gamma, a, b) / (2e-12) - born)
        low_gain_worst = max(low_gain_worst, error)
    if low_gain_worst > 1e-8:
        errors.append("weak one-pair Born alignment")
    if max(norms) > 1e-12:
        errors.append("source norm, without renormalization")
    return {"passed": not errors, "errors": errors, "operator_controls": rows,
            "max_source_norm_error": max(norms), "low_gain_born_worst": low_gain_worst,
            "detector_additive_positive_control": True,
            "detector_or_negative_control": True, "vacuum_control": not errors}


def source_bindings(study):
    files = [CRITERION, Path(__file__), *[(HERE / name).resolve() for name in study["input_sources"]]]
    return {str(path.relative_to(ROOT)): sha256(path) for path in files}


def case_reports(results, study):
    instrument = json.loads((HERE / "../../instrument.json").read_text())
    documented = {"r_one_pair": float(instrument["preparation"]["amplitudes"]["VV"]) /
                  float(instrument["preparation"]["amplitudes"]["HH"])}
    for side, prefix in (("alice", "a"), ("bob", "b")):
        for setting, value in enumerate(instrument["controls"][side]):
            documented[f"{prefix}{setting}_deg"] = float(value)
    cases = {}
    for case in study["cases"]:
        selected = [row["optimum"] for row in results if row["case"] == case]
        band = {}
        comparisons = []
        for key, value in documented.items():
            width = study["band"]["r_widen" if key == "r_one_pair" else "angle_widen_deg"]
            interval = [min(row[key] for row in selected)-width, max(row[key] for row in selected)+width]
            band[key] = interval
            comparisons.append({"component": key, "documented_value": value,
                                "interval": interval, "inside": interval[0] <= value <= interval[1]})
        cases[case] = {"band": band, "comparisons": comparisons,
                       "verdict": "CONSISTENT" if all(row["inside"] for row in comparisons) else "DEVIATION"}
    return cases


def compare(report, study):
    if not PRIMARY.exists():
        return {"passed": None, "worst_deltas": {}, "errors": ["awaiting primary output"]}
    primary = json.loads(PRIMARY.read_text())
    errors = []
    if primary.get("criterion_version") != study["criterion_version"]:
        errors.append("primary criterion version")
    source = {row["point"]["point_id"]: row for row in primary.get("results", [])}
    if len(source) != 19:
        errors.append("primary 19-point coverage")
    worst = {key: 0.0 for key in ("gamma_deg", "r_one_pair", "weak_r", "a0_deg", "a1_deg", "b0_deg", "b1_deg", "CH")}
    for row in report["results"]:
        point = row["point"]
        other = source.get(point["point_id"])
        if other is None:
            errors.append("missing primary point " + point["point_id"])
            continue
        for key in ("case", "point_id", "eta_A", "eta_B", "background_A", "background_B", "pair_scale"):
            if point[key] != other["point"].get(key):
                errors.append(f"primary input identity {point['point_id']} {key}")
        if abs(point["epsilon_squared"]-other["point"]["epsilon_squared"]) > 1e-15:
            errors.append("primary strength identity " + point["point_id"])
        for key in worst:
            delta = abs(row["optimum"][key]-other["optimum"][key])
            worst[key] = max(worst[key], delta)
            tolerance = study["tolerance"]["CH_abs" if key == "CH" else
                "r" if key in ("r_one_pair", "weak_r") else "angle_deg"]
            if delta > tolerance:
                errors.append(f"numerical mismatch {point['point_id']} {key}: {delta:.9g}")
    for case in study["cases"]:
        own = report["cases"][case]
        other = primary["cases"][case]
        own_inside = {item["component"]: item["inside"] for item in own["comparisons"]}
        other_inside = {item["component"]: item["inside"] for item in other["comparisons"]}
        if own_inside != other_inside:
            errors.append("case comparison mismatch " + case)
        for component in own["band"]:
            tolerance = study["tolerance"]["r" if component == "r_one_pair" else "angle_deg"]
            if any(abs(a-b) > tolerance for a, b in zip(own["band"][component], other["band"][component])):
                errors.append(f"case band mismatch {case} {component}")
    report["bindings"][str(PRIMARY.relative_to(ROOT))] = sha256(PRIMARY)
    return {"passed": not errors, "worst_deltas": worst, "errors": errors}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compare-only", action="store_true")
    parser.add_argument("--checks-only", action="store_true")
    args = parser.parse_args()
    study = load_frozen()
    if args.compare_only:
        report = json.loads(OUTPUT.read_text())
        for path, digest in report["bindings"].items():
            if path != str(PRIMARY.relative_to(ROOT)) and sha256(ROOT / path) != digest:
                raise ValueError("stale independent computation binding: " + path)
        report["consistency"] = compare(report, study)
        OUTPUT.write_text(json.dumps(report, indent=2, ensure_ascii=False)+"\n")
        print(json.dumps(report["consistency"], ensure_ascii=False), flush=True)
        return 0 if report["consistency"]["passed"] is not False else 1
    check = controls(study)
    if args.checks_only:
        print(json.dumps(check, ensure_ascii=False, indent=2), flush=True)
        return 0 if check["passed"] else 1
    if not check["passed"]:
        raise ValueError("operator controls failed: " + repr(check["errors"]))
    started = time.perf_counter()
    bindings = source_bindings(study)
    results = []
    centres = {}
    for index, point in enumerate(input_points(study), 1):
        model = Model(point)
        own_centre = None if point["point_id"].endswith(":center") else centres[point["case"]]
        optimum = optimise(model, study, own_centre)
        if own_centre is None:
            centres[point["case"]] = optimum
        results.append({"case": point["case"], "point": point, "optimum": optimum})
        print(f"{index:02d}/19 {point['point_id']} r={optimum['r_one_pair']:.10f} "
              f"angles=({optimum['a0_deg']:.7f},{optimum['a1_deg']:.7f}) CH={optimum['CH']:.10g}", flush=True)
    report = {"schema": "nist-source-code-independent/v1",
              "criterion_version": study["criterion_version"], "criterion_freeze": criterion_freeze(),
              "model_source_identified": True, "publication_configuration_identified": False,
              "production_admitted": False, "bindings": bindings,
              "implementation": "full N4 tensor state; independent Hermitian eigensystems, direct amplitudes and Nelder-Mead",
              "controls": check, "results": results, "cases": case_reports(results, study),
              "elapsed_seconds": time.perf_counter()-started}
    report["consistency"] = compare(report, study)
    for path, digest in bindings.items():
        if path != str(PRIMARY.relative_to(ROOT)) and sha256(ROOT / path) != digest:
            raise ValueError("input changed during independent computation: " + path)
    OUTPUT.write_text(json.dumps(report, indent=2, ensure_ascii=False)+"\n")
    print(json.dumps({"cases": {name: row["verdict"] for name, row in report["cases"].items()},
                      "consistency": report["consistency"], "elapsed_seconds": report["elapsed_seconds"]}, ensure_ascii=False), flush=True)
    return 0 if report["consistency"]["passed"] is not False else 1


if __name__ == "__main__":
    raise SystemExit(main())
