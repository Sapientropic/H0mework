"""Complete one-dimensional training slice, with paired held-out predictions."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
import math
from pathlib import Path
import re

import primary

HERE = Path(__file__).resolve().parent
VERSION = "p23-observable-closure-ef0002"


def load():
    config, _, gaussian, utility, _, _ = primary.configuration()
    freeze = primary.frozen(HERE/"criterion-ef0002.md")
    program = primary.frozen(__file__)
    primary.frozen(HERE/"sources-ef0002.json")
    blocks = re.findall(r"```json\s*(.*?)\s*```", (HERE/"criterion-ef0002.md").read_text(), re.S)
    primary.require(len(blocks) == 1, "NONUNIQUE_SLICE_CRITERION")
    revision = json.loads(blocks[0])
    manifest = json.loads((HERE/"sources-ef0002.json").read_text())
    primary.require(revision["version"] == manifest["version"] == VERSION and
                    revision["status"] == "frozen_before_execution" and
                    revision["boundary_segments_preserved"] is True, "SLICE_CONTRACT_CHANGED")
    for binding in manifest["inputs"]:
        path = primary.ROOT/binding["path"]
        primary.require(primary.digest(path) == binding["sha256"], "SLICE_INPUT_CHANGED")
    return {**config, **revision}, manifest, gaussian, utility, freeze, program


def training_view(counts):
    view = primary.training_view(counts)
    return {"0": view["0"], "3": {k: view["3"][k] for k in ("sA", "sB")}}


def p_add(a, b):
    return [(a[i] if i < len(a) else 0)+(b[i] if i < len(b) else 0)
            for i in range(max(len(a), len(b)))]


def p_scale(a, c):
    return [c*x for x in a]


def p_sub(a, b):
    return p_add(a, p_scale(b, -1))


def p_mul(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def p_value(p, e):
    answer = p[-1]
    for coefficient in reversed(p[:-1]):
        answer = answer*e+coefficient
    return answer


def bernstein_range(p, lo, hi, I):
    degree = len(p)-1
    powers = [sum((math.comb(k, j)*p[k]*lo**(k-j)*(hi-lo)**j
                   for k in range(j, degree+1)), I.point(0)) for j in range(degree+1)]
    coefficients = [sum((F(math.comb(i, j), math.comb(degree, j))*powers[j]
                        for j in range(i+1)), I.point(0)) for i in range(degree+1)]
    return I(min(x.lo for x in coefficients), max(x.hi for x in coefficients))


def shape(training, interval11, config, gaussian, utility):
    primary.require(set(training) == {"0", "3"} and set(training["0"]) == {"sA", "sB", "j"}
                    and set(training["3"]) == {"sA", "sB"}, "NONSLICE_TRAINING_INPUT")
    I = gaussian.I
    ba, bb = map(F, config["background_per_pulse"])
    alpha, beta = [], []
    for key in ("0", "3"):
        row = training[key]
        primary.require(all(isinstance(x, F) and 0 <= x < 1 for x in row.values()), "INVALID_TRAINING_RATE")
        alpha.append((1-ba)/utility.nth_root(1-row["sA"], 5, 40, I)-1)
        beta.append((1-bb)/utility.nth_root(1-row["sB"], 5, 40, I)-1)
    trig = lambda a: utility.trig_deg(a, config, gaussian)
    angles = list(map(F, config["angles_deg"]))
    s, c = zip(*(trig(2*a) for a in angles[:2]))
    denominator = s[1]*beta[0]-s[0]*beta[1]
    primary.require(not denominator.contains(0), "DEGENERATE_SINGLE_RATIO")
    r = (s[1]*alpha[0]-s[0]*alpha[1])/denominator
    u = [(a+r*b)/2 for a, b in zip(alpha, beta)]
    z = (u[1]-u[0])/(c[0]-c[1])
    m = u[0]+z*c[0]
    x = -(alpha[0]-r*beta[0])/(2*s[0])
    C = gaussian.square_root(z.square()+x.square())
    primary.require(r.lo > 0 and C.lo > 0, "DEGENERATE_SOURCE_AXIS")
    h, v = m+C, m-C
    primary.require(v.lo > 0, "PURE_OR_UNRESOLVED_SOURCE_MODE")
    Z, X = z/C, x/C
    cr = gaussian.square_root((1+Z)/2)
    sr = X/(2*cr)
    vectors = []
    for angle in angles:
        a, b = trig(angle)
        vectors.append((a*cr-b*sr, a*sr+b*cr))
    U, V = [(ci-Z)/2 for ci in c], [(ci+Z)/2 for ci in c]
    gs = [2*a*b/r for a, b in zip(U, V)]
    primary.require(not gs[0].contains(0), "UNRESOLVED_SLICE_SEED")
    T2 = [h.square()*v.square(), h*v*(h+v), h*v]
    L, Q = [], []
    for i in range(2):
        Di = (1+alpha[i])*(1+beta[i])
        Li = [Di-(h.square()*U[i].square()+v.square()*V[i].square())/r,
              -(h*U[i].square()+v*V[i].square())/r]
        L.append(Li)
        Q.append(p_sub(p_mul(Li, Li), p_scale(T2, gs[i].square())))
    rootarg = 1-training["0"]["sA"]-training["0"]["sB"]+training["0"]["j"]
    primary.require(0 < rootarg <= 1, "INVALID_SEED_NO_CLICK")
    w0 = utility.nth_root(rootarg, 5, 40, I)/((1-ba)*(1-bb))
    H0 = p_sub(p_scale(Q[0], w0), L[0])
    N1 = p_add(L[1], p_scale(H0, gs[1]/gs[0]))
    lowarg = 1-training["3"]["sA"]-training["3"]["sB"]+interval11.lo
    higharg = 1-training["3"]["sA"]-training["3"]["sB"]+interval11.hi
    primary.require(0 < lowarg <= higharg <= 1, "INVALID_TRAINING_INTERVAL_NO_CLICK")
    wlo = utility.nth_root(lowarg, 5, 40, I)/((1-ba)*(1-bb))
    whi = utility.nth_root(higharg, 5, 40, I)/((1-ba)*(1-bb))
    polynomials = {"phase": p_sub(p_mul(H0, H0), p_scale(T2, gs[0].square())),
                   "low": p_sub(N1, p_scale(Q[1], wlo)),
                   "high": p_sub(p_scale(Q[1], whi), N1), "denominator": Q[1]}
    cells = []
    for ax in range(2):
        for by in range(2):
            ah, av = vectors[ax]
            bh, bv = vectors[2+by]
            Uxy, Vxy = ah*bh, av*bv
            gxy = 2*Uxy*Vxy/r
            Lxy = [(1+alpha[ax])*(1+beta[by])-
                   (h.square()*Uxy.square()+v.square()*Vxy.square())/r,
                   -(h*Uxy.square()+v*Vxy.square())/r]
            Qxy = p_sub(p_mul(Lxy, Lxy), p_scale(T2, gxy.square()))
            Nxy = p_add(Lxy, p_scale(H0, gxy/gs[0]))
            cells.append({"setting": [ax, by], "N": Nxy, "Q": Qxy})
    return {"r": r, "h": h, "v": v, "m": m, "z": z, "x": x,
            "cosR": cr, "sinR": sr, "alpha": alpha, "beta": beta,
            "w0": w0, "g0": gs[0], "T2": T2, "H0": H0,
            "polynomials": polynomials, "cells": cells,
            "training": training, "joint11_interval": interval11}


def cover(source, config, I):
    upper = min(F(1), source["r"].hi)
    certified_upper = min(F(1), source["r"].lo)
    width = F(config["scalar_cover_width"])
    pending = [(F(0), upper, 0)]
    terminal, splits = [], 0
    while pending:
        lo, hi, depth = pending.pop()
        bounds = {key: bernstein_range(p, lo, hi, I) for key, p in source["polynomials"].items()}
        row = {"lower": lo, "upper": hi, "depth": depth, "bounds": bounds}
        if bounds["phase"].lo > 0:
            row.update(classification="excluded", reason="PHASE_OUTSIDE_PHYSICAL_DOMAIN")
        elif bounds["low"].hi < 0 or bounds["high"].hi < 0:
            row.update(classification="excluded", reason="JOINT11_OUTSIDE_TRAINING_INTERVAL")
        elif lo > source["r"].hi or bounds["denominator"].hi <= 0:
            row.update(classification="excluded", reason="ILLEGAL_LOSS_OR_DENOMINATOR")
        elif (lo > 0 and hi <= certified_upper and bounds["phase"].hi <= 0 and
              bounds["low"].lo >= 0 and bounds["high"].lo >= 0 and bounds["denominator"].lo > 0):
            row.update(classification="inside", reason="WHOLE_INTERVAL_LEGAL_AND_TRAINING_ADMISSIBLE")
        elif hi-lo <= width or depth >= config["scalar_cover_depth_cap"] or splits >= config["scalar_cover_split_cap"]:
            row.update(classification="boundary", reason="RETAINED_UNRESOLVED_BOUNDARY")
        else:
            mid = (lo+hi)/2
            pending.extend(((mid, hi, depth+1), (lo, mid, depth+1)))
            splits += 1
            continue
        terminal.append(row)
    terminal.sort(key=lambda x: x["lower"])
    primary.require(terminal and terminal[0]["lower"] == 0 and terminal[-1]["upper"] == upper and
                    all(a["upper"] == b["lower"] for a, b in zip(terminal, terminal[1:])), "INCOMPLETE_SCALAR_PARTITION")
    return {"domain": [F(0), upper], "splits": splits, "segments": terminal,
            "cap_reached": splits >= config["scalar_cover_split_cap"] or
            any(x["depth"] >= config["scalar_cover_depth_cap"] for x in terminal)}


def predictions(source, interval, config, gaussian):
    I = gaussian.I
    ba, bb = map(F, config["background_per_pulse"])
    result = []
    for index, cell in enumerate(source["cells"]):
        ax, by = cell["setting"]
        p0a = gaussian.power((1-ba)/(1+source["alpha"][ax]), 5)
        p0b = gaussian.power((1-bb)/(1+source["beta"][by]), 5)
        Q = bernstein_range(cell["Q"], interval.lo, interval.hi, I)
        N = bernstein_range(cell["N"], interval.lo, interval.hi, I)
        if Q.lo <= 0:
            result.append({"setting": cell["setting"], "status": "UNRESOLVED_DENOMINATOR_OUTER",
                           "sA": 1-p0a, "sB": 1-p0b, "j": I(0, 1), "outcomes": [I(0, 1)]*4})
            continue
        w = source["w0"] if index == 0 else N/Q
        p00 = gaussian.power((1-ba)*(1-bb)*w, 5)
        result.append({"setting": cell["setting"], "status": "PAIRED_SAME_LOSS_OUTER",
                       "sA": 1-p0a, "sB": 1-p0b, "j": 1-p0a-p0b+p00,
                       "pulse_no_click_AB": w,
                       "outcomes": [1-p0a-p0b+p00, p0b-p00, p0a-p00, p00]})
    return result


def member(source, loss, config, gaussian, utility):
    e = gaussian.I.point(loss)
    T = gaussian.square_root(p_value(source["T2"], e))
    c = p_value(source["H0"], e)/(source["g0"]*T)
    primary.require(e.lo > 0 and e.hi <= 1 and (e/source["r"]).hi <= 1 and
                    c.lo >= -1 and c.hi <= 1, "ILLEGAL_CANONICAL_SLICE_MEMBER")
    lam, eb = (1-c)/2, e/source["r"]
    nh, nv = source["h"]/e, source["v"]/e
    cr, sr = source["cosR"], source["sinR"]
    vectors = []
    for angle in config["angles_deg"]:
        sa, ca = utility.trig_deg(F(angle), config, gaussian)
        vectors.append((sa*cr-ca*sr, sa*sr+ca*cr))
    eliminated = predictions(source, e, config, gaussian)
    actual = []
    ba, bb = map(F, config["background_per_pulse"])
    for ax in range(2):
        for by in range(2):
            ah, av = vectors[ax]
            bh, bv = vectors[2+by]
            ma, mb = e*(nh*ah.square()+nv*av.square()), eb*(nh*bh.square()+nv*bv.square())
            kh, kv = gaussian.square_root(nh*(1+nh)*e*eb), gaussian.square_root(nv*(1+nv)*e*eb)
            ds = [(1+ma)*(1+mb)-(kh*ah*bh+ph*kv*av*bv).square() for ph in (1, -1)]
            primary.require(all(d.lo > 0 for d in ds), "NONPOSITIVE_CANONICAL_SOURCE_DETERMINANT")
            w = (1-lam)/ds[0]+lam/ds[1]
            qa, qb = gaussian.power((1-ba)/(1+ma), 5), gaussian.power((1-bb)/(1+mb), 5)
            qab = gaussian.power((1-ba)*(1-bb)*w, 5)
            row = {"setting": [ax, by], "sA": 1-qa, "sB": 1-qb, "j": 1-qa-qb+qab,
                   "outcomes": [1-qa-qb+qab, qb-qab, qa-qab, qab], "pulse_no_click_AB": w}
            for feature in ("sA", "sB", "j"):
                delta = row[feature]-eliminated[2*ax+by][feature]
                primary.require(delta.contains(0) and delta.hi-delta.lo <= F(config["implementation_tolerance"]),
                                "CANONICAL_ELIMINATION_READBACK_UNRESOLVED")
            actual.append(row)
    return {"e": loss, "etaA": e, "etaB": eb, "lambda": lam,
            "phase_coherence": c, "tH": source["h"]/(source["h"]+e),
            "tV": source["v"]/(source["v"]+e), "rotation_cos": source["cosR"],
            "rotation_sin": source["sinR"], "cells": actual, "eliminated_cells": eliminated,
            "exact_source_representation": "rational_loss_and_observable_generated_real_radicals_and_trigonometry"}


def generate(training, interval11, config, gaussian, utility):
    source = shape(training, interval11, config, gaussian, utility)
    partition = cover(source, config, gaussian.I)
    paired = []
    for row in partition["segments"]:
        if row["classification"] != "excluded":
            paired.append({"loss_interval": [row["lower"], row["upper"]],
                           "classification": row["classification"],
                           "cells": predictions(source, gaussian.I(row["lower"], row["upper"]), config, gaussian)})
    inside = [x for x in partition["segments"] if x["classification"] == "inside"]
    canonical = member(source, (inside[0]["lower"]+inside[0]["upper"])/2, config, gaussian, utility) if inside else None
    return {"source": source, "partition": partition, "paired_predictions": paired,
            "canonical_member": canonical, "status": "COMPLETE_SLICE_COVER" if not partition["cap_reached"]
            else "COMPLETE_PARTITION_WITH_CAP_UNRESOLVED", "full_statistical_fiber_certified": False}


def interval_from_receipt(value, I):
    return I(F(value["exact_lower"]), F(value["exact_upper"]))


def compare_cells(cells, confidence):
    included = {key: [] for key in ("j", "sA_cell", "sB_cell")}
    for index, cell in enumerate(cells):
        for feature, name in (("j", "j"), ("sA", "sA_cell"), ("sB", "sB_cell")):
            bounds = confidence[name][index]
            included[name].append(F(bounds["exact_lower"]) <= cell[feature].lo and
                                  cell[feature].hi <= F(bounds["exact_upper"]))
    return included


def run():
    config, manifest, g, fw, freeze, program = load()
    counts = json.loads((HERE/config["public_counts"]).read_text())["counts"]
    training = training_view(counts)
    # Only these six training statistics cross the generation boundary.
    report = json.loads((HERE/config["public_confidence_report"]).read_text())
    ci = report["common_mean_confidence"]
    for row_index, key in ((0, "0"), (3, "3")):
        for feature, name in (("sA", "sA_cell"), ("sB", "sB_cell"), ("j", "j")):
            if feature in training[key]:
                primary.require(interval_from_receipt(ci[name][row_index], g.I).contains(training[key][feature]),
                                "TRAINING_CENTER_NOT_IN_ORIGINAL_DOMAIN")
    interval11 = interval_from_receipt(ci["j"][3], g.I)
    result = generate(training, interval11, config, g, fw)
    canonical = result["canonical_member"]
    if canonical is not None:
        included = compare_cells(canonical["cells"], ci)
        canonical["confidence_inclusion"] = included
        canonical["outcome"] = "EXHIBITED_CALIBRATION_FREE_SLICE_MEMBER" if all(all(x) for x in included.values()) else "MEMBER_OUTSIDE_ORIGINAL_ENVELOPE"
    envelope = []
    for index in range(4):
        cells = [x["cells"][index] for x in result["paired_predictions"]]
        if cells:
            envelope.append({feature: g.I(min(x[feature].lo for x in cells), max(x[feature].hi for x in cells))
                             for feature in ("j", "sA", "sB")})
    result["display_envelope"] = envelope
    if len(envelope) == 4:
        included = compare_cells(envelope, ci)
        result["display_envelope_confidence_inclusion"] = included
        result["held_out_envelope_outcome"] = "SLICE_PREDICTION_ENVELOPE_CONTAINED" if all(
            included[key][i] for key in included for i in (1, 2)) else "SLICE_PREDICTION_NOT_CONTAINED"
    return primary.serial({"schema": "p23-observable-scalar-slice-primary/v1", "version": VERSION,
                           "criterion_freeze": freeze, "program_freeze": program,
                           "manifest_sha256": primary.digest(HERE/"sources-ef0002.json"),
                           "inputs": manifest["inputs"], "result": result,
                           "known_design_exposure": report["complete_trials"], "retrospective": True,
                           "source_mapping_identified": False, "production_admitted": False,
                           "apparatus_optimum_verified": False, "controller_advance": False,
                           "full_statistical_fiber_certified": False, "bell_event_files_read": 0,
                           "private_optimizer_input_required": False, "new_measurement_required": False}, g.I)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE/"slice-primary.json")
    args = parser.parse_args()
    primary.require(not args.output.exists(), "OUTPUT_EXISTS_USE_NEW_PATH")
    result = run()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True, allow_nan=False)+"\n")
    data = result["result"]
    print(json.dumps({"output": str(args.output), "status": data["status"],
                      "segments": len(data["partition"]["segments"]),
                      "canonical_outcome": data["canonical_member"]["outcome"] if data["canonical_member"] else None,
                      "held_out_outcome": data.get("held_out_envelope_outcome")}))


if __name__ == "__main__":
    main()
