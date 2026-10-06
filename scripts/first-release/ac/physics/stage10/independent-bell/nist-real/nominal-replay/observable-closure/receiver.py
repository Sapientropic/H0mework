"""Fixed-source angular jets produce a strict receiver update over the complete slice."""
from fractions import Fraction as F
import argparse
import json
from pathlib import Path
import re

import primary
import slice as scalar
from angular_jet import Jet

HERE = Path(__file__).resolve().parent


def load():
    config, _, g, fw, _, _ = scalar.load()
    freeze = primary.frozen(HERE/"receiver-criterion.md")
    executable = primary.frozen(__file__)
    primary.frozen(HERE/"angular_jet.py")
    primary.frozen(HERE/"receiver-sources.json")
    blocks = re.findall(r"```json\s*(.*?)\s*```", (HERE/"receiver-criterion.md").read_text(), re.S)
    primary.require(len(blocks) == 1, "NONUNIQUE_RECEIVER_CRITERION")
    revision = json.loads(blocks[0])
    manifest = json.loads((HERE/"receiver-sources.json").read_text())
    primary.require(revision["version"] == manifest["version"] == "p23-observable-closure-rx0001" and
                    revision["status"] == "frozen_before_execution" and
                    revision["training_phase_held_fixed_under_receiver_update"] is True, "RECEIVER_SCOPE_CHANGED")
    for binding in manifest["inputs"]:
        primary.require(primary.digest(primary.ROOT/binding["path"]) == binding["sha256"], "RECEIVER_INPUT_CHANGED")
    return {**config, **revision}, manifest, g, fw, freeze, executable


def power(value, exponent):
    result = 1
    for _ in range(exponent):
        result *= value
    return result


def sine_cosine(degrees, config, g):
    arithmetic = g.arithmetic
    radians = degrees*(arithmetic.Interval(*map(F, config["pi"]))/180)
    s = arithmetic.trig(radians.value, config["primary_terms"])
    c = arithmetic.trig(radians.value, config["primary_terms"], True)
    return radians.compose(s, c, -s), radians.compose(c, -s, -c)


def raw_score(source, loss, angle_boxes, config, g):
    I, J = g.I, Jet
    h, v, r = (source[k] for k in ("h", "v", "r"))
    # This is the original training readout; it is constant along every angular jet.
    fixed_k = scalar.p_value(source["H0"], loss)/source["g0"]
    fixed_s = h*v*(h+loss)*(v+loss)
    cr, sr = source["cosR"], source["sinR"]
    vectors, means = [], []
    for index, box in enumerate(angle_boxes):
        s, c = sine_cosine(J.variable(index, box), config, g)
        a, b = s*cr-c*sr, s*sr+c*cr
        vectors.append((a, b))
        mean = a*a*h+b*b*v
        means.append(mean if index < 2 else mean/r)
    ba, bb = map(F, config["background_per_pulse"])
    localA = [power((1-ba)/(1+means[x]), 5) for x in range(2)]
    localB = [power((1-bb)/(1+means[2+y]), 5) for y in range(2)]
    cells = []
    for x in range(2):
        for y in range(2):
            ah, av = vectors[x]
            bh, bv = vectors[2+y]
            U, V = ah*bh, av*bv
            gc = 2*U*V/r
            L = (1+means[x])*(1+means[2+y])-(U*U*h*(h+loss)+V*V*v*(v+loss))/r
            N, Q = L+gc*fixed_k, L*L-gc*gc*fixed_s
            primary.require(Q.value.lo > 0, "ANGULAR_TUBE_DENOMINATOR_UNRESOLVED")
            w = N/Q
            cells.append(power((1-ba)*(1-bb)*w, 5))
    score = cells[0]+cells[1]+cells[2]-cells[3]-localA[0]-localB[0]
    return score


def aggregate_gradients(source, segments, angle_boxes, config, g):
    values = []
    center = [g.I.point(box.midpoint()) for box in angle_boxes]
    offsets = [box-box.midpoint() for box in angle_boxes]
    for row in segments:
        loss = g.I(F(row["lower"]), F(row["upper"]))
        full = raw_score(source, loss, angle_boxes, config, g)
        point = full if all(x.lo == x.hi for x in angle_boxes) else raw_score(source, loss, center, config, g)
        contracted = [point.gradient[i]+sum((full.hessian[i][j]*offsets[j] for j in range(4)), g.I.point(0))
                      for i in range(4)]
        gradients = [g.I(max(a.lo, b.lo), min(a.hi, b.hi)) for a, b in zip(full.gradient, contracted)]
        values.append({"loss_interval": [row["lower"], row["upper"]], "gradients": gradients,
                       "full_gradient": full.gradient, "center_gradient": point.gradient,
                       "whole_box_hessian": full.hessian,
                       "mean_value_gradient_enclosure": contracted})
    return [g.I(min(row["gradients"][i].lo for row in values), max(row["gradients"][i].hi for row in values))
            for i in range(4)], values


def generate(source, segments, config, g):
    I = g.I
    angles = list(map(F, config["angles_deg"]))
    half = F(config["receiver_rounding_half_width_degree"])
    original = [I.point(a) for a in angles]
    rounded = [I(a-half, a+half) for a in angles]
    exact_gradient, exact_rows = aggregate_gradients(source, segments, original, config, g)
    rounding_gradient, rounding_rows = aggregate_gradients(source, segments, rounded, config, g)
    directions = []
    for name in config["direction_order"]:
        vector = config["directions"][name]
        derivative = sum((x*dx for x, dx in zip(vector, rounding_gradient)), I.point(0))
        result = {"name": name, "direction": vector, "rounding_box_derivative": derivative, "probes": [], "update": None}
        for sign in config["signed_update_order"]:
            if (sign*derivative).hi <= 0:
                result["probes"].append({"sign": sign, "status": "DESCENT_DIRECTION_EXCLUDED_AT_ORIGINAL_BOX"})
                continue
            for level in range(config["halving_candidates"]):
                step = F(config["initial_step_degree"])/2**level
                tube = [I(a-half+min(F(0), sign*d*step), a+half+max(F(0), sign*d*step)) for a, d in zip(angles, vector)]
                gradients, rows = aggregate_gradients(source, segments, tube, config, g)
                directional = []
                for row in rows:
                    gradient = sum((sign*d*dx for d, dx in zip(vector, row["gradients"])), I.point(0))
                    directional.append({"loss_interval": row["loss_interval"], "directional_derivative": gradient})
                minimum = min(row["directional_derivative"].lo for row in directional)
                gain = step*minimum
                certified = gain > F(config["strict_improvement_lower_bound"])
                result["probes"].append({"sign": sign, "level": level, "step_degree": step,
                                          "tube": tube, "whole_slice_derivative_lower": minimum,
                                          "gain_lower_bound": gain, "certified": certified,
                                          "segment_derivatives": directional})
                if certified:
                    result["update"] = {"sign": sign, "step_degree": step,
                                          "updated_angles_deg": [a+sign*d*step for a, d in zip(angles, vector)],
                                          "gain_lower_bound": gain, "whole_rounding_box_covered": True}
                    break
            if result["update"] is not None:
                break
        result["status"] = "CERTIFIED_STRICT_RECEIVER_UPDATE" if result["update"] else "NO_UNIFORM_UPDATE_CERTIFIED"
        directions.append(result)
    selected = next((row for row in directions if row["update"] is not None), None)
    return {"exact_point_gradients": exact_gradient, "exact_point_segments": exact_rows,
            "rounding_box_gradients": rounding_gradient, "rounding_box_segments": rounding_rows,
            "directions": directions, "selected_update": selected,
            "status": "CERTIFIED_PUMP_INDEPENDENT_RECEIVER_IMPROVEMENT" if selected else "RECEIVER_UPDATE_UNRESOLVED",
            "retained_scalar_segments": len(segments), "training_phase_recalibrated_after_angle_update": False}


def run():
    config, manifest, g, fw, freeze, program = load()
    counts = json.loads((HERE/config["public_counts"]).read_text())["counts"]
    ci = json.loads((HERE/config["public_confidence_report"]).read_text())["common_mean_confidence"]
    source = scalar.shape(scalar.training_view(counts), scalar.interval_from_receipt(ci["j"][3], g.I), config, g, fw)
    cover = json.loads((HERE/"slice-primary.json").read_text())["result"]["partition"]["segments"]
    segments = [row for row in cover if row["classification"] != "excluded"]
    result = generate(source, segments, config, g)
    return primary.serial({"schema": "p23-receiver-update-primary/v1", "version": config["version"],
                           "criterion_freeze": freeze, "program_freeze": program, "inputs": manifest["inputs"],
                           "result": result, "source_mapping_identified": False,
                           "actual_hardware_drive_identified": False, "apparatus_optimum_verified": False,
                           "controller_advance": False, "retrospective": True, "bell_event_files_read": 0,
                           "mathematical_method": "outward_angle_jets_on_fixed_source_then_finite_mean_value_transport",
                           "angular_jet_sha256": primary.digest(HERE/"angular_jet.py"),
                           "new_Born_or_derivative_kernel_claim": False}, g.I)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE/"receiver-primary.json")
    args = parser.parse_args()
    primary.require(not args.output.exists(), "OUTPUT_EXISTS_USE_NEW_PATH")
    result = run()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True, allow_nan=False)+"\n")
    print(json.dumps({"status": result["result"]["status"], "output": str(args.output)}))
