"""Public complete counts -> memory-robust mean envelopes -> source-family member.

Compatibility uses a frozen center construction without the fourth calibration joint.
It is not a certification of the actual source, detector law, or design optimum.
"""
from __future__ import annotations

import argparse
from decimal import Decimal, localcontext
from fractions import Fraction as F
import importlib.util
import json
import math
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


prediction = module("_public_prediction", HERE / "predict.py")
arithmetic = module("_public_rational_interval", HERE.parent / "response" / "response.py")
I = arithmetic.Interval


def specification():
    text = (HERE / "public-criterion.md").read_text()
    block = text.split("<!-- PO-FROZEN-BEGIN -->")[1].split("<!-- PO-FROZEN-END -->")[0]
    return json.loads(block.split("```json")[1].split("```")[0])


def elementary_enclosure(x, operation, precision):
    """Decimal exp/ln is correctly rounded; adjacent numbers enclose the real value."""
    with localcontext() as context:
        context.prec = precision
        exact = Decimal(x.numerator) / Decimal(x.denominator)
        value = exact.exp() if operation == "exp" else exact.ln()
        return I(F(value.next_minus()), F(value.next_plus()))


def count_envelope(k, n, config):
    if not isinstance(k, int) or not isinstance(n, int) or not 0 <= k <= n or n == 0:
        raise ValueError("invalid complete Bernoulli counts")
    budget = (config["features"] * 40 * config["runs_covered"] * config["pulse_subsets_covered"])
    inverse_delta = F(budget) / F(config["alpha"])
    logarithm = elementary_enclosure(inverse_delta, "ln", config["decimal_precision"])
    lower, upper = F(0), F(n)
    grid = []
    for exponent in range(config["lambda_grid"]["powers_of_two"][0], config["lambda_grid"]["powers_of_two"][1]+1):
        for sign in (1, -1):
            lam = F(sign, 2**exponent)
            denominator = elementary_enclosure(lam, "exp", config["decimal_precision"])-1
            bound = (lam*k-logarithm)/denominator
            if sign == 1:
                lower = max(lower, bound.lo)
            else:
                upper = min(upper, bound.hi)
            grid.append({"lambda": str(lam), "bound_expected_count": bound.receipt()})
    if lower > upper:
        raise ValueError("empty confidence envelope")
    return I(lower, upper)/n, {"count": k, "trials": n,
                              "inverse_delta": str(inverse_delta), "grid": grid}


def feature_counts(counts):
    if len(counts) != 4 or any(len(row) != 4 for row in counts):
        raise ValueError("incomplete setting/outcome table")
    if any(type(k) is not int or k < 0 for row in counts for k in row):
        raise ValueError("invalid public integer count")
    joints = [row[0] for row in counts]
    alice = [sum(counts[2*x+y][0]+counts[2*x+y][1] for y in range(2)) for x in range(2)]
    bob = [sum(counts[2*x+y][0]+counts[2*x+y][2] for x in range(2)) for y in range(2)]
    return joints+alice+bob


def probability_envelopes(counts, config):
    n = sum(sum(row) for row in counts)
    features, receipts = [], []
    epsilon = F(config["settings_predictability"])
    local_lower, local_upper = (1-epsilon)/2, (1+epsilon)/2
    for i, k in enumerate(feature_counts(counts)):
        mean, receipt = count_envelope(k, n, config)
        pl, pu = ((local_lower**2, local_upper**2) if i < 4 else (local_lower, local_upper))
        bound = I(max(F(0), mean.lo/pu), min(F(1), mean.hi/pl))
        features.append(bound)
        receipts.append({**receipt, "feature_index": i,
                         "conditional_setting_probability": [str(pl), str(pu)],
                         "observable_mean": bound.receipt()})
    return {"j": features[:4], "sA": features[4:6], "sB": features[6:8]}, receipts


def center_rates(counts):
    totals = [sum(row) for row in counts]
    joints = [F(row[0], n) for row, n in zip(counts, totals)]
    alice = [F(sum(counts[2*x+y][0]+counts[2*x+y][1] for y in range(2)),
               sum(totals[2*x+y] for y in range(2))) for x in range(2)]
    bob = [F(sum(counts[2*x+y][0]+counts[2*x+y][2] for x in range(2)),
             sum(totals[2*x+y] for x in range(2))) for y in range(2)]
    return {"j": joints, "sA": alice, "sB": bob}, totals


def interval_trig(angle_degrees, config, doubled=False):
    pi = I(*map(F, config["pi"]))
    arg = F(angle_degrees)*pi*(2 if doubled else 1)/180
    return arithmetic.trig(arg, config["interval_terms"]), arithmetic.trig(arg, config["interval_terms"], True)


def rows_interval(angles, config):
    trig = [interval_trig(x, config) for x in angles]
    return [[sa.square()*sb.square(), ca.square()*cb.square(), 2*sa*ca*sb*cb]
            for sa, ca in trig[:2] for sb, cb in trig[2:]]


def interval_inverse(rates, angle_degrees, model, bg, config):
    rows = rows_interval(angle_degrees, config)
    ba, bb = bg
    if model == "independent_OR":
        joint = [rates["j"][2*x+y]-bb*rates["sA"][x]-ba*rates["sB"][y]+ba*bb
                 for x in range(2) for y in range(2)]
    elif model == "named_M3":
        joint = [rates["j"][2*x+y]-rates["sA"][x]*rates["sB"][y]
                 for x in range(2) for y in range(2)]
    else:
        joint = rates["j"]
    m = [rows[i] for i in (0, 1, 3)]
    det = prediction.determinant(m)
    gram = []
    for k in range(3):
        replaced = [row.copy() for row in m]
        for i, index in enumerate((0, 1, 3)):
            replaced[i][k] = joint[index]
        gram.append(prediction.determinant(replaced)/det)
    h, v, coherence = gram
    harmonics = [interval_trig(x, config, True) for x in angle_degrees]
    beta_a = (rates["sA"][0]-rates["sA"][1])/(harmonics[0][1]-harmonics[1][1])
    beta_b = (rates["sB"][0]-rates["sB"][1])/(harmonics[2][1]-harmonics[3][1])
    z = h+v+(4*beta_a*beta_b if model == "named_M3" else 0)
    derivatives = []
    for own, others in ((1, (2, 3)), (3, (0, 1))):
        sine, cosine = harmonics[own]
        s0, c0 = harmonics[others[0]]
        s1, c1 = harmonics[others[1]]
        derivatives.append((-z*sine*(c0-c1)+2*coherence*cosine*(s0-s1))/2)
    return {"gram": {k: x.receipt() for k, x in zip(("H", "V", "X"), gram)},
            "held_out_prediction": sum((a*b for a, b in zip(rows[2], gram)), I.point(0)).receipt(),
            "derivatives_per_radian": [d.receipt() for d in derivatives],
            "derivative_sign": ["positive" if d.lo > 0 else "negative" if d.hi < 0 else "NOT_CERTIFIED" for d in derivatives],
            "minor": det.receipt(),
            "scope": "stationary_named_M3" if model == "named_M3" else "common_mean_source_with_memory"}


def rational_candidate(reconstruction, decimals):
    scale = reconstruction["scale"]
    gram = {k: F(format(x/scale, f".{decimals}f")) for k, x in reconstruction["gram"].items()}
    singles = [F(format(x, f".{decimals}f")) for x in reconstruction["loss_slacks"][:4]]
    return {**gram, **dict(zip(("AH", "AV", "BH", "BV"), singles))}


def make_witness(values):
    h, v, x, ah, av, bh, bv = [values[k] for k in ("H", "V", "X", "AH", "AV", "BH", "BV")]
    uh, uv = ah+bh-h, av+bv-v
    total = uh+uv
    checks = {"positive_H": h > 0, "nonnegative_V": v >= 0, "PSD": x*x <= h*v,
              "loss_nonnegative": min(ah-h, bh-h, av-v, bv-v) >= 0,
              "valid_pair_probability": 0 < total <= 1, "positive_path_weights": uh > 0 and uv > 0}
    if not all(checks.values()):
        return None, checks
    ph = [[F(0)]*3 for _ in range(3)]
    pv = [[F(0)]*3 for _ in range(3)]
    ph[0][0], ph[0][2], ph[2][0] = h/uh, (ah-h)/uh, (bh-h)/uh
    pv[0][0], pv[1][1] = x*x/(h*uv), (v-x*x/h)/uv
    pv[1][2], pv[2][1] = (av-v)/uv, (bv-v)/uv
    phase = [[F(0)]*3 for _ in range(3)]
    phase[0][0] = F(0) if x >= 0 else F(1)
    beta = [[F(0), F(0), F("1/2")]]*2
    recipe = {"name": "public_center_source", "power_H": ph, "power_V": pv,
              "source_mode_phase_V": phase, "beta_A": beta, "beta_B": beta}
    witness = {"Q": total, "uA": F(1), "uB": F(1),
               "preparation_power_H": uh/total, "preparation_power_V": uv/total,
               "recipe": recipe, "statistics": values}
    checks["source_paths_normalized_exactly"] = sum(map(sum, ph)) == sum(map(sum, pv)) == 1
    checks["source_path_powers_nonnegative_exactly"] = min(x for m in (ph,pv) for row in m for x in row) >= 0
    checks["preparation_normalized_exactly"] = uh/total+uv/total == 1
    return witness, checks


def forward_enclosure(values, angle_degrees, model, bg, config):
    trig = [interval_trig(x, config) for x in angle_degrees]
    sa = [values["AH"]*s.square()+values["AV"]*c.square() for s,c in trig[:2]]
    sb = [values["BH"]*s.square()+values["BV"]*c.square() for s,c in trig[2:]]
    joint = [sum((a*values[k] for a,k in zip(row,("H","V","X"))), I.point(0)) for row in rows_interval(angle_degrees, config)]
    ba, bb = bg
    if model == "independent_OR":
        raw_a, raw_b = [ba+(1-ba)*p for p in sa], [bb+(1-bb)*p for p in sb]
        raw_j = [(1-ba)*(1-bb)*joint[2*x+y]+ba*(1-bb)*sb[y]+bb*(1-ba)*sa[x]+ba*bb
                 for x in range(2) for y in range(2)]
    else:
        raw_a, raw_b = [p+ba for p in sa], [p+bb for p in sb]
        raw_j = [joint[2*x+y]+(raw_a[x]*raw_b[y] if model == "named_M3" else 0)
                 for x in range(2) for y in range(2)]
    return {"j": raw_j, "sA": raw_a, "sB": raw_b}


def serial(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, I):
        return value.receipt()
    if isinstance(value, dict):
        return {k: serial(v) for k,v in value.items()}
    if isinstance(value, list):
        return [serial(v) for v in value]
    return value


def run():
    config = specification()
    target = json.loads((HERE/config["target"]).read_text())
    counts = target["counts"]
    centers, totals = center_rates(counts)
    confidence, receipts = probability_envelopes(counts, config)
    op = prediction.criterion()
    angles_deg = op["angles_deg"][0]
    angles = [math.radians(float(F(x))) for x in angles_deg]
    public_bg = [F(x) for x in config["background_per_pulse"]]
    branches = []
    for model in config["models"]:
        bg = ([1-(1-b)**config["window_pulses"] for b in public_bg] if model == "independent_OR"
              else [config["window_pulses"]*b for b in public_bg])
        reconstruction = prediction.inverse(centers, angles, model, bg)
        values = rational_candidate(reconstruction, config["witness_decimal_places"])
        witness, checks = make_witness(values)
        if witness is None:
            branches.append({"model": model, "outcome": "NO_CENTER_WITNESS", "checks": checks})
            continue
        forward = forward_enclosure(values, angles_deg, model, bg, config)
        included = {k: [p.lo >= c.lo and p.hi <= c.hi for p,c in zip(forward[k], confidence[k])]
                    for k in ("j","sA","sB")}
        source_module = prediction.load_source()
        numerical_recipe = {k: serial(v) if k == "name" else v for k,v in witness["recipe"].items()}
        for k in numerical_recipe:
            if k != "name":
                numerical_recipe[k] = [[float(x) for x in row] for row in numerical_recipe[k]]
        source = source_module.OpticalSource(numerical_recipe)
        objects = source.objects_from_preparation(math.sqrt(float(witness["preparation_power_H"])), math.sqrt(float(witness["preparation_power_V"])))
        signal = prediction.read_objects(source_module, objects, angles, float(witness["Q"]), 1.0, 1.0)
        actual = prediction.detection(signal, model, [float(b) for b in bg])
        actual_contained = {k: [interval.contains(F(value)) for value, interval in zip(actual[k], forward[k])]
                            for k in ("j","sA","sB")}
        branches.append({"model": model, "background": bg, "source_member": witness, "checks": checks,
                         "outcome": "EXHIBITED_COMPATIBLE_MEMBER" if all(all(v) for v in included.values()) else "CENTER_MEMBER_OUTSIDE_ENVELOPE",
                         "forward_probability_enclosures": forward, "confidence_inclusion": included,
                         "actual_full_source_forward": actual, "actual_forward_inside_enclosure": actual_contained,
                         "held_out_observed_center": centers["j"][2],
                         "held_out_source_prediction": forward["j"][2],
                         "observable_response_enclosure": interval_inverse(confidence, angles_deg, model, bg, config),
                         "statistical_scope": "stationary_named_M3" if model == "named_M3" else "common_mean_source_with_memory"})
    eberhard = F(counts[0][0],totals[0])-F(counts[1][1],totals[1])-F(counts[2][2],totals[2])-F(counts[3][0],totals[3])
    raw_ch = centers["j"][0]+centers["j"][1]+centers["j"][2]-centers["j"][3]-centers["sA"][0]-centers["sB"][0]
    return serial({"schema":"p23-public-observable-comparison/v1", "version":config["version"],
                   "criterion_sha256":prediction.digest(HERE/"public-criterion.md"), "target_sha256":prediction.digest(HERE/config["target"]),
                   "program_sha256":prediction.digest(__file__), "observable_predictor_sha256":prediction.digest(HERE/"predict.py"),
                   "interval_source_sha256":prediction.digest(HERE.parent/"response/response.py"),
                   "retrospective":True, "private_optimizer_input_required":False,
                   "source_mapping_identified":False,"publication_configuration_identified":False,"production_admitted":False,"bell_event_files_read":0,
                   "setting_trial_totals":totals,"complete_trials":sum(totals),"feature_counts":feature_counts(counts),
                   "centers":centers, "eberhard_center":float(eberhard),"CH_using_pooled_singles_center":float(raw_ch),
                   "confidence_rule":"fixed_exponential_supermartingale_grid_with_Ville_and_family_union",
                   "alpha":config["alpha"], "count_receipts":receipts,"common_mean_confidence":confidence,"branches":branches,
                   "actual_source_or_optimum_verdict":"NOT_IDENTIFIED_BY_COMPATIBILITY",
                   "multipaired_window_qualified":False})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-only", action="store_true")
    args = parser.parse_args()
    content = json.dumps(run(), indent=2, sort_keys=True, allow_nan=False)+"\n"
    if args.check_only:
        print(content,end="")
    else:
        (HERE/"public-comparison.json").write_text(content)


if __name__ == "__main__":
    main()
