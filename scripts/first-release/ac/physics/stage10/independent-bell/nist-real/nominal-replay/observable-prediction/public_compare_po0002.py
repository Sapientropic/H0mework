"""PSD source member; all eight original probability envelopes remain fixed."""
import argparse
from fractions import Fraction as F
import json
import math
from pathlib import Path

import public_compare as base

HERE = Path(__file__).resolve().parent


def revision():
    text = (HERE/"public-criterion-po0002.md").read_text()
    block = text.split("<!-- PO2-FROZEN-BEGIN -->")[1].split("<!-- PO2-FROZEN-END -->")[0]
    return json.loads(block.split("```json")[1].split("```")[0])


def project(values, decimals):
    h, v, x = (values[k] for k in ("H", "V", "X"))
    if min(h,v) < 0:
        return None
    product = h*v
    scale = 10**decimals
    bound = F(math.isqrt(product.numerator*scale*scale//product.denominator), scale)
    chosen = (1 if x >= 0 else -1)*min(abs(x), bound)
    return {**values, "X": chosen}


def actual_forward(witness, angles, model, bg):
    source_module = base.prediction.load_source()
    recipe = {k: v if k == "name" else [[float(x) for x in row] for row in v]
              for k,v in witness["recipe"].items()}
    source = source_module.OpticalSource(recipe)
    objects = source.objects_from_preparation(math.sqrt(float(witness["preparation_power_H"])),
                                              math.sqrt(float(witness["preparation_power_V"])))
    signal = base.prediction.read_objects(source_module, objects, angles, float(witness["Q"]), 1.0, 1.0)
    return base.prediction.detection(signal, model, list(map(float,bg)))


def run():
    rev, config = revision(), base.specification()
    target = json.loads((HERE/config["target"]).read_text())
    counts = target["counts"]
    centers, totals = base.center_rates(counts)
    confidence, receipts = base.probability_envelopes(counts, config)
    angles_deg = base.prediction.criterion()["angles_deg"][0]
    angles = [math.radians(float(F(x))) for x in angles_deg]
    per_pulse = list(map(F,config["background_per_pulse"]))
    branches = []
    for model in config["models"]:
        bg = ([1-(1-b)**config["window_pulses"] for b in per_pulse] if model == "independent_OR"
              else [config["window_pulses"]*b for b in per_pulse])
        reconstruction = base.prediction.inverse(centers, angles, model, bg)
        center = base.rational_candidate(reconstruction,rev["witness_decimal_places"])
        values = project(center,rev["witness_decimal_places"])
        if values is None:
            branches.append({"model":model,"outcome":"NO_PROJECTED_WITNESS","center":center})
            continue
        witness, checks = base.make_witness(values)
        if witness is None:
            branches.append({"model":model,"outcome":"NO_PROJECTED_WITNESS","center":center,"checks":checks})
            continue
        forward = base.forward_enclosure(values, angles_deg, model, bg, config)
        included = {k:[p.lo >= c.lo and p.hi <= c.hi for p,c in zip(forward[k],confidence[k])]
                    for k in ("j","sA","sB")}
        actual = actual_forward(witness,angles,model,bg)
        contains = {k:[interval.contains(F(value)) for value,interval in zip(actual[k],forward[k])]
                    for k in ("j","sA","sB")}
        response = base.interval_inverse(confidence,angles_deg,model,bg,config)
        branches.append({"model":model,"background":bg,"center":center,"projected_statistics":values,
                         "coherence_change":values["X"]-center["X"],"checks":checks,"source_member":witness,
                         "outcome":"EXHIBITED_COMPATIBLE_MEMBER" if all(all(v) for v in included.values()) else "PROJECTED_MEMBER_OUTSIDE_ENVELOPE",
                         "forward_probability_enclosures":forward,"confidence_inclusion":included,
                         "actual_full_source_forward":actual,"actual_forward_inside_enclosure":contains,
                         "held_out_observed_center":centers["j"][2],"held_out_source_prediction":forward["j"][2],
                         "observable_response_enclosure":response,
                         "statistical_scope":"stationary_named_M3" if model == "named_M3" else "common_mean_source_with_memory"})
    return base.serial({"schema":"p23-public-observable-comparison/v2","version":rev["version"],
                        "criterion_sha256":base.prediction.digest(HERE/"public-criterion-po0002.md"),
                        "statistical_criterion_sha256":base.prediction.digest(HERE/"public-criterion.md"),
                        "target_sha256":base.prediction.digest(HERE/config["target"]),"program_sha256":base.prediction.digest(__file__),
                        "parent_program_sha256":base.prediction.digest(HERE/"public_compare.py"),
                        "observable_predictor_sha256":base.prediction.digest(HERE/"predict.py"),
                        "interval_source_sha256":base.prediction.digest(HERE.parent/"response/response.py"),
                        "retrospective":True,"private_optimizer_input_required":False,"source_mapping_identified":False,
                        "publication_configuration_identified":False,"production_admitted":False,"bell_event_files_read":0,
                        "setting_trial_totals":totals,"complete_trials":sum(totals),"feature_counts":base.feature_counts(counts),
                        "centers":centers,"common_mean_confidence":confidence,"count_receipts":receipts,"alpha":config["alpha"],
                        "confidence_rule":"fixed_exponential_supermartingale_grid_with_Ville_and_family_union",
                        "calibration_rows":[0,1,3],"held_out_row":2,"held_out_used_in_projection":False,
                        "branches":branches,"actual_source_or_optimum_verdict":"NOT_IDENTIFIED_BY_COMPATIBILITY",
                        "multipaired_window_qualified":False})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-only",action="store_true")
    args = parser.parse_args()
    content = json.dumps(run(),indent=2,sort_keys=True,allow_nan=False)+"\n"
    if args.check_only:
        print(content,end="")
    else:
        (HERE/"public-comparison-po0002.json").write_text(content)


if __name__ == "__main__":
    main()
