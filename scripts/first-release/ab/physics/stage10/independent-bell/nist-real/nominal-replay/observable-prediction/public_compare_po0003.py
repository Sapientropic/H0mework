"""Whole-cell held-out source member and complete setting-specific single checks."""
import argparse
from fractions import Fraction as F
import json
import math
from pathlib import Path

import public_compare as base
import public_compare_po0002 as source_member

HERE = Path(__file__).resolve().parent


def revision():
    text = (HERE/"public-criterion-po0003.md").read_text()
    section = text.split("<!-- PO3-FROZEN-BEGIN -->")[1].split("<!-- PO3-FROZEN-END -->")[0]
    return json.loads(section.split("```json")[1].split("```")[0])


def training_view(counts):
    return {str(i): counts[i].copy() for i in (0,1,3)}


def train(training, angles, model, bg):
    if set(training) != {"0","1","3"}:
        raise ValueError("training interface permits only 00/01/11")
    totals = {i:sum(row) for i,row in training.items()}
    joints = [F(training[str(i)][0], totals[str(i)]) for i in (0,1,3)]
    sa = [F(training[i][0]+training[i][1],totals[i]) for i in ("0","3")]
    sb = [F(training[i][0]+training[i][2],totals[i]) for i in ("0","3")]
    ba,bb = bg
    if model == "named_M3":
        joints = [j-sa[x]*sb[y] for j,(x,y) in zip(joints,((0,0),(0,1),(1,1)))]
    elif model == "independent_OR":
        joints = [j-bb*sa[x]-ba*sb[y]+ba*bb for j,(x,y) in zip(joints,((0,0),(0,1),(1,1)))]
    rows = [base.prediction.design(angles[x],angles[2+y]) for x,y in ((0,0),(0,1),(1,1))]
    gram,_ = base.prediction.cramer(rows,joints,1e-14)
    alpha_a,beta_a = base.prediction.single_coefficients(sa,angles[:2],1e-14)
    alpha_b,beta_b = base.prediction.single_coefficients(sb,angles[2:],1e-14)
    fa,fb = ((1-float(ba)),(1-float(bb))) if model == "independent_OR" else (1.0,1.0)
    return {"gram":dict(zip(("H","V","X"),gram)),"scale":fa*fb,
            "loss_slacks":[(alpha_a-float(ba)-beta_a)/fa,(alpha_a-float(ba)+beta_a)/fa,
                           (alpha_b-float(bb)-beta_b)/fb,(alpha_b-float(bb)+beta_b)/fb]}


def envelopes(counts, config):
    n = sum(map(sum,counts))
    features = [row[0] for row in counts]+[row[0]+row[1] for row in counts]+[row[0]+row[2] for row in counts]
    eps = F(config["settings_predictability"])
    pl,pu = ((1-eps)/2)**2,((1+eps)/2)**2
    intervals,receipts = [],[]
    for index,k in enumerate(features):
        mean,receipt = base.count_envelope(k,n,config)
        interval = base.I(max(F(0),mean.lo/pu),min(F(1),mean.hi/pl))
        intervals.append(interval)
        receipts.append({**receipt,"feature_index":index,"conditional_setting_probability":[str(pl),str(pu)],
                         "observable_mean":interval.receipt()})
    return {"j":intervals[:4],"sA_cell":intervals[4:8],"sB_cell":intervals[8:]},receipts


def run():
    rev,config = revision(),base.specification()
    config = {**config,"features":rev["features_in_global_union"]}
    target = json.loads((HERE/config["target"]).read_text())
    counts = target["counts"]
    training = training_view(counts)
    angles_deg = base.prediction.criterion()["angles_deg"][0]
    angles = [math.radians(float(F(x))) for x in angles_deg]
    per_pulse = list(map(F,config["background_per_pulse"]))
    # Construct every member before computing any held-out rate or global CI.
    members = []
    for model in config["models"]:
        bg = ([1-(1-b)**config["window_pulses"] for b in per_pulse] if model == "independent_OR"
              else [config["window_pulses"]*b for b in per_pulse])
        center = base.rational_candidate(train(training,angles,model,bg),rev["witness_decimal_places"])
        values = source_member.project(center,rev["witness_decimal_places"])
        witness,checks = base.make_witness(values) if values is not None else (None,{})
        members.append((model,bg,center,values,witness,checks))
    confidence,receipts = envelopes(counts,config)
    branches = []
    for model,bg,center,values,witness,checks in members:
        if witness is None:
            branches.append({"model":model,"outcome":"NO_PROJECTED_WITNESS","center":center,"checks":checks})
            continue
        raw = base.forward_enclosure(values,angles_deg,model,bg,config)
        forward = {"j":raw["j"],"sA_cell":[raw["sA"][x] for x in range(2) for y in range(2)],
                   "sB_cell":[raw["sB"][y] for x in range(2) for y in range(2)]}
        included = {k:[p.lo >= c.lo and p.hi <= c.hi for p,c in zip(forward[k],confidence[k])]
                    for k in forward}
        actual = source_member.actual_forward(witness,angles,model,bg)
        actual_cells = {"j":actual["j"],"sA_cell":[actual["sA"][x] for x in range(2) for y in range(2)],
                        "sB_cell":[actual["sB"][y] for x in range(2) for y in range(2)]}
        contains = {k:[interval.contains(F(value)) for value,interval in zip(actual_cells[k],forward[k])]
                    for k in forward}
        response = base.interval_inverse({"j":confidence["j"],"sA":[confidence["sA_cell"][i] for i in (0,3)],
                                          "sB":[confidence["sB_cell"][i] for i in (0,3)]},angles_deg,model,bg,config)
        branches.append({"model":model,"background":bg,"center":center,"projected_statistics":values,
                         "coherence_change":values["X"]-center["X"],"source_member":witness,"checks":checks,
                         "outcome":"EXHIBITED_COMPATIBLE_MEMBER" if all(all(v) for v in included.values()) else "PROJECTED_MEMBER_OUTSIDE_ENVELOPE",
                         "forward_probability_enclosures":forward,"confidence_inclusion":included,
                         "actual_full_source_forward":actual,"actual_forward_inside_enclosure":contains,
                         "held_out_observed_center":F(counts[2][0],sum(counts[2])),"held_out_source_prediction":forward["j"][2],
                         "observable_response_enclosure":response,
                         "statistical_scope":"stationary_named_M3" if model == "named_M3" else "common_mean_source_with_memory"})
    altered = [row.copy() for row in counts]
    altered[2] = [row+100000 for row in counts[2]]
    independence = training_view(altered) == training
    return base.serial({"schema":"p23-public-observable-comparison/v3","version":rev["version"],
                        "criterion_sha256":base.prediction.digest(HERE/"public-criterion-po0003.md"),
                        "statistical_criterion_sha256":base.prediction.digest(HERE/"public-criterion.md"),
                        "source_criterion_sha256":base.prediction.digest(HERE/"public-criterion-po0002.md"),
                        "target_sha256":base.prediction.digest(HERE/config["target"]),"program_sha256":base.prediction.digest(__file__),
                        "parent_program_sha256":base.prediction.digest(HERE/"public_compare.py"),
                        "member_program_sha256":base.prediction.digest(HERE/"public_compare_po0002.py"),
                        "observable_predictor_sha256":base.prediction.digest(HERE/"predict.py"),
                        "interval_source_sha256":base.prediction.digest(HERE.parent/"response/response.py"),
                        "retrospective":True,"private_optimizer_input_required":False,"source_mapping_identified":False,
                        "publication_configuration_identified":False,"production_admitted":False,"bell_event_files_read":0,
                        "complete_trials":sum(map(sum,counts)),"setting_trial_totals":[sum(row) for row in counts],
                        "training_rows":[0,1,3],"single_training_rows":{"A0":0,"A1":3,"B0":0,"B1":3},"held_out_row":2,
                        "held_out_count_access_in_member_construction":False,"whole_held_out_row_change_leaves_training_identical":independence,
                        "features_evaluated":12,"features_in_global_union":16,"alpha":config["alpha"],
                        "confidence_rule":"fixed_exponential_supermartingale_grid_with_Ville_and_family_union",
                        "common_mean_confidence":confidence,"count_receipts":receipts,"branches":branches,
                        "actual_source_or_optimum_verdict":"NOT_IDENTIFIED_BY_COMPATIBILITY","multipaired_window_qualified":False})


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--check-only",action="store_true")
    args = parser.parse_args()
    content = json.dumps(run(),indent=2,sort_keys=True,allow_nan=False)+"\n"
    if args.check_only:
        print(content,end="")
    else:
        (HERE/"public-comparison-po0003.json").write_text(content)


if __name__ == "__main__":
    main()
