#!/usr/bin/env python3
"""Post-first-receipt comparison; original scientific programs/results remain frozen."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import independent as own
import independent_replay as replay

I = own.I
FIRST_HASHES = {
    "primary_source": "15ee9b8dba95a45fcc8d1775a412e27a5107fce026c3fc97815069e5ce3bb8d1",
    "independent_source": "61c4e7c0e769483a988aa7e40cba863c715277832005a99815dd7bc2bd8f2e70",
    "primary_replay": "48d9de2f58139793093dd7be79f6bc7260cf16e97d426b70b7c28b4f77694ca7",
    "independent_replay": "a5835b901d10fe38d733772f972b55bc96a23a3ff564d0b527d840a144582f4b",
}


def interval(x):
    return I(F(x["exact_lower"]), F(x["exact_upper"]))


def overlaps(a, b):
    return a.lo <= b.hi and b.lo <= a.hi


def within(a, b, tolerance):
    return max(abs(a.lo - b.hi), abs(a.hi - b.lo)) <= tolerance


def same_bounds(a, b, tolerance):
    return max(abs(a.lo - b.lo), abs(a.hi - b.hi)) <= tolerance


def source_checks(a, b):
    loss, rotation = a["loss_inverse"], a["rotation"]
    exact_loss = all(F(loss[key]["rational"]) == F(b["loss"][other]["rational"]) and
                     F(loss[key]["sqrt_coefficient"]) == F(b["loss"][other]["radical_coefficient"]) and
                     F(loss[key]["radicand"]) == F(b["loss"][other]["radicand"])
                     for key, other in (("raw_transmission_A", "TA"), ("raw_transmission_B", "TB")))
    ra, rb = a["lambda_root"]["canonical_isolating_bracket"], b["phase_root"]["bracket"]
    return {"raw_kernel": list(map(F, a["geometric_ratio"])) == list(map(F, b["geometric_ratio"])),
        "common_Jones_Z_X": all(F(rotation[k]) == F(b["rotation"][k]) for k in ("Z", "X")),
        "common_Jones_radius": F(rotation["C_squared"]) == F(b["rotation"]["radius_squared"]),
        "coupled_loss_exact": exact_loss,
        "Klyshko_targets": list(map(F, loss["Klyshko_targets"])) ==
            [F(b["loss"]["KA"]), F(b["loss"]["KB"])],
        "source_lambda_is_exact_root": a["lambda_root"]["source_value_is_dyadic_midpoint"] is False,
        "lambda_target": F(a["lambda_root"]["target"]) == F(b["phase_root"]["DA_target"]),
        "lambda_brackets_overlap": overlaps(I(*map(F, ra)), I(*map(F, rb)))}


def trig_box(value):
    value = I.of(value)
    s, c = own.trig(value.midpoint())
    error = own.PI_HI * value.width / 360
    return s + I(-error, error), c + I(-error, error)


def beta_ratios(gain, beta):
    s, c = trig_box(beta)
    def t(g):
        e = replay.exp_interval(2 * g)
        return ((e - 1) / (e + 1)).square()
    return t(gain * c), t(gain * s)


def published_balance(gain, target):
    target = F(target)
    own.require(0 < target < 1, "illegal_printed_source_ratio")
    left, right = F(0), F(45)
    for _ in range(80):
        if right - left <= F(1, 10 ** 15):
            return I(left, right)
        mid = (left + right) / 2
        th, tv = beta_ratios(gain, I(mid))
        ratio = (tv / th).sqrt()
        if ratio.hi < target:
            left = mid
        elif ratio.lo > target:
            right = mid
        else:
            raise ValueError("PRINTED_RATIO_CONTROL_UNRESOLVED")
    raise ValueError("PRINTED_RATIO_CONTROL_UNRESOLVED")


def detector_box(angle, transmission):
    s, c = trig_box(angle)
    return ((1 - transmission * s.square(), -transmission * s * c),
            (-transmission * s * c, 1 - transmission * c.square()))


def born_box(packet, lam, control, config):
    ratios = beta_ratios(replay.gain_norm(packet), control[0])
    loss = packet["loss"]
    ta, tb, _ = own.coupled_loss(loss["KA"], loss["KB"], loss["t_cal"])
    norm = (1 - ratios[0]) * (1 - ratios[1])
    tail = own.source_tail(*ratios, config["source_pair_cutoff"])
    cells = []
    for a, b in ((control[1], control[3]), (control[1], control[4]),
                 (control[2], control[3]), (control[2], control[4])):
        ea, eb = detector_box(a, ta.interval()), detector_box(b, tb.interval())
        branches = []
        for phase in (1, -1):
            g = own.kernel(packet, phase, ratios)
            ma = own.mm(own.mm(own.transpose(g), ea), g)
            mb = own.mm(own.mm(own.transpose(g), g), own.transpose(eb))
            mj = own.mm(ma, own.transpose(eb))
            values = {}
            for name, matrix in (("A", ma), ("B", mb), ("AB", mj)):
                prefix = norm * sum(own.complete_homogeneous(own.trace(matrix), own.det(matrix),
                                                               config["source_pair_cutoff"]), I(0))
                values[name] = prefix + I(0, tail.hi)
            branches.append(values)
        mixed = {k: (1 - lam) * branches[0][k] + lam * branches[1][k] for k in ("A", "B", "AB")}
        cells.append(own.window(mixed, config))
    ch = cells[0]["j"] + cells[1]["j"] + cells[2]["j"] - cells[3]["j"] - cells[0]["sA"] - cells[0]["sB"]
    return ch, {"j": [c["j"] for c in cells], "sA_cell": [c["sA"] for c in cells],
                "sB_cell": [c["sB"] for c in cells]}


def compare(paths):
    executable = own.frozen(__file__)
    data = {}
    for name, path in paths.items():
        own.require(own.digest(path) == FIRST_HASHES[name], "first_scientific_receipt_changed:" + name)
        data[name] = json.loads(Path(path).read_text())
    config, _, confidence, freeze, bindings = own.configuration()
    primary, independent = data["primary_replay"], data["independent_replay"]
    own.require(primary["point_count"] == independent["box_point_count"] == 9, "incomplete_replay_box")
    primary_source = data["primary_source"]
    own.require(primary_source["point_count"] == 9, "incomplete_source_box")
    scope = all(all(d[k] is False for k in own.FLAGS) for d in data.values())
    own.require(scope and primary["global_maximum_kernel_claimed"] is False and
                independent["global_optimum_kernel_proof"] is False, "scope_upgrade_in_receipt")
    tolerance = config["optimization_tolerance"]
    instrument = json.loads((own.HERE / config["documented_source"]).resolve().read_text())
    r_public = F(instrument["preparation"]["amplitudes"]["VV"]) / F(instrument["preparation"]["amplitudes"]["HH"])
    printed_angles = [I(F(x)) for x in instrument["controls"]["alice"] + instrument["controls"]["bob"]]
    records, max_difference = [], F(0)
    for p, psource, q in zip(primary["points"], primary_source["points"], independent["box_points"]):
        expected = (F(q["K_targets"][0]), F(q["K_targets"][1]), F(q["DA_target"]))
        own.require(all(tuple(F(row["point"][k]) for k in ("K_A", "K_B", "DA_target")) == expected
                        for row in (p, psource)), "box_order_changed")
        identity = source_checks(psource["source_parameters"], q["source"])
        identity.update({"replay_source_matches_forward": p["source_parameters"] == psource["source_parameters"]})
        own.require(all(identity.values()), "scientific_source_identity_mismatch")
        packet = q["source"]
        lam = I(*map(F, packet["phase_root"]["bracket"]))
        a0, a1, b0, b1 = map(F, config["angles_deg"])
        raw_cells = []
        for a, b in ((a0, b0), (a0, b1), (a1, b0), (a1, b1)):
            nc, _ = own.pulse(packet, lam, a, b, config["source_pair_cutoff"])
            raw_cells.append(own.window(nc, config))
        raw = {"j": [x["j"] for x in raw_cells], "sA_cell": [x["sA"] for x in raw_cells],
               "sB_cell": [x["sB"] for x in raw_cells]}
        raw_checks = {}
        for key, values in raw.items():
            checks = []
            for k, value in enumerate(values):
                other = interval(psource["public_probabilities"][key][k])
                max_difference = max(max_difference, abs(value.midpoint() - other.midpoint()))
                ci = confidence[key][k]
                pc, ic = other.contained(ci["exact_lower"], ci["exact_upper"]), value.contained(ci["exact_lower"], ci["exact_upper"])
                checks.append({"primary_contained": pc, "independent_contained": ic,
                    "confidence_conclusion_agrees": pc == ic,
                    "enclosures_overlap": overlaps(other, value),
                    "numeric_tolerance": within(other, value, F(config["implementation_tolerance"]))})
            raw_checks[key] = checks
        pcontrol = [interval(x) for x in p["candidate"]["control_box"]]
        pch, _ = born_box(packet, lam, pcontrol, config)
        printed_beta = published_balance(replay.gain_norm(packet), r_public)
        printed_ch, _ = born_box(packet, lam, [printed_beta, *printed_angles], config)
        printed_gain = interval(q["CH"]) - printed_ch
        qpoint = tuple(q["control"])
        qmath = replay.mathematical_point(packet, lam, qpoint, replay.gain_norm(packet), config)
        pr = interval(p["five_components"]["r_cond"])
        qr = interval(q["five_components"][0])
        angles = [within(interval(x), interval(y), F(tolerance["angle_deg"]))
                  for x, y in zip(p["five_components"]["angles_deg"], q["five_components"][1:])]
        ch_check = within(interval(p["candidate"]["CH"]), interval(q["CH"]), F(tolerance["CH"]))
        independent_control = all(overlaps(interval(x), value)
            for x, value in zip(q["five_components"], [qmath["r"], *(I(F(str(x))) for x in qpoint[1:])]))
        records.append({"point_id": q["name"], "source_identity": identity,
            "original_probability_checks": raw_checks,
            "independent_original_probabilities_restored_from_own_first_source": {k: [x.packet() for x in v] for k, v in raw.items()},
            "original_probability_restoration_is_post_first": True,
            "r_agreement": within(pr, qr, F(tolerance["r"])), "angle_agreement": angles,
            "CH_agreement": ch_check,
            "primary_actual_CH_recomputed": pch.packet(), "primary_actual_CH_overlaps_report": overlaps(pch, interval(p["candidate"]["CH"])),
            "independent_actual_CH_overlaps_report": overlaps(qmath["CH"], interval(q["CH"])),
            "independent_actual_five_controls_recomputed": independent_control,
            "printed_five_balance_recomputed": printed_beta.packet(),
            "printed_five_balance_agrees": overlaps(printed_beta, interval(p["documented_readout"]["fixed_gain_circle_balance_deg"])),
            "printed_five_actual_CH_recomputed": printed_ch.packet(),
            "printed_five_actual_CH_overlaps_primary": overlaps(printed_ch, interval(p["documented_readout"]["CH"])),
            "strict_gain_over_printed_five_controls": printed_gain.packet(),
            "strict_improvement_over_printed_five_controls": printed_gain.lo > 0,
            "primary_CH_midpoint_is_math_value": interval(p["candidate"]["CH"]).lo <= pch.midpoint() <= interval(p["candidate"]["CH"]).hi})
    success = all(row["r_agreement"] and all(row["angle_agreement"]) and row["CH_agreement"] and
        row["primary_actual_CH_overlaps_report"] and row["independent_actual_CH_overlaps_report"] and
        row["independent_actual_five_controls_recomputed"] and
        row["printed_five_balance_agrees"] and row["printed_five_actual_CH_overlaps_primary"] and
        all(all(x["confidence_conclusion_agrees"] and x["enclosures_overlap"] and x["numeric_tolerance"]
                for x in v) for v in row["original_probability_checks"].values())
        for row in records)
    band = []
    for index, (a, b) in enumerate(zip(primary["five_component_candidate_band"], independent["band"])):
        band.append(same_bounds(I(*map(F, a)), interval(b), F(tolerance["r"] if index == 0 else tolerance["angle_deg"])))
    return {"schema": "p23-frame-window-independent-comparison/v1", "version": own.VERSION,
        "executable_freeze": executable, "criterion_freeze": freeze, "bindings": bindings,
        "first_receipt_hashes": FIRST_HASHES, "first_receipts_preserved": True,
        "source_first_receipts_mutually_blind": True, "optimization_first_receipts_mutually_blind": True,
        "comparison_after_both_firsts": True, "records": records,
        "max_original_probability_midpoint_difference": str(max_difference), "band_agreement": band,
        "primary_band_status": primary["band_status"], "independent_band_status": independent["outcome"],
        "verdict": "CERTIFIED_NUMERIC_FRAME_REPLAY_AGREEMENT" if success and all(band) else "REFUTED_NUMERIC_FRAME_REPLAY_AGREEMENT",
        "global_maximum_kernel_claimed": False, "retrospective": True,
        "bell_event_files_read": 0, **{k: False for k in own.FLAGS}}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--primary-source", default="/tmp/p23-fw-primary-first.json")
    parser.add_argument("--independent-source", default="/tmp/p23-fw-independent-first/member.json")
    parser.add_argument("--primary-replay", default="/tmp/p23-fw-primary-replay-first.json")
    parser.add_argument("--independent-replay", default="/tmp/p23-fw-independent-first/replay.json")
    parser.add_argument("--output")
    args = parser.parse_args()
    paths = {name: getattr(args, name) for name in FIRST_HASHES}
    value = compare(paths)
    text = own.json_dump(value)
    if args.output:
        Path(args.output).write_text(text)
    else:
        print(text, end="")


if __name__ == "__main__":
    main()
