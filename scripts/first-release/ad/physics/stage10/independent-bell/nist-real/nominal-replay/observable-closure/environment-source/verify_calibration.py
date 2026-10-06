#!/usr/bin/env python3
"""Rebuild both sealed calibration sources and cross them on public-input coordinates."""
from __future__ import annotations

import argparse
import contextlib
from fractions import Fraction as F
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
FIRST = {
    "calibration-primary.json": ("57d52ca1d3", "6d3b422a5db6bdcd51f4f2a2b850ebcabb706adf15a63b895750bee6fd21d5bc"),
    "calibration-independent-r0002.json": ("7de2651e11", "d6ad02e1bdd6e8e19cbf7d46316ef116e1eaab3dafabc022a8011db1022a6325"),
}


def require(value, reason):
    if not value:
        raise ValueError(reason)


def module(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    result = importlib.util.module_from_spec(spec)
    sys.modules[name] = result
    spec.loader.exec_module(result)
    return result


def ends(packet):
    return F(packet["exact_lower"]), F(packet["exact_upper"])


def gap(a, b):
    al, ah = ends(a)
    bl, bh = ends(b)
    require(al <= ah and bl <= bh, "reversed_source_interval")
    return max(F(0), al - bh, bl - ah)


def sealed(name, primary):
    path = HERE / name
    commit, digest = FIRST[name]
    require(hashlib.sha256(path.read_bytes()).hexdigest() == digest, "sealed_calibration_receipt_changed")
    primary.arithmetic.frozen(path, commit)
    return json.loads(path.read_text())


def certify_matched_source(primary):
    path = HERE / "matched-certification.json"
    primary.arithmetic.frozen(path)
    receipt = json.loads(path.read_text())
    require(receipt["status"] == "certified", "actual_matched_Born_not_certified")
    for name, digest in receipt["bindings"].items():
        require(hashlib.sha256((primary.ROOT / name).read_bytes()).hexdigest() == digest,
                "matched_source_binding_changed:" + name)
    return {"sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "public_mouth": receipt["unconditional_public_mouth"], "status": receipt["status"]}


def verify():
    primary = module("p23_nec_cross_primary", "calibration_source.py")
    ind = module("p23_nec_cross_independent", "independent_calibration_source.py")
    frozen = primary.arithmetic.frozen(Path(__file__))
    spec, _, _, _ = primary.inputs()
    oldp = sealed("calibration-primary.json", primary)
    oldi = sealed("calibration-independent-r0002.json", primary)
    require(oldp["version"] == oldi["version"] == spec["version"], "calibration_version_mismatch")
    require(oldp["status"] == "source_generated" and oldi["passed"] is True,
            "incomplete_calibration_source")
    require(all(oldi["checks"].values()), "independent_calibration_controls_failed")
    freshp = primary.run()
    with contextlib.redirect_stderr(io.StringIO()):
        freshi = ind.generate(progress=False)
    require({k: v for k, v in oldp.items() if k != "runtime_seconds"} ==
            {k: v for k, v in freshp.items() if k != "runtime_seconds"}, "primary_calibration_first_not_rebuilt")
    require(oldi == freshi, "independent_calibration_successful_first_not_rebuilt")
    require(len(oldp["points"]) == len(oldi["rows"]) == 19, "lost_calibration_point")
    symbolic = ind.generate_native_fringe_polynomials()
    cached_gains = {}
    rows = []
    for number, (p, i) in enumerate(zip(oldp["points"], oldi["rows"])):
        for key in spec["four_box_axes_order"]:
            require(F(p["input"][key]) == F(i["inputs"][key]), "different_public_calibration_input")
        require(p["input"]["allocation"] == i["allocation"], "different_environment_allocation")
        require(p["included_in_default_source_box"] is (number < 17), "override_in_default_source_domain")
        proots, iroots = p["K_cubic_all_roots"], i["K_inverse"]
        require([F(x) for x in proots["polynomial"]] == [F(x) for x in iroots["polynomial"]],
                "different_same_input_cubic")
        require(proots["all_real_distinct_root_count"] == iroots["all_real_root_count"] == 3 and
                proots["all_real_roots_retained"] is True and iroots["full_real_cover"] is True,
                "incomplete_cubic_root_cover")
        require(len(proots["roots"]) == len(iroots["root_intervals"]) == 3, "lost_real_cubic_root")
        root_gaps = [gap(a["interval"], b) for a, b in zip(proots["roots"], iroots["root_intervals"])]
        require(max(root_gaps) == 0, "same_exact_cubic_root_intervals_disjoint")
        pbranches = [b for b in p["branches"] if b.get("source")]
        require(len(pbranches) == len(i["sources"]) == proots["legal_root_count"] ==
                iroots["physical_root_count"], "lost_physical_source_branch")
        branch_rows = []
        q = F(i["inputs"]["pair_probability"])
        if q not in cached_gains:
            cached_gains[q] = ind.gain_from_pair_probability(q, spec["reference_pump_beta_deg"])
        regenerated = cached_gains[q]
        own_roots, _ = ind.k_inverse(regenerated["n_grid"], i["inputs"]["K_A"],
                                    i["inputs"]["K_B"], spec["background_per_pulse"])
        for pbranch, ibranch, root in zip(pbranches, i["sources"], own_roots):
            a, b = pbranch["source"], ibranch["source"]
            require(F(a["G_grid"]) == F(b["G_grid15"]) == regenerated["G"] and
                    F(a["n_grid"]) == F(b["balanced_n_grid15"]) == regenerated["n_grid"],
                    "different_unique_source_grid")
            parameter_gaps = {key: gap(a[x], b[y]) for key, x, y in (
                ("G_root", "G", "G_enclosure"), ("TA", "TA", "transmission_A"),
                ("TB", "TB", "transmission_B"), ("c", "c", "c"),
                ("xiA", "xi_A", "xiA"), ("xiB", "xi_B", "xiB"))}
            require(max(parameter_gaps.values()) <= ind.TOL, "native_calibration_sources_disagree")
            require(pbranch["full_fringe_certificate"]["extrema_obtained_only_after_whole_domain_derivative_certificate"] is True and
                    ibranch["fringe_certificate"]["full_fringe_extrema_generated_before_endpoint_readout"] is True,
                    "endpoint_substituted_for_complete_fringe")
            for key in ("K_A", "K_B"):
                require(gap(pbranch["true_source_calibration_K"][key], ibranch["source_readback"][key]) <= ind.TOL,
                        "different_actual_source_K_readback")
            source = {**regenerated, "TA": root["TA"], "TB": root["TB"], "allocation": i["allocation"]}
            source["c"], _ = ind.coherence_inverse(symbolic, regenerated["n"], source["TA"], source["TB"],
                i["inputs"]["DA_raw_visibility"], i["allocation"], spec)
            # Every forward parameter is rebuilt from the public tuple; sealed source fields only compare.
            shared_probes = []
            for beta in (F(45), F(16)):
                packet = ind.source_packet(source, beta)
                convert = lambda value: primary.I(value.lo, value.hi)
                for angle_a, angle_b in ((0, 0), (90, 0), (45, 45), (-45, 45)):
                    effects = [ind.environment_effect(packet["TA"], packet["xiA"], angle_a),
                               ind.environment_effect(packet["TB"], packet["xiB"], angle_b)]
                    born = ind.independent_born(packet, effects, 6, spec["background_per_pulse"])
                    _, native = primary.native_forward(convert(packet["tH"]), convert(packet["tV"]),
                        convert(source["TA"]), convert(source["TB"]), convert(source["c"]), source["allocation"],
                        angle_a, angle_b, *[primary.I(F(x)) for x in spec["background_per_pulse"]])
                    distance = max(gap(native[key].packet(), born["observed_outcomes"][key].packet())
                                   for key in ("++", "+0", "0+", "00"))
                    require(distance == 0, "shared_public_source_native_Fock_intervals_disjoint")
                    shared_probes.append({"beta_deg": str(beta), "angles_deg": [angle_a, angle_b],
                                          "outcome_outer_distance": str(distance),
                                          "original_source_tail": born["tail"].packet()})
            branch_rows.append({"root_index": pbranch["root_index"],
                "parameter_outer_distances": {k: str(v) for k, v in parameter_gaps.items()},
                "unique_G_grid": a["G_grid"], "unique_balanced_n_grid": a["n_grid"],
                "native_gain_descriptor_and_numeric_grid_kept_distinct": True, "shared_source_probes": shared_probes})
        rows.append({"primary_id": p["id"], "independent_id": i["point_id"], "allocation": i["allocation"],
                     "default_source": number < 17, "all_real_root_outer_distances": [str(x) for x in root_gaps],
                     "source_branches": branch_rows})
    matched = certify_matched_source(primary)
    return {"schema": "p23-nominal-environment-calibration-verification/v1", "version": spec["version"],
        "status": "PUBLIC_RAW_CALIBRATION_ALL_ROOTS_AND_SHARED_SOURCE_FOCK_VERIFIED", "program_freeze": frozen,
        "first_receipts": {name: {"commit": c, "sha256": s} for name, (c, s) in FIRST.items()},
        "primary_first_reproduced": True, "independent_successful_first_reproduced": True,
        "independent_original_unresolved_first_preserved": True, "point_count": 19, "default_point_count": 17,
        "shared_source_Fock_probe_count": sum(len(b["shared_source_probes"]) for r in rows for b in r["source_branches"]),
        "source_rows": rows, "actual_matched_Born_certification": matched,
        "foreign_saved_source_gain_overlap_or_probabilities_used_as_forward_inputs": False,
        "CH_optimization_executed": False, "exact_calibration_inverse_kernel_claim": False,
        "new_full_Born_or_general_Gaussian_determinant_kernel_claim": False,
        "actual_source_or_hardware_identity_verified": False, "apparatus_optimum_verified": False,
        "controller_advance": False, "event_files_read": 0, "retrospective": True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    require(not args.output.exists(), "calibration_verification_output_already_exists")
    result = verify()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(result["status"])


if __name__ == "__main__":
    main()
