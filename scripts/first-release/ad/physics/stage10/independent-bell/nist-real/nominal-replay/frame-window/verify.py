#!/usr/bin/env python3
"""Source-bound intake of the complete calibrated Jones-source replay."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
VERSION = "p23-frame-window-fw0001"
SCHEMA = "p23-frame-window-verification/v1"
CONTRACT = "4c86dd68e7feccd66fe0370a67175c4697d8d760"
FLAGS = ("source_mapping_identified", "publication_configuration_identified", "production_admitted",
         "actual_window_model_identified", "calibration_protocol_identified", "noise_channel_identified",
         "source_pair_rate_reference_identified", "common_Jones_map_identified",
         "equal_branch_conversion_identified", "actual_pump_actuator_identified")
REQUIRED = ("both_public_members_verified", "all_nine_numeric_replays_verified",
            "full_printed_five_control_gain_verified", "source_calibration_inverse_kernel")
FIRST_HASHES = {
    "primary_source": "15ee9b8dba95a45fcc8d1775a412e27a5107fce026c3fc97815069e5ce3bb8d1",
    "independent_source": "61c4e7c0e769483a988aa7e40cba863c715277832005a99815dd7bc2bd8f2e70",
    "primary_replay": "48d9de2f58139793093dd7be79f6bc7260cf16e97d426b70b7c28b4f77694ca7",
    "independent_replay": "a5835b901d10fe38d733772f972b55bc96a23a3ff564d0b527d840a144582f4b",
}
RECEIPTS = {
    "forward.json": "9ad0bc8023680fef1a8e34ab070bd787b7985c16b719983022d324668bb5c77c",
    "forward-source.json": "683a65672544383c309ea6654aa19827e64d357a8bb9e84047cf83b0a0126925",
    "storage-intake.json": "da017705bb7bba43ec0a0eddc9d50801328540fab71fa3a93dfc29630e727d3d",
    "independent.json": FIRST_HASHES["independent_source"],
    "replay.json": FIRST_HASHES["primary_replay"],
    "independent_replay.json": FIRST_HASHES["independent_replay"],
    "independent-comparison.json": "6bec307f3a52ec29b24c7919971ecd66c5bc3b3731cd4c7be75bfc638f4270f6",
    "inverse-certification.json": "64150331dba561f662b4fec18d54dceb8e794a33a71643b05e58a5234c2e69b9",
}
PROGRAMS = {
    "forward.py": "6d3e97a6425d08fdcb965a20965347201a81a84fcc7bfbdf9c5873a2df4f4666",
    "replay.py": "b0cee41a211eb92f44aa8b4c4b652376a4ea981a9a56d7becb5dd6565fd00c3e",
    "independent.py": "7e3e014413c25f7f158bb4c5fae9e552bbd7a935bed24f3a6f96b9b593045084",
    "independent_replay.py": "4eadeee8995b6a0f9339558b3b660df0e704b2bab13413053de3c092f4419468",
    "independent_comparison.py": "134ad1067973ce8525dd13b02f8aaa23949467335034edc01cc87f5be549030a",
    "intake.py": "9b10552761e169d2faaf216a36e7e57a8c026b907bed87b0d1e80c8404226013",
}


def require(value, reason):
    if not value:
        raise ValueError(reason)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def hash_value(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text(), parse_constant=lambda x: (_ for _ in ()).throw(ValueError("nonfinite_json:" + x)))


def committed(path, commit=None):
    path = Path(path).resolve()
    name = path.relative_to(ROOT).as_posix()
    if commit is None:
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", name], cwd=ROOT, text=True).strip()
    require(bool(commit), "uncommitted_execution_source:" + name)
    require(subprocess.check_output(["git", "show", commit + ":" + name], cwd=ROOT) == path.read_bytes(),
            "unfrozen_execution_source:" + name)
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    return {"path": name, "commit": commit, "sha256": digest(path)}


def bound_source(binding):
    path = (ROOT / binding["path"]).resolve()
    require(path.is_relative_to(ROOT) and digest(path) == binding["sha256"], "source_binding_changed")
    if "commit" in binding:
        committed(path, binding["commit"])


def load_owned(name, filename):
    path = HERE / filename
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, "owned_module_unavailable")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


@lru_cache(maxsize=1)
def modules():
    for name, expected in PROGRAMS.items():
        require(digest(HERE / name) == expected, "scientific_program_changed:" + name)
        committed(HERE / name)
    own = load_owned("independent", "independent.py")
    replay = load_owned("independent_replay", "independent_replay.py")
    comparison = load_owned("p23_fw_owned_comparison", "independent_comparison.py")
    primary = load_owned("p23_fw_owned_forward", "forward.py")
    intake = load_owned("p23_fw_owned_intake", "intake.py")
    return own, replay, comparison, primary, intake


def scope(value):
    require(value.get("version") == VERSION and all(value.get(k) is False for k in FLAGS), "actual_identity_scope_changed")
    require(value.get("retrospective") is True and type(value.get("bell_event_files_read")) is int and
            value["bell_event_files_read"] == 0, "information_access_scope_changed")


def inputs(directory):
    committed(__file__)
    committed(HERE / "criterion.md", CONTRACT)
    committed(HERE / "sources.json", CONTRACT)
    own, replay, cmp, primary, intake = modules()
    config, counts, confidence, freeze, bindings = own.configuration()
    require(config["status"] == "frozen_before_execution" and config["nine_point_band_replaces_r0003_band"] is False and
            config["global_optimum_kernel_proof"] is False, "scientific_contract_scope_changed")
    public_text = (HERE.parent / "shalm2015-channel-inputs.txt").read_text()
    rows = re.findall(r"(\d+(?:\.\d+)?)\s+\+-\s+(\d+(?:\.\d+)?)\s*%\s*\((Alice|Bob)\)", public_text)
    require(len(rows) == 2 and {x[2] for x in rows} == {"Alice", "Bob"}, "ambiguous_public_efficiency")
    efficiencies = {name: (F(center) / 100, F(width) / 100) for center, width, name in rows}
    require([efficiencies[k][0] for k in ("Alice", "Bob")] == list(map(F, config["klyshko_target_center"])) and
            all(x[1] == F(config["klyshko_probability_half_width"]) == F(".003") for x in efficiencies.values()),
            "text_machine_efficiency_unit_mismatch")
    data = {}
    for name, expected in RECEIPTS.items():
        committed(HERE / name)
        require(digest(HERE / name) == expected and digest(directory / name) == expected, "frozen_receipt_changed:" + name)
        data[name] = read(directory / name)
    for name in ("forward.json", "forward-source.json", "independent.json", "replay.json",
                 "independent_replay.json", "independent-comparison.json"):
        scope(data[name])
    require(data["forward.json"]["bindings"] == data["forward-source.json"]["bindings"] ==
            data["independent.json"]["bindings"] == data["independent_replay.json"]["bindings"] ==
            data["independent-comparison.json"]["bindings"] == bindings, "original_source_bindings_changed")
    for name, sha in PROGRAMS.items():
        require(digest(HERE / name) == sha, "scientific_program_changed:" + name)
    for binding in data["replay.json"]["bindings"].values():
        bound_source(binding)
    for name in ("forward.json", "forward-source.json", "independent.json", "independent_replay.json", "independent-comparison.json"):
        bound_source(data[name]["executable_freeze"])
        bound_source(data[name]["criterion_freeze"])
    bound_source(data["independent_replay.json"]["library_freeze"])
    return config, counts, confidence, freeze, bindings, data


def inverse_certificate(certificate):
    require(certificate["schema"] == "p23-klyshko-inverse-lean-certification/v1" and certificate["version"] == VERSION and
            certificate["status"] == "certified" and certificate["criterion_freeze"] == CONTRACT, "invalid_inverse_certificate")
    for path, sha in certificate["bindings"].items():
        require(digest(ROOT / path) == sha, "inverse_kernel_source_changed")
    expected = {"generated_legal_coupled_transmissions": True, "original_PGF_singles_joint_readback": True,
                "both_original_Klyshko_targets_readback": True, "nonzero_herald_generated": True,
                "large_root_excluded_by_source_legality": True, "Gaussian_vacuum_Born_identity": False,
                "whole_window_Born_identity": False, "actual_NIST_calibration_protocol": False}
    require(set(certificate["kernel_claims"]) == set(expected) and
            all(certificate["kernel_claims"][k] is v for k, v in expected.items()), "inverse_kernel_scope_changed")
    require(certificate["authorized_axioms"] == ["propext", "Classical.choice", "Quot.sound"], "inverse_axioms_changed")
    audit = certificate["source_audit"]
    for key, number in (("inverse_namespace_declarations_including_audit", 73), ("dependency_nodes", 15401),
                        ("required_nodes", 32), ("primitive_nodes", 10886)):
        require(type(audit[key]) is int and audit[key] == number, "inverse_dependency_closure_changed")
    require(audit["original_PGF_and_both_herald_directions_in_closure"] is True and
            audit["target_readback_in_primitive"] is False and audit["operational_root_in_closure"] is False and
            audit["public_domain_nonempty_kernel_examples"] is True, "inverse_primitive_scope_changed")
    focused = certificate["focused_verification"]
    require(focused["fresh_source_compilation"] is True and type(focused["trust_level"]) is int and focused["trust_level"] == 0 and
            focused["warning_as_error"] is True and len(focused["commands"]) == len(focused["lsp"]) == 5,
            "inverse_focused_verification_missing")
    for row in focused["commands"]:
        require(type(row["returncode"]) is int and row["returncode"] == 0 and digest(ROOT / row["source"]) == row["sha256"],
                "inverse_source_compilation_failed")
    require(all(type(row["errors"]) is int and type(row["warnings"]) is int and row["errors"] == row["warnings"] == 0
                for row in focused["lsp"]), "inverse_LSP_errors")
    require(all(certificate[k] is False for k in ("source_mapping_identified", "publication_configuration_identified",
            "production_admitted", "calibration_protocol_identified", "actual_source_failure_claimed")), "inverse_actual_identity_changed")


def source_check(primary, independent, expected, config, counts):
    own, replay, cmp, _, _ = modules()
    name, ka, kb, target = expected
    primary_name = name if name == "center" else "corner_" + format(int(name.removeprefix("corner_")), "03b")
    require(primary["point"]["point_id"] == primary_name and
            tuple(map(F, (primary["point"][k] for k in ("K_A", "K_B", "DA_target")))) == (ka, kb, target) and
            independent["name"] == name and tuple(map(F, independent["K_targets"])) == (ka, kb) and
            F(independent["DA_target"]) == target, "missing_or_changed_calibration_corner")
    packet, _, _, reconstruction = own.source_from_view(own.training_view(counts), ka, kb, config)
    actual = independent["source"]
    require(all(canonical(packet[k]) == canonical(actual[k]) for k in packet), "single_only_source_or_K_target_mapping_changed")
    require(canonical(reconstruction) == canonical(independent["single_construction"]), "single_reconstruction_changed")
    phase = actual["phase_root"]
    require(phase["representation"] == "exact_complete_DA_left_threshold" and F(phase["DA_target"]) == target,
            "lambda_source_is_not_exact_threshold")
    lam = own.I(*map(F, phase["bracket"]))
    require(lam.contained(0, F(1, 2)) and 0 < lam.width <= F(config["lambda_bracket_width"]), "illegal_lambda_root_bracket")
    identity = cmp.source_checks(primary["source_parameters"], actual)
    require(all(v is True for v in identity.values()), "independent_source_identity_changed")
    require(primary["source_parameters"]["lambda_root"]["profile_rotation"] == primary["source_parameters"]["rotation"] and
            primary["source_parameters"]["lambda_root"]["profile_loss_inverse"] == primary["source_parameters"]["loss_inverse"],
            "lambda_profile_source_mismatch")
    require(cmp.overlaps(cmp.interval(primary["phase_flip_probability_enclosure"]), lam), "source_lambda_enclosure_changed")
    return actual, lam


def polynomial(primary, packet, probe, config):
    U, A, B, K0 = primary.fringe_profile(packet, probe["axis"], config)
    lam = F(probe["lambda"])
    left = primary.p_sub(primary.p_mul(primary.p_derivative(U), A), primary.p_mul(U, primary.p_derivative(A)))
    right = primary.p_sub(primary.p_mul(primary.p_derivative(U), B), primary.p_mul(U, primary.p_derivative(B)))
    P = primary.primitive(primary.p_add(primary.p_scale(primary.p_mul(left, primary.p_mul(B, B)), 1-lam),
                                    primary.p_scale(primary.p_mul(right, primary.p_mul(A, A)), lam)))
    for name, values in (("U", U), ("A", A), ("B", B), ("derivative_polynomial", P)):
        record = probe[name + "_coefficients"]
        require(type(record["degree"]) is int and record["degree"] == len(values)-1 and
                record["sha256"] == hash_value(primary.coefficient_receipt(values)) and
                record["rebuild_from_frozen_generator"] is True, "fringe_profile_coefficients_changed")
    require(len(P) <= 7, "fringe_degree_exceeded")
    return U, A, B, K0, P


def primary_probe_structure(probe, config):
    own, _, cmp, _, _ = modules()
    inventory = probe["root_inventory"]
    require(probe["constant_fringe"] is False and type(inventory["real_root_count"]) is int and
            inventory["real_root_count"] == len(probe["root_brackets"]) and
            inventory["variation_minus_bound"]-inventory["variation_plus_bound"] == inventory["real_root_count"],
            "fringe_root_inventory_incomplete")
    require(type(inventory["cauchy_bound"]) is int and inventory["cauchy_bound"] > 0 and
            type(inventory["sturm_splits"]) is int and 0 <= inventory["sturm_splits"] <= config["fringe_sturm_split_cap"] and
            type(probe["refinement_depth"]) is int and 0 < probe["refinement_depth"] <= config["fringe_root_refinement_depth_cap"],
            "fringe_resource_contract_changed")
    previous = F(-inventory["cauchy_bound"])
    for row in probe["root_brackets"]:
        lo, hi = F(row["lo"]), F(row["hi"])
        require(previous <= lo <= hi <= inventory["cauchy_bound"] and type(row["count"]) is int and row["count"] == 1 and
                row["chain"] in inventory["chains"] and row["exact_root"] is False and
                row["variation_lo"]-row["variation_hi"] == 1, "fringe_root_bracket_missing_or_invalid")
        previous = hi
    require(len(probe["candidate_values"]) == len(probe["root_brackets"])+1 and
            canonical(probe["candidate_values"][-1]) == canonical(probe["q_infinity"]), "fringe_projective_infinity_missing")
    values = [cmp.interval(x) for x in probe["candidate_values"]]
    maximum, minimum = cmp.interval(probe["maximum"]), cmp.interval(probe["minimum"])
    require((maximum.lo, maximum.hi) == (max(x.lo for x in values), max(x.hi for x in values)) and
            (minimum.lo, minimum.hi) == (min(x.lo for x in values), min(x.hi for x in values)) and
            minimum.lo >= 0 and maximum.lo+minimum.lo > 0, "fringe_extrema_not_generated_from_all_roots")
    require(cmp.overlaps((maximum-minimum)/(maximum+minimum), cmp.interval(probe["visibility"])), "fringe_visibility_readout_changed")


def primary_calibration(row, config):
    own, _, cmp, primary, _ = modules()
    c, packet = row["calibration_readouts"], row["source_parameters"]
    target = F(row["point"]["DA_target"])
    require(c["calibration_protocol_identified"] is False and F(c["target"]) == target and
            c["lambda_root"] == packet["lambda_root"] and c["lambda_root"]["source_value_is_dyadic_midpoint"] is False,
            "lambda_midpoint_substituted_for_source")
    probes = c["threshold_probes"]
    require(2 < len(probes) <= config["lambda_decision_cap"]+2 and [F(x["lambda"]) for x in probes[:2]] == [F(0), F(1, 2)],
            "lambda_endpoint_or_decision_missing")
    lo, hi = F(0), F(1, 2)
    require(cmp.interval(probes[0]["visibility"]).lo > target > cmp.interval(probes[1]["visibility"]).hi, "lambda_root_not_bracketed")
    for index, probe in enumerate(probes):
        require(probe["axis"] == "DA", "lambda_used_wrong_fringe_axis")
        primary_probe_structure(probe, config)
        polynomial(primary, packet, probe, config)
        if index < 2:
            continue
        require(list(map(F, probe["bracket_before"])) == [lo, hi] and F(probe["lambda"]) == (lo+hi)/2,
                "lambda_bisection_trajectory_changed")
        v = cmp.interval(probe["visibility"])
        if v.lo > target:
            lo = F(probe["lambda"])
        elif v.hi < target:
            hi = F(probe["lambda"])
        else:
            raise ValueError("unresolved_lambda_decision")
    require(list(map(F, c["threshold_bracket"])) == list(map(F, packet["lambda_root"]["canonical_isolating_bracket"])) == [lo, hi] and
            hi-lo <= F(config["lambda_bracket_width"]), "lambda_final_enclosure_changed")
    result = list(probes)
    for axis, key in (("HV", "HV_full_fringe"), ("DA", "DA_full_fringe")):
        for side, weight in (("left_probe", lo), ("right_probe", hi)):
            p = c[key][side]
            require(p["axis"] == axis and F(p["lambda"]) == weight, "final_fringe_source_changed")
            primary_probe_structure(p, config)
            polynomial(primary, packet, p, config)
            result.append(p)
    hv = cmp.interval(c["HV_full_fringe"]["visibility"])
    da = cmp.interval(c["DA_full_fringe"]["visibility_enclosure"])
    require(hv.contained(*config["visibility_HV_interval"]) and da.lo <= target <= da.hi and
            F(c["DA_full_fringe"]["exact_by_threshold_definition"]) == target and
            max(abs(da.lo-target), abs(da.hi-target)) <= F(config["calibration_center_computational_error"]),
            "public_calibration_enclosure_changed")
    return result


def independent_probe(probe, curve, config):
    own, _, cmp, _, _ = modules()
    require(probe["chart_count"] == 2 and probe["infinity_is_cot_zero"] is True and
            probe["finite_prefix_renormalized"] is False and probe["Gamma_trace_recurrence"] is True and
            probe["Gaussian_inverse_used"] is False and F(probe["source_tail"]) == curve.tail and
            type(probe["splits"]) is int and 0 <= probe["splits"] <= config["fringe_bernstein_split_cap"],
            "independent_fringe_basis_or_tail_changed")
    poly = curve._profile(F(probe["lambda_probe"]))
    expected_hash = hashlib.sha256(json.dumps([x.packet() for x in poly], sort_keys=True).encode()).hexdigest()
    require(probe["polynomial_sha256"] == expected_hash, "independent_fringe_polynomial_changed")
    for chart in ("tan", "cot"):
        coverage = sorted((x for x in probe["coverage"] if x["chart"] == chart), key=lambda x: F(x["left"]))
        edge = F(-1)
        for box in coverage:
            left, right = F(box["left"]), F(box["right"])
            require(left == edge and left < right <= 1 and type(box["variation"]) is int and box["variation"] in (0, 1),
                    "independent_fringe_chart_gap")
            edge = right
        require(edge == 1, "independent_fringe_chart_missing")
        critical = [x for x in probe["critical_boxes"] if x["chart"] == chart]
        positive = [x for x in coverage if x["variation"] == 1]
        require(len(critical) == len(positive) and all(any(F(c["left"]) <= F(r["left"]) <= F(r["right"]) <= F(c["right"])
                    for c in positive) for r in critical), "independent_fringe_critical_box_missing")
    maximum, minimum = cmp.interval(probe["prefix_maximum"]), cmp.interval(probe["prefix_minimum"])
    m, s = maximum+own.I(0, curve.tail), minimum+own.I(0, curve.tail)
    visibility = own.I.outward((m.lo-s.hi)/(m.lo+s.hi), (m.hi-s.lo)/(m.hi+s.lo))
    require(canonical(visibility.packet()) == canonical(probe["full_visibility"]), "independent_fringe_visibility_changed")


def independent_calibration(row, config):
    own, _, cmp, _, _ = modules()
    packet, c = row["source"], row["calibration"]
    target = F(row["DA_target"])
    ta, tb, _ = own.coupled_loss(*row["K_targets"], config["calibration_geometric_ratio"])
    curves = {axis: own.Fringe(packet, ta, tb, axis, config) for axis in ("DA", "HV")}
    require(c["representation"] == "exact_left_threshold_root" and c["midpoint_is_source_weight"] is False and
            c["DA_exact_root_realizes_target"] is True and F(c["DA_target"]) == target and list(map(F, c["domain"])) == [0, F(1, 2)],
            "independent_lambda_midpoint_substituted")
    probes = c["probes"]
    require(2 < len(probes) <= config["lambda_decision_cap"]+2 and
            [F(x["lambda_probe"]) for x in probes[:2]] == [0, F(1, 2)], "independent_lambda_endpoint_missing")
    require(cmp.interval(probes[0]["full_visibility"]).lo > target > cmp.interval(probes[1]["full_visibility"]).hi,
            "independent_lambda_not_bracketed")
    lo, hi = F(0), F(1, 2)
    for i, p in enumerate(probes):
        require(p["basis"] == "DA", "independent_wrong_fringe_axis")
        independent_probe(p, curves["DA"], config)
        if i < 2:
            continue
        require(F(p["lambda_probe"]) == (lo+hi)/2, "independent_lambda_trajectory_changed")
        v = cmp.interval(p["full_visibility"])
        if p["decision"] == "above_target" and v.lo > target:
            lo = F(p["lambda_probe"])
        elif p["decision"] == "below_target" and v.hi < target:
            hi = F(p["lambda_probe"])
        else:
            raise ValueError("independent_lambda_decision_unresolved")
    lam = cmp.interval(c["bracket"])
    require((lam.lo, lam.hi) == (lo, hi) and list(map(F, packet["phase_root"]["bracket"])) == [lo, hi] and
            0 < hi-lo <= F(config["lambda_bracket_width"]), "independent_final_lambda_changed")
    for axis in ("DA", "HV"):
        require(len(c["final_"+axis]) == 2, "independent_final_fringe_missing")
        for p, weight in zip(c["final_"+axis], (lo, hi)):
            require(p["basis"] == axis and F(p["lambda_probe"]) == weight, "independent_final_fringe_weight_changed")
            independent_probe(p, curves[axis], config)
    da, hv = cmp.interval(c["DA_interval"]), cmp.interval(c["HV_interval"])
    require(da.lo <= target <= da.hi and da.width <= 2*F(config["calibration_center_computational_error"]) and
            hv.contained(*config["visibility_HV_interval"]), "independent_public_calibration_changed")
    return len(probes)+4


def rebuilt_probe(packet, probe, config, gaussian):
    """Recount every real root from a newly constructed complete Sturm chain."""
    own, _, cmp, fw, _ = modules()
    U, A, B, K0, P = polynomial(fw, packet, probe, config)
    square = fw.square_free(P)
    coefficients = fw.coefficient_receipt(square)
    inventory = probe["root_inventory"]
    require(not inventory["deflations"], "unexpected_frozen_rational_root_deflation")
    require(hash_value(coefficients) == inventory["square_free_coefficients"]["sha256"] and
            len(square)-1 == inventory["square_free_coefficients"]["degree"], "square_free_polynomial_changed")
    chain = fw.sturm(square)
    serialized = [fw.coefficient_receipt(x) for x in chain]
    identity = hashlib.sha256(json.dumps(coefficients, sort_keys=True).encode()).hexdigest()
    require(set(inventory["chains"]) == {identity}, "Sturm_chain_inventory_changed")
    stored = inventory["chains"][identity]
    require(stored["polynomial_sha256"] == hash_value(coefficients) and stored["sequence_sha256"] == hash_value(serialized) and
            stored["sequence_degrees"] == [len(x)-1 for x in chain], "complete_Sturm_sequence_changed")
    bound = fw.cauchy_bound(square)
    minus, plus = fw.variations(chain, -bound), fw.variations(chain, bound)
    require(bound == inventory["cauchy_bound"] and minus == inventory["variation_minus_bound"] and
            plus == inventory["variation_plus_bound"] and minus-plus == len(probe["root_brackets"]), "all_real_root_count_changed")
    variations = []
    for row in probe["root_brackets"]:
        lo, hi = F(row["lo"]), F(row["hi"])
        vl, vr = fw.variations(chain, lo), fw.variations(chain, hi)
        require(vl == row["variation_lo"] and vr == row["variation_hi"] and vl-vr == 1 and
                hi-lo <= F(1, 2**probe["refinement_depth"]), "reconstructed_root_bracket_count_changed")
        variations.append([vl, vr])
    def enclosure(value):
        return value.enclosure(gaussian) if isinstance(value, fw.Quadratic) else gaussian.I.point(value)
    ai, bi = tuple(map(enclosure, A)), tuple(map(enclosure, B))
    lam = F(probe["lambda"])
    infinity = enclosure(K0)+(1-lam)/enclosure(A[-1])+lam/enclosure(B[-1])
    values = []
    for root in probe["root_brackets"]:
        q = gaussian.I(F(root["lo"]), F(root["hi"]))
        av, bv = fw.p_value(ai, q), fw.p_value(bi, q)
        require(av.lo > 0 and bv.lo > 0, "fringe_denominator_not_positive")
        values.append(enclosure(K0)+(1-lam)*(1+q.square())/av+lam*(1+q.square())/bv)
    values.append(infinity)
    require(canonical(fw.serial(values)) == canonical(probe["candidate_values"]) and
            canonical(fw.serial(infinity)) == canonical(probe["q_infinity"]), "reconstructed_fringe_values_changed")
    maximum = gaussian.I(max(v.lo for v in values), max(v.hi for v in values))
    minimum = gaussian.I(min(v.lo for v in values), min(v.hi for v in values))
    visibility = (maximum-minimum)/(maximum+minimum)
    require(canonical(fw.serial(visibility)) == canonical(probe["visibility"]), "reconstructed_visibility_changed")
    return {"probe_sha256": hash_value(probe), "derivative_sha256": probe["derivative_polynomial_coefficients"]["sha256"],
            "square_free_sha256": hash_value(coefficients), "Sturm_sequence_sha256": hash_value(serialized),
            "cauchy_bound": bound, "whole_domain_variations": [minus, plus], "real_root_count": minus-plus,
            "root_bracket_variations": variations, "q_infinity_and_all_extrema_reconstructed": True,
            "visibility_reconstructed": True}


def reconstruct_fringes(directory):
    config, _, _, freeze, _, data = inputs(directory)
    _, _, _, fw, _ = modules()
    primary_config, _, _, _, gaussian, _, _ = fw.inputs()
    rows, roots, started = [], 0, time.monotonic()
    for row in data["forward.json"]["points"]:
        probes = primary_calibration(row, config)
        records = []
        for probe in probes:
            record = rebuilt_probe(row["source_parameters"], probe, primary_config, gaussian)
            roots += record["real_root_count"]
            records.append(record)
        rows.append({"point_id": row["point"]["point_id"], "probes": records})
        print("full Sturm replay " + row["point"]["point_id"] + " probes=" + str(len(records)), file=sys.stderr, flush=True)
    require(sum(len(x["probes"]) for x in rows) == 585 and roots == 1170, "full_fringe_coverage_changed")
    print("full Sturm replay seconds=" + str(round(time.monotonic()-started, 3)), file=sys.stderr, flush=True)
    return {"schema": "p23-frame-window-complete-fringe-check/v1", "version": VERSION,
            "executable_freeze": committed(__file__), "criterion_freeze": freeze,
            "primary_intake_sha256": RECEIPTS["forward.json"], "original_first_source_sha256": FIRST_HASHES["primary_source"],
            "scientific_generator_sha256": PROGRAMS["forward.py"], "point_count": 9, "probe_count": 585,
            "real_root_count": roots, "all_sequences_reconstructed": True, "all_real_roots_recounted": True,
            "q_infinity_extrema_visibility_and_lambda_enclosures_verified": True, "records": rows,
            "global_optimum_kernel_proof": False, "retrospective": True, "bell_event_files_read": 0,
            **{flag: False for flag in FLAGS}}


def fringe_certificate(directory, data, *, fresh):
    receipt_path = HERE / "fringe-checks.json"
    frozen = committed(receipt_path)
    require(digest(directory / "fringe-checks.json") == frozen["sha256"], "complete_fringe_receipt_changed")
    receipt = read(directory / "fringe-checks.json")
    scope(receipt)
    require(receipt["schema"] == "p23-frame-window-complete-fringe-check/v1" and
            receipt["primary_intake_sha256"] == RECEIPTS["forward.json"] and
            receipt["original_first_source_sha256"] == FIRST_HASHES["primary_source"] and
            receipt["scientific_generator_sha256"] == PROGRAMS["forward.py"] and
            all(receipt[k] is True for k in ("all_sequences_reconstructed", "all_real_roots_recounted",
                "q_infinity_extrema_visibility_and_lambda_enclosures_verified")) and receipt["global_optimum_kernel_proof"] is False,
            "complete_fringe_scope_changed")
    bound_source(receipt["executable_freeze"])
    count = roots = 0
    config, *_ = modules()[0].configuration()
    require(len(receipt["records"]) == 9 and type(receipt["point_count"]) is int and receipt["point_count"] == 9,
            "complete_fringe_corner_missing")
    for source, record in zip(data["forward.json"]["points"], receipt["records"]):
        probes = primary_calibration(source, config)
        require(record["point_id"] == source["point"]["point_id"] and len(record["probes"]) == len(probes), "complete_fringe_probe_missing")
        for p, r in zip(probes, record["probes"]):
            inv = p["root_inventory"]
            require(r["probe_sha256"] == hash_value(p) and r["derivative_sha256"] == p["derivative_polynomial_coefficients"]["sha256"] and
                    r["square_free_sha256"] == inv["square_free_coefficients"]["sha256"] and
                    r["Sturm_sequence_sha256"] in {x["sequence_sha256"] for x in inv["chains"].values()} and
                    type(r["real_root_count"]) is int and r["real_root_count"] == inv["real_root_count"] and
                    r["whole_domain_variations"] == [inv["variation_minus_bound"], inv["variation_plus_bound"]] and
                    r["root_bracket_variations"] == [[x["variation_lo"], x["variation_hi"]] for x in p["root_brackets"]] and
                    r["q_infinity_and_all_extrema_reconstructed"] is True and r["visibility_reconstructed"] is True,
                    "complete_fringe_reconstruction_binding_changed")
            count += 1
            roots += r["real_root_count"]
    require(type(receipt["probe_count"]) is int and receipt["probe_count"] == count == 585 and
            type(receipt["real_root_count"]) is int and receipt["real_root_count"] == roots == 1170, "complete_fringe_totals_changed")
    if fresh:
        require(canonical(reconstruct_fringes(directory)) == canonical(receipt), "fresh_complete_fringe_reconstruction_changed")
    return frozen, count, roots


def generated_report(directory, *, fresh=False):
    config, counts, confidence, freeze, bindings, data = inputs(directory)
    own, replay, cmp, _, intake = modules()
    inverse_certificate(data["inverse-certification.json"])
    forward, source, primary = (data[x] for x in ("forward.json", "forward-source.json", "replay.json"))
    independent, comparison = data["independent_replay.json"], data["independent-comparison.json"]
    require(forward["schema"] == "p23-frame-window-primary-intake/v1" and forward["scientific_schema"] == "p23-frame-window-primary/v1" and
            source["schema"] == "p23-frame-window-source-snapshot/v1" and primary["schema"] == "p23-frame-window-replay/v1" and
            independent["schema"] == "p23-frame-window-independent-replay/v1", "lookalike_scientific_receipt")
    require(all(type(x) is int and x == 9 for x in (forward["point_count"], source["point_count"], primary["point_count"], independent["box_point_count"])) and
            all(len(x) == 9 for x in (forward["points"], source["points"], primary["points"], independent["box_points"])), "missing_calibration_corner")
    require(primary["global_maximum_kernel_claimed"] is False and independent["global_optimum_kernel_proof"] is False and
            primary["joint_counts_used_to_optimize"] is False and primary["public_CI_used_to_optimize"] is False and
            independent["primary_code_or_results_read_before_first"] is False, "optimization_scope_changed")
    snapshot = intake.source_snapshot(forward)
    snapshot["scientific_schema"] = forward["scientific_schema"]
    require(canonical(snapshot) == canonical(source), "source_snapshot_changed")
    storage = data["storage-intake.json"]
    require(storage["full_scientific_json_sha256"] == forward["derivative_intake"]["full_scientific_json_sha256"] == FIRST_HASHES["primary_source"] and
            storage["compact_sha256"] == RECEIPTS["forward.json"] and storage["source_snapshot_sha256"] == RECEIPTS["forward-source.json"] and
            storage["source_and_probability_values_changed"] is False and storage["first_scientific_json_changed"] is False and
            forward["derivative_intake"]["all_source_calibration_probability_and_root_fields_preserved"] is True and
            forward["derivative_intake"]["intake_is_original_first_scientific_json"] is False and
            len(set(forward["derivative_intake"]["coefficient_fields_omitted"])) == storage["omitted_coefficient_field_count"] == 4095,
            "storage_adapter_changed_science")
    require([(x["point_index"], x["probe_index"]) for x in storage["recompute_checkpoints"]] ==
            [(i, j) for i in range(9) for j in (0, 1)] and all(x["byte_canonical_equal"] is True for x in storage["recompute_checkpoints"]),
            "storage_endpoint_reconstruction_missing")
    require(comparison["verdict"] == "CERTIFIED_NUMERIC_FRAME_REPLAY_AGREEMENT" and comparison["first_receipt_hashes"] == FIRST_HASHES and
            all(comparison[k] is True for k in ("first_receipts_preserved", "source_first_receipts_mutually_blind",
                "optimization_first_receipts_mutually_blind", "comparison_after_both_firsts")) and
            comparison["global_maximum_kernel_claimed"] is False and len(comparison["records"]) == 9 and
            all(x is True for x in comparison["band_agreement"]), "independent_comparison_scope_changed")
    instrument = read((HERE / config["documented_source"]).resolve())
    r_public = F(instrument["preparation"]["amplitudes"]["VV"])/F(instrument["preparation"]["amplitudes"]["HH"])
    printed_angles = list(map(F, instrument["controls"]["alice"]+instrument["controls"]["bob"]))
    tolerance = config["optimization_tolerance"]
    records, independent_probes = [], 0
    for i, (p, f, q, expected, saved) in enumerate(zip(primary["points"], forward["points"], independent["box_points"],
                                                     replay.box_points(config), comparison["records"])):
        packet, lam = source_check(f, q, expected, config, counts)
        require(p["point"] == f["point"] and p["source_parameters"] == f["source_parameters"] and
                p["source_calibration_fields_reoptimized"] is False, "replay_source_not_frozen_member")
        independent_probes += independent_calibration(q, config)
        cells = [own.window(own.pulse(packet, lam, a, b, config["source_pair_cutoff"])[0], config)
                 for a, b in ((F(config["angles_deg"][0]), F(config["angles_deg"][2])),
                              (F(config["angles_deg"][0]), F(config["angles_deg"][3])),
                              (F(config["angles_deg"][1]), F(config["angles_deg"][2])),
                              (F(config["angles_deg"][1]), F(config["angles_deg"][3])))]
        raw = {k: [c[field] for c in cells] for k, field in (("j", "j"), ("sA_cell", "sA"), ("sB_cell", "sB"))}
        for key, values in raw.items():
            require(len(f["public_probabilities"][key]) == len(confidence[key]) == 4, "public_probability_cell_missing")
            for j, v in enumerate(values):
                other, ci = cmp.interval(f["public_probabilities"][key][j]), confidence[key][j]
                require(v.contained(ci["exact_lower"], ci["exact_upper"]) and other.contained(ci["exact_lower"], ci["exact_upper"]) and
                        cmp.overlaps(v, other) and cmp.within(v, other, F(config["implementation_tolerance"])) and
                        f["confidence_inclusion"][key][j] is True and
                        canonical(v.packet()) == canonical(saved["independent_original_probabilities_restored_from_own_first_source"][key][j]),
                        "original_public_probability_or_CI_changed")
        require(f["outcome"] == "EXHIBITED_FRAME_WINDOW_MEMBER" and
                saved["original_probability_restoration_is_post_first"] is True, "member_or_access_history_changed")
        gain = replay.gain_norm(packet)
        require(cmp.overlaps(gain, cmp.interval(q["gain_norm"])) and cmp.overlaps(gain, cmp.interval(p["gain_readout"]["gain_norm"])),
                "fixed_gain_norm_changed")
        pcontrol = list(map(cmp.interval, p["candidate"]["control_box"]))
        require(len(pcontrol) == len(q["control"]) == 5 and pcontrol[0].contained(*config["pump_balance_domain_deg"]), "five_control_actuator_changed")
        pch, _ = cmp.born_box(packet, lam, pcontrol, config)
        qmath = replay.mathematical_point(packet, lam, tuple(q["control"]), gain, config)
        require(cmp.overlaps(pch, cmp.interval(p["candidate"]["CH"])) and cmp.overlaps(qmath["CH"], cmp.interval(q["CH"])) and
                cmp.within(cmp.interval(p["candidate"]["CH"]), cmp.interval(q["CH"]), F(tolerance["CH"])), "actual_model_score_changed")
        pr, qr = cmp.interval(p["five_components"]["r_cond"]), cmp.interval(q["five_components"][0])
        tr = cmp.beta_ratios(gain, pcontrol[0])
        require(cmp.overlaps(pr, (tr[1]/tr[0]).sqrt()) and cmp.overlaps(qr, qmath["r"]) and cmp.within(pr, qr, F(tolerance["r"])),
                "source_ratio_not_from_actual_pump")
        require(all(cmp.within(cmp.interval(a), cmp.interval(b), F(tolerance["angle_deg"]))
                    for a, b in zip(p["five_components"]["angles_deg"], q["five_components"][1:])) and
                all(cmp.overlaps(cmp.interval(a), own.I(F(str(b)))) for a, b in zip(q["five_components"][1:], q["control"][1:])),
                "four_receiver_controls_changed")
        printed_beta = cmp.published_balance(gain, r_public)
        printed_ch, _ = cmp.born_box(packet, lam, [printed_beta, *(own.I(x) for x in printed_angles)], config)
        strict_gain = qmath["CH"]-printed_ch
        require(cmp.overlaps(printed_beta, cmp.interval(p["documented_readout"]["fixed_gain_circle_balance_deg"])) and
                F(p["documented_readout"]["r_public"]) == r_public and list(map(F, p["documented_readout"]["raw_angles_deg"])) == printed_angles and
                cmp.overlaps(printed_ch, cmp.interval(p["documented_readout"]["CH"])) and strict_gain.lo > 0 and
                saved["strict_improvement_over_printed_five_controls"] is True and
                cmp.overlaps(strict_gain, cmp.interval(saved["strict_gain_over_printed_five_controls"])), "printed_five_control_gain_changed")
        source_beta = own.I(F(str(q["original_control"][0])))
        require(not cmp.overlaps(source_beta, printed_beta), "printed_ratio_conflated_with_source_initial_balance")
        records.append({"point_id": expected[0], "source_and_exact_Klyshko_inverse_verified": True,
                        "full_fringe_exact_lambda_source_verified": True, "original_CI_count": 12,
                        "five_controls_and_actual_model_score_verified": True, "printed_five_balance": printed_beta.packet(),
                        "primary_actual_CH": pch.packet(), "independent_actual_CH": qmath["CH"].packet(),
                        "strict_gain_over_full_printed_five_controls": strict_gain.packet()})
    member = data["independent.json"]
    require(member["schema"] == "p23-frame-window-independent/v1" and member["source"] == independent["box_points"][0]["source"] and
            member["outcome"] == "EXHIBITED_FRAME_WINDOW_MEMBER" and all(all(x is True for x in values) for values in member["confidence_inclusion"].values()),
            "independent_first_public_member_changed")
    require(all(x["actual_rotated_amplitudes_agree"] is True and x["Born_trace_recurrence_agrees"] is True
                for x in member["controls"]["actual_R_source_creation_and_Born"]), "actual_R_source_identity_control_failed")
    widths = [F(config["five_component_rounding_half_width_r"])]+[F(config["five_component_rounding_half_width_angle_deg"])]*4
    pvalues = [[cmp.interval(x["five_components"]["r_cond"]), *map(cmp.interval, x["five_components"]["angles_deg"])] for x in primary["points"]]
    qvalues = [list(map(cmp.interval, x["five_components"])) for x in independent["box_points"]]
    pband, qband = [], []
    for j, half in enumerate(widths):
        pband.append(own.I(min(x[j].lo for x in pvalues)-half, max(x[j].hi for x in pvalues)+half))
        qband.append(own.I(min(x[j].lo for x in qvalues)-half, max(x[j].hi for x in qvalues)+half))
        require((pband[-1].lo, pband[-1].hi) == tuple(map(F, primary["five_component_candidate_band"][j])) and
                canonical(qband[-1].packet()) == canonical(independent["band"][j]) and
                cmp.same_bounds(pband[-1], qband[-1], F(tolerance["r"] if j == 0 else tolerance["angle_deg"])), "original_component_band_changed")
    documented = [r_public, *printed_angles]
    inclusion = [box.lo <= v <= box.hi for box, v in zip(qband, documented)]
    require(list(map(F, independent["documented"])) == documented and all(type(x) is bool for x in independent["comparison"]) and
            independent["comparison"] == inclusion and primary["band_status"] == "NUMERICAL_CANDIDATE_BAND", "printed_component_band_decision_changed")
    outcome = "NUMERICAL_BAND_CONTAINS_ALL_PRINTED_COMPONENTS" if all(inclusion) else "NUMERICAL_DEVIATION_EXCEEDS_DECLARED_BAND"
    require(independent["outcome"] == outcome, "numeric_outcome_changed")
    fringe_freeze, probe_count, root_count = fringe_certificate(directory, data, fresh=fresh)
    require(independent_probes == 585, "independent_full_fringe_coverage_changed")
    execution = {name: committed(HERE/name) for name in (*PROGRAMS, "verify.py")}
    report_bindings = {**bindings, **{name: digest(directory/name) for name in (*RECEIPTS, "fringe-checks.json")}}
    return {"schema": SCHEMA, "version": VERSION, "status": "verified", "evidence_valid": True,
            "criterion_freeze": freeze, "first_scientific_receipt_hashes": FIRST_HASHES,
            "execution_source_freezes": execution, "bindings": report_bindings,
            **{name: True for name in REQUIRED}, "global_optimum_kernel_proof": False,
            "numeric_outcome": outcome, "printed_five_component_band_inclusion": inclusion,
            "source_point_count": 9, "original_public_CI_count": 108, "numeric_replay_count_per_implementation": 9,
            "primary_full_fringe_probe_count": probe_count, "primary_real_root_count": root_count,
            "independent_full_fringe_probe_count": independent_probes, "complete_fringe_reconstruction_freeze": fringe_freeze,
            "fringe_intake_mode": "frozen_complete_Sturm_reconstruction_and_rebuilt_all_profile_coefficients",
            "fresh_full_fringe_reconstruction": fresh, "fresh_source_compilation": False,
            "source_calibration_inverse_kernel_scope": data["inverse-certification.json"]["kernel_claims"],
            "source_first_receipts_mutually_blind": True, "optimization_first_receipts_mutually_blind": True,
            "comparison_after_both_firsts": True, "records": records,
            "nominal_optimum_verdict_changed": False, "nine_point_band_replaces_r0003_band": False,
            "retrospective": True, "bell_event_files_read": 0, **{flag: False for flag in FLAGS}}


def assess(report_dir=None, *, enabled=True, fresh=False):
    base = {"schema": SCHEMA, "version": VERSION, "evidence_valid": False, "global_optimum_kernel_proof": False,
            **{name: False for name in REQUIRED}, **{flag: False for flag in FLAGS}}
    if not enabled:
        return {**base, "status": "disabled_by_override"}
    directory = HERE if report_dir is None else Path(report_dir).resolve()
    try:
        stored = read(directory / "verification.json")
        require(stored.get("schema") == SCHEMA and stored.get("version") == VERSION and stored.get("status") == "verified" and
                stored.get("evidence_valid") is True and all(stored.get(k) is True for k in REQUIRED) and
                all(stored.get(k) is False for k in FLAGS) and stored.get("global_optimum_kernel_proof") is False,
                "lookalike_or_nonboolean_verification")
        generated = generated_report(directory, fresh=fresh)
        comparable = {**generated, "fresh_full_fringe_reconstruction": False}
        require(canonical(stored) == canonical(comparable), "stored_verification_differs_from_source_intake")
        return generated
    except FileNotFoundError as error:
        return {**base, "status": "missing_frame_window_evidence", "reason": str(error)}
    except (ValueError, KeyError, TypeError, AttributeError, ArithmeticError, ImportError, OSError, RuntimeError, subprocess.SubprocessError) as error:
        return {**base, "status": "invalid_frame_window_evidence", "reason": str(error)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path)
    parser.add_argument("--disabled", action="store_true")
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--fresh", action="store_true", help="reconstruct every complete Sturm chain and recount every root")
    parser.add_argument("--generate", action="store_true")
    parser.add_argument("--certify-fringe", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    directory = HERE if args.directory is None else args.directory.resolve()
    try:
        if args.certify_fringe:
            result = reconstruct_fringes(directory)
        elif args.generate:
            result = generated_report(directory, fresh=args.fresh)
            # The stored intake describes the complete frozen receipt, independent of this run's refresh mode.
            result["fresh_full_fringe_reconstruction"] = False
        else:
            result = assess(directory, enabled=not args.disabled, fresh=args.fresh)
    except (ValueError, KeyError, TypeError, AttributeError, ArithmeticError, OSError, RuntimeError, subprocess.SubprocessError) as error:
        result = {"schema": SCHEMA, "version": VERSION, "status": "invalid_frame_window_evidence", "evidence_valid": False,
                  "reason": str(error), **{flag: False for flag in FLAGS}}
    text = json.dumps(result, indent=2, allow_nan=False)+"\n"
    if args.output:
        args.output.write_text(text)
    else:
        print(text, end="")
    return 0 if result.get("status") in ("verified", "disabled_by_override") or result.get("all_real_roots_recounted") is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
