#!/usr/bin/env python3
"""Independent checking of calibrated ENV source witnesses and a continuous bound."""
from __future__ import annotations
import argparse
from fractions import Fraction as F
import gzip
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[7]
VERSION = "p23-calibrated-count-cross-ncc-cross0001"
SCHEMA = "p23-calibrated-count-cross/v1"
EVIDENCE_SCHEMA = "public-calibrated-count-evidence/v1"
FIELDS = (("sA_cell", "sA"), ("sB_cell", "sB"), ("j", "j"))
TRUE = ("all_19_source_count_readouts_independently_verified", "public_72_CI_consumed", "continuous_nominal_ENV_domain_single_bound_certified",
        "nominal_continuous_source_domain_rejected", "finite_19_calibrated_ENV_sources_rejected_by_original_CI",
        "public_calibrated_count_review_completed")
FALSE = ("continuous_domain_from_point_scan", "source_search_rerun", "foreign_EF_fields_used", "actual_source_epoch_identified",
         "experimental_or_Born_law_rejected", "calibration_sigma_hard_confidence_bound", "new_continuum_Lean_kernel_claim", "controller_advance",
         "actual_hardware_identity_verified", "source_epoch_identified", "nominal_optimum_contract_replaced")


def require(value, reason):
    if not value:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def frozen(path, commit=None):
    path = Path(path).resolve(); require(path.is_relative_to(ROOT), "foreign_calibrated_audit_path")
    relative = path.relative_to(ROOT).as_posix()
    if commit is None:
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", relative], cwd=ROOT, text=True).strip()
    require(bool(commit), "uncommitted_calibrated_audit:" + relative)
    blob = subprocess.check_output(["git", "show", commit + ":" + relative], cwd=ROOT)
    require(hashlib.sha256(blob).hexdigest() == digest(path), "unfrozen_calibrated_audit:" + relative)
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    return {"path": relative, "commit": commit, "sha256": digest(path)}


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def equal(a, b, reason):
    require(canonical(a) == canonical(b), reason)


def bind_check(rows):
    seen = set()
    for row in rows:
        path = (ROOT / row["path"]).resolve()
        require(path.is_relative_to(ROOT) and row["path"] not in seen, "invalid_duplicate_calibrated_binding")
        seen.add(row["path"])
        require(digest(path) == row["sha256"], "calibrated_bound_source_changed:" + row["path"])


def native():
    name = "calibrated_count_audit_candidate"
    if name in sys.modules:
        return sys.modules[name]
    loader = importlib.util.spec_from_file_location(name, HERE / "review.py")
    module = importlib.util.module_from_spec(loader); sys.modules[name] = module; loader.loader.exec_module(module)
    return module


def configuration():
    text = (HERE / "criterion-cross.md").read_text()
    blocks = re.findall(r"<!-- NCC-CROSS-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- NCC-CROSS-FROZEN-END -->", text, re.S)
    require(len(blocks) == 1, "ambiguous_calibrated_audit_contract")
    config = json.loads(blocks[0]); manifest = json.loads((HERE / "sources-cross.json").read_text())
    require(config["version"] == manifest["version"] == VERSION and config["source_points"] == 19 and
            config["CI_count"] == 72 and config["default_points"] == 17 and config["outcomes_per_source"] == 96 and
            config["pair_cutoff"] == 6 and F(config["adapter_tolerance"]) == F("1e-12") and all(config[key] is False for key in FALSE),
            "calibrated_audit_exact_contract_changed")
    bind_check(manifest["inputs"])
    owned = [frozen(HERE/name) for name in ("criterion-cross.md", "sources-cross.json", "verify.py", "tests_verify.py")]
    return config, manifest, owned


def source_closure(manifest, owned):
    table = {row["path"]: row for row in owned}; queue = list(manifest["inputs"])
    for module in list(sys.modules.values()):
        filename = getattr(module, "__file__", None)
        if filename:
            path = Path(filename).resolve()
            if path.is_relative_to(ROOT) and path.suffix == ".py":
                queue.append({"path": path.relative_to(ROOT).as_posix(), "sha256": digest(path)})
    while queue:
        row = queue.pop(); path = (ROOT/row["path"]).resolve()
        require(path.is_relative_to(ROOT) and digest(path) == row["sha256"], "calibrated_semantic_dependency_changed:" + row["path"])
        if row["path"] in table:
            require(table[row["path"]]["sha256"] == row["sha256"], "conflicting_calibrated_binding"); continue
        table[row["path"]] = frozen(path, row.get("commit"))
        if path.suffix == ".json" and path.stat().st_size < 1000000:
            value = json.loads(path.read_text()); inputs = value.get("inputs", [])
            if isinstance(inputs, list) and all(isinstance(x, dict) and "path" in x and "sha256" in x for x in inputs):
                queue.extend(inputs)
    return [table[key] for key in sorted(table)]


def load_first(path=None):
    metadata = json.loads((HERE / "first-storage.json").read_text())
    candidate = HERE/"first.json.gz" if path is None else Path(path)
    require(digest(candidate) == metadata["stored_sha256"] and candidate.stat().st_size == metadata["stored_bytes"], "unbound_or_lookalike_calibrated_first")
    raw = gzip.decompress(candidate.read_bytes())
    require(hashlib.sha256(raw).hexdigest() == metadata["logical_sha256"] and len(raw) == metadata["logical_bytes"], "calibrated_lossless_first_changed")
    report = json.loads(raw)
    stage = {k: v for k, v in report.items() if k not in ("source_stage_sha256", "runtime_seconds")}
    require(hashlib.sha256(canonical(stage)).hexdigest() == report["source_stage_sha256"] == metadata["source_stage_sha256"], "calibrated_source_stage_changed")
    return report, {"first": frozen(HERE/"first.json.gz"), "storage": frozen(HERE/"first-storage.json"),
                    "logical_sha256": metadata["logical_sha256"]}


def candidate_scope(report, m):
    require(report["schema"] == m.SCHEMA and report["version"] == m.VERSION and report["status"] == "complete" and
            report["source_point_count"] == 19 and report["default_point_count"] == 17 and
            len(report["source_branches"]) == len(report["source_point_inventory"]) == 19,
            "calibrated_candidate_missing_sources_or_wrong_scope")
    require(report["finite_point_rejection_implies_continuum_rejection"] is False and report["bell_event_files_read"] == 0 and
            report["foreign_EF_source_or_fields_used"] is report["r6_optimum_parameters_used_as_forward_inputs"] is
            report["new_general_Born_or_statistical_coverage_kernel_claim"] is False and
            all(report[key] is False for key in m.FALSE_SCOPE), "calibrated_candidate_claim_inflation")


def compare_paths(paths, endpoints):
    certificates, contained, count, outcomes = [], True, 0, 0
    for i, endpoint in enumerate(endpoints):
        require(all(path[i]["endpoint"] == endpoint["id"] and path[i]["N"] == endpoint["N"] and len(path[i]["cells"]) == 4 for path in paths), "source_window_mapping_changed")
        for row in range(4):
            for field, name in FIELDS:
                values = [path[i]["cells"][row][name] for path in paths]
                require(max(v.lo for v in values) <= min(v.hi for v in values), "independent_ENV_source_readouts_disjoint")
                target = endpoint["CI"][field][row]; lo, hi = F(target["exact_lower"]), F(target["exact_upper"])
                contained &= all(lo <= v.lo <= v.hi <= hi for v in values)
                if all(v.hi < lo or hi < v.lo for v in values):
                    certificates.append({"endpoint": endpoint["id"], "N": endpoint["N"], "row": row, "field": field,
                        "original_CI": target, "primary": values[0], "independent": values[1], "actual_Born": values[2]})
                count += 1
            for outcome in range(4):
                values = [path[i]["cells"][row]["outcomes"][outcome] for path in paths]
                require(max(v.lo for v in values) <= min(v.hi for v in values), "independent_ENV_outcomes_disjoint"); outcomes += 1
    require(count == 72 and outcomes == 96, "not_all_calibrated_CI_or_outcomes_checked")
    return {"verdict": "SOURCE_REJECTED_BY_ORIGINAL_CI" if certificates else "ALL_72_CI_CONTAINED" if contained else "CI_OVERLAP_UNRESOLVED",
            "all_72_reads_and_96_outcomes_crossed": True, "all_72_CI_contained": bool(contained), "actual_strict_disjoint_certificates": certificates}


def continuous(spec, endpoints, m):
    tolerance = F(spec["readout_tolerance"]); require(tolerance == F("1e-12"), "wrong_calibration_adapter_tolerance")
    qlo, qhi = F(spec["nominal_pair_input_box"][0])-tolerance, F(spec["nominal_pair_input_box"][1])+tolerance
    ka_hi, kb_lo = F(spec["nominal_K_A_box"][1])+tolerance, F(spec["nominal_K_B_box"][0])-tolerance
    ba, bb = map(F, spec["background_per_pulse"])
    require(0 < qlo <= qhi < 1 and 0 <= ba < 1 and 0 <= bb < 1 and 0 < kb_lo < 1 and ba < ka_hi < 1, "continuous_bound_denominator_or_domain_not_qualified")
    nlo, nhi = qlo/2, qhi/(2*(1-qhi))
    tblo = (kb_lo*(1-ba)/(1+nhi)-bb)/(1+2*nhi)
    require(0 < tblo < 1, "continuous_Bob_transmission_lower_not_physical")
    sblo = bb+(1-bb)*tblo*nlo/(1+tblo*nlo)
    require(bb < sblo < 1, "continuous_herald_denominator_not_positive")
    tahi = (ka_hi-ba)/((1-ba)*(1-bb/sblo))
    require(0 < tahi < 1, "continuous_Alice_upper_not_qualified")
    beta_s, beta_c = m.independent.born.trig(F(spec["reference_beta_deg"]))
    a_s, a_c = m.independent.born.trig(F(spec["published_angles_deg"][0]))
    require(0 < beta_s.lo < beta_s.hi < beta_c.lo and (a_c.square()-a_s.square()).lo > 0, "continuous_population_fraction_order_not_qualified")
    fraction = a_s.square()+beta_s.square()*(a_c.square()-a_s.square())
    population = qhi/(1-qhi)
    upper = (m.independent.I(ba)+(1-ba)*tahi*population*fraction).hi
    primary_beta, _ = m.primary.arithmetic.trig_sin_cos(F(spec["reference_beta_deg"]))
    primary_a, primary_c = m.primary.arithmetic.trig_sin_cos(F(spec["published_angles_deg"][0]))
    second_fraction = primary_a.square()+primary_beta.square()*(primary_c.square()-primary_a.square())
    require(max(fraction.lo, second_fraction.lo) <= min(fraction.hi, second_fraction.hi), "independent_whole_domain_trig_bounds_disjoint")
    second_upper = (m.primary.I(ba)+(1-ba)*tahi*population*second_fraction).hi
    require(0 < upper < 1, "continuous_click_upper_outside_probability_domain")
    transports, witnesses = [], []
    for e in endpoints:
        high = 1-(1-upper)**e["N"]; target = e["CI"]["sA_cell"][0]; lower = F(target["exact_lower"])
        transports.append({"endpoint": e["id"], "N": e["N"], "single_upper": high, "original_CI": target})
        if high < lower:
            witnesses.append({"endpoint": e["id"], "N": e["N"], "row": 0, "field": "sA_cell", "all_nominal_source_upper": high,
                "original_CI_lower": lower, "strict_gap": lower-high, "spacelike_scope": e["spacelike_scope"]})
    original = {"continuous_nominal_ENV_input_domain_rejected": bool(witnesses),
        "input_domain": {"q": [qlo,qhi], "K_A_upper": ka_hi, "K_B_lower": kb_lo}, "balanced_n_domain": [nlo,nhi],
        "transmission_B_lower": tblo, "herald_B_lower": sblo, "transmission_A_upper": tahi,
        "total_reference_mean_upper": population, "V_population_fraction_upper": beta_s.square(),
        "receiver_weighted_fraction": fraction, "single_pulse_click_upper": upper, "all_N_transport": transports,
        "strict_original_CI_witnesses": witnesses, "all_legal_environment_allocations_and_calibration_roots_covered": True,
        "calibration_k1_band_role": "nominal_condition_not_95_percent_coverage",
        "pair_interval_role": "old_self_chosen_nominal_box_not_public_uncertainty", "new_general_Born_kernel_claim": False,
        "more_point_scans_performed": False}
    return original, {"second_native_trig_single_pulse_upper": str(second_upper), "analytic_chain_static_audit_complete": True,
        "bound_independent_of_all_finite_source_points": True, "K_A_herald": "Bob", "K_B_herald": "Alice",
        "reference_q_and_balanced_n_have_distinct_definitions": True, "background_added_per_pulse_before_window": True}


def point_calibration_domain(branch, spec, m):
    source = branch["source"]; src = m.unpack_source(source, "primary")
    balanced = m.primary.drive_source(src["G"], F(45))
    n = balanced["tH"]/(1-balanced["tH"])
    equal(source["n_balanced"], n.packet(), "source_balanced_n_not_same_G_generated")
    equal(source["t_balanced"], balanced["tH"].packet(), "source_balanced_t_not_same_G_generated")
    ua, ub, _, _ = m.primary.allocation(src["c"], src["allocation"])
    xa, xb = m.primary.environment_xi(src["c"], src["allocation"])
    for name, value in (("u_A",ua),("u_B",ub),("xi_A",xa),("xi_B",xb)):
        equal(source[name], value.packet(), "source_owned_allocation_readback_changed:"+name)
    ba, bb = map(F, spec["background_per_pulse"])
    raw = m.primary.raw_matched(n, src["TA"], src["TB"], ba, bb)
    q = m.primary.drive_source(src["G"], F(16))["q"]
    tol = F(spec["readout_tolerance"])
    for name, value in (("K_A", raw["K_A"]), ("K_B", raw["K_B"]), ("pair_probability", q)):
        target = F(branch["input"][name])
        require(target-tol <= value.lo <= value.hi <= target+tol, "full_generated_source_interval_outside_adapter_input_domain:"+name)
    return {"same_G_reference_q": q.packet(), "same_G_balanced_n": n.packet(), "N1_matched_K_A": raw["K_A"].packet(),
        "N1_matched_K_B": raw["K_B"].packet(), "entire_generated_intervals_inside_1e12_adapter_expansion": True}


def verify_first(first_path=None, CI_path=None):
    started = time.monotonic(); config, manifest, owned = configuration(); m = native()
    spec, candidate_bindings = m.configuration()
    _, _, units_primary, _ = m.primary.inputs(); _, _, units_independent = m.independent.load_frozen()
    equal(units_primary["Alice"], {"center_probability":"747/1000", "half_width_probability":"3/1000"}, "Alice_percentage_role_changed")
    equal(units_independent["probability_center"], ["747/1000","189/250"], "independent_percentage_party_role_changed")
    bindings = source_closure(manifest, owned)
    report, first_identity = load_first(first_path); candidate_scope(report,m)
    endpoints = m.load_endpoints(CI_path); equal(report["all_original_72_CI"], endpoints, "calibrated_original_CI_changed")
    points, branches = m.source_inventory(spec)
    require(len(branches) == 19 and len({(b["point_id"],b["root_index"]) for b in branches}) == 19, "calibrated_point_root_inventory_not_complete")
    equal(report["source_point_inventory"], points, "calibrated_source_default_override_inventory_changed")
    equal(report["bindings"], candidate_bindings, "calibrated_candidate_provenance_changed")
    rows, total_disjoint = [], 0
    for branch, saved in zip(branches, report["source_branches"]):
        domain = point_calibration_domain(branch,spec,m)
        a, a_src = m.primary_forward(branch["source"],spec,endpoints)
        b, actual, b_src = m.independent_forward(branch["source"],spec,endpoints)
        comparison = compare_paths([a,b,actual],endpoints)
        expected = m.serialize({**branch, "primary_source":a_src,"independent_source":b_src,"primary_all_windows":a,
            "independent_all_windows":b,"actual_positive_Born_all_windows":actual,"comparison":comparison})
        equal(saved, expected, "calibrated_full_native_source_or_readout_changed:"+branch["point_id"])
        require(comparison["verdict"] == "SOURCE_REJECTED_BY_ORIGINAL_CI", "calibrated_source_not_strictly_excluded")
        probes = b_src["actual_occupation_Born_probes"]
        require(len(probes) == 4 and all(p["prefix_renormalized"] is False and p["Gamma_sector_dimensions"] == list(range(1,8)) and
                p["original_numberMass_tail"] is True and 0 <= p["tail"].lo <= p["tail"].hi < 1 for p in probes), "wrong_original_ENV_Gamma_tail_or_normalization")
        total_disjoint += len(comparison["actual_strict_disjoint_certificates"])
        rows.append({"point_id":branch["point_id"],"root_index":branch["root_index"],"allocation":branch["source"]["allocation"],
            "default":branch["default"],"probabilities_crossed":72,"outcomes_crossed":96,
            "strict_disjoint_features":len(comparison["actual_strict_disjoint_certificates"]),"calibration_adapter_domain":domain})
        print(json.dumps({"calibrated_cross_source_checked":branch["point_id"],"strict_features":rows[-1]["strict_disjoint_features"]}),flush=True)
    continuous_bound, math_audit = continuous(spec,endpoints,m)
    equal(report["continuum_single_certificate"],m.serialize(continuous_bound),"continuous_whole_domain_bound_changed")
    require([w["endpoint"] for w in continuous_bound["strict_original_CI_witnesses"]] == ["full_N3","full_N5","full_N7","full_N9","old_stop_N5"], "continuous_domain_strict_witnesses_not_complete")
    require(report["all_19_sources_rejected_by_original_CI"] is True,"calibrated_finite_verdict_changed")
    bind_check(bindings)
    return {"schema":SCHEMA,"version":VERSION,"evidence_valid":True,"bindings":bindings,"first_identity":first_identity,
        "source_points_checked":19,"default_points_checked":17,"probabilities_crossed":1368,"path_probability_reads":4104,
        "outcomes_crossed":1824,"native_Gamma_Fock_settings_regenerated":76,"strict_disjoint_features":total_disjoint,
        "source_rows":rows,"continuous_nominal_domain":m.serialize(continuous_bound),"analytic_audit":math_audit,
        "units_primary":units_primary,"units_independent":units_independent,
        **{key:True for key in TRUE},**{key:False for key in FALSE},"bell_event_files_read":0,"retrospective":True,
        "runtime_seconds":time.monotonic()-started}


def summary_check(report):
    require(report["schema"] == SCHEMA and report["version"] == VERSION and report["evidence_valid"] is True and
            all(report[key] is True for key in TRUE) and all(report[key] is False for key in FALSE) and
            report["source_points_checked"] == 19 and report["default_points_checked"] == 17 and
            report["probabilities_crossed"] == 1368 and report["path_probability_reads"] == 4104 and
            report["outcomes_crossed"] == 1824 and report["native_Gamma_Fock_settings_regenerated"] == 76 and
            len(report["source_rows"]) == 19 and all(r["strict_disjoint_features"] > 0 for r in report["source_rows"]) and
            report["analytic_audit"]["bound_independent_of_all_finite_source_points"] is True and
            report["analytic_audit"]["analytic_chain_static_audit_complete"] is True and report["bell_event_files_read"] == 0,
            "calibrated_evidence_exact_claim_or_coverage_changed")
    require(report["continuous_nominal_domain"]["continuous_nominal_ENV_input_domain_rejected"] is True and
            [w["endpoint"] for w in report["continuous_nominal_domain"]["strict_original_CI_witnesses"]] ==
            ["full_N3","full_N5","full_N7","full_N9","old_stop_N5"],"missing_continuous_domain_exact_CI_witnesses")


def consume(certpath=None, disabled=False):
    result = {"schema":EVIDENCE_SCHEMA,"evidence_valid":False,"disabled":disabled,
              **{key:False for key in TRUE+FALSE},"bell_event_files_read":0}
    if disabled:
        result["reason"] = "explicitly_disabled"; return result
    try:
        path = HERE/"verification.json"; identity = frozen(path)
        candidate = path if certpath is None else Path(certpath)
        require(digest(candidate) == identity["sha256"],"unbound_or_lookalike_calibrated_certificate")
        report = json.loads(candidate.read_text()); summary_check(report); bind_check(report["bindings"])
        result.update(evidence_valid=True,certificate=identity,reason="nominal_ENV_finite_and_complete_continuous_count_review_certified",
            source_points_checked=19,probabilities_crossed=1368,outcomes_crossed=1824,
            continuous_nominal_domain=report["continuous_nominal_domain"],analytic_audit=report["analytic_audit"],
            **{key:True for key in TRUE},retrospective=True,no_inverse_optimization_source_search_or_native_recomputation=True)
    except (ValueError,OSError,KeyError,TypeError,ImportError,subprocess.CalledProcessError) as error:
        result.update(reason=str(error),exception_kind=type(error).__name__)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path);parser.add_argument("--check-only",action="store_true")
    parser.add_argument("--certificate",type=Path);parser.add_argument("--disabled",action="store_true")
    args=parser.parse_args()
    if args.check_only:
        result=consume(args.certificate,args.disabled);print(json.dumps(result,sort_keys=True))
        return 0 if result["evidence_valid"] or args.disabled else 1
    require(args.output is not None and not args.output.exists(),"new_calibrated_verification_output_required")
    report=verify_first();summary_check(report);args.output.write_text(json.dumps(report,indent=2,sort_keys=True,allow_nan=False)+"\n")
    print(json.dumps({"output":str(args.output),"sha256":digest(args.output),"sources_checked":19,"probabilities_crossed":1368,"runtime_seconds":report["runtime_seconds"]}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
