#!/usr/bin/env python3
"""Concrete opposite CH signs inside the same original public-CI source fibre."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import gc
import hashlib
import json
from pathlib import Path
import subprocess
import time

import verify_all_data as base

HERE = Path(__file__).resolve().parent
ROOT = base.ROOT
VERSION = "p23-all-data-CH-sign-ambiguity-ef0003.1"
SCHEMA = "p23-all-data-CH-sign-ambiguity-certificate/v1"
DEFAULT_RECEIPT = HERE / "all-data-sign-certification.json"
BASE_SHA = "ce4ea2155413e8a5fb3a3c9decb925c7a10fd852701f335840c3c5027b414924"
FALSE_SCOPE = base.FALSE_SCOPE


def ch_value(born):
    cells = [base.restore_ind(cell) for cell in born["cells"]]
    return (cells[0]["j"] + cells[1]["j"] + cells[2]["j"] - cells[3]["j"] -
            cells[0]["sA"] - cells[0]["sB"])


def strict_sign(value):
    lo, hi = base.bounds(value)
    return "positive" if lo > 0 else "negative" if hi < 0 else "unresolved"


def reconstructed_member(kind, number, member, config, original, selected):
    const = base.ind.constants(config)
    recipe = member["recipe"]
    I = base.primary.context()["I"]
    if kind == "primary":
        native = list(map(base.as_primary, recipe["inverse_single_means"]))
        loss, phase = base.as_primary(recipe["loss"]), base.as_primary(recipe["phase_amplitude"])
        base.require(len(native) == 4 and loss.lo == loss.hi and phase.lo == phase.hi, "nonpoint_CH_member_recipe")
        raw = [1 - ((1 - bg) / (1 + mean.lo)) ** 5 for mean, bg in zip(native, const["background"] * 2)]
        e, k = loss.lo, phase.lo
        saved = member["actual_positive_Fock"]["readout"]
        saved_source = member["actual_positive_Fock"]["source"]
    else:
        base.require(recipe["coordinate_space"] == "original_single_probability_CI_intersections" and
                     member["id"] == number, "wrong_CH_native_member_identity")
        raw = list(map(F, recipe["single_probability_coordinates"]))
        e, k = F(recipe["loss"]), F(recipe["rational_common_k"])
        native = [base.primary.inverse_single(I.point(point), bg) for point, bg in zip(raw, const["background"] * 2)]
        saved = member["actual_positive_Fock_readout"]
        saved_source = member["source"]
    shape, reconstruction = base.ind.member_shape(raw, config, const)
    source = base.ind.physical_source(shape + [base.ind.I(e)], base.ind.I(k))
    born = base.ind.serial(base.ind.fock_readout(source, const, 6))
    base.same(saved_source, source, "foreign_CH_source_not_native")
    base.same(saved, born, "foreign_CH_readout_not_native")
    base.qualified_born(born, original)
    psource = base.primary.covariance(native + [I.point(e)])
    base.require(psource is not None, "CH_member_primary_source_not_physical")
    cells = base.primary.coefficients(psource)
    base.require(cells is not None, "CH_member_primary_geometry_undefined")
    gaussian = base.primary.pack([base.primary.window_readout(cell, I.point(k)) for cell in cells])
    base.cross_cells(gaussian, born["cells"], F(config["comparison_tolerance"]))
    for first, second, field in base.LOCAL_PAIRS:
        base.require(base.intersects(born["cells"][first][field], born["cells"][second][field]), "CH_source_no_signaling_cross_failed")
    CH = base.ind.serial(ch_value(born))
    return {"implementation": kind, "member": number, "native_recipe": recipe,
            "source": base.source_summary(source), "actual_positive_Fock": born, "Gaussian": gaussian,
            "actual_positive_Fock_CH_N5": CH, "strict_sign": strict_sign(CH),
            "all_twelve_original_exact_CI_verified": True, "physical_bounds_verified": True,
            "all_16_outcomes_crossed": True, "shared_phase_no_signaling_crossed": True,
            "foreign_source_fields_used_as_forward_inputs": False}


def selected_signs(kind, receipt):
    members = receipt["members"] if kind == "primary" else receipt["source_stage"]["members"]
    found = {}
    for number, member in enumerate(members):
        saved = member["actual_positive_Fock"]["readout"] if kind == "primary" else member["actual_positive_Fock_readout"]
        sign = strict_sign(base.ind.serial(ch_value(saved)))
        if sign in ("positive", "negative") and sign not in found:
            found[sign] = (number, member)
    base.require(set(found) == {"positive", "negative"}, "no_concrete_opposite_CH_candidates")
    return found


def verify():
    start = time.monotonic()
    execution = [base.frozen(HERE / name) for name in
                 ("criterion-all-data-signs.md", "sources-all-data-signs.json", "all_data_signs.py", "test_all_data_signs.py")]
    manifest = base.read_json(HERE / "sources-all-data-signs.json")
    base.require(manifest["version"] == VERSION and manifest["base_certificate_sha256"] == BASE_SHA, "wrong_CH_sign_source_contract")
    base.check_bindings(manifest["inputs"])
    certified = base.consume()
    base.require(certified["evidence_valid"] is True and certified["certificate"]["sha256"] == BASE_SHA,
                 "unqualified_complete_all_data_fibre_certificate")
    config, _, _ = base.independent.configuration()
    _, original, selected, provenance = base.public_domain(
        (HERE.parent.parent / "observable-prediction/public-comparison-po0003.json").read_text(), config)
    witnesses, firsts = {}, {}
    for kind in ("primary", "independent"):
        receipt, firsts[kind] = base.load_first(kind)
        found = selected_signs(kind, receipt)
        witnesses[kind] = {}
        for sign in ("positive", "negative"):
            number, member = found[sign]
            proof = reconstructed_member(kind, number, member, config, original, selected)
            base.require(proof["strict_sign"] == sign, "selected_CH_sign_not_reconstructed")
            witnesses[kind][sign] = proof
        del found, receipt
        gc.collect()
    result = {"schema": SCHEMA, "version": VERSION, "status": "certified", "statistical_role": base.ROLE,
              "evidence_valid": True, "readout_certified": True, "complete_public_CI_fibre_opposite_CH_signs_verified": True,
              "uniform_CH_N5_strictly_positive_refuted": True, "uniform_CH_N5_strictly_negative_refuted": True,
              "uniform_CH_N5_strictly_positive": False, "uniform_CH_N5_strictly_negative": False,
              "uniform_CH_N5_sign": "mixed_certified", "original_NIST_experiment_statistical_rejection_claimed": False,
              "retrospective": True, **{key: False for key in FALSE_SCOPE}, "bell_event_files_read": 0,
              "foreign_source_fields_used_as_forward_inputs": False,
              "base_certificate": certified["certificate"], "source_bindings": manifest["inputs"],
              "execution_bindings": execution, "firsts": firsts, "original_twelve_CI": original,
              "single_CI_intersections": provenance, "concrete_CH_sign_witnesses": witnesses,
              "full_tree_recomputed_again": False, "source_and_epoch_identifiability_paid": False,
              "runtime_seconds": time.monotonic() - start}
    validate_result(result)
    return result


def validate_result(result):
    base.require(result.get("schema") == SCHEMA and result.get("version") == VERSION and result.get("status") == "certified" and
                 result.get("statistical_role") == base.ROLE, "wrong_CH_sign_certificate_kind")
    base.require(all(result.get(key) is True for key in ("evidence_valid", "readout_certified",
        "complete_public_CI_fibre_opposite_CH_signs_verified", "uniform_CH_N5_strictly_positive_refuted",
        "uniform_CH_N5_strictly_negative_refuted")) and result.get("uniform_CH_N5_sign") == "mixed_certified" and
        result.get("uniform_CH_N5_strictly_positive") is False and result.get("uniform_CH_N5_strictly_negative") is False,
        "inconsistent_concrete_CH_sign_certificate")
    base.require(all(result.get(key) is False for key in FALSE_SCOPE) and result.get("retrospective") is True and
                 result.get("original_NIST_experiment_statistical_rejection_claimed") is False and
                 result.get("foreign_source_fields_used_as_forward_inputs") is False and
                 result.get("source_and_epoch_identifiability_paid") is False and
                 type(result.get("bell_event_files_read")) is int and result["bell_event_files_read"] == 0,
                 "inflated_CH_sign_certificate_scope")
    base.require(result["base_certificate"]["sha256"] == BASE_SHA, "wrong_CH_base_certificate_identity")
    witnesses = result["concrete_CH_sign_witnesses"]
    base.require(set(witnesses) == {"primary", "independent"}, "missing_CH_implementation_witness")
    for family in witnesses.values():
        base.require(set(family) == {"positive", "negative"}, "missing_CH_sign_witness")
        for sign, witness in family.items():
            base.require(witness["strict_sign"] == sign and strict_sign(witness["actual_positive_Fock_CH_N5"]) == sign and
                         witness["all_twelve_original_exact_CI_verified"] is True and witness["physical_bounds_verified"] is True,
                         "unsupported_concrete_CH_sign_witness")
    base.require("source_overrides" not in result and "force_pass" not in result, "CH_scientific_source_override_forbidden")
    return True


def consume(certificate_path=None, disabled=False):
    base.require(type(disabled) is bool, "disable_must_be_boolean")
    if disabled:
        return base.consume(disabled=True)
    certified = base.consume()
    if not certified.get("evidence_valid"):
        return certified
    try:
        canonical = base.frozen(DEFAULT_RECEIPT)
        path = DEFAULT_RECEIPT if certificate_path is None else Path(certificate_path)
        base.require(base.sha(path.read_bytes()) == canonical["sha256"], "unfrozen_or_lookalike_CH_sign_certificate")
        result = base.read_json(path)
        validate_result(result)
        base.check_bindings(result["source_bindings"] + result["execution_bindings"])
        base.require(certified["certificate"]["sha256"] == result["base_certificate"]["sha256"], "changed_CH_base_certificate")
        return {**certified, "uniform_CH_N5_sign": "mixed_certified", "uniform_CH_N5_strictly_positive": False,
                "uniform_CH_N5_strictly_negative": False, "uniform_CH_N5_strictly_positive_refuted": True,
                "uniform_CH_N5_strictly_negative_refuted": True,
                "complete_public_CI_fibre_opposite_CH_signs_verified": True, "sign_certificate": canonical,
                "reason": "certified_complete_public_CI_fibre_with_concrete_opposite_CH_signs"}
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as error:
        return {"evidence_valid": False, "production_eligible": False, "readout_certified": False, "reason": str(error)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    parser.add_argument("--disabled", action="store_true")
    args = parser.parse_args()
    if args.check_only:
        base.require(args.output is None, "check_only_does_not_create_sign_science")
        result = consume(args.certificate, args.disabled)
        print(json.dumps(result, sort_keys=True))
        return 0 if result["evidence_valid"] else 1
    base.require(args.output is not None and args.certificate is None and not args.disabled, "fresh_CH_sign_verification_requires_output")
    base.require(not args.output.exists(), "protected_existing_CH_sign_certificate")
    result = verify()
    args.output.write_text(json.dumps(result, sort_keys=True, indent=2, allow_nan=False) + "\n")
    print(json.dumps({"output": str(args.output), "status": result["status"], "uniform_CH_N5_sign": result["uniform_CH_N5_sign"],
                      "runtime_seconds": result["runtime_seconds"]}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
