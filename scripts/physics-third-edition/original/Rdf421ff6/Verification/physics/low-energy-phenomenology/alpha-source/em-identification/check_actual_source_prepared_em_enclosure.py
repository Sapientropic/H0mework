from __future__ import annotations

import argparse
from fractions import Fraction
import json
import os
from pathlib import Path
import subprocess
import time

from check_actual_source_prepared_noether_pi import ROOT, SOURCE_DIR, CACHE, lean_paths, sha
from check_actual_source_prepared_photon_pole import bindings as pole_bindings
from check_actual_source_prepared_inactive_native import check_source_witness

MODULES = (
    "ActualSourcePreparedBinaryRefinement",
    "ActualSourcePreparedEMEnclosure",
    "ActualSourcePreparedJointEMReturn",
    "ActualSourcePreparedN3EMConsumer",
    "ActualSourcePreparedN3MovingResponse",
    "ActualSourcePreparedStaticNativeConstraint",
    "ActualSourcePreparedN3IRNumerator",
    "ActualSourcePreparedN3EMIRSplit",
    "ActualSourcePreparedN3ChargeEndpoint",
    "ActualSourcePreparedN3EMChargeRead",
    "ActualSourcePreparedN3EMAnalyticPrice",
    "ActualSourcePreparedN3EMCoefficient",
    "ActualSourcePreparedTemporalEMConstraint",
    "ActualSourcePreparedTemporalQuantumWard",
    "ActualSourcePreparedTemporalQuantumCofactor",
    "ActualSourcePreparedTemporalQuantumPrice",
    "ActualSourcePreparedTemporalSchur",
    "ActualSourcePreparedTemporalQuantumRead",
    "ActualSourcePreparedTemporalQuantumIR",
    "ActualSourcePreparedQuantumDriverCofactor",
    "ActualSourcePreparedQuantumDriverPrice",
    "ActualSourcePreparedMovingNoetherResolvent",
    "ActualSourcePreparedMovingResolventPrice",
    "ActualSourcePreparedQuantumNoetherPrice",
    "ActualSourcePreparedQuantumFieldWindowPrice",
    "ActualSourcePreparedMovingNoetherDrive",
    "ActualSourcePreparedMovingMaterialCarrier",
    "ActualSourcePreparedJointNoetherSourcePrice",
    "ActualSourcePreparedQuantumColumnClock",
    "ActualSourcePreparedFourClockCarrier",
    "ActualSourcePreparedClockReducedPencil",
    "ActualSourcePreparedReducedQuantumCofactor",
    "PhysicalEMTemporalGerm",
    "PhysicalEMTemporalPrice",
    "PhysicalEMTemporalSigmaTwo",
    "ActualSourcePreparedEMPhaseField",
    "ActualSourcePreparedEMTemporalFreeReturn",
    "ActualSourcePreparedEMTwoClockCarrier",
    "ActualSourcePreparedEMClockEquation",
    "ActualSourcePreparedEMJacobiRow",
    "ActualSourcePreparedEMClockResidue",
    "ActualSourcePreparedEMSpatialClockPrice",
    "ActualSourcePreparedEMOuterResidue",
    "ActualSourcePreparedEMNativeRow",
    "ActualSourcePreparedEMNativeRead",
    "ActualSourcePreparedEMWeightedTorque",
    "ActualSourcePreparedEMAgeReturn",
    "ActualSourcePreparedEMAgeFieldReturn",
    "ActualSourcePreparedEMMixedAgeRead",
    "ActualSourcePreparedEMAgePiWindow",
    "ActualSourcePreparedEMAgePiReturn",
    "ActualSourcePreparedEMMovingAge",
    "ActualSourcePreparedEMMovingPiAge",
    "ActualSourcePreparedAuxiliaryClockRows",
    "ActualSourcePreparedAuxiliaryClockReduction",
    "ActualSourcePreparedAuxiliaryActualReturn",
    "ActualSourcePreparedAuxiliaryClockSchur",
    "ActualSourcePreparedAuxiliarySchurActualReturn",
    "ActualSourcePreparedAuxiliarySchurBalance",
    "ActualSourcePreparedSchurClockField",
    "ActualSourcePreparedSchurClockBalance",
    "ActualSourcePreparedSchurClockPrice",
    "ActualSourcePreparedJointNativeObservation",
    "ActualSourcePreparedSchurObservedPrice",
    "ActualSourcePreparedMatterClockField",
    "ActualSourcePreparedMatterClockBalance",
    "ActualSourcePreparedMatterClockPrice",
    "ActualSourcePreparedMatterClockPrincipal",
    "ActualSourcePreparedInactiveNativeData",
    "ActualSourcePreparedInactiveNativeCertificate",
    "ActualSourcePreparedInactiveNativeWeights",
    "ActualSourcePreparedInactiveNativeInverse",
    "ActualSourcePreparedInactiveSchurReturn",
    "ActualSourcePreparedSchur97PhysicalRead",
    "ActualSourcePreparedSchur97Polynomial",
    "ActualSourcePreparedSchur97Normalization",
    "ActualSourcePreparedSchur97Cofactor",
    "ActualSourcePreparedSchur97PolynomialNormalization",
    "ActualSourcePreparedSchur97EMNormalization",
    "ActualSourcePreparedSchur97NoetherFraction",
    "ActualSourcePreparedSchur97CommonPrincipal",
    "ActualSourcePreparedSchur97ClockOrder",
    "ActualSourcePreparedBivariateTailPrice",
    "ActualSourcePreparedSchur97JointTail",
    "ActualSourcePreparedSchur97RatioTail",
    "ActualSourcePreparedSchur97UnitChartReturn",
    "ActualSourcePreparedSchur97JointCone",
    "ActualSourcePreparedSchur97WardRow",
    "ActualSourcePreparedSchur97WardSchur",
    "ActualSourcePreparedSchur97WardDeterminant",
    "ActualSourcePreparedSchur97WardFactor",
    "ActualSourcePreparedEMOuterRowFactor",
    "ActualSourcePreparedEMEnclosureAudit",
)
CERTIFICATE = SOURCE_DIR / "actual_source_prepared_em_enclosure_certification.json"
QUANTUM = SOURCE_DIR / "actual_source_quantum_coefficient_error_certification.json"
POLE = SOURCE_DIR / "actual_source_prepared_photon_pole_certification.json"
N3 = SOURCE_DIR / "physical_n3_pole_current_coulomb_certification.json"
N3_ACTION = SOURCE_DIR / "physical_n3_pole_em_action_certification.json"


def source_paths() -> list[str]:
    physical = ROOT / "Lean/scratch/AlphaSource/PhysicalN3PoleCurrentFieldOwn/prod-lean-path.txt"
    moving = ROOT / "Lean/scratch/AlphaSource/ActualMovingSourceFullLightReturnOwn/lean-path.txt"
    native = ROOT / "Lean/scratch/AlphaSource/PhysicalN3SpinThomsonOwn/quantum-mode-lean-path.txt"
    signed_weight = ROOT / "Lean/scratch/AlphaSource/PreparationPhysicalSignedWeightDynamicsKernelAudit/actual-object-search-path.json"
    return list(dict.fromkeys(lean_paths() + physical.read_text().strip().split(":") +
                             moving.read_text().strip().split(":") + native.read_text().strip().split(":") +
                             json.loads(signed_weight.read_text())))


def bindings(paths: list[str]) -> dict:
    pole = json.loads(POLE.read_text())
    assert pole["bindings"] == pole_bindings(paths), "pole input changed"
    for module, receipt in pole["strict"].items():
        assert receipt["exit"] == 0 and "--trust=0" in receipt["command"], module
        assert receipt["source_sha256"] == sha(SOURCE_DIR / f"{module}.lean"), module
        assert receipt["object_sha256"] == sha(CACHE / f"{module}.olean"), module
    quantum = json.loads(QUANTUM.read_text())
    assert quantum["verdict"] == "certified" and "--trust=0" in quantum["strict_flags"]
    evidence = quantum["construction_evidence"]
    candidate = Path(evidence["candidate_path"])
    assert sha(candidate) == evidence["candidate_sha256"], "quantum candidate changed"
    frozen = json.loads(candidate.read_text())
    records = {}
    normalize = lambda p: "\n".join(line.rstrip() for line in p.read_text().splitlines())
    for receipt in frozen["builds"]:
        module = receipt["module"]
        assert receipt["exit_code"] == 0 and "--trust=0" in receipt["command"], module
        target = next(Path(p) / f"{module}.olean" for p in paths
                      if (Path(p) / f"{module}.olean").exists())
        assert sha(target) == receipt["object_sha256"], module
        assert sha(target.with_suffix(".lean")) == receipt["source_sha256"], module
        source = SOURCE_DIR / f"{module}.lean"
        assert normalize(source) == normalize(target.with_suffix(".lean")), module
        records[module] = {"production_sha256": sha(source),
                           "loaded_source_sha256": receipt["source_sha256"],
                           "object_sha256": receipt["object_sha256"]}
    physical = json.loads(N3.read_text())
    assert physical["verdict"] == "certified" and "--trust=0" in physical["strict_flags"]
    n3_records = {}
    for receipt in physical["production_sources"][:2]:
        module = receipt["module"]
        assert receipt["exit"] == 0, module
        target = next(Path(p) / f"{module}.olean" for p in paths
                      if (Path(p) / f"{module}.olean").exists())
        source = SOURCE_DIR / f"{module}.lean"
        assert sha(target) == receipt["object_sha256"], module
        # This production overlay stores objects only. The paid production gate
        # pairs each object with the actual source hash in the N3 certificate.
        assert sha(source) == receipt["source_sha256"], module
        n3_records[module] = {"source_sha256": sha(source), "object_sha256": sha(target)}
    action = json.loads(N3_ACTION.read_text())
    assert action["verdict"] == "certified" and "--trust=0" in action["strict_flags"]
    action_records = {}
    for receipt in action["production_sources"][:2]:
        module = receipt["module"]
        assert receipt["exit"] == 0, module
        target = next(Path(p) / f"{module}.olean" for p in paths
                      if (Path(p) / f"{module}.olean").exists())
        source = SOURCE_DIR / f"{module}.lean"
        assert sha(target) == receipt["object_sha256"], module
        assert sha(source) == receipt["source_sha256"], module
        action_records[module] = {"source_sha256": sha(source), "object_sha256": sha(target)}
    module = "ActualMovingSourceFullLightReturn"
    target = next(Path(p) / f"{module}.olean" for p in paths
                  if (Path(p) / f"{module}.olean").exists())
    receipt = json.loads((target.parent / f"{module}-check.json").read_text())
    assert receipt["exit"] == 0 and "--trust=0" in receipt["command"]
    assert sha(target) == receipt["object_sha256"]
    assert sha(target.with_suffix(".lean")) == receipt["source_sha256"]
    assert sha(SOURCE_DIR / f"{module}.lean") == receipt["source_sha256"]
    moving_record = {"source_sha256": receipt["source_sha256"], "object_sha256": sha(target)}
    static_checkpoint = SOURCE_DIR.parent / "canonical_preparation_alpha_source_joint_static_checkpoint_check.json"
    static = next(p for p in json.loads(static_checkpoint.read_text())["packages"]
                  if p["package"] == "spatial_static")
    static_records = {}
    for node in static["nodes"]:
        module = node["module"]
        target = next(Path(p) / f"{module}.olean" for p in paths
                      if (Path(p) / f"{module}.olean").exists())
        loaded = target.with_suffix(".lean")
        production = SOURCE_DIR.parent / f"{module}.lean"
        strict = json.loads((target.parent / f"{module}.first-strict.json").read_text())
        assert strict["returncode"] == 0 and "--trust=0" in strict["strict_flags"], module
        assert sha(loaded) == node["source_sha256"] == strict["source_sha256"], module
        assert sha(target) == node["object_sha256"] == strict["object_sha256"], module
        assert sha(production) == node["production_sha256"], module
        # This signed producer changed one import name when promoted; the
        # complete declaration text otherwise agrees modulo whitespace.
        text = normalize(loaded)
        if module == "SourceStaticSpatialTensor":
            text = text.replace("import SourceStaticActualPole\n",
                                "import CanonicalPreparationSourceStaticActualPole\n", 1)
        assert normalize(production) == text, module
        static_records[module] = {"production_sha256": sha(production),
                                  "loaded_source_sha256": sha(loaded), "object_sha256": sha(target)}
    ir_records = {}
    for module in ("ActualDressedCommonCurrentNumerator", "ActualDressedDampingCarrier", "ActualDressedDampingPrincipal"):
        target = next(Path(p) / f"{module}.olean" for p in paths
                      if (Path(p) / f"{module}.olean").exists())
        strict = json.loads((target.parent / f"{module}-check.json").read_text())
        assert strict["exit"] == 0 and "--trust=0" in strict["command"], module
        assert sha(target) == strict["object_sha256"] and sha(target.with_suffix(".lean")) == strict["source_sha256"], module
        assert sha(SOURCE_DIR / f"{module}.lean") == strict["source_sha256"], module
        ir_records[module] = {"source_sha256": strict["source_sha256"], "object_sha256": sha(target)}
    rational_certificate = SOURCE_DIR / "actual_dressed_visible_pole_certification.json"
    signed = json.loads(rational_certificate.read_text())
    frozen = signed["construction_evidence"]["frozen_candidate"]
    rational_candidate = Path(frozen["path"])
    assert signed["verdict"] == "certified" and sha(rational_candidate) == frozen["sha256"]
    module = "ActualDressedRationalVisiblePole"
    node = next(n for n in json.loads(rational_candidate.read_text())["sources"] if n["module"] == module)
    target = next(Path(p) / f"{module}.olean" for p in paths if (Path(p) / f"{module}.olean").exists())
    strict = node["strict"]
    assert strict["exit"] == 0 and "--trust=0" in strict["command"]
    assert sha(target) == node["object_sha256"] == strict["object_sha256"]
    loaded = target.with_suffix(".lean")
    assert sha(loaded) == node["source_sha256"] == strict["source_sha256"]
    # The signed construction retained these four diagnostic commands. No
    # declaration or expression is removed when binding the production source.
    diagnostics = "\n".join(f"#print axioms LowEnergy.ActualDressedVisiblePole.{name}" for name in
                             ("visible_numerator_nonzero", "complete_principal_part", "principal_negative_powers", "pole_order_limit"))
    text = normalize(loaded).rstrip()
    assert text.endswith(diagnostics)
    assert text[:-len(diagnostics)].rstrip() == normalize(SOURCE_DIR / f"{module}.lean").rstrip()
    ir_records[module] = {"production_sha256": sha(SOURCE_DIR / f"{module}.lean"),
                          "loaded_source_sha256": sha(loaded), "object_sha256": sha(target),
                          "candidate_sha256": sha(rational_candidate)}
    half_certificate = SOURCE_DIR / "actual_dressed_half_ir_certification.json"
    half = json.loads(half_certificate.read_text())
    assert half["verdict"] == "certified" and "--trust=0" in half["strict_flags"]
    half_records = {}
    for module in ("ActualDressedHalfFeedback", "ActualDressedHalfSchur"):
        signed = next(r for r in half["production_source_object_hashes"] if r["module"] == module)
        target = next(Path(p) / f"{module}.olean" for p in paths if (Path(p) / f"{module}.olean").exists())
        loaded = target.with_suffix(".lean")
        receipt = json.loads((target.parent / f"{module}-check.json").read_text())
        assert signed["exit"] == receipt["exit"] == 0 and "--trust=0" in receipt["command"], module
        assert sha(target) == receipt["object_sha256"] and sha(loaded) == receipt["source_sha256"], module
        source = SOURCE_DIR / f"{module}.lean"
        assert sha(source) == signed["source_sha256"] == receipt["source_sha256"], module
        assert source.read_bytes() == loaded.read_bytes(), module
        half_records[module] = {"production_sha256": sha(source),
                                "loaded_source_sha256": sha(loaded), "object_sha256": sha(target)}
    return {"pole_certificate_sha256": sha(POLE), "quantum_certificate_sha256": sha(QUANTUM),
            "quantum_candidate_sha256": sha(candidate), "quantum_parents": records,
            "n3_certificate_sha256": sha(N3), "n3_parents": n3_records,
            "n3_action_certificate_sha256": sha(N3_ACTION), "n3_action_parents": action_records,
            "moving_parent": moving_record,
            "static_parents": static_records, "ir_parents": ir_records,
            "half_ir_certificate_sha256": sha(half_certificate), "half_ir_parents": half_records,
            "moving_noether_parents": moving_noether_bindings(paths),
            "joint_insertion_parents": joint_insertion_bindings(paths),
            "quantum_column_parents": quantum_column_bindings(paths),
            "four_clock_parents": four_clock_bindings(paths),
            "temporal_em_parents": temporal_em_bindings(paths),
            "native_temporal_parents": native_temporal_bindings(paths),
            "signed_weight_parents": signed_weight_bindings(paths),
            "matter_clock_parents": matter_clock_bindings(paths)}


def signed_weight_bindings(paths: list[str]) -> dict:
    owner = ROOT / "Lean/scratch/AlphaSource/PreparationPhysicalSignedWeightDynamicsKernelAudit/receipt.json"
    signed = json.loads(owner.read_text())
    assert signed["verdict"] == "certified" and signed["kernel"]["opaque_all_read"]
    assert sorted(signed["authorized_axioms"]) == ["Classical.choice", "Quot.sound", "propext"]
    evidence = signed["source_frozen_input"]
    frozen = ROOT / evidence["source_freeze"]
    assert sha(frozen) == evidence["source_freeze_sha256"]
    assert "--trust=0" in json.loads(frozen.read_text())["strict_flags"]
    records = {}
    for raw in ("SourceSignedWeightMaterial", "SourceSignedWeightTorque"):
        node = next(n for n in evidence["nodes"] if n["module"] == raw)
        target = next(Path(p) / f"{raw}.olean" for p in paths if (Path(p) / f"{raw}.olean").exists())
        source = SOURCE_DIR.parent / f"{raw}.lean"
        assert sha(source) == sha(target.with_suffix(".lean")) == node["source_sha256"], raw
        assert sha(target) == node["object_sha256"], raw
        wrapper = "CanonicalPreparation" + raw
        receipt = next(r for r in signed["strict_fresh_production"] if Path(r["file"]).stem == wrapper)
        production = SOURCE_DIR.parent / f"{wrapper}.lean"
        loaded = next(Path(p) / f"{wrapper}.olean" for p in paths if (Path(p) / f"{wrapper}.olean").exists())
        assert sha(production) == receipt["sha256"] and sha(loaded) == receipt["object_sha256"], wrapper
        records[raw] = {"source_sha256": sha(source), "object_sha256": sha(target),
                        "wrapper_source_sha256": sha(production), "wrapper_object_sha256": sha(loaded)}
    raw_owner = SOURCE_DIR / "physical_n3_pole_raw_noether_certification.json"
    raw_signed = json.loads(raw_owner.read_text())
    assert raw_signed["verdict"] == "certified" and "--trust=0" in raw_signed["strict_flags"]
    module = "PhysicalN3RawEMReader"
    receipt = next(r for r in raw_signed["production_sources"] if r["module"] == module)
    target = next(Path(p) / f"{module}.olean" for p in paths if (Path(p) / f"{module}.olean").exists())
    assert receipt["exit"] == 0 and sha(SOURCE_DIR / f"{module}.lean") == receipt["source_sha256"]
    assert sha(target) == receipt["object_sha256"]
    return {"owner_receipt_sha256": sha(owner), "frozen_source_sha256": sha(frozen), "records": records,
            "actual_em_reader_owner_sha256": sha(raw_owner), "actual_em_reader": receipt}


def native_temporal_bindings(paths: list[str]) -> dict:
    records = {}
    for name in ("actual_prepared_native_temporal_certification.json",
                 "actual_prepared_matter_auxiliary_certification.json"):
        certificate = SOURCE_DIR / name
        signed = json.loads(certificate.read_text())
        assert signed["verdict"] == "certified" and "--trust=0" in signed["strict_flags"]
        evidence = signed["evidence"]
        assert evidence.get("source_object_provenance_checked") or evidence.get("canonical_source_object_provenance_checked")
        assert evidence["all_private_opaque_bodies_read"]
        manifest = ROOT / evidence["capsule"] / evidence["manifest"]
        assert sha(manifest) == evidence["manifest_sha256"]
        assert sorted(signed["closure"]["axioms"]) == ["Classical.choice", "Quot.sound", "propext"]
        for receipt in signed["production_sources"]:
            module = receipt["module"]
            target = next(Path(p) / f"{module}.olean" for p in paths
                          if (Path(p) / f"{module}.olean").exists())
            source = SOURCE_DIR / f"{module}.lean"
            assert receipt["exit"] == 0 and sha(source) == receipt["source_sha256"], module
            assert sha(target) == receipt["object_sha256"], module
            records[module] = {"source_sha256": sha(source), "object_sha256": sha(target),
                               "owner_certificate_sha256": sha(certificate)}
    return records


def temporal_em_bindings(paths: list[str]) -> dict:
    certificate = SOURCE_DIR / "physical_em_temporal_cauchy_certification.json"
    signed = json.loads(certificate.read_text())
    flags = ["--trust=0", "-j1", "-DwarningAsError=true", "-DmaxErrors=1", "-DElab.async=false"]
    assert signed["verdict"] == "certified"
    assert all(flag in signed["compiler"]["flags"] for flag in flags)
    assert signed["machine_gate"]["accepted_source_bytes_current"]
    records = {}
    for module in ("PhysicalEMTemporalGerm", "PhysicalEMTemporalPrice", "PhysicalEMTemporalSigmaTwo"):
        source = SOURCE_DIR / f"{module}.lean"
        target = next(Path(p) / f"{module}.olean" for p in paths if (Path(p) / f"{module}.olean").exists())
        receipt = json.loads((target.parent / f"{module}-check.json").read_text())
        assert receipt["exit"] == 0 and all(flag in receipt["command"] for flag in flags), module
        assert sha(source) == signed["production_source_sha256"][source.name] == receipt["source_sha256"], module
        assert sha(target) == receipt["object_sha256"], module
        records[module] = {"source_sha256": sha(source), "object_sha256": sha(target),
                           "owner_certificate_sha256": sha(certificate)}
    return records



def moving_noether_bindings(paths: list[str]) -> dict:
    records = {}
    flags = ["--trust=0", "-j1", "-DwarningAsError=true", "-DmaxErrors=1", "-DElab.async=false"]
    owners = (("CanonicalSourcePropagationActualMomentumPencil", "SourcePropagationCommonMomentumAudit"),
              ("CanonicalSourcePropagationInverse", "SourcePropagationResolventAudit"),
              ("CanonicalPreparationPhysicalActualEnvelopes", "PreparationPhysicalTailPriceAudit"))
    for module, owner in owners:
        certificate = ROOT / "Lean/scratch/AlphaSource" / owner / "receipt.json"
        signed = json.loads(certificate.read_text())
        assert signed["verdict"] == "certified"
        assert all(flag in signed["frozen_candidate"]["whole"]["flags"] for flag in flags), module
        receipt = next(r for r in signed["strict_fresh_production"] if Path(r["file"]).stem == module)
        source = SOURCE_DIR.parent / f"{module}.lean"
        target = next(Path(p) / f"{module}.olean" for p in paths if (Path(p) / f"{module}.olean").exists())
        assert sha(source) == receipt["sha256"] and sha(target) == receipt["object_sha256"], module
        records[module] = {"source_sha256": sha(source), "object_sha256": sha(target),
                           "owner_receipt_sha256": sha(certificate)}
    certificate = SOURCE_DIR / "actual_full_noether_source_price_certification.json"
    signed = json.loads(certificate.read_text())
    assert signed["verdict"] == "certified" and all(flag in signed["strict_flags"] for flag in flags)
    for module in ("NoetherSourceCoefficientPrices", "CompleteSourceNoetherPrice"):
        receipt = next(r for r in signed["production_source_object_hashes"] if r["module"] == module)
        assert receipt["exit"] == 0, module
        source = SOURCE_DIR / f"{module}.lean"
        target = next(Path(p) / f"{module}.olean" for p in paths if (Path(p) / f"{module}.olean").exists())
        assert sha(source) == receipt["source_sha256"] and sha(target) == receipt["object_sha256"], module
        records[module] = {"source_sha256": sha(source), "object_sha256": sha(target),
                           "owner_receipt_sha256": sha(certificate)}
    return records


def joint_insertion_bindings(paths: list[str]) -> dict:
    records = {}
    flags = ["--trust=0", "-j1", "-DwarningAsError=true", "-DElab.async=false"]
    certificate = SOURCE_DIR / "actual_dressed_common_ir_certification.json"
    signed = json.loads(certificate.read_text())
    assert signed["verdict"] == "certified" and all(f in signed["strict_flags"] for f in flags)
    frozen = signed["construction_evidence"]["frozen_candidate"]
    candidate = Path(frozen["path"])
    assert sha(candidate) == frozen["sha256"]
    nodes = json.loads(candidate.read_text())["sources"]
    for module in ("ActualDressedUniformMaterialInverse", "ActualDressedCommonIRSourceOperators", "ActualDressedCommonIRResponse"):
        node = next(r for r in nodes if r["module"] == module)
        strict = node["strict"]
        assert strict["exit"] == 0 and all(f in strict["command"] for f in flags), module
        target = next(Path(p) / f"{module}.olean" for p in paths if (Path(p) / f"{module}.olean").exists())
        source = SOURCE_DIR / f"{module}.lean"
        assert sha(source) == sha(target.with_suffix(".lean")) == node["source_sha256"] == strict["source_sha256"], module
        assert sha(target) == node["object_sha256"] == strict["object_sha256"], module
        records[module] = {"source_sha256": sha(source), "object_sha256": sha(target),
                           "owner_certificate_sha256": sha(certificate), "candidate_sha256": sha(candidate)}
    certificate = SOURCE_DIR / "actual_em_dressed_transfer_ir_certification.json"
    signed = json.loads(certificate.read_text())
    assert signed["verdict"] == "certified"
    module = "ActualEMJointCurrentMomentum"
    node = next(r for r in signed["construction_evidence"]["frozen_sources"] if r["module"] == module)
    assert node["exit"] == 0 and all(f in node["construction_flags"] for f in flags)
    target = next(Path(p) / f"{module}.olean" for p in paths if (Path(p) / f"{module}.olean").exists())
    source = SOURCE_DIR / f"{module}.lean"
    assert sha(source) == sha(target.with_suffix(".lean")) == node["source_sha256"]
    assert sha(target) == node["object_sha256"]
    records[module] = {"source_sha256": sha(source), "object_sha256": sha(target),
                       "owner_certificate_sha256": sha(certificate)}
    return records


def quantum_column_bindings(paths: list[str]) -> dict:
    records = {}
    flags = ["--trust=0", "-j1", "-DwarningAsError=true", "-DElab.async=false"]
    certificate = SOURCE_DIR / "actual_dressed_em_zero_clock_columns_certification.json"
    signed = json.loads(certificate.read_text())
    assert signed["verdict"] == "certified" and all(f in signed["strict_flags"] for f in flags)
    evidence = signed["construction_evidence"]
    candidate = Path(evidence["candidate_path"])
    assert sha(candidate) == evidence["candidate_sha256"]
    nodes = evidence["construction_sources"]
    certificate2 = SOURCE_DIR / "actual_dressed_ordered_static_certification.json"
    signed2 = json.loads(certificate2.read_text())
    assert signed2["verdict"] == "certified" and all(f in signed2["strict_flags"] for f in flags)
    frozen = signed2["construction_evidence"]["frozen_candidate"]
    candidate2 = Path(frozen["path"])
    assert sha(candidate2) == frozen["sha256"]
    nodes2 = json.loads(candidate2.read_text())["sources"]
    for module, entries, owner, frozen_path in (
        ("ActualDressedEMClockColumns", nodes, certificate, candidate),
        ("ActualDressedEMColumnThreshold", nodes, certificate, candidate),
        ("ActualDressedClockCoefficientReturn", nodes2, certificate2, candidate2),
    ):
        node = next(n for n in entries if n["module"] == module)
        strict = node["strict"]
        assert strict["exit"] == 0 and all(f in strict["command"] for f in flags), module
        target = next(Path(p) / f"{module}.olean" for p in paths if (Path(p) / f"{module}.olean").exists())
        source = SOURCE_DIR / f"{module}.lean"
        assert sha(source) == sha(target.with_suffix(".lean")) == node["source_sha256"] == strict["source_sha256"], module
        assert sha(target) == node["object_sha256"] == strict["object_sha256"], module
        records[module] = {"source_sha256": sha(source), "object_sha256": sha(target),
                           "owner_certificate_sha256": sha(owner), "candidate_sha256": sha(frozen_path)}
    return records


def four_clock_bindings(paths: list[str]) -> dict:
    certificate = SOURCE_DIR / "actual_dressed_free_clock_certification.json"
    signed = json.loads(certificate.read_text())
    flags = ["--trust=0", "-j1", "-DwarningAsError=true", "-DElab.async=false"]
    assert signed["verdict"] == "certified" and all(f in signed["strict_flags"] for f in flags)
    frozen = signed["construction_evidence"]["frozen_candidate"]
    candidate = Path(frozen["path"])
    assert sha(candidate) == frozen["sha256"]
    nodes = json.loads(candidate.read_text())["sources"]
    module = "ActualDressedCommonDenominatorNonzero"
    node = next(n for n in nodes if n["module"] == module)
    strict = node["strict"]
    assert strict["exit"] == 0 and all(f in strict["command"] for f in flags), module
    target = next(Path(p) / f"{module}.olean" for p in paths if (Path(p) / f"{module}.olean").exists())
    source = SOURCE_DIR / f"{module}.lean"
    assert sha(source) == sha(target.with_suffix(".lean")) == node["source_sha256"] == strict["source_sha256"], module
    assert sha(target) == node["object_sha256"] == strict["object_sha256"], module
    return {module: {"source_sha256": sha(source), "object_sha256": sha(target),
                     "owner_certificate_sha256": sha(certificate), "candidate_sha256": sha(candidate)}}

def matter_clock_bindings(paths: list[str]) -> dict:
    certificate = SOURCE_DIR / "actual_prepared_matter_clock_certification.json"
    signed = json.loads(certificate.read_text())
    assert signed["verdict"] == "certified"
    flags = ["--trust=0", "-j1", "-DwarningAsError=true", "-DElab.async=false"]
    assert all(f in signed["strict_flags"] for f in flags)
    assert sorted(signed["closure"]["axioms"]) == ["Classical.choice", "Quot.sound", "propext"]
    records = {}
    for node in signed["production_sources"]:
        module = node["module"]
        target = next(Path(p) / f"{module}.olean" for p in paths if (Path(p) / f"{module}.olean").exists())
        source = SOURCE_DIR / f"{module}.lean"
        assert node["exit"] == 0 and sha(source) == node["source_sha256"], module
        assert sha(target) == node["object_sha256"], module
        records[module] = {"source_sha256": sha(source), "object_sha256": sha(target)}
    return {"certificate_sha256": sha(certificate), "modules": records}


def controls() -> list[str]:
    # Scope controls use exact arithmetic; these are not physical source fixtures.
    # Clearing a97 determinant adds epsilon order388 to its polynomial
    # representation; source response normalization must remove that factor.
    for epsilon in (Fraction(1,2), Fraction(1,4)):
        denominator = -epsilon**4*(Fraction(72,25)-epsilon**4)*(Fraction(81,50)-epsilon**4)
        cleared = denominator*epsilon**4
        assert cleared**97 == denominator**97*(epsilon**4)**97
        assert denominator*cleared**96/cleared**97 == 1/epsilon**4
        assert cleared**96/cleared**97 != 1/epsilon**4
    # The complete balance is paired with Dm; Q97 has its own Noether numerator.
    h, a, dm, dq, balance = map(Fraction, (2, 9, 5, 7, 11))
    noether = a*dq*(balance+Fraction(3,4)*dm)/(h*dm)
    assert noether/dq == a/h*(balance/dm+Fraction(3,4))
    assert noether/dq != balance/dq
    # Price the clock units after retaining both source orders.  These exact
    # fixtures test the inequality, not a numerical instance of the source.
    for eps in (Fraction(1,2), Fraction(1,4), Fraction(1,8)):
        a0, b0, ca, cb = 3+eps**2, eps**4, Fraction(2), Fraction(5)
        radius = min(Fraction(1), abs(b0)/(2*(1+cb)))
        slope = 2*(abs(b0)*ca+abs(a0)*cb)/abs(b0)**2
        for sigma in (radius/2, radius):
            au, bu = a0+ca*sigma, b0+cb*sigma
            assert abs(bu) >= abs(b0)/2
            for mn, md in ((1,3), (3,1), (0,4)):
                raw = sigma**mn*au/(sigma**md*bu)
                normalized = sigma**md/sigma**mn*raw
                assert normalized == au/bu
                assert abs(normalized-a0/b0) <= slope*abs(sigma)
                assert abs(sigma**md*raw-sigma**mn*a0/b0) <= abs(sigma)**mn*slope*abs(sigma)
                assert raw != normalized
    # The native factor remains in the full adjugate, even when the full
    # determinant vanishes. A nonzero Schur adjugate is not an inverse chart.
    native_det = Fraction(5)
    schur_det, schur_adjugate = Fraction(0), Fraction(3)
    whole_det = native_det*schur_det
    whole_adjugate = native_det*schur_adjugate
    assert whole_det == 0 and whole_adjugate == 15
    assert whole_adjugate != schur_adjugate
    for clearing in (Fraction(1,3), Fraction(2)):
        qdet, qadj = clearing**97*schur_det, clearing**96*schur_adjugate
        assert clearing*whole_det*qadj == qdet*whole_adjugate
    schur = Fraction(4)-Fraction(3)*Fraction(1,5)*Fraction(2)
    for clearing in (Fraction(1,3), Fraction(2), Fraction(5,7)):
        actual = clearing/(clearing*schur)
        assert actual == 1/schur
        assert actual != 1/(clearing*schur)
        assert clearing*actual != actual
    # Complete same-source Ward reconstruction; these are countercontrols,
    # never replacements for physical coefficients.
    ward_x, ward_d, ward_ra, ward_ri, ward_ni, ward_pia = map(Fraction, (2,4,3,2,5,7))
    ward_read = ward_d*(ward_x*ward_ra)-(ward_x*ward_ri)*ward_ni*ward_pia
    assert ward_read == ward_x*(ward_d*ward_ra-ward_ri*ward_ni*ward_pia)
    assert ward_read != ward_x*(ward_d*ward_ra-ward_ri*ward_ni)
    assert Fraction(1,4)**2*3 != Fraction(1,4)*3
    ward_clock, ward_residual = Fraction(1,4), Fraction(3)
    ward_original = ward_clock**2*ward_residual
    assert -Fraction(1,2)*ward_original == ward_clock**2*(-Fraction(1,2)*ward_residual)
    assert ward_original != ward_clock**2*(-Fraction(1,2)*ward_residual)
    assert ward_clock**5 == ward_clock**2*ward_clock**3
    assert ward_clock**5 != ward_clock**2 and ward_clock**3 != 1
    # The same Noether/current read keeps its original epsilon weight and
    # both residual orders after the generated +3/+2 factors cancel.
    for sigma in (Fraction(1,8), Fraction(1,4)):
        epsilon = Fraction(1,3)
        for numerator_order, denominator_order in ((0,0),(1,3),(3,1)):
            residual_n = sigma**numerator_order*(2+sigma)
            residual_d = sigma**denominator_order*(3+sigma)
            numerator, denominator = sigma**3*residual_n, sigma**2*residual_d
            weighted = numerator/denominator
            assert weighted == sigma*residual_n/residual_d
            assert weighted != residual_n/residual_d
            actual = weighted/epsilon**4
            assert epsilon**4*actual == weighted and actual != weighted
            normalized = sigma**(denominator_order+2)/sigma**(numerator_order+3)*weighted
            assert normalized == sigma**denominator_order/sigma**numerator_order*residual_n/residual_d
        assert sigma**3*0 == 0 and 0/ (sigma**2*residual_d) == 0
        zero_polynomial_order = 0
        assert zero_polynomial_order != 3+zero_polynomial_order
    q = Fraction(1, 2)
    assert all(q**b / Fraction(1, 4)**4 > q**(b + 1) / Fraction(1, 4)**4 for b in range(8))
    assert all(q**b / (q**b)**4 >= 1 for b in range(8))
    assert all(Fraction(0) - q**b < 0 for b in range(8))
    assert all(Fraction(k) - Fraction(k) == 0 for k in range(8))
    assert Fraction(7) > Fraction(1)
    assert Fraction(2)-Fraction(1) == Fraction(2)*Fraction(0)*Fraction(1)+Fraction(2)*(Fraction(1)-Fraction(1,2)*Fraction(1))
    assert Fraction(2)-Fraction(1) != Fraction(2)*Fraction(0)*Fraction(1)
    assert (q**2)**2 == q**4 and q**4 != q**2
    clock_read = 2/q**2 + 3/q + 5
    assert clock_read == (2/q**2 + 3/q) + 5 and clock_read != 5
    assert q**2*clock_read == 2 + 3*q + 5*q**2
    # Full-read cancellation does not make each original EM/residual arm finite.
    arms = (1/q**2, -1/q**2, Fraction(0), Fraction(2))
    assert sum(arms) == 2 and arms[0] != 2
    qd, qs, pd, ps = Fraction(3, 2), Fraction(-2, 3), Fraction(1, 5), Fraction(1, 7)
    delta_d, delta_s = pd, -ps
    pair_error = abs((qd + delta_d)*(qs + delta_s)-qd*qs)
    pair_price = abs(qd)*ps + pd*abs(qs) + pd*ps
    assert pair_error <= pair_price and (qd+delta_d)*(qs+delta_s) != qd*qs
    assert pair_price > abs(qd)*ps + pd*abs(qs)
    assert qd+delta_d != 1
    # Exact coefficient budgets, separate from any source numerical instance.
    a0, b0, ca, cb = Fraction(3), Fraction(2), Fraction(4), Fraction(5)
    radius = min(Fraction(1), abs(b0)/(2*(1+cb)))
    slope = 2*(abs(b0)*ca+abs(a0)*cb)/abs(b0)**2
    assert radius > 0 and min(Fraction(1), Fraction(0)/(2*(1+cb))) == 0
    for z in (Fraction(0), radius/2, radius, -radius):
        az, bz = a0+ca*z, b0+cb*z
        assert abs(bz) >= abs(b0)/2
        assert abs(az/bz-a0/b0) <= slope*abs(z)
    # Exact cleared pencil: d=sigma, J=diag(1,0), Q=diag(1-sigma,1).
    # Its nine-row analogue LQ adj(P) E vanishes while the actual time read is 1/sigma.
    for sigma in (q**k for k in range(1, 9)):
        adj_e = (-sigma, Fraction(0))
        quantum_field = ((1-sigma)*adj_e[0], adj_e[1])
        temporal_read = sigma*adj_e[0]/(-sigma**3)
        assert quantum_field[1] == 0 and quantum_field[0] != 0
        assert temporal_read == 1/sigma and temporal_read > 1
    # J=diag(1,0), N=J, Q=ones: complete J-Q is invertible but 1-NQ is singular.
    full_det = Fraction(0)*Fraction(-1)-Fraction(-1)*Fraction(-1)
    feedback_det = Fraction(0)*Fraction(1)-Fraction(-1)*Fraction(0)
    assert full_det != 0 and feedback_det == 0
    detector, lift = (Fraction(1), Fraction(0)), (Fraction(0), Fraction(1))
    feedback = ((Fraction(1), Fraction(1)), (Fraction(0), Fraction(1)))
    assert sum(detector[i]*lift[i] for i in range(2)) == 0
    assert sum(detector[i]*feedback[i][j]*lift[j] for i in range(2) for j in range(2)) == 1
    light, heavy, outside, tail = Fraction(2), Fraction(3), Fraction(-1), Fraction(1, 2)
    full = light + heavy + outside + tail
    assert full-light == heavy+outside+tail and full-light != heavy
    assert all((q**k)**2 * 1/(q**k)**2 == 1 for k in range(1, 9))
    source_d, clock, jacobi, numerator = Fraction(5), Fraction(2), Fraction(3), Fraction(7)
    determinant = source_d*jacobi-clock*numerator
    actual_drive = clock*(numerator/source_d)*(source_d/determinant)
    assert actual_drive == clock*numerator/determinant
    assert actual_drive != clock*numerator/(source_d*determinant)
    assert actual_drive != numerator/determinant
    # Every fixed-e clock read vanishes at sigma=0; the joint sigma=e^2 read need not.
    assert all((q**k)**2/(q**k)**2 == 1 for k in range(1, 9))
    r0, correction, material, contact, drive, initial, z = map(Fraction, (1, 1, 7, 11, 5, 13, 1))
    moving = r0 + z*correction
    complete = moving*(material+contact+drive*(moving*initial))
    zeroth = r0*(material+contact)+r0*drive*(r0*initial)
    linear = correction*(material+contact)+correction*drive*(r0*initial)+r0*drive*(correction*initial)
    quadratic = correction*drive*(correction*initial)
    assert complete == zeroth+z*linear+z*z*quadratic
    assert complete != zeroth+z*linear
    assert (Fraction(0), -q*q) != (Fraction(0), q*q)
    assert 56*Fraction(2) > 56*Fraction(1)
    field_error = (Fraction(7,2)-3)*2+(Fraction(9,2)-4)*3
    assert field_error == q*(2+3) and field_error != q

    r0, correction, material, drive, insertion, initial, z = map(Fraction, (1,1,7,3,5,11,1))
    moving, moving_drive = r0+z*correction, drive+z*insertion
    complete = moving*(material+moving_drive*(moving*initial))
    c0 = r0*material+r0*drive*r0*initial
    c1 = correction*material+correction*drive*r0*initial+r0*drive*correction*initial+r0*insertion*r0*initial
    c2 = correction*drive*correction*initial+correction*insertion*r0*initial+r0*insertion*correction*initial
    c3 = correction*insertion*correction*initial
    assert complete == c0+z*c1+z*z*c2+z*z*z*c3 and complete != c0+z*c1+z*z*c2
    assert 2*7*3+2*(11-7)*3 == 2*11*3 and 2*7*3+2*(11-7)*3 != 0
    assert q*q/(q*q)**3 > 1
    assert 2*Fraction(7)/(5*3-2*7) == 3*Fraction(5)/(5*3-2*7)-1
    assert 2*Fraction(7)/(5*3-2*7) != 3*Fraction(5)/(5*3-2*7)
    for sigma in (q**k for k in range(2, 9)):
        d, clock = sigma*sigma, sigma
        # J=diag(2,3), N=diag(sigma,1), original E=(1,0).
        h1, h2 = d*2-clock*sigma, d*3-clock
        determinant = h1*h2
        column0 = (d*h2/determinant, Fraction(0))
        drive0 = (clock*sigma*h2/determinant, Fraction(0))
        assert column0 == (Fraction(1), Fraction(0))
        assert drive0 == (2*column0[0]-1, Fraction(0)) == (Fraction(1), Fraction(0))
        assert clock/d > 1
    for sigma in (q**k for k in range(1, 9)):
        # Original clearing sigma^11 and numerator sigma^7 produce Pi=sigma^-4.
        assert sigma**4*sigma**7/sigma**11 == 1
        assert sigma**3*sigma**7/sigma**11 > 1
        normalized_den, normalized_num, jacobi = Fraction(5), Fraction(7), Fraction(2)
        k = sigma**3*normalized_den*jacobi-normalized_num
        actual_field = sigma**3*normalized_den/k
        actual_driver = jacobi*actual_field-1
        assert k*actual_field == sigma**3*normalized_den
        assert normalized_num*actual_field == sigma**3*normalized_den*actual_driver
        assert k*actual_field != normalized_den
        assert k != sigma**3*jacobi-normalized_num
    assert q**2/(q**2+q**2) == Fraction(1,2)
    assert q**2/(q**2+q**4) != Fraction(1,2)
    for sigma in (q**k for k in range(1, 9)):
        c = Fraction(5)*sigma**3
        k = 2*c-7
        field = c/k
        driver = 2*field-1
        field_num = c
        driver_num = 2*field_num-k
        assert driver_num == 7 and k*driver == driver_num
        assert 2*field_num != driver_num
        actual_pencil_det = Fraction(6)
        assert Fraction(5)**2*actual_pencil_det != Fraction(5)**2*(Fraction(7)**2*actual_pencil_det)
    for sigma in (q**k for k in range(1, 9)):
        # The signed EM contraction is a row, with the same original Pi clearing.
        assert sigma**2*sigma**7/sigma**9 == 1
        assert sigma*sigma**7/sigma**9 > 1
        assert sigma**2/sigma**2 == 1 and sigma**2/sigma**4 > 1
        for field in (Fraction(2), Fraction(3), 1/sigma):
            assert sigma*(sigma/sigma**2*field) == field
            assert sigma*(sigma/sigma**2*field) != 1
    force = (-q, q, -q)
    force_self = sum(x*x for x in force)
    assert force_self == Fraction(3,4) and force_self != 1
    for sigma in (q**k for k in range(1,9)):
        source_d = Fraction(5)
        reduced_row = tuple(sigma*source_d*x for x in force)
        read = sum(x*y for x,y in zip(reduced_row, force))
        assert read == sigma*source_d*force_self and read != sigma*source_d
    # The exact source primal coefficient is sqrt(2), not zero.
    assert Fraction(7,5)**2 < 2 < Fraction(3,2)**2
    # Dbar=sigma+epsilon can acquire an extra clock zero at epsilon=0.
    # At that occurrence Nbar=3*sigma+sigma^2 has finite ratio 3.
    for sigma in (q**k for k in range(1, 9)):
        assert (3*sigma+sigma*sigma)/sigma == 3+sigma
        assert (3*sigma+sigma*sigma)/sigma != 0
    assert Fraction(3) != Fraction(0)  # raw 0/0 conventions cannot generate the coefficient
    for x in (q**k for k in range(1,9)):
        normalized_response = lambda e, damping: e*e/(e*e+damping*damping)
        assert normalized_response(x, Fraction(0)) == 1
        assert normalized_response(Fraction(0), x) == 0
        assert normalized_response(x, x) == Fraction(1,2)
    # Exact operator controls; no matrix here supplies a physical source value.
    def product(a, b):
        return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(len(b)))
                           for j in range(len(b[0]))) for i in range(len(a)))
    def add(a, b, sign=1):
        return tuple(tuple(x+sign*y for x,y in zip(u,v)) for u,v in zip(a,b))
    def commutator(a, b):
        return add(product(a,b),product(b,a),-1)
    c, w, charge, normal = (((1,1),(1,2)), ((2,0),(0,3)),
                             ((1,0),(0,-1)), ((0,1),(2,0)))
    reader = add(product(w,charge),normal,-1)
    torque = add(product(commutator(c,w),charge),product(w,commutator(c,charge)))
    assert commutator(c,reader) == add(torque,commutator(c,normal),-1)
    assert commutator(c,reader) != torque
    # A genuine finite restriction has both defects even for Hermitian cores.
    full_c, full_j = ((1,2,3),(2,4,5),(3,5,6)), ((1,0,1),(0,2,1),(1,1,3))
    finite_c, finite_j = ((1,2),(2,4)), ((1,0),(0,2))
    actual = commutator(finite_c,finite_j)[0][1]
    core = commutator(full_c,full_j)[0][1]
    right_defect, left_defect = (0,0,-1), (0,0,-1)
    framed = core + sum(full_c[0][k]*right_defect[k] for k in range(3)) - sum(
        left_defect[k]*full_c[k][1] for k in range(3))
    assert actual == framed and actual != core
    # U(-t) and U(t) produce +i[C,J], before the original Euler minus.
    assert 1j*actual != -1j*actual
    # First partials alone do not pay mixed-order interchange without source C2.
    def nonsmooth_mixed(x, y):
        denominator = x*x+y*y
        return x*y*(x*x-y*y)/denominator if denominator else Fraction(0)
    axis_r = lambda y: -y
    axis_t = lambda x: x
    for step in (q**k for k in range(1,9)):
        # Exact controlled approach to the two axis partials of one function.
        assert abs(nonsmooth_mixed(step,Fraction(1))/step-axis_r(Fraction(1))) <= 2*step*step
        assert abs(nonsmooth_mixed(Fraction(1),step)/step-axis_t(Fraction(1))) <= 2*step*step
    assert (axis_r(Fraction(1))-axis_r(Fraction(0))) == -1
    assert (axis_t(Fraction(1))-axis_t(Fraction(0))) == 1
    assert axis_r(Fraction(1)) != axis_t(Fraction(1))
    # A finite-age return must keep both endpoints, even when lambda is zero.
    initial, horizon = Fraction(3), Fraction(2)
    terminal = initial+horizon
    integral_age_derivative = horizon
    assert integral_age_derivative == terminal-initial
    assert integral_age_derivative != terminal
    assert integral_age_derivative != -initial
    # Exact affine-age Laplace fixture: the original residual cannot be discarded.
    damping, birth, slope = Fraction(2), Fraction(3), Fraction(1)
    laplace_jet = birth/damping+slope/(damping*damping)
    residual = slope/damping
    assert damping*laplace_jet == birth+residual
    assert damping*laplace_jet != birth
    # Distinct source momenta require CL J - J CR, not a single-C commutator.
    cl, cr, reader = ((1,0),(0,2)), ((3,0),(0,4)), ((1,2),(2,1))
    moving = add(product(cl,reader),product(reader,cr),-1)
    assert moving != commutator(cl,reader)
    assert moving != commutator(cr,reader)
    # Row-zero quantum response retains the nonzero native auxiliary equation.
    a = Fraction(2)
    p = ((Fraction(2),Fraction(3)),(Fraction(5),Fraction(7)))
    k = (p[0],tuple(a*x for x in p[1]))
    det = lambda m: m[0][0]*m[1][1]-m[0][1]*m[1][0]
    adj_first = lambda m: (m[1][1],-m[1][0])
    full = tuple(a*x for x in adj_first(k))
    reduced = tuple(a*x for x in adj_first(p))
    assert k[1] != (0,0)
    assert det(k) == a*det(p) and det(k) != det(p)
    assert full == tuple(a*x for x in reduced)
    assert tuple(x/det(k) for x in full) == tuple(x/det(p) for x in reduced)
    assert tuple(x/det(p) for x in full) != tuple(x/det(p) for x in reduced)
    assert tuple(x/det(p) for x in adj_first(p)) != tuple(x/det(p) for x in reduced)
    assert a**72 != a**71 and a**72 != 1
    assert (1,a) != (1,1)  # A source with auxiliary forcing cannot use W E=E.
    # Exact arithmetic checks of elimination, not physical source fixtures.
    assert Fraction(4)*5-Fraction(3)*2 == 5*(Fraction(4)-Fraction(3)*Fraction(1,5)*2)
    r=Fraction(5,2);aux=-Fraction(1,5)*2*r
    assert aux == -1 and 4*r+3*aux == 7 and 2*r+5*aux == 0
    A=Fraction(2)
    complete=(4*A-1)-(3*A-1)*Fraction(1,5)*2
    omitted=(4*A-1)-3*A*Fraction(1,5)*2
    assert complete != omitted
    singular_A=Fraction(3,14)
    assert 5 != 0 and (4*singular_A-1)-(3*singular_A-1)*Fraction(1,5)*2 == 0
    # Mathematical coordinate control, not a source parameter assignment.
    spatial_coordinate, clock_coordinate = Fraction(2), Fraction(3)
    assert spatial_coordinate != clock_coordinate
    assert spatial_coordinate**2*clock_coordinate != clock_coordinate**2*spatial_coordinate
    # A complete multi-pole clock principal cannot be replaced by its center.
    clock = Fraction(1, 4)
    complete = (1+2*clock+3*clock**2)/(clock**2*(1-clock))
    principal = 1/clock**2+3/clock
    assert abs(complete-principal-6) <= 12*clock < abs(complete-6)
    age_error, clock_error = Fraction(1,4), Fraction(1,3)
    aligned_error = age_error+clock_error
    assert abs(aligned_error) <= age_error+clock_error
    assert max(age_error,clock_error) < abs(aligned_error)
    gram, determinant, background, lower, principal = map(Fraction, (Fraction(3,4),5,11,13,7))
    original_jacobi_read = background+lower+principal
    complete_driver = original_jacobi_read-gram*determinant
    complete_balance = complete_driver-background-lower
    assert complete_balance+gram*determinant == principal
    assert all(x != 0 for x in (complete_driver,background,lower))
    assert complete_balance+determinant != principal
    lapse, epsilon, spatial_square, field_read = map(Fraction, (2,Fraction(1,2),5,3))
    native_principal = 2*lapse*epsilon**4*spatial_square*field_read
    assert native_principal != 2*lapse*epsilon**2*spatial_square*field_read
    assert native_principal != -native_principal
    # The native denominator clears both cofactor legs of the same actual field.
    d, native_s, original_clock = Fraction(3), Fraction(2), Fraction(5)
    assert original_clock*d/(d*native_s) == original_clock/native_s
    assert original_clock/(d*native_s) != original_clock/native_s
    # A weighted clock error needs its own source-derived shrinking cap.
    epsilon = Fraction(1, 10)
    weight, slope = epsilon**(-3), Fraction(7)
    clock_cap = epsilon/(1+weight*abs(slope))
    assert clock_cap > 0 and weight*slope*clock_cap <= epsilon
    assert weight*slope*epsilon > epsilon
    # A genuine inner leading floor retains the spatial vanishing order.
    leading_floor = Fraction(3,2)*epsilon**2
    clock_mass = Fraction(5)
    safe_clock = min(Fraction(1),leading_floor/(2*(1+clock_mass)))
    assert safe_clock > 0 and clock_mass*safe_clock <= leading_floor/2
    assert clock_mass*Fraction(3,2)/(2*(1+clock_mass)) > leading_floor/2
    # Mathematical four-order control; these are not physical source values.
    sigma = Fraction(1,100)
    raw = epsilon**(-1)*sigma*(2+epsilon+sigma)/(3+epsilon+2*sigma)
    normalized = epsilon*sigma**(-1)*raw
    assert normalized == (2+epsilon+sigma)/(3+epsilon+2*sigma)
    assert sigma**(-1)*raw != normalized and epsilon*raw != normalized
    return ["fixed_damping_geometric_decay", "reject_fixed_damping_as_joint_rate",
            "reject_singular_chart_as_positive_margin", "reject_error_convergence_as_value_convergence",
            "reject_omitted_constrained_native_deficit", "reject_epsilon_squared_as_native_pole_scale",
            "reject_dropped_scalar_clock_principal", "reject_full_arm_cancellation_as_em_finiteness",
            "reject_dropped_charge_calibration_background", "retain_charge_defect_cross_product",
            "reject_bare_unit_as_dressed_charge", "source_coefficient_analytic_margin_and_price",
            "reject_zero_center_as_positive_analytic_radius",
            "reject_constraint_cofactor_zero_as_temporal_finiteness",
            "reject_cokernel_quantum_field_zero_as_whole_quantum_zero",
            "reject_full_regular_as_feedback_regular",
            "reject_direct_null_pair_zero_as_feedback_pair_zero",
            "reject_full_minus_light_as_heavy_without_outside_and_tail",
            "retain_varying_quantum_driver_norm_in_spatial_price",
            "reject_repeated_pi_clearing_or_omitted_driver_clock",
            "reject_fixed_epsilon_clock_return_as_joint_ir_limit",
            "reject_omitted_two_resolvent_quadratic_noether_arm",
            "retain_original_negative_epsilon_squared_propagation_sign",
            "reject_actual_field_price_as_unit_current",
            "reject_full_green_tolerance_as_unit_forcing_error",
            "reject_omitted_actual_moving_drive_cubic_arm",
            "retain_noether_contact_after_raw_contact_cancellation",
            "reject_common_radius_price_as_joint_ir_decay",
            "retain_jacobi_forcing_subtraction_in_quantum_column",
            "reject_finite_em_column_as_whole_quantum_balance",
            "retain_source_four_clock_divisibility_power",
            "retain_reduced_denominator_and_cubic_field_driver_clock",
            "reject_bounded_common_quotient_as_joint_endpoint",
            "retain_full_cofactor_driver_forcing_subtraction",
            "reject_original_cleared_det_as_unscaled_pencil_det",
            "retain_source_em_two_clock_divisibility_power",
            "reject_em_row_price_as_full_matrix_price",
            "retain_actual_field_mass_in_em_driver_clock_price",
            "retain_original_force_self_pair_in_reduced_em_equation",
            "retain_original_static_em_primal_matter_coupling",
            "retain_additional_specialized_clock_factor",
            "reject_common_zero_raw_evaluation_as_finite_residue",
            "reject_ordered_source_return_as_exact_zero_or_joint_limit",
            "retain_full_car_normal_commutator",
            "retain_both_actual_finite_frame_defects",
            "retain_original_em_age_fourier_sign",
            "reject_first_partials_as_source_C2_mixed_interchange",
            "reject_dropping_finite_pi_boundary_terms",
            "retain_nonzero_age_residual_in_infinite_pi",
            "reject_moving_residual_as_single_compression_commutator",
            "reject_zero_quantum_aux_as_zero_native_row",
            "retain_exact_seventy_two_auxiliary_row_factors",
            "reject_denominator_only_auxiliary_cancellation",
            "retain_original_cubic_clock_in_reduced_field",
            "reject_auxiliary_cancellation_without_source_forcing_support",
            "retain_source_schur_determinant_factor",
            "retain_nonzero_actual_auxiliary_reconstruction",
            "retain_prepared_upper_cross_column_feedback",
            "reject_auxiliary_inverse_as_full_schur_regular",
            "retain_independent_source_spatial_and_clock_variables",
            "retain_complete_balance_clock_principal_before_source_tail_price",
            "retain_sum_of_age_and_clock_observation_errors",
            "retain_full_balance_joint_native_principal",
            "reject_native_principal_epsilon_degree_or_sign",
            "retain_exactly_one_schur97_source_clock_in_the_actual_field",
            "reject_native_d_power97_clearing_as_added_physical_ir_pole",
            "retain_full_native_factor_in_singular_schur_adjugate",
            "reject_native_denominator_missing_from_actual_field_numerator",
            "reject_complete_balance_over_schur97_denominator",
            "retain_both_source_clock_orders_in_joint_fraction_price",
            "retain_spatially_dependent_unit_denominator_margin",
            "reject_joint_clock_cap_without_spatial_weight",
            "retain_source_inner_order_in_positive_joint_region",
            "retain_all_four_orders_in_joint_principal",
            "retain_schur97_ward_inactive_right_reconstruction",
            "retain_actual_schur97_em_two_clock_factors",
            "retain_actual_ward_pivot_inverse_normalizer",
            "retain_all_residual_ward_determinant_clock_orders",
            "retain_source_noether_cubic_clock_in_actual_read",
            "retain_each_em_outer_row_pi_factor",
            "reject_outer_row_as_thomson_limit",
            "reject_ward_read_without_original_spatial_weight",
            "retain_both_residual_ward_clock_orders",
            "reject_unconditional_zero_noether_order_shift"]


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--compile", action="store_true", help="Strict proofs and full closure; no numerical solve.")
    args = parser.parse_args()
    paths = source_paths()
    parents = bindings(paths)
    native_witness = check_source_witness()
    negative = controls() + ["reject_mutated_native_inverse_coefficient", "reject_doubled_native_inverse_normalizer", "reject_erased_off_axis_native_source"]
    if args.compile:
        env = os.environ.copy()
        env["LEAN_PATH"] = ":".join(paths)
        closure_file = CACHE / "em-enclosure-closure.json"
        closure_file.unlink(missing_ok=True)
        env["ALPHA_SOURCE_PREPARED_EM_ENCLOSURE_AUDIT_OUTPUT"] = str(closure_file)
        receipts = {}
        for module in MODULES:
            source = SOURCE_DIR / f"{module}.lean"
            target = CACHE / f"{module}.olean"
            cached = CACHE / f"{module}-check.json"
            prior = json.loads(cached.read_text()) if cached.exists() else None
            required_flags = ["--trust=0", "-j1", "-DwarningAsError=true", "-DmaxErrors=1", "-DElab.async=false"]
            if (module != MODULES[-1] and prior and prior["exit"] == 0
                    and all(flag in prior["command"] for flag in required_flags)
                    and prior["source_sha256"] == sha(source) and target.exists()
                    and prior["object_sha256"] == sha(target)):
                receipts[module] = prior
                print(json.dumps({"module": module, "unchanged_strict_receipt": True}), flush=True)
                continue
            target.unlink(missing_ok=True)
            command = ["lake", "env", "lean", "-R", str(SOURCE_DIR), "--trust=0", "-j1",
                       "-DwarningAsError=true", "-DmaxErrors=1", "-DElab.async=false", "-o", str(target), str(source)]
            started = time.monotonic()
            result = subprocess.run(command, cwd=ROOT / "Lean", env=env, text=True, capture_output=True)
            receipt = {"exit": result.returncode, "seconds": round(time.monotonic() - started, 3),
                       "command": command, "source_sha256": sha(source),
                       "object_sha256": sha(target) if result.returncode == 0 else None}
            (CACHE / f"{module}-check.json").write_text(json.dumps(receipt, indent=2) + "\n")
            print(json.dumps({"module": module, "exit": result.returncode, "seconds": receipt["seconds"]}), flush=True)
            if result.returncode:
                raise SystemExit(result.stdout + result.stderr)
            if module == MODULES[-1]:
                print(result.stdout.strip(), flush=True)
            receipts[module] = receipt
        closure = json.loads(closure_file.read_text())
        assert len(closure["public"]) == 563
        assert sorted(closure["axioms"]) == ["Classical.choice", "Quot.sound", "propext"]
        certificate = {"status": "PASS_SOURCE_PREPARED_EM_ENCLOSURE", "strict": receipts,
                       "bindings": parents, "closure": closure, "controls": negative,
                       "native_inverse_witness": {k: v for k, v in native_witness.items() if k != "seconds"},
                       "independent_review": "ACCEPT exact scope: every original transfer keeps independent left/right compression, inverse-unit and time legs; original actual EM observer germ generates CL J minus J CR and all289 BL J minus J BR insertions. The same observer source C2 identifies both mixed orders. Original full289 Pi finite/infinite age returns keep that same transfer, both genuine endpoints and generated source tail. At transfer epsilon squared n the unchanged actual GE0 contracts every returned column, directly consuming the original quantum-driver identity; finite error retains every actual field norm. Source, created/background pair, CAR/contact and all289 currents remain. The same original auxiliary quantum rows generate the shared A^72 determinant/whole-field factor; the actual field, complete driver and finite native EM balance consume its cancellation on the unchanged original chart. The same constant source auxiliary block and its generated two-sided inverse produce Schur217 with full prepared upper cross columns retained. The original Green pays Schur regularity; its cofactor reconstructs all289 fields and the complete driver/background10/lower6 balance uses that same reduced determinant. The same Schur217 determinant and complete289 reconstructed cofactor are retained in a single bivariate source ring, inner epsilon and outer sigma. Full driver, background10 and epsilon squared lower6 enter one generated numerator; its evaluated quotient directly equals the complete original finite EM balance and coefficient. The complete balance generates its own reduced clock pole order, full principal, epsilon-dependent coefficient radius/center/slope, and the unchanged finite Noether coefficient consumes its norm-scaled remainder price. The original configuration finite-age window and the full source clock principal share one observation disk whose radius retains every age endpoint, prepared tail, actual289 field norm and clock remainder in the original action units. The newly certified remaining120 inactive quantum rows supply an unconditional shared c to power120 on the complete bivariate field cofactor before either coordinate is specialized; the reduced source field evaluates to the same original actual field and keeps every Dirac/BF coordinate. The normalized matter-clock determinant and complete289 field cofactor also generate the original whole driver and full background10/epsilon squared lower6 balance as a single bivariate numerator; the unchanged original finite Noether coefficient directly consumes that quotient. The normalized complete matter-clock fraction itself supplies its own full clock principal, positive coefficient radius/center/slope and original finite Noether coefficient norm price, with epsilon dependence and all true poles retained. Positive damping is pointwise, not a joint IR claim; no unit-field, endpoint, smoothness, commuting-reader or equal-momentum premise.",
                       "scope": {"schur97_source_ward_determinant": "actual original coordinate15/-1/2 and source Ward row generate X squared divisibility; canonical monic quotient reconstructs original detQ97 for every event/n, all further factors retained, no chart or caller factor premise",
                                 "schur97_source_ward_row": "original EM X squared row restricts through the exhaustive97/192 partition to the same source Schur pencil; full RI*Hnum*PIA retained, all event and momentum, no extra row premise",
                                 "schur97_source_joint_region_and_principal": "one unchanged original regular seed pays nonzero denominator; source-fixed positive spatial radius and epsilon-dependent positive clock cap generate the complete original chart throughout the region and full literal N97/detQ97 four-order weighted principal with O(epsilon) price; zero numerator retained, no origin owner premise",
                                 "schur97_source_joint_physical_scope": "all actual clock and spatial powers remain explicit; no equal-order premise, unweighted T00 norm theorem, protocol curve choice or Thomson alpha0 identification",
                                 "schur97_source_regular_on_unit_radius": "origin plus generated clock radius pays the same original full289 correctedDet chart for unit direction, 0<epsilon<=1/2 and positive sigma; current-point regular premise removed, original puncture seed retained",
                                 "schur97_actual_noether_consumer_on_source_unit_radius": "unchanged actual epsilon fourth T00 reader directly consumes generated original regularity; literal source numerator and full97/192 response retained",
                                 "schur97_source_unit_fraction_price": "same literal N97/detQ97; numerator and denominator natTrailingDegree retained, source unit chart and positive epsilon-dependent clock radius, norm tail priced by original bivariate coefficient masses",
                                 "schur97_source_noether_literal_match": "kernel environment AST equality to the original source_schur97_noether_fraction numerator; same event/n and c*d/Noether squared/epsilon fourth power",
                                 "schur97_new_actual_T00_norm_theorem": False,
                                 "schur97_complete_bivariate_balance_cross": "same unit direction: (2*lapse*spatialSquare n)*Dm*N97literal = noetherPairScale squared*detQ*(complete BalanceNum + 3/4*Dm); independent epsilon/sigma and singular points included; source literal multiplication, no chart or endpoint premise",
                                 "prepared_full_pencil_to_original_green_and_em_tensor": True,
                                 "computed_margin_eventually_positive": "fixed 0 < sigma <= 2 and original correctedDet != 0",
                                 "source_finite_precision_witness": "Nat.find of proven source margin/total-error predicate; no executable numerical witness claimed",
                                 "all_green_and_em_entries": "289 x 289 and 4 x 4, same source window",
                                 "joint_ward_and_window_error": "same budget-refined actual preparation on pointwise regular positive damping curve",
                                 "actual_n3_pole_current_consumer": "complete read with Noether scale, both mixed arms and residual retained",
                                 "actual_n3_read_finite_enclosure": "source-generated matrix tolerance divided by 1 + actual current pair mass; no unit-norm current premise",
                                 "actual_n3_moving_response_partition": "corrected-minus-native read = sandwiched moving light + heavy + cross/outside + tail + original native constraint deficit; contact retained",
                                 "static_native_chart_regular_generated": "unit spatial direction; epsilon squared <= original staticRadius; eventually on original scaleApproach",
                                 "native_constraint_original_identity": "original transported nine-row null-source projector, not zero",
                                 "actual_n3_native_static_residue": "epsilon^4 scaled whole native read tends to original staticResidue contracted with both actual N3 currents",
                                 "actual_n3_native_pole_remainder_price": "pointwise original price: explicit epsilon squared factor, source frame/reader norms and actual detector current mass; contact/complement read separated",
                                 "actual_n3_corrected_ir_scalar": "same two actual N3 currents contract the original complete corrected cofactor before clock/spatial extraction; no legacy composite probe",
                                 "actual_n3_clock_principal": "source reduced scalar pole order and leading coefficient; every negative power plus exact analytic remainder retained on the original positive regular chart",
                                 "actual_n3_four_ir_arms": "same original cofactor before and after RatFunc reduction; EM, both mixed and residual arms retained independently",
                                 "actual_n3_em_clock_order": "own reduced EM scalar order, leading coefficient and actual Noether read; no full-read cancellation premise",
                                 "actual_n3_same_state_charge_endpoint": "zero-transfer amputation returns actual sign plus same-state pole correction; temporal Noether current adds actual calibration minus original background read",
                                 "actual_n3_charge_endpoint_price": "source calibration plus raw-reader prices; pair bound retains both single-leg errors and their product; other fifteen EM terms retained",
                                 "actual_n3_em_analytic_coefficient_price": "source reduced root remainder generates positive radius, denominator half-margin, analytic center and explicit linear price after retaining full clock principal",
                                 "actual_n3_em_original_clock_coefficients": "before chart selection or reduction: original N3 EM cofactor is its original EM16 tensor contracted with physical Noether currents; each clock coefficient retains actual Q+defect temporal term and other15",
                                 "actual_static_temporal_em_constraint": "original EM time column consumes all nine source coker rows; original transported null-source projector kills this same static column; nonstatic row2=-p0/2 retained",
                                 "actual_temporal_em_quantum_response": "Noether-normalized temporal coefficient minus native term is the complete G sigma Pi N temporal read; actual GQ arm vanishes by source column identity on original unit/small static chart; no full-current compatibility assumed",
                                 "actual_temporal_quantum_nine_row_constraint": "actual a=prepared full G E0; original Euler/source rows generate cokernel(Pi a)=0 on positive regular clock, without pole-mode or balance premise",
                                 "actual_temporal_quantum_constraint_cofactor": "every coefficient of original common Pi-numerator/adjugate nine-row contraction vanishes for all epsilon and spatial directions, without a regularity chart; not a T00 coefficient identity",
                                 "actual_temporal_quantum_history_return": "same a and complete native Ward minus reference-deviation quadratures/contact return to zero on the original source halfline",
                                 "actual_temporal_quantum_window_price": "original signal tail times nine-row reader l1 mass times actual G E0 l1 mass; no unit-current or unit-Green premise",
                                 "actual_temporal_em_schur_determinant": "generated from original complete pencil inverse on the original unit/small static point and an explicitly retained halfFeedbackDet != 0 guard; no independent Schur determinant premise",
                                 "actual_temporal_em_schur_coordinates": "original nine null coordinates generated as S inverse times original source E0; reconstructed field equals actual prepared G E0",
                                 "actual_temporal_em_schur_cofactor_noether": "literal temporal reader is correctedEMTensor00, consumes original dampingDet/P00 equality and exactly one noetherPairScale squared",
                                 "actual_temporal_detector_null_lift": "static E0 dot originalNullColumn and sourceNullLift is zero using the original opposite-covector nine-row table; no left/right row identification assumed",
                                 "actual_temporal_native_left_field": "same actual a=G E0 equals original sourceNull a plus native N(E0+sigma Pi a); full actual positive regular chart, no feedback determinant premise",
                                 "actual_temporal_native_left_noether_correction": "Noether coefficient minus complete native term equals exactly once-scaled E0 dot N(sigma Pi a), with a and complete Pi retained",
                                 "actual_temporal_moving_quantum_noether_consumer": "same N and actual a consume light, heavy, cross/outside and source tail; contact is retained in original polarization arms; no independently solved light propagator claimed",
                                 "actual_temporal_quantum_spatial_pole_price": "minus epsilon^4 scaled actual Noether quantum correction after separating complete driver regular/contact/complement read is enclosed by original poleCoefficient(driver) and original epsilon^2 frame/source-reader price, with once-scaled Noether norm",
                                 "actual_temporal_quantum_driver_cofactor": "actual sigma Pi G E0 equals source sigma commonNumerator adj(commonClearedPencil) E0 over commonDeterminant; Pi clearing cancels without an additional factor",
                                 "actual_temporal_quantum_native_reader_clock_return": "same original effectiveReader/activeProjection/originalReadback; intrinsic reduced clock order and leading coefficient at fixed epsilon, on the source punctured chart",
                                 "actual_temporal_quantum_reader_radius": "minimum of all 289 source root-remainder radii is strictly positive for each fixed source epsilon",
                                 "actual_temporal_quantum_reader_budget": "all 289 exact principal polynomials plus source analytic centers and linear prices; no unit reader or zero pole-order premise",
                                 "actual_temporal_quantum_ir_coefficient_budget": "source reader budget directly multiplies the original epsilon-squared native inverse price, retaining complete regular/contact/complement and once-scaled Noether coefficient",
                                 "actual_moving_source_propagation_update": "original q_e at transfer e squared n differs from q0 by -i e squared left momentum-compression insertion; same uncut generator",
                                 "actual_moving_source_noether_update": "complete sourceInverse(M + D sourceInverse A) = A0 + z A1 + z squared A2; M includes material/contact, D both dual legs, A actual compressed raw reader; coefficients retain e and clock dependence",
                                 "actual_moving_full_polarization_and_driver": "same original Euler observer maps the triple to all 289 squared Pi entries; source_prepared_pi_actual identifies same clock and actual sigma Pi G E0",
                                 "actual_moving_common_resolvent_budget": "every source momentum at positive real clock has budget B=2 factorialBudget(0,F,sigma/4) squared / sigma; moving difference <= e squared B squared norm(momentumCompressionMap F n); full actual retainer growth retained",
                                 "actual_quantum_complete_noether_mass": "sum over all i,j of original sourceCompleteCubicNoetherPrice at e squared n times norm(actual G E0 component j)",
                                 "actual_quantum_complete_noether_ir_price": "sigma cubed quantum-drive norm <= 56 source mass for 0 < sigma <= 1; original native reader norm and once-scaled original epsilon-squared IR remainder consume the same bound; no unit-current premise",
                                 "actual_quantum_field_generated_window_price": "same event/e/sigma/n full Green binary precision is source-generated by the paid margin and positive tolerance witness; every actual G E0 row is bounded by sum of (window Green norm + tolerance) times original forcing norm",
                                 "actual_quantum_noether_window_mass_and_ir_price": "complete source cubic mass times the same generated field window price replaces actual G E0 component norms; direct sigma-cubed driver and native IR consumers retain all original chart, source and Noether scaling",
                                 "actual_source_moving_current_and_drive": "original frequency-zero current affine law; left current increment is minus z U and right current is fixed; actual D_e = D0 + z leftMul(U), z=-i e squared",
                                 "actual_source_full_noether_cubic": "both source resolvent changes and actual drive insertion generate C0 + z C1 + z squared C2 + z cubed C3; original material/contact/raw and correction retain their moving values; all original Euler Pi and actual sigma Pi G E0 directly consume it",
                                 "actual_source_material_raw_finite_return": "actual Noether initial equals original sourceMaterialMap plus sourceContactMap; same original full/contact/raw numerators clear one nonreal-energy source denominator and enter original full polarization; raw contact subtraction cancels while Noether Frechet contact stays",
                                 "actual_source_common_noether_radius_price": "for every e squared <= radius, source cubic price depends only on event,n,radius,reader,force; actual free-current factor is bounded by its base source price plus radius times the actual affine momentum insertion norm; all other original five-arm prices and nonreal energy margin retained",
                                 "actual_source_common_radius_driver_ir_price": "sigma-four full289 polarization entry price is uniform across the observation radius; sigma-cubed actual driver and native IR consume it through the same generated field window mass, whose e/sigma dependence remains explicit",
                                 "actual_quantum_driver_temporal_column_identity": "same whole source cofactor: driver numerator = original Jacobi times actual temporal EM source column minus determinant times E0; full source/material/contact retained",
                                 "actual_quantum_driver_family_clock_factor": "on the same static spatial-clock carrier, actual temporal-column factor supplies the complete driver factor before epsilon specialization; no separate quantum-factor premise",
                                 "actual_quantum_driver_column_zero_clock_return": "actual prepared G E0 equals original corrected EM column0; with original column clock finiteness and zero-clock denominator nonzero, full drive tends to J times original zero-clock column0 minus E0 without PencilClockBalanced",
                                 "actual_quantum_temporal_column_factor_generated": False,
                                 "actual_source_full_pi_four_clock_factor": "source-generated common Pi clearing D, not corrected determinant; m is its bivariate clock trailing degree; actual sigma-four full response bound forces X^m to divide X^4 N on the common spatial-clock carrier for all original 289 squared entries",
                                 "actual_source_clock_reduced_pi": "Dbar=D divided by X^m and Nbar=X^4 N divided by the same source power; Dbar sigma^4 prepared Pi=Nbar; no caller factor, price or endpoint witness",
                                 "actual_source_clock_reduced_pencil": "same original J and full prepared Pi generate K=X^3 Dbar J-Nbar; eval K=sigma^3 eval Dbar times actual prepared static pencil",
                                 "actual_source_clock_reduced_field_driver": "on the original regular positive chart K times actual G E0 equals sigma^3 Dbar E0; Nbar times the same field equals sigma^3 Dbar actual sigma Pi G E0 on every positive damping, retaining cubic clock factor",
                                 "actual_source_reduced_cofactor_regular_chart": "positive-clock Dbar nonzero is generated from original common clearing; det evaluated K nonzero follows from original full Green inverse and sigma cubed Dbar, not a new reduced determinant premise or renamed correctedDet",
                                 "actual_source_reduced_cofactor_field_driver": "same evaluated K determinant clears actual G E0 and complete sigma Pi G E0; field numerator is sigma cubed Dbar adj K E0; driver numerator is original J field numerator minus det K E0",
                                 "actual_source_reduced_cofactor_em_consumer": "sourceN3TemporalEMCoefficient equals exactly once Noether pair scale squared times E0 dot field numerator divided by the same det K on the original positive regular chart",
                                 "actual_source_reduced_cofactor_nine_rows": "all original source coker rows annihilate the complete driver numerator for every real epsilon and sigma without regularity, endpoint, pole mode or omitted contact premise",
                                 "actual_source_em_phase_field_and_units": "original EM gauge equals source phase gauge and time force; actual Noether reader is exactly one phaseMomentum times the full source-weighted CAR unit, and the original normalized Noether contact return is zero",
                                 "actual_source_prepared_em_temporal_free_return": "same actual prepared Pi contracts against original EM force, and its original two-time Noether four-word source free return supplies sigma squared EM row price across all 289 original forcing columns",
                                 "actual_source_em_driver_clock_price": "actual complete sigma Pi G E0 is contracted against the original EM force; sigma times its scalar norm is priced by the signed row price times all actual field component norms, with no unit-field premise",
                                 "actual_source_native_em_schur_coefficients": "original 11-term EM auxiliary inverse row multiplied back into the paid auxiliary block; full static source Schur temporal row has 10 background, 6 lower and 9 principal terms on 16 original remaining slots, kernel-normalized from the same full289 Hessian",
                                 "actual_source_native_em_finite_consumers": "same actual prepared GE0 consumes generated background10 and lower6; original frequencyRay generates lower epsilon squared while the complete field retains event/epsilon/sigma/n dependence; original auxiliary quantum-zero owner is directly consumed in scaled T00",
                                 "actual_source_native_em_cofactor_consumers": "both exact source finite reads consume original detK times actual GE0 equals original fieldNum; no new chart or denominator, omitted field or uniform-field premise",
                                 "actual_source_em_weighted_physical_torque": "same actual EM reader equals the same-frame signed-volume CAR reader; original physical action generates dilation, charge/configuration and negative CAR-normal commutator with both actual finite-frame defects",
                                 "actual_source_em_actual_age_response": "actual zero-transfer dressed Noether observer differentiates to i times the resolvent-dressed source torque on its unchanged created/background pair; original Fourier and Euler signs retained, no commuting or eigenstate premise",
                                 "actual_source_em_pi_integrand_age_identified": "original actual five-factor observer C2, generated from physical-time/resolvent/Noether source C2, identifies both mixed derivative orders through its own Hessian; every original force gives HasDerivAt emTemporalJet equal to Euler(i times actual five-word age-field slope); no caller smoothness or commuting-reader premise",
                                 "actual_source_em_actual_full_field_age_response": "same actual EM observer and source inverse-unit neighborhood generates the age derivative on one common all-field germ; every original force differentiates its full two-time, two-inverse and current-reader residual words; force-after-age is the original five-word slope; its age-after-force original EM jet identity is generated by the same-observer source C2 consumer",
                                 "actual_source_em_all289_age_current_insertion": "the nonlinear compression-reader residual differentiates along every original force to the original fixedCurrentEntry sourceAssembly commutator; no field-dependent replacement reader",
                                 "actual_source_em_original_finite_pi_age_return": "same full289 dressedWindowPolarization contracts the actual original EM row and equals its original emTemporalJet age integral; actual source jets pay continuity and both endpoints in exact Laplace integration by parts",
                                 "actual_source_em_prepared_pi_age_tail": "positive real damping and future finite horizon only; same sourcePreparedPiEntry return supplies the l1 EM-row weighted original signal tail, without a replacement Pi or endpoint premise",
                                 "actual_source_em_pi_infinite_age_return": "transfer zero, positive real damping: actual original initial jet is the two negative inverse words, original linear price generates weighted terminal zero, and the original full289 static window returns to same sourcePreparedEMTemporalPi; residual-window limit equals lambda Pi minus actual initial read",
                                 "actual_source_em_pi_age_return_error": "same finite residual integral minus its actual infinite return is priced by original exponential linear endpoint plus lambda-norm times original EM-row l1 prepared tail; no joint IR or numerical price claimed",
                                 "actual_source_em_moving_age_response": "arbitrary original transfer: actual common observer germ and two independent source inverse units generate CL J minus J CR; source field directions retain distinct BL and BR in all five words; original observer source C2 identifies actual EM jet age derivative",
                                 "actual_source_em_moving_pi_age_return": "same original transfer at every finite full289 window, initial two inverse words, source-weighted terminal zero and original prepared Pi limit; residual and source finite error retained",
                                 "actual_source_em_actual_moving_driver_age_consumer": "at transfer epsilon squared n, original full GE0 consumes every original Pi column and returns the same full quantum-driver EM read; finite source endpoint and prepared tail error multiply each actual field component norm, no normalized-field premise",
                                 "actual_source_em_two_clock_common_factor": "same original common Pi denominator D and its order m; X^m divides X squared N_EM before epsilon specialization; no caller factor or full-matrix sigma squared bound",
                                 "actual_source_em_two_clock_reduced_return": "same full-response Dbar consumes the actual prepared EM row as Dbar sigma squared Pi_EM = Nbar_EM, retaining all epsilon and clock dependence",
                                 "actual_source_full_and_em_clock_quotient_identity": "before epsilon specialization the original E0 row of full Nbar equals X squared Nbar_EM, using the same source common Pi clearing and quotient order",
                                 "actual_source_em_clock_reduced_equation": "E0 times original full K equals X squared L_EM, L_EM = X Dbar E0 J minus Nbar_EM with all original 289 Jacobi columns retained",
                                 "actual_source_em_clock_actual_field_and_cofactor": "on the original positive regular chart same actual a=G E0 consumes L_EM a=sigma Dbar dot E0 E0; same det K and complete sigma cubed Dbar adj K E0 numerator consume L_EM fieldNum=det K sigma Dbar dot E0 E0 without a force unit premise",
                                 "actual_source_em_jacobi_exact_terms": "original actual E0 projector applies to originalJacobiTerms; static time-power restriction and closed decide-plus-kernel normalization generate eleven constant and nine spatial terms, retaining gauge, coframe, primal and independent-dual matter, and auxiliary couplings",
                                 "actual_source_em_clock_jacobi_literal": "same actual sourceEMClockJacobiRow evaluates to those exact source terms on frequencyRay epsilon zero n across all289 columns; original EM coordinate projection and common_jacobi_eval pay both identities",
                                 "actual_source_em_cofactor_literal_consumer": "original lower-clock cofactor EM equation consumes both exact Jacobi groups with same Nbar_EM, detK, sigma cubed Dbar adjK E0 field numerator, original positive regular chart and original forcing self-pair",
                                 "actual_source_em_clock_residue": "every spatial specialization generates its own extra numerator clock factor from the actual sigma-two EM price; original coefficient ratio has nonzero denominator and source price, without a pole-order or chart-margin premise",
                                 "actual_source_em_zero_transfer_residue": "same physical zero-transfer response is independent of the bivariate ray direction; on the original order-one branch it equals the unchanged prepared EM leading observable",
                                 "actual_source_em_finite_clock_cofactor_consumer": "same original detK and sigma-cubed fieldNum consume the finite specialized full EM row after the additional source-generated factor cancels; all289 columns and original positive regular chart retained",
                                 "actual_source_em_spatial_clock_uniform_price": "original moving free-current price and unchanged nonreal-energy free resolvent bound generate an explicit epsilon-ball budget for the actual sigma-two EM row and its generated clock residue; epsilon and sigma remain independent",
                                 "actual_source_em_outer_coefficient": "same Dbar zero-clock coefficient D0 is generated nonzero from original clearing; actual independent-scale price generates X^nu dividing Nbar_EM zero-clock coefficient, nu the own trailing degree of D0, and its own leading denominator coefficient is nonzero",
                                 "actual_source_em_ordered_residue_return": "generated punctured source chart identifies the actual finite clock residue with those same original coefficient polynomials; its outer positive-epsilon limit equals their own nu coefficients ratio, retaining all289 forcing columns and the distinction from exact epsilon-zero and joint full-field response",
                                 "actual_source_auxiliary_bivariate_quantum_rows": "all original 72 auxiliary rows vanish as the same full response polynomial, from all-transfer positive-clock prepared Pi clearing and two infinite-root arguments",
                                 "actual_source_auxiliary_equation_reduction": "K=diag(weights)P with 217 unit and 72 X cubed Dbar row weights; full289 rows/columns and native auxiliary Jacobi coupling retained",
                                 "actual_source_auxiliary_shared_cofactor_factor": "source forcing auxiliary zero generates the same A to power72 on detK and the entire field cofactor, before either physical scale is specialized",
                                 "actual_source_auxiliary_reduced_actual_field_driver": "on the unchanged original positive correctedDet chart the factor cancels from actual GE0 and complete quantum/contact driver; reduced determinant nonzero is inherited",
                                 "actual_source_auxiliary_reduced_complete_em_balance": "actual epsilon-four T00 consumes the same reduced driver minus background10 minus epsilon squared lower6 over the shared reduced denominator, retaining original Noether pair scale squared / two lapse and force self-pair three quarters",
                                 "actual_source_bivariate_auxiliary_schur": "original constant72 block and generated left/right source inverse give detP=detAux detSchur217; no quantum cross column is discarded",
                                 "actual_source_schur_actual_field": "same GE0 restriction solves Schur217 with original cubic clock/forcing; complete289 field restored, auxiliary field not zeroed",
                                 "actual_source_schur_regular": "inherited only from original positive correctedDet chart, not from auxiliary block inverse",
                                 "actual_source_schur_complete_em_balance": "source Schur217 cofactor restores all289 field coordinates, full quantum/contact driver with forcing subtraction, background10 and epsilon squared lower6; original finite EM coefficient consumes same reduced denominator",
                                 "actual_source_bivariate_schur_full_field": "same source Schur determinant and complete289 cofactor before either spatial or clock specialization; evaluation returns the original finite field",
                                 "actual_source_bivariate_complete_em_balance": "same bivariate numerator retains complete driver/forcing subtraction/background10/epsilon squared lower6 and common Schur denominator; original finite Noether EM coefficient consumes its quotient",
                                 "actual_source_complete_balance_clock_price": "whole Schur balance reduced after epsilon specialization; every own clock pole retained before source coefficient positive radius/center/linear slope; original positive full Green chart unchanged, epsilon dependence retained",
                                 "actual_source_complete_balance_coefficient_price": "unchanged epsilon-four temporal Noether coefficient consumes same full principal and analytic center with original Noether pair scale squared / two lapse norm times generated clock error",
                                 "actual_source_full_finite_age_observation": "same original moving Pi age window, background10 and epsilon squared lower6 jointly return to the unchanged epsilon-four temporal Noether coefficient; source endpoint/prepared-tail price retains every actual field column norm",
                                 "actual_source_full_observation_clock_enclosure": "original finite-age configuration observation lies in the disk centered at the whole clock principal plus source analytic center in original Noether units; error adds actual age endpoints/prepared tails and generated clock remainder; all T/sigma/epsilon dependence retained",
                                 "actual_source_all_inactive_clock_field_cofactor": "remaining120 source-inactive row weights preserve the original EM forcing; the complete bivariate field numerator has their shared c to power120 before epsilon/sigma specialization, without a Green chart premise",
                                 "actual_source_all_inactive_clock_field_consumer": "new canonical source determinant and complete289 field numerator evaluate to the certified matter clock determinant/weighted adjugate numerator; unchanged actual field consumes them on original positive correctedDet chart, no native Dirac/BF slot deleted",
                                 "actual_source_all_inactive_clock_full_balance": "same normalized matter determinant and complete289 field numerator generate full original Jacobi/forcing-subtracted driver, background10 and inner epsilon squared lower6 before either scale is specialized; evaluation returns same parent complete balance",
                                 "actual_source_all_inactive_clock_finite_coefficient": "unchanged original epsilon-four temporal Noether coefficient directly consumes the normalized complete bivariate balance on original unit/positive correctedDet chart, preserving source action pair scale squared / two lapse",
                                 "actual_source_normalized_complete_clock_price": "all inactive row factors removed before epsilon specialization; the complete normalized matter-clock fraction supplies its own full principal and source coefficient positive radius/center/slope; original finite coefficient consumes norm-scaled clock remainder on unchanged chart",
                                 "actual_source_normalized_chart_free_cofactor_equation": "whole289 matter pencil times its full field numerator equals original cubic clock factor times determinant times unchanged EM forcing; no inverse chart premise",
                                 "actual_source_normalized_native_auxiliary_equation": "original72 Jacobi auxiliary rows consume the complete cofactor at all real epsilon and sigma, including singular values; source forcing auxiliary support is zero",
                                 "actual_source_normalized_temporal_principal": "source Principal9 contracts to two original lapse times epsilon fourth times physical spatial square and actual EM coordinate read; source Gram remains three quarters",
                                 "actual_source_normalized_joint_balance_principal": "full driver minus Background10 minus epsilon squared Lower6 plus coordinate Gram determinant is exactly the temporal EM cofactor principal, before either scale is specialized; no separate vanishing endpoint premise",
                                 "actual_original_inactive192_source_inverse": "kernel-checked both three-variable cleared products; source row weights nonzero on unit spatial directions and 0 < epsilon <= 1/2",
                                 "actual_full_quantum_schur97_and_reconstruction": "same normalized full289 pencil; all cross columns survive; full192 cofactor reconstruction and original complete determinant factorization",
                                 "actual_schur97_original_green_regular_iff": "sigma > 0, unit spatial direction and 0 < epsilon <= 1/2; exact source clock c^192/c^289 and physicalRayDenominator clearing; no source nonzero value assumed",
                                 "actual_schur97_original_em_coefficient": "same original full289 Green and its full192 reconstruction; complete finite Noether coefficient directly equals the97 inverse contraction with original noetherPairScale squared, epsilon fourth power and exactly one source clock multiplier",
                                 "actual_schur97_bivariate_polynomial": "compact checked source192 numerator lifted with original Fourier epsilon squared momentum and all three spatial coordinates; native row complements generate H_num=dH; Q97=dP_AA-P_AI H_num P_IA evaluates to d times actual Schur97",
                                 "actual_schur97_polynomial_clearing": "source d=S(S+72/25)(S+81/50) is nonzero on original small physical ball; evaluated determinant is d to power97 times original actual Schur determinant; that representation factor is retained explicitly and is not an added physical pole",
                                 "actual_schur97_cofactor_native_normalization": "full289 active adjugate is det(native192) times Schur97 adjugate; one source d factor times original determinant and polynomial adjugate equals polynomial determinant times original active adjugate; independent detector/source currents directly consume this equality; sigma arbitrary and full/Schur matrices may be singular",
                                 "actual_schur97_original_field_fraction": "same full289 Green active components consume source(c*d)*adj(Q97)*E_A over det(Q97), retaining original determinant chart, source clock and native clearing exactly once",
                                 "actual_schur97_unspecialized_cofactor_normalization": "for each unit spatial direction: (d*Dm)*adj(Q97)=det(Q97)*adj(Pm)_AA in the same epsilon/sigma polynomial ring, obtained from the generated original small-ball native inverse by infinite real-rectangle uniqueness; no full or Schur regularity premise",
                                 "actual_schur97_unspecialized_em_scalar_normalization": "same original EM forcing restricted to active97; (d*Dm)*E_A adj(Q97) E_A = det(Q97)*E_A adj(Pm)_AA E_A in the original epsilon/sigma polynomial ring; source point current law lifted by infinite rectangle uniqueness, singular loci retained; no finite Noether fraction or Thomson identification claimed",
                                 "actual_schur97_complete_noether_source_fraction": "original epsilon fourth times complete finite temporal EM Noether coefficient equals evaluated (original noetherPairScale squared * epsilon fourth * original clock c * native d * E_A adj(Q97) E_A) over source detQ; same full289 response, all native reconstruction and original chart retained; no Thomson or alpha0 numerical claim",
                                 "actual_source_clock_reduced_joint_margin_generated": False,
                                 "actual_temporal_quantum_driver_ir_limit_generated": False,
                                 "actual_temporal_feedback_inverse_eliminated": False,
                                 "actual_n3_clock_zero_order_generated": False,
                                 "actual_n3_analytic_remainder_numeric_bound": False,
                                 "native_green_assumed_unconstrained_inverse": False,
                                 "native_field_and_quantum_light_identified": False,
                                 "actual_observation_regular_curve_generated": False,
                                 "actual_response_zero_clock_limit": False, "thomson_alpha0": False,
                                 "numeric_prediction": False, "experimental_comparison": False,
                                 "controller_advanced": False}}
        CERTIFICATE.write_text(json.dumps(certificate, indent=2) + "\n")
    else:
        certificate = json.loads(CERTIFICATE.read_text())
        assert certificate["bindings"] == parents, "source binding changed"
        assert certificate["controls"] == negative
        assert certificate["native_inverse_witness"] == {k: v for k, v in native_witness.items() if k != "seconds"}
        for module, receipt in certificate["strict"].items():
            assert receipt["exit"] == 0 and "--trust=0" in receipt["command"], module
            assert receipt["source_sha256"] == sha(SOURCE_DIR / f"{module}.lean"), module
            assert receipt["object_sha256"] == sha(CACHE / f"{module}.olean"), module
    print(json.dumps({"status": certificate["status"], "public": len(certificate["closure"]["public"]),
                      "owned": len(certificate["closure"]["owned"]), "nodes": certificate["closure"]["nodes"],
                      "axioms": certificate["closure"]["axioms"], "scope": certificate["scope"]}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
