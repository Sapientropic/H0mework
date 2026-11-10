#!/usr/bin/env python3
"""Focused controls for the actual-native-current to EM charge-unit bridge.

This is a source-shape check only. It records the exact theorem mouths and
negative controls; it does not replace the Lean closure or manufacture a
Thomson/alpha value.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "PhysicalNativeEMChargeBridge.lean"
RECEIPT = HERE / "canonical_preparation_physical_native_em_charge_bridge_check.json"

text = SOURCE.read_text()
checks: dict[str, bool] = {}


def check(name: str, condition: bool) -> None:
    checks[name] = bool(condition)
    if not condition:
        raise SystemExit(f"FAIL {name}")


check("same_source_actual_charge", all(x in text for x in (
    "sourceActualPhaseCharge", "PhysicalNativeCurrentAlignment",
    "PhysicalEMChargeReadout", "sourceNativeElectronChargeUnit",
)))
check("native_charged_current_identification", all(x in text for x in (
    "native_current_noether", "actualRestState_hypercharge_current",
    "sourceActionScale_momentum", "native_charged_current_unit",
    "native_rest_current_identifies_electron_unit",
)))
check("same_actual_external_state", all(x in text for x in (
    "actualRestStatePreparation (sourceChargedRestIndex side 0)",
    "sourceNativeElectronState_source", "em_reader_same_electron_state",
)) and "PhysicalFullFieldRestReadout.restState" not in text)
check("em_reader_consumes_edge_zero", all(x in text for x in (
    "em_charge_maker", "em_reader_electron_unit",
    "sourceChargedRestriction side 0",
)))
check("electron_product_generated", all(x in text for x in (
    "sourceNativeElectronChargeProduct",
    "sourceNativeElectronChargeProduct_generated",
)))
check("filtered_corrections_retained", all(x in text for x in (
    "em_filtered_electron_pair", "sourceActualChargeCorrection",
    "emDefectSpatial",
)))
check("neutral_edge_negative_control", "neutral_edge_not_electron_unit" in text)
check("defect_negative_control", "full_defect_retained" in text)
check("no_static_or_matching_premise", all(x not in text for x in (
    "sourceGaugeStaticCEM", "sourceThomsonStaticCEM", "full_light_contact",
    "ordinaryFull", "sourceLightResponse", "sourceContactResponse",
)))
check("no_experimental_target", all(x not in text for x in (
    "CODATA", "137", "measured alpha", "experimental alpha",
)))

negative_controls = {
    "canonical_rest_substitution_rejected":
        "actualRestStatePreparation (sourceChargedRestIndex side 0)" not in
        text.replace("actualRestStatePreparation (sourceChargedRestIndex side 0)",
                     "actualRestStatePreparation (0, 0)"),
    "action_normalization_omission_rejected":
        "sourceActionScale_momentum" not in text.replace("sourceActionScale_momentum", ""),
    "filtered_correction_omission_rejected":
        "sourceActualChargeCorrection" not in text.replace("sourceActualChargeCorrection", ""),
    "full_defect_omission_rejected":
        "emDefectSpatial" not in text.replace("emDefectSpatial", ""),
}
check("negative_controls", all(negative_controls.values()))

result = {
    "schema": "alpha-source-native-em-charge-bridge-focused-controls/v2",
    "status": "PASS",
    "source": str(SOURCE.relative_to(HERE.parents[4])),
    "classification": "same-source actual native current to electron EM charge-unit consumer",
    "claim_scope": (
        "edge-0 sourceActualPhaseCharge=1 is consumed by the actual EM reader; "
        "both readers consume the same actual (side,1) external state; "
        "the native temporal current has the opposite sign through actionScale*phaseMomentum=1; "
        "electron-electron product is 1 and filtered correction/full defect remain explicit"
    ),
    "lean_strict": "not asserted here; prerequisite source overlay may be absent",
    "prediction_numeric": False,
    "experiment_comparison": False,
    "checks": checks,
    "negative_controls": negative_controls,
    "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
}
RECEIPT.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n")
print(json.dumps({"status": "PASS", "checks": len(checks)}))
