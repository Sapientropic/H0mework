"""Cross the frozen independent native-effect matrices through the other source path."""
from fractions import Fraction as F
import argparse
import json
from pathlib import Path

import decode

HERE = Path(__file__).resolve().parent
ROOT = decode.primary.ROOT
require = decode.primary.require


def verify():
    frozen = {name: decode.primary.frozen(HERE/name) for name in
              ("verify.py", "decode.py", "decoder.json", "independent_decode.py", "independent-decoder.json",
               "criterion.md", "sources.json")}
    main = json.loads((HERE/"decoder.json").read_text())
    independent = json.loads((HERE/"independent-decoder.json").read_text())
    require(main["version"] == independent["version"] == decode.VERSION, "WRONG_VERSION")
    require(main["source_manifest_sha256"] == independent["criterion_freeze"]["sources_sha256"] ==
            frozen["sources.json"]["sha256"], "SOURCE_IDENTITY_DIFFERS")
    require(main["criterion_freeze"]["sha256"] == independent["criterion_freeze"]["criterion_sha256"] ==
            frozen["criterion.md"]["sha256"], "CRITERION_IDENTITY_DIFFERS")
    require(main["program_freeze"]["sha256"] == frozen["decode.py"]["sha256"] and
            independent["executable_freeze"]["program_sha256"] == frozen["independent_decode.py"]["sha256"],
            "EXECUTABLE_CHANGED")
    for path, digest in independent["bindings"].items():
        target = (ROOT/path).resolve()
        require(target.is_relative_to(ROOT) and decode.primary.digest(target) == digest, "BINDING_CHANGED")
    for flag in ("PC_on_retarder_identified", "recipe_controls_prove_argmax", "apparatus_optimum_verified",
                 "actual_epoch_required_by_original_nominal_gate", "controller_advance"):
        require(main[flag] is False and independent[flag] is False, "SCOPE_CHANGED")
    require(all(value is True for value in independent["controls"].values()), "FAILED_INDEPENDENT_CONTROL")
    require(independent["access_disclosure"]["primary_decoder_source_read"] is False and
            independent["access_disclosure"]["primary_decoder_output_read"] is False and
            independent["other_implementation_output_used_as_input"] is False, "BLIND_FIRST_RUN_CHANGED")
    recipes = decode.recipes((HERE/"source-and-receiver-recipe.txt").read_text())
    require(set(recipes) == set(main["controls"]) == {x["member"] for x in independent["recipes"]} and
            len(independent["recipes"]) == 4, "SOURCE_RECIPE_SET_CHANGED")
    cases = []
    for recipe in independent["recipes"]:
        expected = decode.demonstrate(recipes[recipe["member"]])
        require(expected["pump_mechanical_degree"] == F(recipe["native_initial_commands"]["PumpHWP"]["degrees"]),
                "PUMP_COMMAND_DIFFERS")
        for row in expected["rows"]:
            foreign = recipe["stations"][row["side"].lower()][row["setting"]]
            for local, remote in (("HWP1", "HWP1_degree"), ("HWP2", "HWP2_degree"),
                                  ("QWP", "QWP_degree"), ("generated_effective_angle", "effective_degree")):
                require(row[local] == F(foreign[remote]), "NATIVE_CONTROL_DIFFERS")
            cases.append(foreign)
    require(len(cases) == 16 and len(independent["general_controls"]) == 60, "INCOMPLETE_MATRIX_CROSS")
    cases += independent["general_controls"]
    errors = []
    for row in cases:
        args = [F(row[key]) for key in ("HWP1_degree", "HWP2_degree", "QWP_degree")]
        foreign = [[complex(*cell) for cell in line] for line in row["native_V_effect"]]
        discrepancy = decode.distance(decode.native_effect(*args), foreign)
        require(discrepancy < 2e-12, "NATIVE_MATRIX_CROSS_FAILED")
        errors.append(discrepancy)
    return {"schema": "p23-receiver-control-source-matrix-cross/v1", "version": decode.VERSION,
            "status": "INDEPENDENT_NATIVE_EFFECT_AND_SOURCE_CONTROL_CROSS_PASSED", "bindings": frozen,
            "recipe_effects": 16, "general_effects": 60, "max_matrix_difference": max(errors),
            "first_results_frozen_before_comparison": True, "source_recipe_inputs_exactly_agree": True,
            "public_nominal_PCoff_effect_verified": True, "apparatus_optimum_verified": False,
            "PC_on_retarder_identified": False, "actual_hardware_identity_verified": False,
            "controller_advance": False, "retrospective": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE/"verification.json")
    args = parser.parse_args()
    require(not args.output.exists(), "OUTPUT_EXISTS_USE_NEW_PATH")
    result = verify()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True, allow_nan=False)+"\n")
    print(json.dumps({"status": result["status"], "effects": 76,
                      "max_matrix_difference": result["max_matrix_difference"]}))
