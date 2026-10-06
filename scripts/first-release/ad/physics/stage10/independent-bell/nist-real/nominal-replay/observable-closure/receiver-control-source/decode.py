"""Parse inert public recipe constants and independently build their nominal Jones effects."""
from fractions import Fraction as F
import argparse
import ast
import json
import math
from pathlib import Path
import re
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import primary

HERE = Path(__file__).resolve().parent
VERSION = "p23-receiver-control-source-rc0001"
NAMES = {"AHWP1", "AHWP2", "AQWP1", "BHWP1", "BHWP2", "BQWP1", "Angles", "Alice_angles", "Bob_angles"}


def expression(node, environment):
    if isinstance(node, ast.Constant) and type(node.value) in (int, float):
        return F(str(node.value))
    if isinstance(node, ast.Name) and node.id in environment:
        return environment[node.id]
    if isinstance(node, ast.List):
        return [expression(x, environment) for x in node.elts]
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
        value = expression(node.operand, environment)
        factor = -1 if isinstance(node.op, ast.USub) else 1
        return [factor*x for x in value] if isinstance(value, list) else factor*value
    if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute) and isinstance(node.func.value, ast.Name) and
            node.func.value.id == "np" and node.func.attr == "array" and len(node.args) == 1 and not node.keywords):
        result = expression(node.args[0], environment)
        primary.require(isinstance(result, list), "ARRAY_REQUIRES_LITERAL_VECTOR")
        return result
    if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.Div)):
        a, b = expression(node.left, environment), expression(node.right, environment)
        def operation(x, y):
            if isinstance(node.op, ast.Add):
                return x+y
            if isinstance(node.op, ast.Sub):
                return x-y
            if isinstance(node.op, ast.Mult):
                return x*y
            primary.require(y != 0, "ZERO_SOURCE_DIVISOR")
            return x/y
        if isinstance(a, list) or isinstance(b, list):
            length = len(a) if isinstance(a, list) else len(b)
            primary.require(not isinstance(a, list) or not isinstance(b, list) or len(a) == len(b), "INCONSISTENT_VECTOR_SHAPE")
            return [operation(a[i] if isinstance(a, list) else a, b[i] if isinstance(b, list) else b) for i in range(length)]
        return operation(a, b)
    raise ValueError("UNSUPPORTED_NONDATA_SOURCE_EXPRESSION")


def recipes(text):
    packets = {}
    chunks = text.split("MEMBER ")[1:]
    for chunk in chunks:
        name = chunk.splitlines()[0].strip()
        env, moves = {}, {}
        for line in chunk.splitlines()[1:]:
            match = re.fullmatch(r"\d+: (.*)", line)
            if match is None:
                continue
            code = match[1].split("#", 1)[0].strip()
            assignment = re.match(r"([A-Za-z_][A-Za-z_0-9]*)\s*=\s*(.*)", code)
            if assignment and assignment[1] in NAMES:
                env[assignment[1]] = expression(ast.parse(assignment[2], mode="eval").body, env)
            move = re.fullmatch(r"(mc_source|mc_alice|mc_bob)\.goto\('([A-Za-z0-9]+)',\s*(.*)\)", code)
            if move:
                key = (move[1], move[2])
                primary.require(key not in moves, "AMBIGUOUS_SOURCE_MOVE")
                moves[key] = expression(ast.parse(move[3], mode="eval").body, env)
        required = {"AHWP1", "AHWP2", "AQWP1", "BHWP1", "BHWP2", "BQWP1", "Alice_angles", "Bob_angles"}
        if required <= set(env):
            expected = {(object_name, side+element) for object_name, side in (("mc_alice", "Alice"), ("mc_bob", "Bob"))
                        for element in ("HWP1", "HWP2", "QWP1")} | {("mc_source", "PumpHWP")}
            primary.require(set(moves) == expected, "INCOMPLETE_NATIVE_CONTROL_MOVES")
            primary.require(all(isinstance(env[key], list) and len(env[key]) == 2
                                for key in ("Alice_angles", "Bob_angles")), "INVALID_SETTING_VECTOR")
            for object_name, side, prefix in (("mc_alice", "Alice", "A"), ("mc_bob", "Bob", "B")):
                primary.require(moves[object_name, side+"HWP2"] == env[prefix+"HWP2"] and
                                moves[object_name, side+"HWP1"] == env[prefix+"HWP1"], "NATIVE_OFFSET_COMMAND_MISMATCH")
                primary.require(moves[object_name, side+"QWP1"] == 2*env[prefix+"HWP2"]+(90 if side == "Bob" else 0),
                                "NATIVE_QWP_COMMAND_MISMATCH")
            packets[name] = {"constants": env, "pump_HWP": moves["mc_source", "PumpHWP"],
                             "QWP_moves": {"Alice": moves["mc_alice", "AliceQWP1"], "Bob": moves["mc_bob", "BobQWP1"]}}
    primary.require(packets, "NO_COMPLETE_SOURCE_RECIPE")
    return packets


def mul(a, b):
    return [[sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


def adjoint(a):
    return [[a[j][i].conjugate() for j in range(2)] for i in range(2)]


def hwp(angle):
    s, c = math.sin(2*math.radians(float(angle))), math.cos(2*math.radians(float(angle)))
    return [[complex(c), complex(s)], [complex(s), complex(-c)]]


def qwp(angle):
    H = hwp(angle)
    return [[(int(i == j)-1j*H[i][j])/math.sqrt(2) for j in range(2)] for i in range(2)]


def native_effect(m, o, q, port=1):
    primary.require(port in (0, 1), "INVALID_PHYSICAL_PORT")
    U = mul(mul(hwp(o), qwp(q)), hwp(m))
    dagger = adjoint(U)
    vector = [dagger[i][port] for i in range(2)]
    return [[vector[i]*vector[j].conjugate() for j in range(2)] for i in range(2)]


def projector(angle):
    v = [math.sin(math.radians(float(angle))), math.cos(math.radians(float(angle)))]
    return [[complex(v[i]*v[j]) for j in range(2)] for i in range(2)]


def distance(a, b):
    return max(abs(a[i][j]-b[i][j]) for i in range(2) for j in range(2))


def serial(value):
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {key: serial(item) for key, item in value.items()}
    if isinstance(value, (tuple, list)):
        return [serial(item) for item in value]
    return value


def demonstrate(packet):
    c = packet["constants"]
    rows = []
    for side in ("Alice", "Bob"):
        prefix = "A" if side == "Alice" else "B"
        o = c[prefix+"HWP2"]
        q = packet["QWP_moves"][side]
        for index, m in enumerate(c[side+"_angles"]):
            angle = 2*(o-m)
            discrepancy = distance(native_effect(m, o, q), projector(angle))
            primary.require(discrepancy < 2e-12, "NATIVE_EFFECT_MAPPING_FAILED")
            rows.append({"side": side, "setting": index, "HWP1": m, "HWP2": o, "QWP": q,
                         "generated_effective_angle": angle, "native_Jones_error": discrepancy})
    return {"pump_mechanical_degree": packet["pump_HWP"], "pump_polarization_degree": 2*packet["pump_HWP"], "rows": rows}


def run():
    executable = primary.frozen(__file__)
    criterion = primary.frozen(HERE/"criterion.md")
    blocks = re.findall(r"<!-- RC-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- RC-FROZEN-END -->",
                        (HERE/"criterion.md").read_text(), re.S)
    primary.require(len(blocks) == 1, "NONUNIQUE_RC_CRITERION")
    config = json.loads(blocks[0])
    primary.require(config["version"] == VERSION and config["status"] == "frozen_before_execution" and
                    config["physical_click_port"] == "V" and config["measurement_scope"] == "ideal_nominal_PCoff_static_waveplate_recipe" and
                    config["mechanical_to_effective_angle"] == "2*(HWP2-HWP1)" and
                    config["recipe_controls_prove_argmax"] is False, "RC_CONTRACT_CHANGED")
    manifest_path = HERE/"sources.json"
    primary.frozen(manifest_path)
    manifest = json.loads(manifest_path.read_text())
    primary.require(manifest["schema"] == "p23-public-receiver-control-source-review/v1" and
                    next(x for x in manifest["archives"] if x["name"] == "bell_client.zip")["sha256"] ==
                    config["source_archive_sha256"], "SOURCE_ARCHIVE_IDENTITY_CHANGED")
    for item in manifest["extracts"]:
        primary.require(primary.digest(HERE/item["path"]) == item["sha256"], "SOURCE_EXTRACT_CHANGED")
    packet = recipes((HERE/"source-and-receiver-recipe.txt").read_text())
    controls = {name: demonstrate(value) for name, value in packet.items()}
    general = []
    for m, o in ((F(13, 7), F(-5, 3)), (F(-17, 4), F(9, 2)), (F(26), F(4)), (F(-31), F(-8))):
        for shift in (F(0), F(90)):
            discrepancy = distance(native_effect(m, o, 2*o+shift), projector(2*(o-m)))
            primary.require(discrepancy < 2e-12, "GENERAL_NATIVE_PORT_MAPPING_FAILED")
            general.append({"m": m, "o": o, "QWP_quarter_shift": shift, "error": discrepancy})
    return serial({"schema": "p23-public-native-receiver-decoder/v1", "version": VERSION,
                           "criterion_freeze": criterion, "program_freeze": executable, "source_manifest_sha256": primary.digest(manifest_path),
                           "controls": controls, "general_controls": general, "source_scripts_imported_or_executed": False,
                           "hardware_connections_opened": False, "recipe_controls_prove_argmax": False,
                           "actual_epoch_required_by_original_nominal_gate": False, "apparatus_optimum_verified": False,
                           "native_PCoff_effect_identity_numerically_verified": True, "PC_on_retarder_identified": False,
                           "controller_advance": False, "retrospective": True})


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE/"decoder.json")
    args = parser.parse_args()
    primary.require(not args.output.exists(), "OUTPUT_EXISTS_USE_NEW_PATH")
    result = run()
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True, allow_nan=False)+"\n")
    print(json.dumps({"status": "SOURCE_RECIPE_AND_NATIVE_PCoff_EFFECT_VERIFIED", "output": str(args.output)}))
