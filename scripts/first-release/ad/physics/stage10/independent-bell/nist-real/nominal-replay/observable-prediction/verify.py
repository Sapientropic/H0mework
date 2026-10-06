#!/usr/bin/env python3
"""Verify the frozen observable predictor with full-mode forward controls."""
from __future__ import annotations

import argparse
import ast
import cmath
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
FREEZE = "be90dbed91730c1bd4049aaecde52fa49c888aa9"
VERSION = "p23-observable-prediction-op0001"
SCHEMA = "p23-observable-prediction-verification/v1"
PRIMARY, INDEPENDENT = "prediction.json", "independent_prediction.json"
PROGRAMS = ("predict.py", "independent.py")
MODELS = ("S1_signal", "independent_OR", "named_M3")
IDENTITY = ("source_mapping_identified", "publication_configuration_identified", "production_admitted")
LEAN_CHAIN = (HERE.parent/"investigation/collected-source/Collection.lean",
              HERE.parent/"collected-response/SourceResponse.lean",
              HERE/"ObservableLaw.lean", HERE/"ObservableConsumer.lean", HERE/"ObservableCertification.lean")


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def relative(path):
    return Path(path).relative_to(ROOT).as_posix()


def same_structure(actual, expected):
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return actual.keys() == expected.keys() and all(same_structure(actual[k], v) for k,v in expected.items())
    if isinstance(expected, list):
        return len(actual) == len(expected) and all(same_structure(a,b) for a,b in zip(actual,expected))
    return actual == expected


def frozen_file(path, commit):
    subprocess.run(["git","merge-base","--is-ancestor",commit,"HEAD"],cwd=ROOT,check=True)
    require(subprocess.check_output(["git","show",commit+":"+relative(path)],cwd=ROOT) == Path(path).read_bytes(),
            "frozen_file_changed:"+relative(path))


def program_freeze(path):
    name = relative(path)
    commit = subprocess.check_output(["git","log","-1","--format=%H","--",name],cwd=ROOT,text=True).strip()
    require(bool(commit), "execution_source_not_committed:"+name)
    subprocess.run(["git","merge-base","--is-ancestor",FREEZE,commit],cwd=ROOT,check=True)
    frozen_file(path,commit)
    return {"commit":commit,"sha256":digest(path)}


def parse_criterion(text):
    begin,end = "<!-- OP-FROZEN-BEGIN -->","<!-- OP-FROZEN-END -->"
    require(text.count(begin) == text.count(end) == 1,"nonunique_observable_criterion")
    blocks = re.findall(r"```json\s*(.*?)\s*```",text,re.S)
    require(len(blocks) == 1,"nonunique_observable_criterion")
    config = json.loads(blocks[0])
    require(config["version"] == VERSION and config["scope"] == "source_generated_collected_HHVV_observable_family",
            "observable_criterion_scope_mismatch")
    require(all(config[k] is False for k in IDENTITY) and config["statistical_verdict_enabled"] is False,
            "observable_family_cannot_admit_empirical_identity")
    require(tuple(config["models"]) == MODELS and config["row_order"] == ["00","01","10","11"] and
            config["calibration_rows"] == [0,1,3] and config["held_out_row"] == 2,"fixed_holdout_contract_mismatch")
    require(config["public_target_role"] == "retrospective_published_rounding_only","public_target_role_mismatch")
    require(type(config["bell_event_files_read"]) is int and config["bell_event_files_read"] == 0,"unexpected_archive_input")
    require(list(map(F,config["paired_update_deg"])) == [F(0),-F(1,20),F(0),F(1,20)],"fixed_update_mismatch")
    return config


def scientific_inputs():
    for name in ("criterion.md","sources.json"):
        frozen_file(HERE/name,FREEZE)
    config = parse_criterion((HERE/"criterion.md").read_text())
    packet = json.loads((HERE/"sources.json").read_text())
    require(packet["schema"] == "p23-observable-prediction-sources/v1" and
            all(packet[k] is False for k in IDENTITY) and packet["private_optimizer_input_required"] is False,
            "source_packet_scope_mismatch")
    for commit in ["40a278fec15e667ad393caa60527e55bc1247ab8"]+packet["source_commits"]:
        subprocess.run(["git","merge-base","--is-ancestor",commit,FREEZE],cwd=ROOT,check=True)
    bindings = {}
    for row in packet["inputs"]:
        path = (ROOT/row["path"]).resolve()
        require(path.is_relative_to(ROOT) and row["path"] not in bindings,"invalid_source_path")
        require(digest(path) == row["sha256"],"source_binding_mismatch:"+row["path"])
        bindings[row["path"]] = row["sha256"]
    for name in ("criterion.md","sources.json"):
        bindings[relative(HERE/name)] = digest(HERE/name)
    return config,bindings


def implementation(path):
    path = Path(path)
    specification = importlib.util.spec_from_file_location("_op_verified_"+path.stem+digest(path)[:12],path)
    module = importlib.util.module_from_spec(specification)
    sys.modules[specification.name] = module
    specification.loader.exec_module(module)
    return module


def printed_percentage(text):
    match = re.fullmatch(r"\s*(\d+)(?:\.(\d+))?\s*%\s*",text)
    require(match is not None,"invalid_printed_percentage")
    digits = len(match.group(2) or "")
    value = F(match.group(1)+("."+match.group(2) if match.group(2) else ""))/100
    require(0 <= value <= 1,"printed_probability_outside_unit_interval")
    half = F(1,200*10**digits)
    return {"printed":text,"unit":"percent","exact_center":str(value),
            "exact_lower":str(value-half),"exact_upper":str(value+half),
            "rounding_half_width":str(half),"counts":None,"denominator":None,
            "statistical_verdict":None,"role":"retrospective_published_rounding_only"}


def det3(rows):
    a,b,c = rows
    return sum(a[i]*(b[(i+1)%3]*c[(i+2)%3]-b[(i+2)%3]*c[(i+1)%3]) for i in range(3))


def solve3(rows, values, tolerance):
    determinant = det3(rows)
    require(abs(determinant) > tolerance,"NOT_IDENTIFIABLE: fixed calibration minor")
    matrix = [list(row)+[value] for row,value in zip(rows,values)]
    for column in range(3):
        pivot = max(range(column,3),key=lambda i:abs(matrix[i][column]))
        matrix[column],matrix[pivot] = matrix[pivot],matrix[column]
        factor = matrix[column][column]
        require(factor != 0,"NOT_IDENTIFIABLE: fixed calibration minor")
        matrix[column] = [x/factor for x in matrix[column]]
        for i in range(3):
            if i != column:
                factor = matrix[i][column]
                matrix[i] = [x-factor*y for x,y in zip(matrix[i],matrix[column])]
    return [row[-1] for row in matrix],determinant


def design(angles):
    return [[math.sin(a)**2*math.sin(b)**2,math.cos(a)**2*math.cos(b)**2,
             2*math.sin(a)*math.cos(a)*math.sin(b)*math.cos(b)]
            for a in angles[:2] for b in angles[2:]]


def corrected(rates,model,background):
    ba,bb = background
    if model == "S1_signal":
        return list(rates["j"])
    if model == "named_M3":
        return [rates["j"][k]-rates["sA"][k//2]*rates["sB"][k%2] for k in range(4)]
    require(model == "independent_OR","unknown_rate_model")
    return [rates["j"][k]-bb*rates["sA"][k//2]-ba*rates["sB"][k%2]+ba*bb for k in range(4)]


def observable_readout(rates,angles,model,background,tolerance):
    rows = design(angles)
    joint = corrected(rates,model,background)
    gram,minor = solve3([rows[k] for k in (0,1,3)],[joint[k] for k in (0,1,3)],tolerance)
    cofactor = [(-1)**i*det3([row for j,row in enumerate(rows) if j != i]) for i in range(4)]
    scale = max(map(abs,cofactor))
    cofactor = [value/scale for value in cofactor]
    prediction = sum(x*y for x,y in zip(rows[2],gram))
    coefficients = []
    for side,axis in (("sA",angles[:2]),("sB",angles[2:])):
        c0,c1 = (math.cos(2*a) for a in axis)
        require(abs(c0-c1) > tolerance,"NOT_IDENTIFIABLE: single effect contrast")
        beta = (rates[side][0]-rates[side][1])/(c0-c1)
        coefficients.extend((rates[side][0]-beta*c0,beta))
    aa,ab,ba,bb = coefficients
    dark_a,dark_b = background
    factor_a,factor_b = ((1-dark_a),(1-dark_b)) if model == "independent_OR" else (1.,1.)
    require(factor_a*factor_b > 0,"NOT_IDENTIFIABLE: certain OR background")
    endpoints = [(aa-dark_a-ab)/factor_a,(aa-dark_a+ab)/factor_a,
                 (ba-dark_b-bb)/factor_b,(ba-dark_b+bb)/factor_b]
    h,v,x = gram
    signal_h,signal_v = h/(factor_a*factor_b),v/(factor_a*factor_b)
    ah,av,bh,bv = endpoints
    loss = [ah,av,bh,bv,ah-signal_h,bh-signal_h,av-signal_v,bv-signal_v,
            1-ah-bh+signal_h-av-bv+signal_v]
    z = h+v+(4*ab*bb if model == "named_M3" else 0)
    derivatives = []
    for own,other in ((angles[1],angles[2:]),(angles[3],angles[:2])):
        derivatives.append(( -z*math.sin(2*own)*(math.cos(2*other[0])-math.cos(2*other[1]))+
                            2*x*math.cos(2*own)*(math.sin(2*other[0])-math.sin(2*other[1])))/2)
    return {"gram":dict(zip(("H","V","X"),gram)),"determinant":minor,
            "held_out_prediction":prediction,"held_out_residual":joint[2]-prediction,
            "cofactor":cofactor,"cofactor_residual":sum(x*y for x,y in zip(cofactor,joint)),
            "psd_slack":h*v-x*x,"loss_slacks":loss,"single_coefficients":coefficients,
            "scale":factor_a*factor_b,"derivatives":derivatives}


def or_branch_table(signal,ba,bb):
    result = []
    for k,pair in enumerate(signal["j"]):
        table = [pair,signal["sA"][k//2]-pair,signal["sB"][k%2]-pair,
                 1-signal["sA"][k//2]-signal["sB"][k%2]+pair]
        observed = [0.,0.,0.,0.]
        for (a,b),weight in zip(((1,1),(1,0),(0,1),(0,0)),table):
            for out_a,out_b in itertools.product((0,1),repeat=2):
                pa = (1. if out_a else 0.) if a else (ba if out_a else 1-ba)
                pb = (1. if out_b else 0.) if b else (bb if out_b else 1-bb)
                index = {(1,1):0,(1,0):1,(0,1):2,(0,0):3}[out_a,out_b]
                observed[index] += weight*pa*pb
        result.append(observed)
    return result


def detect(signal,model,background):
    ba,bb = background
    if model == "independent_OR":
        tables = or_branch_table(signal,ba,bb)
        return {"sA":[tables[0][0]+tables[0][1],tables[2][0]+tables[2][1]],
                "sB":[tables[0][0]+tables[0][2],tables[1][0]+tables[1][2]],
                "j":[table[0] for table in tables]}
    sa,sb = [p+ba for p in signal["sA"]],[p+bb for p in signal["sB"]]
    require(model in ("S1_signal","named_M3"),"unknown_rate_model")
    return {"sA":sa,"sB":sb,"j":[p+(sa[k//2]*sb[k%2] if model == "named_M3" else 0.)
                                      for k,p in enumerate(signal["j"])]}


def ch(rates):
    return math.fsum((*rates["j"][:3],-rates["j"][3],-rates["sA"][0],-rates["sB"][0]))


def source_rates(source,state,angles,q,ua,ub):
    read = [source.amplitude_read(state,(.5-a/math.pi,0),(.5-b/math.pi,0),q,ua,ub)
            for a in angles[:2] for b in angles[2:]]
    return {"sA":[read[0]["sA"],read[2]["sA"]],"sB":[read[0]["sB"],read[1]["sB"]],
            "j":[row["j"] for row in read]}


def close(actual,expected,tolerance):
    return (isinstance(actual,(int,float)) and not isinstance(actual,bool) and math.isfinite(actual)
            and abs(actual-expected) <= tolerance)


def numeric_structure(actual,expected,tolerance):
    if isinstance(expected,dict):
        return isinstance(actual,dict) and expected.keys() <= actual.keys() and all(numeric_structure(actual[k],v,tolerance) for k,v in expected.items())
    if isinstance(expected,list):
        return isinstance(actual,list) and len(actual) == len(expected) and all(numeric_structure(a,b,tolerance) for a,b in zip(actual,expected))
    if isinstance(expected,(float,int)) and not isinstance(expected,bool):
        return close(actual,expected,tolerance)
    return type(actual) is type(expected) and actual == expected


@lru_cache(maxsize=4)
def forward_oracle(fingerprint):
    config,_ = scientific_inputs()
    source = implementation(HERE.parent/"investigation/collected-source/independent.py")
    recipes = {r["name"]:r for r in source.specification()["fixtures"]}
    q,ua,ub,ba,bb = (float(F(config["rates"][k])) for k in ("Q","uA","uB","background_A","background_B"))
    tolerance = float(F(config["singular_absolute_tolerance"]))
    step = float(F(config["derivative_step_radians"]))
    update = [math.radians(float(F(x))) for x in config["paired_update_deg"]]
    rows = {}
    for fixture,p,phase,a,model in itertools.product(config["fixtures"],range(4),config["source_phase_pi"],range(2),MODELS):
        h,v = (float(F(x)) for x in config["preparations"][p]);norm = math.hypot(h,v)
        state = source.state_from_preparation(recipes[fixture],(h/norm,v/norm*cmath.exp(1j*math.pi*float(F(phase)))))
        angles = [math.radians(float(F(x))) for x in config["angles_deg"][a]]
        signal = source_rates(source,state,angles,q,ua,ub)
        rates = detect(signal,model,(ba,bb))
        reconstruction = observable_readout(rates,angles,model,(ba,bb),tolerance)
        finite = []
        for index in (1,3):
            plus,minus = list(angles),list(angles);plus[index] += step;minus[index] -= step
            finite.append((ch(detect(source_rates(source,state,plus,q,ua,ub),model,(ba,bb)))-
                           ch(detect(source_rates(source,state,minus,q,ua,ub),model,(ba,bb))))/(2*step))
        moved = [x+d for x,d in zip(angles,update)]
        direct = ch(detect(source_rates(source,state,moved,q,ua,ub),model,(ba,bb)))-ch(rates)
        def correlation(axis,cosine):
            values = [math.cos(2*x) if cosine else math.sin(2*x) for x in axis]
            return values[0]*values[2]+values[0]*values[3]+values[1]*values[2]-values[1]*values[3]
        g = reconstruction["gram"];co = reconstruction["single_coefficients"]
        z = g["H"]+g["V"]+(4*co[1]*co[3] if model == "named_M3" else 0)
        predicted = (z/4*(correlation(moved,True)-correlation(angles,True))+
                     g["X"]/2*(correlation(moved,False)-correlation(angles,False)))
        objects = source.density_objects(state)
        source_gram = {"H":q*ua*ub*objects["AB"][0][0].real,"V":q*ua*ub*objects["AB"][3][3].real,
                       "X":q*ua*ub*objects["AB"][0][3].real}
        name = f"{fixture}/p{p}/ph{phase}/a{a}/{model}"
        rows[name] = {"fixture":fixture,"preparation_index":p,"phase_pi":phase,"angles_index":a,"model":model,
                      "rates":rates,"signal":signal,"corrected_joint":corrected(rates,model,(ba,bb)),
                      "reconstruction":{k:v for k,v in reconstruction.items() if k != "derivatives"},
                      "response":{"derivatives":reconstruction["derivatives"],"finite_difference":finite,
                                  "paired_gain_prediction":predicted,"paired_gain_direct":direct},"source_gram":source_gram}
    return rows


def canonical_row(row):
    result = dict(row)
    if "prep_index" in row:
        result["preparation_index"] = row["prep_index"]
    if "angle_index" in row:
        result["angles_index"] = row["angle_index"]
    reconstruction = dict(row["reconstruction"])
    if "OR_cone_scale" in reconstruction:
        reconstruction["scale"] = reconstruction["OR_cone_scale"]
    if isinstance(reconstruction["single_coefficients"],dict):
        coefficients = reconstruction["single_coefficients"]
        reconstruction["single_coefficients"] = [coefficients[k] for k in ("alpha_A","beta_A","alpha_B","beta_B")]
    norm = max(map(abs,reconstruction["cofactor"]))
    require(norm > 0,"zero_cofactor")
    reconstruction["cofactor"] = [x/norm for x in reconstruction["cofactor"]]
    # A cofactor is homogeneous; its persisted residual has the same scale as its vector.
    reconstruction["cofactor_residual"] /= norm
    result["reconstruction"] = reconstruction
    return result


def validate_rows(report,expected,config):
    rows = report["rows"]
    indexed = {row["case_id"]:canonical_row(row) for row in rows}
    require(len(rows) == len(indexed) == len(expected) == 336 and indexed.keys() == expected.keys(),"incomplete_frozen_source_controls")
    probability,derivative = float(F(config["probability_tolerance"])),float(F(config["derivative_tolerance"]))
    maxima = {"held_out_residual":0.,"cofactor_residual":0.,"derivative_error":0.,"paired_gain_error":0.}
    for name,row in indexed.items():
        true = expected[name]
        if "status" in row:
            require(row["status"] == "PASS" and all(value is True for value in row["checks"].values()),"incorrect_source_case_verdict")
        for key in ("fixture","preparation_index","phase_pi","angles_index","model"):
            require(type(row[key]) is type(true[key]) and row[key] == true[key],"source_case_identity_mismatch")
        require(all(numeric_structure(row[k],true[k],probability) for k in
                    ("rates","signal","corrected_joint","reconstruction","source_gram")),"source_or_inverse_recomputation_mismatch:"+name)
        require(numeric_structure(row["response"],true["response"],derivative),"response_recomputation_mismatch:"+name)
        reconstructed = row["reconstruction"]
        scale = reconstructed["scale"]
        require(all(close(reconstructed["gram"][k],row["source_gram"][k]*scale,probability) for k in ("H","V","X")),"wrong_source_coherence_convention")
        require(reconstructed["gram"]["H"] >= -probability and reconstructed["gram"]["V"] >= -probability and
                reconstructed["psd_slack"] >= -probability and min(reconstructed["loss_slacks"]) >= -probability,"source_cone_or_loss_control_failed")
        maxima["held_out_residual"] = max(maxima["held_out_residual"],abs(reconstructed["held_out_residual"]))
        maxima["cofactor_residual"] = max(maxima["cofactor_residual"],abs(reconstructed["cofactor_residual"]))
        maxima["derivative_error"] = max(maxima["derivative_error"],*(abs(x-y) for x,y in zip(row["response"]["derivatives"],row["response"]["finite_difference"])))
        maxima["paired_gain_error"] = max(maxima["paired_gain_error"],abs(row["response"]["paired_gain_prediction"]-row["response"]["paired_gain_direct"]))
    require(maxima["held_out_residual"] <= probability and maxima["cofactor_residual"] <= probability and
            maxima["derivative_error"] <= derivative and maxima["paired_gain_error"] <= probability,"observable_control_failed")
    return maxima


def scientific_ast(code):
    tree = ast.parse(code)
    tree.body = [node for node in tree.body if not isinstance(node,ast.FunctionDef) or node.name != "append_comparison"]
    return ast.dump(tree,include_attributes=False)


def verify_independent_snapshot(report,module,bindings,primary_hash):
    freeze = report["executable_freeze"]
    path = HERE/"independent.py"
    for older,newer in ((FREEZE,freeze["commit"]),(freeze["commit"],"HEAD")):
        subprocess.run(["git","merge-base","--is-ancestor",older,newer],cwd=ROOT,check=True)
    frozen_file(HERE/"criterion.md",report["criterion_freeze"]["commit"])
    original = subprocess.check_output(["git","show",freeze["commit"]+":"+relative(path)],cwd=ROOT)
    require(hashlib.sha256(original).hexdigest() == freeze["program_sha256"] and
            scientific_ast(original.decode()) == scientific_ast(path.read_text()),"independent_scientific_source_changed")
    require(report["criterion_freeze"] == module.criterion_freeze() and
            report["inverse_inputs"] == ["three calibration joints","two full singles per side","physical angles","named model","background"] and
            report["statistical_verdict_enabled"] is False and report["other_implementation_output_used_as_input"] is False,
            "independent_input_or_scope_mismatch")
    expected = module.compute()
    for name in ("schema","version","status","rows","controls","diagnostics","inverse_inputs","coherence_convention",
                 "public_target_role","statistical_verdict_enabled","bell_event_files_read","other_implementation_output_used_as_input"):
        require(same_structure(report[name],expected[name]),"independent_recomputation_mismatch:"+name)
    packet_bindings = module.source_bindings()
    if "comparison" in report:
        packet_bindings[relative(HERE/PRIMARY)] = primary_hash
        comparison = report["comparison"]
        require(comparison["primary_sha256"] == primary_hash and comparison["passed"] is True and
                type(comparison["rows_compared"]) is int and comparison["rows_compared"] == 336 and
                comparison["row_status_agrees"] is True and comparison["comparison_program_freeze"] == module.executable_freeze(),
                "independent_comparison_mismatch")
        _,primary_bindings = scientific_inputs()
        primary_bindings[relative(HERE/"predict.py")] = digest(HERE/"predict.py")
        require(comparison["primary_bindings"] == primary_bindings,"independent_primary_binding_mismatch")
    require(report["bindings"] == packet_bindings,"independent_source_binding_mismatch")
    bindings.update(packet_bindings)


def lean_certification(bindings):
    receipt = json.loads((HERE/"certification.json").read_text())
    require(receipt["schema"] == "p23-observable-prediction-lean-certification/v1" and
            receipt["status"] == "certified" and receipt["criterion_freeze"]["commit"] == FREEZE,"missing_lean_certification")
    require(receipt["criterion_freeze"]["criterion_sha256"] == digest(HERE/"criterion.md") and
            receipt["criterion_freeze"]["sources_sha256"] == digest(HERE/"sources.json"),"lean_criterion_binding_mismatch")
    require(receipt["authorized_axioms"] == ["propext","Classical.choice","Quot.sound"],"unauthorized_lean_axioms")
    require(all(receipt[k] is False for k in IDENTITY) and receipt["numerical_interval_kernel_proof"] is False and
            receipt["statistical_confidence_kernel_proof"] is False,"lean_scope_mismatch")
    _,required_bindings = scientific_inputs()
    required_bindings.update({relative(path):digest(path) for path in (*LEAN_CHAIN,ROOT/"Lean/lean-toolchain",ROOT/"Lean/lake-manifest.json")})
    require(receipt["bindings"] == required_bindings,"incomplete_lean_source_bindings")
    for name,sha in required_bindings.items():
        bindings[name] = sha
    freezes = receipt["execution_source_freezes"]
    require(freezes.keys() == {relative(path) for path in LEAN_CHAIN},"incomplete_lean_execution_freezes")
    for path in LEAN_CHAIN:
        row = freezes[relative(path)]
        require(row["sha256"] == digest(path),"lean_source_binding_mismatch:"+relative(path))
        frozen_file(path,row["commit"])
        if path.parent == HERE:
            subprocess.run(["git","merge-base","--is-ancestor",FREEZE,row["commit"]],cwd=ROOT,check=True)
    focused = receipt["focused_verification"]
    require(focused["fresh_source_compilation"] is True and type(focused["trust_level"]) is int and
            focused["trust_level"] == 0 and focused["warning_as_error"] is True and
            [row["source"] for row in focused["commands"]] == [relative(path) for path in LEAN_CHAIN] and
            all(type(row["exit_code"]) is int and row["exit_code"] == 0 and
                row["command"][1:3] == ["--trust=0","-DwarningAsError=true"] for row in focused["commands"]),
            "invalid_lean_compile_receipt")
    require([row["file"] for row in focused["lsp"]] == [path.name for path in LEAN_CHAIN] and
            all(row["errors"] == row["warnings"] == 0 for row in focused["lsp"]),"invalid_lean_LSP_receipt")
    audit = receipt["source_audit"]
    require(all(audit[k] is True for k in ("actual_branch_Born_and_partner_loss_in_closure",
            "all_advertised_consumers_in_closure","independent_nonempty_physical_training_domain")) and
            audit["target_or_completed_Gram_in_primitive"] is False and audit["operational_root_in_closure"] is False,
            "invalid_lean_source_audit")
    bindings[relative(HERE/"certification.json")] = digest(HERE/"certification.json")
    return receipt


def assess(report_dir=None,*,enabled=True):
    base = {"schema":SCHEMA,"version":VERSION,"evidence_valid":False,**{k:False for k in IDENTITY},
            "statistical_verdict_enabled":False,"private_optimizer_input_required":False}
    if not enabled:
        return {**base,"status":"disabled_by_override"}
    directory = HERE if report_dir is None else Path(report_dir)
    try:
        config,bindings = scientific_inputs()
        programmes = {relative(HERE/name):program_freeze(HERE/name) for name in (*PROGRAMS,"verify.py","tests.py")}
        lean_certification(bindings)
        main_hash,own_hash = digest(directory/PRIMARY),digest(directory/INDEPENDENT)
        reports = [json.loads((directory/name).read_text()) for name in (PRIMARY,INDEPENDENT)]
        expected = forward_oracle(tuple(sorted(bindings.items())))
        maxima = []
        for report,name,role in zip(reports,PROGRAMS,("primary","independent")):
            require(report["schema"] == "p23-observable-prediction-"+role+"/v1" and report["version"] == VERSION,"observable_schema_or_revision_mismatch")
            require(all(report[k] is False for k in IDENTITY) and report.get("private_optimizer_input_required",False) is False,"observable_family_cannot_admit_empirical_identity")
            module = implementation(HERE/name)
            if role == "primary":
                require(report["criterion_sha256"] == digest(HERE/"criterion.md") and report["sources_sha256"] == digest(HERE/"sources.json") and
                        report["program_sha256"] == digest(HERE/name),"observable_program_or_source_binding_mismatch")
                fresh = module.generate()
                require(same_structure(report,fresh),"primary_recomputation_mismatch")
            else:
                verify_independent_snapshot(report,module,bindings,main_hash)
            require(report["controls"] and all(value is True for value in report["controls"].values()),"observable_negative_control_failed")
            maxima.append(validate_rows(report,expected,config))
        require(digest(directory/PRIMARY) == main_hash and digest(directory/INDEPENDENT) == own_hash,"observable_evidence_changed_during_verification")
        return {**base,"status":"verified","evidence_valid":True,"criterion_freeze":{"commit":FREEZE,
                "criterion_sha256":digest(HERE/"criterion.md"),"sources_sha256":digest(HERE/"sources.json")},
                "execution_source_freezes":programmes,"source_controls":336,"models":list(MODELS),"maxima":maxima,
                "lean_candidate_certified":True,"source_full_mode_and_OR_branch_recomputed":True,
                "holdout_rows":{"calibration":[0,1,3],"held_out":2},
                "bindings":{**bindings,**{name:row["sha256"] for name,row in programmes.items()},
                            "prediction.json":main_hash,"independent_prediction.json":own_hash},
                "scope":config["scope"],"public_target_role":config["public_target_role"]}
    except FileNotFoundError as error:
        return {**base,"status":"missing_observable_evidence","reason":str(error)}
    except (ValueError,KeyError,TypeError,IndexError,AttributeError,ArithmeticError,ImportError,OSError,subprocess.SubprocessError) as error:
        return {**base,"status":"invalid_observable_evidence","reason":str(error)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only",action="store_true")
    parser.add_argument("--directory",type=Path)
    parser.add_argument("--disabled",action="store_true")
    args = parser.parse_args()
    result = assess(args.directory,enabled=not args.disabled)
    print(json.dumps(result,indent=2,allow_nan=False))
    return 0 if result["status"] == "verified" else 1


if __name__ == "__main__":
    raise SystemExit(main())
