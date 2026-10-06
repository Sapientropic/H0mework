#!/usr/bin/env python3
"""Read public constants as data; independently generate PCoff Jones effects."""
from __future__ import annotations

import argparse
import ast
import cmath
from fractions import Fraction as F
import hashlib
import itertools
import json
import math
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[7]
FREEZE = "0919a10e64b2616358d7d26b83422f650f727406"
VERSION = "p23-receiver-control-source-rc0001"
OUTPUT = HERE/"independent-decoder.json"
SCRIPTS = ("CH_over_network.py","CH_with_one_pockels_cell.py",
           "CH_with_one_pockels_cell_log.py","CH_with_one_pockels_cell_log2.py")
TOLERANCE = 2e-12


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def relative(path):
    return Path(path).relative_to(ROOT).as_posix()


def committed_bytes(path, commit):
    subprocess.run(["git","merge-base","--is-ancestor",commit,"HEAD"],cwd=ROOT,check=True)
    return subprocess.check_output(["git","show",commit+":"+relative(path)],cwd=ROOT)


def executable_freeze():
    path = Path(__file__)
    commit = subprocess.check_output(["git","log","-1","--format=%H","--",relative(path)],cwd=ROOT,text=True).strip()
    require(commit and committed_bytes(path,commit) == path.read_bytes(),"freeze independent decoder before execution")
    subprocess.run(["git","merge-base","--is-ancestor",FREEZE,commit],cwd=ROOT,check=True)
    return {"commit":commit,"program_sha256":digest(path)}


def extract_members(text):
    members={}; current=None; original=None
    for line in text.splitlines():
        if line.startswith("MEMBER "):
            current=line.removeprefix("MEMBER ")
            require(current not in members,"duplicate source member")
            members[current]={"lines":{},"original_sha256":None}
        elif line.startswith("ORIGINAL_SHA256 "):
            require(current is not None,"orphan source hash")
            original=line.split()[1]
            require(re.fullmatch(r"[0-9a-f]{64}",original) is not None,"invalid original member hash")
            members[current]["original_sha256"]=original
        elif match:=re.fullmatch(r"(\d+): ?(.*)",line):
            require(current is not None,"orphan source line")
            number=int(match.group(1)); code=match.group(2)
            require(number not in members[current]["lines"],"duplicate source line")
            members[current]["lines"][number]=code
    require(members and all(row["original_sha256"] for row in members.values()),"incomplete source member context")
    return members


def source_inputs():
    for name in ("criterion.md","sources.json"):
        path=HERE/name
        require(committed_bytes(path,FREEZE)==path.read_bytes(),"frozen source input changed:"+name)
    text=(HERE/"criterion.md").read_text()
    start,end="<!-- RC-FROZEN-BEGIN -->","<!-- RC-FROZEN-END -->"
    require(text.count(start)==text.count(end)==1,"nonunique receiver criterion")
    blocks=re.findall(r"```json\s*(.*?)\s*```",text.split(start)[1].split(end)[0],re.S)
    require(len(blocks)==1,"nonunique receiver specification")
    spec=json.loads(blocks[0])
    require(spec["version"]==VERSION and spec["measurement_scope"]=="ideal_nominal_PCoff_static_waveplate_recipe" and
            spec["physical_click_port"]=="V" and spec["QWP_axes"]==["2*HWP2","2*HWP2+90degree"],"wrong receiver contract")
    for key in ("recipe_controls_prove_argmax","actual_epoch_required_by_original_nominal_gate",
                "actual_source_or_hardware_identity_verified","PC_on_retarder_identified",
                "apparatus_optimum_verified","controller_advance"):
        require(spec[key] is False,"receiver scope changed")
    require(spec["effective_angle_inputs_from_recipe"] is True and spec["retrospective"] is True and
            type(spec["raw_event_archives_read"]) is int and spec["raw_event_archives_read"]==0 and
            type(spec["archive_programs_executed"]) is int and spec["archive_programs_executed"]==0,"wrong source exposure role")
    packet=json.loads((HERE/"sources.json").read_text())
    require(packet["schema"]=="p23-public-receiver-control-source-review/v1" and packet["source_scripts_imported_or_executed"] is False and
            packet["trial_event_files_read"]==0 and packet["published_five_controls_used_for_fit_or_admission"] is False,"unsafe or fitted source packet")
    extracts={}; bindings={relative(HERE/name):digest(HERE/name) for name in ("criterion.md","sources.json")}
    for row in packet["extracts"]:
        path=HERE/row["path"]
        require(path.parent==HERE and digest(path)==row["sha256"] and len(path.read_bytes())==row["bytes"] and
                committed_bytes(path,FREEZE)==path.read_bytes(),"source extract binding mismatch:"+row["path"])
        members=extract_members(path.read_text())
        require(members.keys()=={item["member"] for item in row["members"]},"member coverage mismatch")
        for member in row["members"]:
            actual=members[member["member"]]
            require(actual["original_sha256"]==member["original_sha256"],"original member hash mismatch")
            lines=set(itertools.chain.from_iterable(range(lo,hi+1) for lo,hi in member["selected_line_ranges"]))
            require(actual["lines"].keys()==lines,"selected source line context incomplete")
        extracts[row["path"]]=members
        bindings[relative(path)]=row["sha256"]
    require(len(extracts)==6,"six source extracts required")
    notice=HERE/packet["notice"]["path"]
    require(digest(notice)==packet["notice"]["sha256"],"source notice mismatch")
    bindings[relative(notice)]=digest(notice)
    return spec,packet,extracts,bindings


def literal_expression(expression, environment):
    """A small data interpreter; no Python eval, imports or archive calls."""
    def apply_binary(operation,left,right):
        if isinstance(left,list) or isinstance(right,list):
            width=len(left) if isinstance(left,list) else len(right)
            if isinstance(left,list) and isinstance(right,list):
                require(len(left)==len(right),"constant array shape mismatch")
            return [apply_binary(operation,left[i] if isinstance(left,list) else left,
                                 right[i] if isinstance(right,list) else right) for i in range(width)]
        if isinstance(operation,ast.Add): return left+right
        if isinstance(operation,ast.Sub): return left-right
        if isinstance(operation,ast.Mult): return left*right
        if isinstance(operation,ast.Div): return left/right
        raise ValueError("unrecognized constant operator")
    def visit(node):
        if isinstance(node,ast.Constant) and type(node.value) in (int,float):
            return F(ast.get_source_segment(expression,node))
        if isinstance(node,ast.Name):
            require(node.id in environment,"undefined recipe constant:"+node.id)
            return environment[node.id]
        if isinstance(node,ast.List): return [visit(item) for item in node.elts]
        if isinstance(node,ast.UnaryOp) and isinstance(node.op,(ast.USub,ast.UAdd)):
            value=visit(node.operand)
            return apply_binary(ast.Mult(),F(-1) if isinstance(node.op,ast.USub) else F(1),value)
        if isinstance(node,ast.BinOp): return apply_binary(node.op,visit(node.left),visit(node.right))
        if (isinstance(node,ast.Call) and isinstance(node.func,ast.Attribute) and isinstance(node.func.value,ast.Name) and
                node.func.value.id=="np" and node.func.attr=="array" and len(node.args)==1 and not node.keywords):
            value=visit(node.args[0]); require(isinstance(value,list),"array requires literal list"); return value
        raise ValueError("archive expression outside constant grammar")
    return visit(ast.parse(expression,mode="eval").body)


def parse_recipe(member):
    names={"AHWP2","AHWP1","AQWP1","BHWP1","BHWP2","BQWP1","Angles","Alice_angles","Bob_angles"}
    values={}; assignments={}; commands={}
    for number,raw in sorted(member["lines"].items()):
        code=raw.split("#",1)[0].strip()
        if match:=re.fullmatch(r"([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.+)",code):
            name,expression=match.groups()
            if name in names:
                require(name not in values,"ambiguous recipe assignment")
                values[name]=literal_expression(expression,values)
                assignments[name]={"line":number,"expression":expression}
        if match:=re.fullmatch(r"mc_(source|alice|bob)\.goto\('([^']+)',\s*(.+)\)",code):
            station,name,expression=match.groups()
            require(name not in commands,"duplicate initial command")
            commands[name]={"station":station,"line":number,"expression":expression,
                            "degrees":literal_expression(expression,values)}
    require(values.keys()==names,"incomplete recipe assignments")
    required={"PumpHWP","AliceQWP1","AliceHWP1","AliceHWP2","BobQWP1","BobHWP1","BobHWP2"}
    require(commands.keys()==required and commands["PumpHWP"]["degrees"]==F(8),"incomplete native initial commands")
    require(commands["AliceHWP2"]["degrees"]==values["AHWP2"] and commands["BobHWP2"]["degrees"]==values["BHWP2"] and
            commands["AliceQWP1"]["degrees"]==2*values["AHWP2"] and
            commands["BobQWP1"]["degrees"]==2*values["BHWP2"]+90,"native QWP relation mismatch")
    require(len(values["Alice_angles"])==len(values["Bob_angles"])==2,"recipe setting coverage changed")
    defaults=[raw.strip() for raw in member["lines"].values() if raw.strip().startswith("collect_data_with_waveplates(")]
    require(len(defaults)==1,"default waveplate branch unidentified")
    return values,assignments,commands,defaults[0]


def multiply(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(len(b))) for j in range(len(b[0]))] for i in range(len(a))]


def dagger(a):
    return [[a[j][i].conjugate() for j in range(len(a))] for i in range(len(a[0]))]


def apply(a,v):
    return [sum(x*y for x,y in zip(row,v)) for row in a]


def delta(a,b):
    return max(abs(x-y) for left,right in zip(a,b) for x,y in zip(left,right))


def retarder(axis_degrees, retardance):
    axis=math.radians(float(axis_degrees)); c,s=math.cos(axis),math.sin(axis)
    eigenvectors=[[complex(c),complex(-s)],[complex(s),complex(c)]]
    phases=[[cmath.exp(-.5j*retardance),0j],[0j,cmath.exp(.5j*retardance)]]
    return multiply(multiply(eigenvectors,phases),dagger(eigenvectors))


def receiver(m,o,q, *, port=1):
    # Actual eigenaxis retarders are multiplied in physical propagation order.
    unitary=multiply(multiply(retarder(o,math.pi),retarder(q,math.pi/2)),retarder(m,math.pi))
    vector=[unitary[port][i].conjugate() for i in range(2)]
    effect=[[vector[i]*vector[j].conjugate() for j in range(2)] for i in range(2)]
    return unitary,vector,effect


def real_projector(degrees):
    angle=math.radians(float(degrees)); vector=[math.sin(angle),math.cos(angle)]
    return [[complex(x*y) for y in vector] for x in vector]


def born(effect,state):
    return sum(z.conjugate()*w for z,w in zip(state,apply(effect,state))).real


def serial(value):
    if isinstance(value,F): return str(value)
    if isinstance(value,complex): return [value.real,value.imag]
    if isinstance(value,dict): return {k:serial(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)): return [serial(v) for v in value]
    return value


def measurement_row(m,o,q):
    unitary,vector,effect=receiver(m,o,q)
    effective=2*(o-m)
    predicted=real_projector(effective)
    identity=[[1+0j,0j],[0j,1+0j]]
    errors={"projector":delta(effect,predicted),"unitarity":delta(multiply(dagger(unitary),unitary),identity),
            "idempotence":delta(multiply(effect,effect),effect),"Hermitian":delta(dagger(effect),effect),
            "unit_trace":abs(effect[0][0]+effect[1][1]-1)}
    return {"HWP1_degree":m,"HWP2_degree":o,"QWP_degree":q,"effective_degree":effective,
            "unitary":unitary,"pulled_V":vector,"native_V_effect":effect,"generated_real_projector":predicted,
            "errors":errors,"passed":all(value<=TOLERANCE for value in errors.values())}


def basis_control(m,o,q):
    _,_,effect=receiver(m,o,q)
    transport=[[0j,-1+0j],[1+0j,0j]]
    angle=math.radians(float(2*(o-m))); first=[math.cos(angle),-math.sin(angle)]
    expected=[[complex(x*y) for y in first] for x in first]
    effect_t=multiply(multiply(transport,effect),dagger(transport))
    initial=[math.cos(.39),math.sin(.39)]
    rotation=[[complex(math.cos(.17)),complex(-math.sin(.17))],[complex(math.sin(.17)),complex(math.cos(.17))]]
    phase=[[1+0j,0j],[0j,cmath.exp(.71j)]]
    state=apply(rotation,apply(phase,initial))
    moved_rotation=multiply(multiply(transport,rotation),dagger(transport))
    moved_phase=multiply(multiply(transport,phase),dagger(transport))
    moved_state=apply(moved_rotation,apply(moved_phase,apply(transport,initial)))
    identity_error=delta(effect_t,expected)
    probability_error=abs(born(effect,state)-born(effect_t,moved_state))
    wrong=abs(born(effect,state)-born(effect,apply(transport,state)))
    return {"projector_transport_error":identity_error,"source_effect_R_phase_Born_transport_error":probability_error,
            "only_state_basis_wrong_probability_gap":wrong,"all_objects_transport_passed":max(identity_error,probability_error)<=TOLERANCE,
            "only_state_basis_rejected":wrong>1e-3}


def source_readout_roles(extracts):
    # Roles are tied to actual expression text, without acquiring any hardware count values.
    herald=extracts["windows-and-heralds.txt"]
    cmd=herald["bell_client/cmdline2.py"]["lines"]
    coin=herald["bell_client/coin_plot.py"]["lines"]
    for line,token in ((258,"coin_count)/alice_data['singles']"),(259,"coin_count)/bob_data['singles']")):
        require(token.replace(" ","") in cmd[line].replace(" ",""),"herald denominator source changed")
    require("metrics_bob['singles']" in coin[88] and "metrics_alice['singles']" in coin[84],"opposite receiver eta role changed")
    motor=extracts["motor-frame.txt"]["bell_client/RotationController.py"]["lines"]
    require("absPosition + self.attributes['zero']" in motor[16] and "absolutePos - self.attributes['zero']" in motor[22],"motor frame roundtrip source changed")
    calibration=extracts["polarization-calibration.txt"]["bell_client/motorScriptExample.py"]["lines"]
    require(all(name in "\n".join(calibration.values()) for name in ("PHWP = 45","PHWP = 0","PHWP = 22.5","AliceOffset","BobOffset")),"calibration roles not retained")
    window=herald["bell_client/multi_networkCalc.py"]["lines"]
    require("singlesMask[pockelBool].sum()" in window[463] and "singlesMask & settingBool" not in window[463],"window count readout changed")
    objective=extracts["counts-objectives.txt"]["bell_client/CH_over_network.py"]["lines"]
    require("counts['SET00']" in objective[121] and "INT_TIME*79e6" in objective[140],"branch exposure roles changed")
    return {"cmdline_alice_eff":{"denominator":"Alice singles","heralded_receiver":"Bob","line":258},
            "cmdline_bob_eff":{"denominator":"Bob singles","heralded_receiver":"Alice","line":259},
            "coin_plot_eta1":"C/S_B -> Alice given Bob","coin_plot_eta2":"C/S_A -> Bob given Alice",
            "motor_frame":"command+same configured zero; getPos subtracts same zero modulo360",
            "calibration":"pure H/V and balanced DA/AA roles preserved; no measured count values supplied",
            "counts":"PC setting exposure and waveplate pulse exposure have distinct source denominators",
            "window":"detector-record sums after single/slot/setting masks, not complete-trial anyclick",
            "actual_calibration_receipt_generated":False}


def compute():
    execution=executable_freeze()
    spec,packet,extracts,bindings=source_inputs()
    recipes=[]; maxima={}; native=extracts["source-and-receiver-recipe.txt"]
    require(native.keys()=={"bell_client/"+name for name in SCRIPTS},"four source recipes required")
    for name in SCRIPTS:
        member=native["bell_client/"+name]
        values,assignments,commands,default=parse_recipe(member)
        stations={}
        for side,prefix in (("alice","A"),("bob","B")):
            o=values[prefix+"HWP2"]
            q=commands["AliceQWP1" if side=="alice" else "BobQWP1"]["degrees"]
            rows=[measurement_row(m,o,q) for m in values["Alice_angles" if side=="alice" else "Bob_angles"]]
            stations[side]=rows
            for row in rows:
                require(row["passed"],"native source recipe projector mismatch")
                for key,error in row["errors"].items(): maxima[key]=max(maxima.get(key,0.),error)
        recipes.append({"member":"bell_client/"+name,"original_sha256":member["original_sha256"],
                        "constant_assignments":assignments,"parsed_constants":values,"native_initial_commands":commands,
                        "default_branch":default,"stations":stations})
    general=[]; offset=[]
    for m,o,choice in itertools.product(map(F,("-31","-5.905","0","3.405","17.5","42")),
                                     map(F,("-20","-8","0","5.5","33")),(0,90)):
        q=2*o+choice
        row=measurement_row(m,o,q); require(row["passed"],"general PCoff projector mismatch")
        row["QWP_choice_offset_degree"]=choice; general.append(row)
        shift=F("7.125")
        moved=receiver(m+shift,o+shift,q+2*shift)[2]
        error=delta(row["native_V_effect"],moved)
        require(error<=TOLERANCE,"common control offset changed projector")
        offset.append(error)
    sample=measurement_row(F(7),F(19),F(38))
    wrong_half=delta(sample["native_V_effect"],real_projector(sample["effective_degree"]/2))
    wrong_port=delta(sample["native_V_effect"],receiver(F(7),F(19),F(38),port=0)[2])
    basis=basis_control(F(7),F(19),F(38))
    checks={"all_four_native_recipes":len(recipes)==4,"sixteen_native_V_effects":sum(len(side) for r in recipes for side in r["stations"].values())==16,
            "general_o_m_two_QWP_choices":len(general)==60 and all(row["passed"] for row in general),
            "common_offset_same_effect":max(offset)<=TOLERANCE,"wrong_mechanical_half_angle_rejected":wrong_half>1e-3,
            "wrong_physical_H_port_rejected":wrong_port>1e-3,
            "source_effect_R_phase_basis_transport":basis["all_objects_transport_passed"],
            "only_source_basis_swap_rejected":basis["only_state_basis_rejected"]}
    require(all(checks.values()),"independent receiver control failed")
    bindings[relative(Path(__file__))]=digest(Path(__file__))
    return serial({"schema":"p23-receiver-control-source-independent/v1","version":VERSION,"status":"PASS",
                   "criterion_freeze":{"commit":FREEZE,"criterion_sha256":digest(HERE/"criterion.md"),"sources_sha256":digest(HERE/"sources.json")},
                   "executable_freeze":execution,"bindings":bindings,"recipes":recipes,"general_controls":general,
                   "diagnostics":{"native_effect_maxima":maxima,"general_projector_error":max(row["errors"]["projector"] for row in general),
                      "common_offset_max_effect_error":max(offset),"wrong_half_angle_effect_gap":wrong_half,"wrong_port_effect_gap":wrong_port,
                      "basis_transport":basis},"controls":checks,"source_readout_roles":source_readout_roles(extracts),
                   "measurement_scope":spec["measurement_scope"],"physical_click_port":"V","public_nominal_recipe_identity_verified":True,
                   "native_PCoff_effect_is_generated_real_projector":True,"recipe_controls_prove_argmax":False,
                   "actual_source_or_hardware_identity_verified":False,"PC_on_retarder_identified":False,"apparatus_optimum_verified":False,
                   "actual_epoch_required_by_original_nominal_gate":False,"controller_advance":False,"retrospective":True,
                   "raw_event_archives_read":0,"archive_programs_executed":0,"other_implementation_output_used_as_input":False,
                   "implementation":"independent restricted constant grammar and complex retarder eigenbasis Jones propagation",
                   "numerical_tolerance":TOLERANCE,
                   "access_disclosure":{"official_archive_programs_imported":False,"official_archive_programs_executed":False,
                      "primary_decoder_source_read":False,"primary_decoder_output_read":False,"source_extracts_read":6}})


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only",action="store_true")
    args=parser.parse_args()
    result=compute()
    if not args.check_only:
        require(not OUTPUT.exists(),"first independent receipt already exists; preserve immutable output")
        OUTPUT.write_text(json.dumps(result,indent=2,sort_keys=True,allow_nan=False)+"\n")
    print(json.dumps({"schema":result["schema"],"status":result["status"],"recipes":len(result["recipes"]),
                      "general_controls":len(result["general_controls"]),"controls":result["controls"],"diagnostics":result["diagnostics"]}))
    return 0


if __name__=="__main__":
    raise SystemExit(main())
