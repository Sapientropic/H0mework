#!/usr/bin/env python3
"""Fresh source-only intake for native detector effects; no science replay."""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import itertools
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[7]
FREEZE = "1458fa3856fc0d2a097010c0ef8a07089d45ea13"
VERSION = "p23-native-effects-ge0001"
SCHEMA = "p23-native-effects-verification/v1"
IDENTITY = ("source_mapping_identified","publication_configuration_identified","production_admitted","actual_window_model_identified")
CHAIN = (HERE.parent/"GaussianSource.lean",HERE.parent/"Consumer.lean",
         HERE/"DetectorGamma.lean",HERE/"GammaConsumer.lean",HERE/"GammaCertification.lean")
TRUTH = {"native_ports_generated":True,"native_occupation_isometry_generated":True,
         "all_n_tensor_port_Born_identity":True,"all_n_Gamma_positive_contraction":True,
         "native_three_paired_effects_to_source_tail":True,"gaussian_vacuum_kernel_proof":False,
         "whole_window_Born_kernel_proof":False}


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def relative(path):
    return Path(path).relative_to(ROOT).as_posix()


def committed(path, *, new=False):
    name = relative(path)
    commit = subprocess.check_output(["git","log","-1","--format=%H","--",name],cwd=ROOT,text=True).strip()
    require(bool(commit),"source_not_committed:"+name)
    require(subprocess.check_output(["git","show",commit+":"+name],cwd=ROOT) == Path(path).read_bytes(),"execution_source_changed:"+name)
    subprocess.run(["git","merge-base","--is-ancestor",commit,"HEAD"],cwd=ROOT,check=True)
    if new:
        subprocess.run(["git","merge-base","--is-ancestor",FREEZE,commit],cwd=ROOT,check=True)
    return {"commit":commit,"sha256":digest(path)}


def inputs():
    subprocess.run(["git","merge-base","--is-ancestor",FREEZE,"HEAD"],cwd=ROOT,check=True)
    for name in ("criterion.md","sources.json"):
        path = HERE/name
        require(subprocess.check_output(["git","show",FREEZE+":"+relative(path)],cwd=ROOT) == path.read_bytes(),"native_effects_freeze_changed")
    packet = json.loads((HERE/"sources.json").read_text())
    require(packet["schema"] == "p23-native-effects-sources/v1" and packet["version"] == VERSION and
            all(packet[k] is False for k in IDENTITY[:3]) and packet["private_optimizer_input_required"] is False and
            type(packet["bell_event_files_read"]) is int and packet["bell_event_files_read"] == 0,"invalid_native_effects_source_contract")
    for older in (packet["parent_source_freeze"],packet["parent_result_commit"]):
        subprocess.run(["git","merge-base","--is-ancestor",older,FREEZE],cwd=ROOT,check=True)
    bindings = {}
    for row in packet["inputs"]:
        path = (ROOT/row["path"]).resolve()
        require(path.is_relative_to(ROOT) and row["path"] not in bindings and digest(path) == row["sha256"],"native_effects_input_binding_mismatch")
        bindings[row["path"]] = row["sha256"]
    freezes = {relative(path):committed(path,new=path.parent == HERE) for path in CHAIN}
    freezes[relative(Path(__file__))] = committed(Path(__file__),new=True)
    for path in (HERE/"criterion.md",HERE/"sources.json",*CHAIN,Path(__file__)):
        bindings[relative(path)] = digest(path)
    return bindings,freezes


def compile_sources(*, lsp=False):
    bindings,freezes = inputs()
    project = ROOT/"Lean"
    env = json.loads(subprocess.check_output(["lake","env","python3","-c",
        "import json,os; print(json.dumps(dict(os.environ)))"],cwd=project,text=True))
    checks=[]
    with tempfile.TemporaryDirectory(prefix="p23-native-effects-certify-") as fresh:
        env["LEAN_PATH"] = fresh+os.pathsep+env.get("LEAN_PATH","")
        for path in CHAIN:
            argv = ["lean","--trust=0","-DwarningAsError=true","--root="+os.path.relpath(path.parent,project),
                    "-o",str(Path(fresh)/(path.stem+".olean")),os.path.relpath(path,project)]
            run = subprocess.run(argv,cwd=project,env=env,text=True,capture_output=True,timeout=120)
            shown=argv.copy(); shown[5]="${fresh_olean}/"+path.stem+".olean"
            checks.append({"source":relative(path),"command":shown,"exit_code":run.returncode,"stdout":run.stdout,"stderr":run.stderr})
            require(run.returncode == 0,"native_effects_focused_compile_failed:"+path.name+":"+run.stdout+run.stderr)
        diagnostics=[]
        if lsp:
            cs = HERE.parent.parent/"investigation/collected-source"
            old_verify = sys.modules.pop("verify",None)
            sys.path.insert(0,str(cs))
            try:
                spec=importlib.util.spec_from_file_location("_native_effects_LSP",cs/"certify.py")
                helper=importlib.util.module_from_spec(spec); spec.loader.exec_module(helper)
                diagnostics=helper.lsp_check(project,env,list(CHAIN))
            finally:
                sys.path.remove(str(cs)); sys.modules.pop("verify",None)
                if old_verify is not None:
                    sys.modules["verify"] = old_verify
    for name,row in freezes.items():
        require(digest(ROOT/name) == row["sha256"],"source_changed_during_native_effects_compilation")
    return {"bindings":bindings,"execution_source_freezes":freezes,"commands":checks,"lsp":diagnostics}


def finite_pairing():
    """Pair the declared word/port basis with independent creation polynomials."""
    maximum=0.; missing_normalization=False; wrong_local_coherence=False; count=0
    for th,tv,a in ((0.,0.,0.),(1.,1.,0.),(1.,1.,math.pi/2),(.8,.6,math.pi/4)):
        ports = [(math.sqrt(th)*math.sin(a),math.sqrt(tv)*math.cos(a)),
                 (math.sqrt(th)*math.cos(a),-math.sqrt(tv)*math.sin(a)),
                 (math.sqrt(1-th),0.),(0.,math.sqrt(1-tv))]
        # Numeric column 0 is H, corresponding to the Lean Bool value true.
        e = [[float(i==j)-ports[0][i]*ports[0][j] for j in range(2)] for i in range(2)]
        for n in (0,1,2,3):
            words=list(itertools.product((0,1),repeat=n))
            born=[]
            for output in itertools.product(range(1,4),repeat=n):
                born.append([math.fsum(math.prod(ports[output[k]][word[k]] for k in range(n))
                    for word in words if word.count(0)==h)/math.sqrt(math.comb(n,h)) for h in range(n+1)])
            word_gram=[[math.fsum(row[h]*row[k] for row in born) for k in range(n+1)] for h in range(n+1)]
            polynomial=[[0.]*(n+1) for _ in range(n+1)]
            for source_h in range(n+1):
                coefficients=[1.]
                for column in [0]*source_h+[1]*(n-source_h):
                    nxt=[0.]*(len(coefficients)+1)
                    for h,value in enumerate(coefficients):
                        nxt[h]+=value*e[1][column]; nxt[h+1]+=value*e[0][column]
                    coefficients=nxt
                for h,value in enumerate(coefficients):
                    polynomial[h][source_h]=value*math.sqrt(math.factorial(h)*math.factorial(n-h)/
                        (math.factorial(source_h)*math.factorial(n-source_h)))
            maximum=max(maximum,*(abs(word_gram[h][k]-polynomial[h][k]) for h in range(n+1) for k in range(n+1)))
            if n==2 and th==.8:
                missing_normalization=abs(word_gram[1][1]*(math.comb(n,1)-1))>1e-6
                wrong_local_coherence=abs(word_gram[0][1])>1e-6
            count+=1
    require(maximum<=1e-12 and missing_normalization and wrong_local_coherence,"native_word_creation_pairing_failed")
    return {"cases":count,"sectors":[0,1,2,3],"max_matrix_delta":maximum,
            "missing_occupation_normalization_detected":missing_normalization,"full_Gamma_is_not_local_paired_block":wrong_local_coherence,
            "role":"finite basis pairing; all-n theorem comes from the kernel consumer"}


def assess(report_dir=None, *, enabled=True, fresh=False):
    base={"schema":SCHEMA,"version":VERSION,"evidence_valid":False,**{key:False for key in IDENTITY},
          "private_optimizer_input_required":False,"bell_event_files_read":0}
    if not enabled:
        return {**base,"status":"disabled_by_override"}
    try:
        bindings,freezes=inputs()
        directory=HERE if report_dir is None else Path(report_dir)
        receipt=json.loads((directory/"certification.json").read_text())
        require(receipt==json.loads((HERE/"certification.json").read_text()),"untrusted_native_effects_receipt_changed")
        require(receipt["schema"]=="p23-native-effects-lean-certification/v1" and receipt["status"]=="certified" and
                receipt["criterion_freeze"]=={"commit":FREEZE,"criterion_sha256":digest(HERE/"criterion.md"),
                  "sources_sha256":digest(HERE/"sources.json")} and all(receipt[k] is False for k in IDENTITY) and
                receipt["kernel_claims"].keys()==TRUTH.keys() and
                all(receipt["kernel_claims"][key] is value for key,value in TRUTH.items()) and receipt["bindings"]==bindings and
                receipt["authorized_axioms"]==["propext","Classical.choice","Quot.sound"],"invalid_native_effects_certification")
        audit=receipt["source_audit"]
        require(audit["actual_ports_occupation_pairing_and_tail_in_closure"] is True and
                audit["target_or_caller_Gamma_in_primitive"] is False and audit["operational_root_in_closure"] is False,
                "invalid_native_effects_source_audit")
        focused=receipt["focused_verification"]
        require(focused["fresh_source_compilation"] is True and type(focused["trust_level"]) is int and focused["trust_level"]==0 and
                focused["warning_as_error"] is True and [row["source"] for row in focused["commands"]]==[relative(path) for path in CHAIN] and
                all(type(row["exit_code"]) is int and row["exit_code"]==0 and
                    row["command"][1:3]==["--trust=0","-DwarningAsError=true"] for row in focused["commands"]) and
                [row["file"] for row in focused["lsp"]]==[path.name for path in CHAIN] and
                all(type(row["errors"]) is int and type(row["warnings"]) is int and
                    row["errors"]==row["warnings"]==0 for row in focused["lsp"]),"invalid_native_effects_fresh_receipt")
        require(receipt["execution_source_freezes"].keys()=={relative(path) for path in CHAIN},"incomplete_native_effects_source_freezes")
        for path in CHAIN:
            row=receipt["execution_source_freezes"][relative(path)]
            require(row["sha256"]==digest(path) and subprocess.check_output(
                ["git","show",row["commit"]+":"+relative(path)],cwd=ROOT)==path.read_bytes(),"native_effects_compiled_source_changed")
            subprocess.run(["git","merge-base","--is-ancestor",row["commit"],"HEAD"],cwd=ROOT,check=True)
        log=compile_sources()["commands"][-1]["stdout"] if fresh else focused["commands"][-1]["stdout"]
        values=re.search(r"NATIVE_EFFECT_CERTIFIED declarations=(\d+) nodes=(\d+) required=(\d+) primitive=(\d+)",log)
        require(values is not None,"missing_native_effects_closure_audit")
        fields=("candidate_declarations","dependency_nodes","required_nodes","primitive_nodes")
        require(all(audit[key]==int(value) for key,value in zip(fields,values.groups())),"native_effects_closure_receipt_mismatch")
        pairing=finite_pairing()
        return {**base,"status":"verified","evidence_valid":True,"kernel_claims":TRUTH,
                "criterion_freeze":receipt["criterion_freeze"],"source_audit":audit,"finite_pairing":pairing,
                "fresh_source_compilation":fresh,"consumed_fresh_source_certificate":True,"execution_source_freezes":freezes,
                "bindings":{**bindings,"certification.json":digest(directory/"certification.json")},
                "scope":"Native raw ports and normalized word occupation generate all-n three paired effects and the same-source infinite Born tail. Gaussian vacuum and whole-window equality remain separate."}
    except FileNotFoundError as error:
        return {**base,"status":"missing_native_effects_evidence","reason":str(error)}
    except (ValueError,KeyError,TypeError,AttributeError,ArithmeticError,ImportError,OSError,subprocess.SubprocessError) as error:
        return {**base,"status":"invalid_native_effects_evidence","reason":str(error)}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only",action="store_true")
    parser.add_argument("--directory",type=Path)
    parser.add_argument("--disabled",action="store_true")
    parser.add_argument("--fresh",action="store_true",help="explicitly recompile the source-only proof chain")
    args=parser.parse_args()
    result=assess(args.directory,enabled=not args.disabled,fresh=args.fresh)
    print(json.dumps(result,indent=2,allow_nan=False))
    return 0 if result["status"]=="verified" else 1


if __name__=="__main__":
    raise SystemExit(main())
