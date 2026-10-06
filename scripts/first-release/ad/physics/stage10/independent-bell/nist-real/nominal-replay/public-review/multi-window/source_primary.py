#!/usr/bin/env python3
"""All-window source cover and original positive Fock/Born witnesses."""
from fractions import Fraction as F
import argparse
import heapq
import importlib.util
import itertools
import json
import lzma
import math
from pathlib import Path
import re
import sys

HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
FIB=BASE/"observable-closure/full-statistical-fiber"
spec=importlib.util.spec_from_file_location("_mws_public",HERE/"primary.py")
public=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=public
spec.loader.exec_module(public)
sys.path.insert(0,str(FIB))
import primary_fiber as kernel
import independent_fiber as born

VERSION="p23-public-multi-window-source-mws0001"
CTX=None


def configuration():
    global CTX
    if CTX is not None:
        return CTX
    text=(HERE/"criterion-source.md").read_text()
    config=json.loads(re.findall(r"<!-- MW-SOURCE-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- MW-SOURCE-FROZEN-END -->",text,re.S)[0])
    manifest=json.loads((HERE/"sources-source.json").read_text())
    public.require(config["version"]==manifest["version"]==VERSION and config["all_CI_count"]==72,"source_contract_changed")
    for item in manifest["inputs"]:
        public.require(public.digest(public.ROOT/item["path"])==item["sha256"],"source_input_changed:"+item["path"])
    bindings=[public.frozen(HERE/n) for n in ("criterion-source.md","sources-source.json","source_primary.py")]
    c=kernel.context()
    bc,bf,bb=born.configuration()
    CTX={"config":config,"bindings":bindings,"kernel":c,"I":c["I"],"born_config":bc,
         "born_const":born.constants(bc),"born_bindings":bb,"background":list(map(F,c["spec"]["background_per_pulse"]))}
    return CTX


def nth_root(q,n,digits=50):
    public.require(0<=q<=1 and n>0,"source_root_domain")
    I=configuration()["I"]
    scale=10**digits
    target=q.numerator*scale**n//q.denominator
    if target==0:
        low=0
    elif n==1:
        low=target
    else:
        low=1<<((target.bit_length()+n-1)//n)
        while True:
            nxt=((n-1)*low+target//low**(n-1))//n
            if nxt>=low:
                break
            low=nxt
        while low**n>target:
            low-=1
        while (low+1)**n<=target:
            low+=1
    a=F(low,scale)
    return I(a,a if a**n==q else F(low+1,scale))


def read_ci(packet):
    I=configuration()["I"]
    return {key:[I(F(v["exact_lower"]),F(v["exact_upper"])) for v in packet[key]]
            for key in ("j","sA_cell","sB_cell")}


def inputs():
    config=configuration()["config"]
    data=json.loads((HERE/"primary-first.json").read_text())
    run=next(r for r in data["runs"] if r["workbook"]==config["workbook"])
    groups=[{"identity":"full_N"+str(g["pulse_count"]),"N":g["pulse_count"],"ci":read_ci(g["common_mean_confidence"])}
            for g in run["groups"]]
    old=json.loads((HERE/config["old_cut_CI"]).read_text())
    groups.append({"identity":"old_cut_N5","N":5,"ci":read_ci(old["common_mean_confidence"])})
    public.require(len(groups)==6,"source_window_inputs_incomplete")
    return groups


def initial_domain(groups):
    c=configuration()
    I=c["I"]
    means=[]
    for field,rows,bg in (("sA_cell",[0,1],c["background"][0]),("sB_cell",[0,2],c["background"][1]),
                          ("sA_cell",[2,3],c["background"][0]),("sB_cell",[1,3],c["background"][1])):
        values=[]
        for g in groups:
            for row in rows:
                target=g["ci"][field][row]
                low=(1-bg)/nth_root(1-target.lo,g["N"])-1
                high=(1-bg)/nth_root(1-target.hi,g["N"])-1
                values.append(I(low.lo,high.hi))
        lo,hi=max(v.lo for v in values),min(v.hi for v in values)
        public.require(0<lo<=hi,"source_single_mean_domain_empty")
        means.append(I(lo,hi))
    return means+[I(0,1)]


def single_window(mean,bg,n):
    return 1-kernel.powi((1-bg)/(1+mean),n)


def shared_phase(source,cells,groups):
    c=configuration(); I=c["I"]
    T=c["kernel"]["gauss"].square_root(source["T2"])
    K=I(-T.hi,T.hi); slabs=[]
    ba,bb=c["background"]
    for group in groups:
        n=group["N"]
        for row,cell in enumerate(cells):
            sa=single_window(cell["ma"],ba,n)
            sb=single_window(cell["mb"],bb,n)
            target=group["ci"]["j"][row]
            noclick=1-sa-sb+target
            lo,hi=max(F(0),noclick.lo),min(F(1),noclick.hi)
            if lo>hi:
                return None,[{"identity":group["identity"],"row":row,"reason":"no_click_outer_empty"}]
            q=I(nth_root(lo,n).lo,nth_root(hi,n).hi)/((1-ba)*(1-bb))
            lower=q.lo*cell["E"]-cell["L"]
            upper=q.hi*cell["E"]-cell["L"]
            K=kernel.affine_phase_clip(K,cell["g"],lower,upper)
            slabs.append({"identity":group["identity"],"row":row,"g":cell["g"],"lower":lower,"upper":upper,"phase_after":K})
            if K is None:
                return None,slabs
    return K,slabs


def window(cell,K,n):
    I=configuration()["I"]
    ba,bb=configuration()["background"]
    pa,pb=(1-ba)/(1+cell["ma"]),(1-bb)/(1+cell["mb"])
    sa,sb=1-kernel.powi(pa,n),1-kernel.powi(pb,n)
    excess=kernel.positive_outer((cell["A"]+cell["D"]*cell["g"]*K)/cell["E"])
    public.require(excess is not None,"negative_source_connected_outer")
    j=sa*sb+sum((math.comb(n,k)*kernel.powi(pa*pb,n)*kernel.powi(excess,k) for k in range(1,n+1)),I.point(0))
    j=kernel.intersect(j,I(0,min(sa.hi,sb.hi)))
    public.require(j is not None,"empty_source_joint_outer")
    return {"sA":sa,"sB":sb,"j":j,"outcomes":[kernel.intersect(x,I(0,1)) for x in (j,sa-j,sb-j,1-sa-sb+j)]}


def evaluate(box,groups):
    source=kernel.covariance(box)
    if source is None:
        return {"status":"excluded","reason":"whole_box_physical_violation"}
    cells=kernel.coefficients(source)
    if cells is None:
        return {"status":"unresolved","reason":"source_denominator_outer_requires_refinement"}
    K,slabs=shared_phase(source,cells,groups)
    if K is None:
        return {"status":"excluded","reason":"whole_box_shared_all_window_phase_empty","slabs":slabs}
    try:
        windows={str(n):[window(cell,K,n) for cell in cells] for n in (1,3,5,7,9)}
    except ValueError:
        return {"status":"unresolved","reason":"physical_window_outer_requires_refinement"}
    for group in groups:
        rows=windows[str(group["N"])]
        for index,row in enumerate(rows):
            for field,name in (("sA_cell","sA"),("sB_cell","sB"),("j","j")):
                if kernel.intersect(row[name],group["ci"][field][index]) is None:
                    return {"status":"excluded","reason":"whole_box_original_CI_disjoint","identity":group["identity"],"row":index,"field":field}
    ch={n:rows[0]["j"]+rows[1]["j"]+rows[2]["j"]-rows[3]["j"]-rows[0]["sA"]-rows[0]["sB"] for n,rows in windows.items()}
    return {"status":"retained","source":source,"phase":K,"slabs":slabs,"windows":windows,"CH":ch,
            "one_source_and_one_phase_for_all_windows":True}


def cover(groups,domain):
    cfg=configuration()["config"]
    queue=[(-5,0,"",tuple((F(0),F(1)) for _ in range(5)),0)]
    sequence=0; splits=[]; nodes=[]; leaves=[]
    while queue:
        _,_,path,unit,depth=heapq.heappop(queue)
        value=evaluate(kernel.source_box(unit,domain),groups)
        nodes.append({"path":path,"status":value["status"]})
        if value["status"]=="excluded":
            leaves.append({"path":path,"classification":"excluded","proof":value}); continue
        axis=kernel.split_axis(unit)
        if len(splits)>=cfg["primary_split_cap"] or depth>=cfg["max_depth"] or unit[axis][1]-unit[axis][0]<=F(cfg["normalized_width_stop"]):
            leaves.append({"path":path,"classification":"retained_boundary","unit_box":unit,"qualified_outer":value,
                           "stop":"resource_cap" if len(splits)>=cfg["primary_split_cap"] else "width_or_depth"}); continue
        lo,hi=unit[axis]; mid=(lo+hi)/2
        splits.append({"path":path,"axis":axis,"midpoint":mid})
        for label,ends in (("L",(lo,mid)),("R",(mid,hi))):
            child=list(unit);child[axis]=ends;child=tuple(child);sequence+=1
            heapq.heappush(queue,(-sum(b-a for a,b in child),sequence,path+str(axis)+label,child,depth+1))
        if len(splits)%256==0:
            print(json.dumps({"source_primary_splits":len(splits),"pending":len(queue)}),flush=True)
    public.require(len(nodes)==2*len(splits)+1 and len(leaves)==len(splits)+1,"incomplete_source_cover")
    return {"initial_box":domain,"nodes":nodes,"splits":splits,"leaves":leaves,"all_leaves_preserved":True}


def fock_windows(source):
    c=configuration()
    raw=born.fock_readout(source,c["born_const"],c["config"]["source_pair_cutoff"])
    ba,bb=c["background"]
    windows={}
    for n in (1,3,5,7,9):
        rows=[]
        for row in raw["cells"]:
            pulse=row["pulse_positive_Born"]
            pa,pb=ba+(1-ba)*pulse["A"],bb+(1-bb)*pulse["B"]
            j=((1-ba)*(1-bb)*pulse["J"]+ba*(1-bb)*pulse["B"]+bb*(1-ba)*pulse["A"]+ba*bb)
            sa,sb=1-(1-pa).power(n),1-(1-pb).power(n)
            D=(1-pa)*(1-pb); connected=j-pa*pb
            J=sa*sb+sum((math.comb(n,k)*D.power(n-k)*connected.power(k) for k in range(1,n+1)),born.I(0))
            rows.append({"sA":sa,"sB":sb,"j":J,"outcomes":[J,sa-J,sb-J,1-sa-sb+J]})
        windows[str(n)]=rows
    return raw,windows


def members(groups,domain):
    c=configuration();cfg=c["config"];I=c["I"]
    found=[];by_sign={"positive":0,"negative":0}
    fractions=list(map(F,cfg["member_mean_fractions"]))
    for fs in itertools.product(fractions,repeat=4):
        means=[I.point(d.lo+f*(d.hi-d.lo)) for d,f in zip(domain[:4],fs)]
        for index in range(1,cfg["member_loss_denominator"]+1):
            e=F(index,cfg["member_loss_denominator"])
            box=means+[I.point(e)]
            value=evaluate(box,groups)
            if value["status"]!="retained": continue
            for fraction in map(F,cfg["member_phase_fractions"]):
                K=value["phase"];k=K.lo+fraction*(K.hi-K.lo)
                cells=kernel.coefficients(value["source"])
                windows={str(n):[window(cell,I.point(k),n) for cell in cells] for n in (1,3,5,7,9)}
                if not all(pred.lo>=target.lo and pred.hi<=target.hi for g in groups for row in range(4)
                           for pred,target in [(windows[str(g["N"])][row][name],g["ci"][field][row])
                                               for name,field in (("sA","sA_cell"),("sB","sB_cell"),("j","j"))]): continue
                ch=windows["5"][0]["j"]+windows["5"][1]["j"]+windows["5"][2]["j"]-windows["5"][3]["j"]-windows["5"][0]["sA"]-windows["5"][0]["sB"]
                sign="positive" if ch.lo>0 else "negative" if ch.hi<0 else "unresolved"
                if sign=="unresolved" or by_sign[sign]>=cfg["member_per_sign_limit"]: continue
                raw_probabilities=[1-((1-bg)/(1+m.lo))**5 for m,bg in zip(means,(c["background"]*2))]
                shape,reconstruction=born.member_shape(raw_probabilities,c["born_config"],c["born_const"])
                try:
                    source=born.physical_source(shape+[born.I(e)],born.I(k))
                    native,native_windows=fock_windows(source)
                except ValueError:
                    continue
                checks=[native_windows[str(g["N"])][row][name].within_exact({"exact_lower":str(g["ci"][field][row].lo),"exact_upper":str(g["ci"][field][row].hi)})
                        for g in groups for row in range(4) for name,field in (("sA","sA_cell"),("sB","sB_cell"),("j","j"))]
                native_ch=native_windows["5"][0]["j"]+native_windows["5"][1]["j"]+native_windows["5"][2]["j"]-native_windows["5"][3]["j"]-native_windows["5"][0]["sA"]-native_windows["5"][0]["sB"]
                if not all(checks) or not (native_ch.lo>0 if sign=="positive" else native_ch.hi<0): continue
                found.append({"recipe":{"mean_fractions":fs,"means":means,"loss":e,"common_k":k},
                              "source":born.serial(source),"reconstruction":born.serial(reconstruction),"native_Fock":born.serial(native),
                              "native_windows":born.serial(native_windows),"all_72_CI_contained":True,"checks":checks,
                              "CH_N5":born.serial(native_ch),"strict_CH_N5_sign":sign,"Gaussian_windows":windows})
                by_sign[sign]+=1
                print(json.dumps({"source_member":len(found),"sign":sign,"loss":str(e)}),flush=True)
                if len(found)>=cfg["member_limit"]: return found
    return found


def main():
    parser=argparse.ArgumentParser();parser.add_argument("--output",type=Path,required=True);args=parser.parse_args()
    public.require(not args.output.exists(),"source_first_receipt_already_exists")
    c=configuration();groups=inputs();domain=initial_domain(groups)
    witness=members(groups,domain)
    result={"schema":"p23-public-multi-window-source/v1","version":VERSION,"bindings":c["bindings"],"implementation":"primary",
            "input_groups":groups,"all_72_CI_consumed":True,"domain":domain,"members":witness,"cover":cover(groups,domain),
            "old_cut_and_full_run_not_independent":True,"bell_event_files_read":0,"publication_configuration_identified":False}
    encoded=json.dumps(kernel.pack(result),indent=2,sort_keys=True,allow_nan=False).encode()+b"\n"
    args.output.write_bytes(lzma.compress(encoded,preset=6))
    print(json.dumps({"output":str(args.output),"sha256":public.digest(args.output),"logical_sha256":__import__("hashlib").sha256(encoded).hexdigest(),
                      "members":len(witness),"positive":sum(m["strict_CH_N5_sign"]=="positive" for m in witness),
                      "negative":sum(m["strict_CH_N5_sign"]=="negative" for m in witness),"nodes":len(result["cover"]["nodes"])}))


if __name__=="__main__":
    main()
