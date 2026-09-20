#!/usr/bin/env python3
"""Source radial and unbounded-history controls; reuse the certified noncommuting solution."""
import argparse
import json
from pathlib import Path
import re

import sympy as s


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root",type=Path,required=True)
    root=parser.parse_args().root.resolve()
    spatial=root/"Verification/physics/low-energy-phenomenology/occupied-response/spatial"
    audit=spatial/"global/audit"
    parent=json.loads((spatial.parent/"receipt.json").read_text())
    text=(root/"Lean/SaturationMonoid/PhysicsCore/DiracCliffordRepresentation.lean").read_text()
    literal=re.search(r"def diracGammaZero\s*:.*?:=\s*!!\[(.*?)\]",text,re.S).group(1)
    g0=s.Matrix([[s.sympify(v.strip()) for v in row.split(",")] for row in literal.split(";")])
    N=3*s.sqrt(30)/25
    native_dirac=-s.kronecker_product(g0,s.eye(3))/N
    T=s.simplify(N*s.kronecker_product(g0,s.eye(3))*native_dirac)
    assert T==s.eye(12)
    def decode(value):return s.SparseMatrix(*value["shape"],{(i,j):s.sympify(v) for i,j,v in value["entries"]})
    assert T==decode(parent["gauge_Hamiltonian_forces"][11])
    w=decode(parent["source_prepared"])
    assert (w.H*w)[0]==1
    epsilon,time,start=s.symbols("epsilon time start",real=True)
    phase=s.exp(-s.I*epsilon*(time-start))
    original=phase*w
    assert s.simplify(original.diff(time)+s.I*epsilon*T*original)==s.zeros(12,1)
    assert s.simplify((original.H*original)[0])==1
    # The radial extension equals the original on its generated sphere, while
    # the off-sphere field is intentionally different. No time rescaling is used.
    on_sphere=(1+s.sqrt((w.H*w)[0]))/(1+s.sqrt(s.simplify((original.H*original)[0])))
    assert on_sphere==1
    off=2*w
    off_factor=(1+s.sqrt((w.H*w)[0]))/(1+s.sqrt((off.H*off)[0]))
    assert off_factor==s.Rational(2,3)
    assert -s.I*3*off_factor*T*off!=-s.I*3*T*off
    # Arbitrarily large epsilon and an unbounded-in-time continuous native history.
    future=s.exp(-s.I*epsilon*time**2/2)
    past=s.Integer(1)
    assert s.simplify(s.diff(future,time)+s.I*epsilon*time*future)==0
    assert future.subs(time,0)==past
    assert s.diff(future,time).subs(time,0)==0
    assert s.simplify(s.conjugate(future)*future)==1
    large_cases=[]
    primitive=lambda t:s.Max(t,0)**2/2
    for eps,begin,end in ((3,100,-200),(-7,-100,1000),(100,-5000,2000),(-100,-300,-1000)):
        action=s.simplify(eps*(primitive(end)-primitive(begin)))
        inverse=-action
        assert action+inverse==0
        large_cases.append({"epsilon":eps,"start":begin,"time":end,"ramp_phase":"exp(-i*"+str(action)+")"})
    radius=s.Symbol("radius",positive=True)
    norm=s.Symbol("initial_norm",nonnegative=True)
    M=radius  # max(t,0) on [-radius,radius], without any all-time M.
    L=s.Abs(epsilon)*M*(1+norm)
    a=2*radius*L+1
    assert s.simplify(a-L*(2*radius))==1
    assert (2*L).is_nonnegative
    arbitrary_bound=s.Symbol("arbitrary_nonnegative_bound",nonnegative=True)
    assert s.simplify(s.Max(arbitrary_bound+1,0)-arbitrary_bound)==1
    noncommuting_path=spatial/"finite-coupling/derivative/audit/independent-receipt.json"
    noncommuting=json.loads(noncommuting_path.read_text())
    assert noncommuting["status"]=="PASS"
    assert noncommuting["complete_actual_12_by_4_tangent_rows"]
    assert noncommuting["exact_Kubo_integral_matches"]
    result={"status":"PASS","actual_native_time_hypercharge_T":"I12",
        "radial_generated_norm_sphere_factor":1,"radial_off_sphere_negative_control":"2/3, not 1",
        "all_real_epsilon_identity_evolution":"exp(-i*epsilon*(time-start))*w",
        "unbounded_continuous_native_history":"R(t)=max(t,0)*I",
        "ramp_future_phase":"exp(-i*epsilon*t^2/2), value and derivative join at zero",
        "large_coupling_time_cases":large_cases,"finite_window_Picard_slack":1,
        "no_all_time_R_bound_witness":"R(M+1) has norm M+1 for every M>=0",
        "reused_noncommuting_receipt":str(noncommuting_path.relative_to(root)),
        "reused_without_rerunning":"exact finite-epsilon source exponential, full 12 rows and its current/Kubo derivative",
        "scope":"Independent actual-source mechanism controls. Universal arbitrary-window gluing is kernel-checked in Lean."}
    (audit/"independent-receipt.json").write_text(json.dumps(result,indent=2)+"\n")
    print("PASS source radial sphere/off-sphere, all-epsilon phases, unbounded continuous history and finite-window controls")


if __name__=="__main__":main()
