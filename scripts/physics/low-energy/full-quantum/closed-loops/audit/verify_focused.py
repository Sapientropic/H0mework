#!/usr/bin/env python3
"""Independent focused kernel replay; do not modify the frozen candidates or caches."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess
import time


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root",type=Path,required=True)
    root=parser.parse_args().root.resolve()
    capsule=root/"Verification/physics/low-energy-phenomenology/full-quantum/closed-loops"
    audit=capsule/"audit"
    modules=["Grading","Source","Words"]
    targets=[(name,root/"Lean/SaturationMonoid/PhysicsCore/LowEnergy/FullQuantum/ClosedLoops"/(name+".lean")) for name in modules]
    targets.extend((name,capsule/(name+".lean")) for name in ["Consumer","Audit"])

    def run(target):
        name,path=target
        command=["lake","env","lean","--trust=0","-DwarningAsError=true",str(path)]
        start=time.monotonic()
        result=subprocess.run(command,cwd=root/"Lean",stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (audit/(name+"-strict.log")).write_text(result.stdout)
        print(name,result.returncode,flush=True)
        return {"name":name,"exit_code":result.returncode,"seconds":round(time.monotonic()-start,3),
            "command":command,"writes_olean":False}

    with ThreadPoolExecutor(max_workers=3) as executor:
        results=list(executor.map(run,targets))
    lint=[]
    for name,path in targets[:3]:
        command=["python3",str(root/".agents/skills/lean-agent/scripts/theorem_mouth_lint.py"),str(path),"--fail-on","never"]
        result=subprocess.run(command,cwd=root,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        (audit/(name+"-mouth.log")).write_text(result.stdout)
        lint.append({"name":name,"exit_code":result.returncode})
    (audit/"focused.json").write_text(json.dumps({"checks":results,"mouth_lint":lint},indent=2)+"\n")
    assert all(row["exit_code"]==0 for row in results+lint)


if __name__=="__main__":main()
