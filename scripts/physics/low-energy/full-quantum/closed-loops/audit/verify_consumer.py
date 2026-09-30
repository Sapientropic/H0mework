#!/usr/bin/env python3
"""Reuse the certified current-joint-vacuum consumer in a temporary module."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root",type=Path,required=True)
    root=parser.parse_args().root.resolve()
    base=root/"Verification/physics/low-energy-phenomenology/full-quantum"
    audit=base/"closed-loops/audit"
    support=base/"triangular/audit/Consumer.lean"
    text=support.read_text().replace("import scratch.LowEnergyFullQuantum.Triangular",
        "import SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Triangular")
    lean_root=root/"Lean"
    lean=subprocess.check_output(["lake","env","which","lean"],cwd=lean_root,text=True).strip()
    path=subprocess.check_output(["lake","env","printenv","LEAN_PATH"],cwd=lean_root,text=True).strip()
    checks=[]
    with tempfile.TemporaryDirectory(prefix="closed-loop-audit-") as directory:
        temporary=Path(directory);snapshot=temporary/"TriangularAuditSnapshot.lean"
        snapshot.write_text(text)
        environment=dict(os.environ);environment["LEAN_PATH"]=str(temporary)+os.pathsep+path
        jobs=[("Support",[lean,"--root="+str(temporary),"--trust=0","-DwarningAsError=true","-o",
            str(temporary/"TriangularAuditSnapshot.olean"),str(snapshot)]),
            ("IndependentConsumer",[lean,"--trust=0","-DwarningAsError=true",str(audit/"Consumer.lean")])]
        for name,command in jobs:
            start=time.monotonic()
            result=subprocess.run(command,cwd=lean_root,env=environment,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            (audit/(name+"-strict.log")).write_text(result.stdout)
            checks.append({"name":name,"exit_code":result.returncode,"seconds":round(time.monotonic()-start,3),
                "trust":0,"warnings_as_errors":True})
            print(name,result.returncode,flush=True)
            if result.returncode:break
    (audit/"consumer-focused.json").write_text(json.dumps({"support_source":str(support.relative_to(root)),
        "proof_bodies_copied_without_changes":True,"imports_use_promoted_Triangular_modules":True,
        "temporary_oleans_removed":True,"checks":checks},indent=2)+"\n")
    assert len(checks)==2 and all(item["exit_code"]==0 for item in checks)


if __name__=="__main__":main()
