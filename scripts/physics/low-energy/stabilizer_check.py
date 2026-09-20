#!/usr/bin/env python3
"""Exact finite checks used by the accompanying analytic stabilizer proof.
The global group classification is the written proof, not a Lean certificate.
Run check_readout.py first to verify the receipt against its original sources.
"""
import argparse, hashlib, itertools, json
from pathlib import Path

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--receipt',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args(); raw=args.receipt.read_bytes(); data=json.loads(raw)
    terms={tuple(s):n for s,n in data['joint_scalar_terms']}
    expected={(0,1,2,6):1,(0,1,2,4):1,(0,1,5,6):1,(0,1,4,5):1}
    assert terms==expected, 'The analytic proof applies to the specified original vector'
    outputs=list(itertools.combinations(range(7),5)); matrix=[]
    for out in outputs:
        row=[]
        for i in range(7):
            total=0
            for s,n in terms.items():
                if i not in s and tuple(sorted((i,)+s))==out:
                    total+=n*((-1)**sum(i>j for j in s))
            row.append(total)
        matrix.append(row)
    gram=[[sum(row[i]*row[j] for row in matrix) for j in range(7)] for i in range(7)]
    diagonal=[0,0,2,4,2,2,2]
    assert gram==[[diagonal[i] if i==j else 0 for j in range(7)] for i in range(7)]
    omega={}
    for a,b,c in [(2,4,1),(5,4,-1),(2,6,1),(5,6,1)]:
        key=tuple(sorted((a,b))); omega[key]=omega.get(key,0)+c*(1 if a<b else -1)
    assert {(0,1)+s:n for s,n in omega.items()}==terms
    phases=[{'term':s,'powers_c_w_h':[-1+int(2 in s),int(3 in s)-int(4 in s),int(5 in s)-int(6 in s)]} for s in sorted(terms)]
    powers={tuple(x['powers_c_w_h']) for x in phases}
    assert {(-1,0,0),(0,-1,0),(0,0,-1)}.issubset(powers)
    result={'scope':'FINITE_CHECKS_FOR_ANALYTIC_BARE_SCALAR_STABILIZER_PROOF_NOT_LEAN',
      'receipt_sha256':hashlib.sha256(raw).hexdigest(),'output_basis':outputs,
      'wedge_matrix':matrix,'wedge_gram':gram,'p286_phase_exponents':phases,
      'checks':['distinct orthogonal eigenspaces A, B, C','symplectic two-form factorization','three primitive circle phases forced to identity']}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print('PASS: wedge Gram diag(0,0,2,4,2,2,2), symplectic factorization, native phase equations')
if __name__=='__main__': main()
