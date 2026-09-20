#!/usr/bin/env python3
"""Original electric/magnetic kinetic coefficients and their matter comparison."""
import argparse
import json
from pathlib import Path
import sys
import sympy as s

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
sys.path.insert(0,str(HERE.parent/"nonlinear-contact"))
import exact_readout as source
from slice_checks import GAMMA


def clean(matrix):return s.SparseMatrix(matrix).applyfunc(s.expand)


def decode(record):
    return s.SparseMatrix(*record["shape"],{(i,j):s.sympify(v) for i,j,v in record["entries"]})


def encode(matrix):
    return {"shape":list(matrix.shape),"entries":[[int(i),int(j),str(value)]
        for (i,j),value in sorted(s.SparseMatrix(matrix).todok().items())]}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root",type=Path,required=True)
    parser.add_argument("--out",type=Path,required=True)
    args=parser.parse_args()
    base=args.root/"Verification/physics/low-energy-phenomenology"
    active=json.loads((base/"active-gauge/receipt.json").read_text())
    phase=json.loads((base/"full-phase/receipt.json").read_text())
    matter=json.loads((base/"matter-modes/source.json").read_text())
    vertices=json.loads((base/"matter-vertices/receipt.json").read_text())
    n=s.sympify(active["source_lapse"]);sigma=s.sympify(active["source_coupling"])
    assert n*n==s.Rational(54,125) and sigma==s.Rational(1,2)
    native=source.generators([(0,1,2),(3,4)])
    fundamental=[s.Matrix(matrix)*(s.I if imaginary else 1) for _,imaginary,matrix in native]
    pairing=s.Matrix(12,12,lambda i,j:s.re(-s.trace(fundamental[i]*fundamental[j])))
    assert pairing[11,11]==2
    pairing[11,11]=1
    assert pairing.det()!=0 and all(value>0 for value in pairing.eigenvals())
    p=s.symbols("p0 p1 p2 p3")
    fields=[i for i,item in enumerate(active["fields"]) if item["group"]=="gauge_A"]
    assert [active["fields"][i]["coordinate"] for i in fields]==[[mu,a] for mu in range(4) for a in range(12)]
    positions={value:i for i,value in enumerate(fields)}
    principal=s.MutableSparseMatrix(48,48,{})
    for row,col,powers,value in active["primitive_121_Fourier_Jacobi_entries"]:
        if row in positions and col in positions and sum(powers)==2:
            principal[positions[row],positions[col]]+=s.sympify(value)*s.prod(v**power for v,power in zip(p,powers))
    spacetime=s.MutableSparseMatrix(4,4,{})
    square=sum(p[i]**2 for i in range(1,4))
    spacetime[0,0]=-n*square/sigma
    for i in range(1,4):
        spacetime[0,i]=spacetime[i,0]=n*p[0]*p[i]/sigma
        for j in range(1,4):
            spacetime[i,j]=(-n*p[0]**2/sigma+square/(sigma*n))*int(i==j)-p[i]*p[j]/(sigma*n)
    assert clean(principal-s.kronecker_product(spacetime,pairing))==s.zeros(48)
    assert clean(spacetime*s.Matrix(p))==s.zeros(4,1)
    # A homogeneous Lagrangian with actual signed derivative adjoints reproduces that matrix.
    electric=[];magnetic=[]
    for i in range(1,4):
        row=s.zeros(1,4);row[0,i]=p[0];row[0,0]=-p[i];electric.append(row)
    for i in range(1,4):
        for j in range(i+1,4):
            row=s.zeros(1,4);row[0,j]=p[i];row[0,i]=-p[j];magnetic.append(row)
    action_hessian=clean(-n/sigma*sum((row.T*row for row in electric),s.zeros(4))+
        1/(sigma*n)*sum((row.T*row for row in magnetic),s.zeros(4)))
    assert clean(action_hessian-spacetime)==s.zeros(4)
    print("PASS: original all48 gauge principal coefficients = native pairing times actual E/B action",flush=True)
    nu=s.symbols("nu")
    coordinate_change=s.diag(n,1,1,1)
    proper=clean(coordinate_change*spacetime.subs(p[0],n*nu)*coordinate_change/n)
    assert proper[1,1].coeff(nu,2)==-n*n/sigma
    assert s.expand(proper[1,1]).coeff(p[2],2)==1/(sigma*n*n)
    principal_matter=clean(sum((p[mu]*decode(phase["principal_coefficients"][mu]) for mu in range(4)),s.zeros(252)))
    scalar_polynomial=p[0]**2/n**2-square
    assert clean(principal_matter*principal_matter-scalar_polynomial*s.eye(252))==s.zeros(252)
    scalar_source=json.loads((base/"scalar-exchange/receipt.json").read_text())
    ur=s.symbols("u r1 r2 r3")
    scalar_operator=decode(scalar_source["normalized_full_scalar_operator"])
    scalar_principal=scalar_operator.applyfunc(lambda value: sum(
        coefficient*s.prod(variable**power for variable,power in zip(ur,powers))
        for powers,coefficient in s.Poly(value,*ur).terms() if sum(powers)==2))
    scalar_principal=clean(scalar_principal.subs(dict(zip(ur,
        [p[0]/(n*s.sqrt(2))]+[p[i]/s.sqrt(2) for i in range(1,4)]))))
    assert scalar_principal==scalar_polynomial*s.eye(70)
    # The already source-isolated transverse weak waves exhibit the gauge cone without quotient assumptions.
    weak=json.loads((base/"weak-exchange/spatial/receipt.json").read_text())
    lam,k=s.symbols("lam k",real=True)
    weakK=decode(weak["weak_four_by_four_operator"]).subs({s.Symbol("lam"):lam,
        s.Symbol("k1"):0,s.Symbol("k2"):0,s.Symbol("k3"):k})
    transverse=s.SparseMatrix(4,2,{(1,0):1,(2,1):1})
    scalar=-4*n*(lam*lam+k*k/(n*n)-s.Rational(1,2))
    assert clean(weakK*transverse-scalar*transverse)==s.zeros(4,2)
    # At least one genuine free-free transverse source can detect the original weak action.
    F=decode(matter["source_isometry"])
    S=clean(s.kronecker_product(GAMMA[0]*s.diag(-1,-1,1,1),s.eye(63)))
    label_index=active["native_P286_labels"].index("A34")
    vertex=next(decode(item["operator"]) for item in vertices["primitive_vertices"]
        if item["group"]=="gauge_A" and item["coordinate"]==[1,label_index])
    real_vertex=clean(s.sqrt(2)*(S*vertex+vertex.H*S)/2)
    source_current=clean(F.H*real_vertex*F)
    assert source_current!=s.zeros(216)
    witness=next(iter(source_current.todok().items()))
    inverse_electric= s.simplify(n*n/sigma)
    inverse_magnetic= s.simplify(1/(sigma*n*n))
    speed_ratio=s.simplify(1/(n*n))
    result={"scope":"ORIGINAL_PRINCIPAL_ACTION_COUPLING_AND_CHARACTERISTIC_NORMALIZATION",
        "source_lapse":str(n),"source_sigma":str(sigma),"native_pairing":encode(pairing),
        "all48_gauge_principal_Hessian":encode(principal),
        "source_spacetime_factor":encode(spacetime),"proper_time_spacetime_factor":encode(proper),
        "coordinate_action":"L=N/(2*sigma)*sum_i pairing(E_i,E_i)-1/(2*sigma*N)*sum_i pairing(B_i,B_i)",
        "proper_clock":"tau=N*t, A_tau=A_t/N; fixed actual coframe only",
        "proper_time_action":"L_tau=N^2/(2*sigma)*pairing(E_tau,E_tau)-1/(2*sigma*N^2)*pairing(B,B)",
        "electric_squared_coupling_in_native_pairing":str(s.simplify(1/inverse_electric)),
        "magnetic_squared_coupling_in_native_pairing":str(s.simplify(1/inverse_magnetic)),
        "electric_inverse_coefficient":str(inverse_electric),"magnetic_inverse_coefficient":str(inverse_magnetic),
        "matter_scalar_coordinate_speed":str(n),"gauge_transverse_coordinate_speed":str(1/n),
        "gauge_transverse_over_matter_speed":str(speed_ratio),
        "proper_matter_scalar_speed":"1","proper_gauge_transverse_speed":str(speed_ratio),
        "matter_principal_square":str(scalar_polynomial),
        "actual_all70_scalar_principal":encode(scalar_principal),
        "exact_source_weak_transverse_operator":str(scalar),
        "free_transverse_current_nonzero_witness":{"row":int(witness[0][0]),"column":int(witness[0][1]),"value":str(witness[1])},
        "single_Lorentz_invariant_tree_coupling_identified":False,
        "loop_corrections_or_empirical_carrier_identification":False}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")
    print("PASS: original matter/scalar and transverse gauge cones; proper-time coefficient pair",inverse_electric,inverse_magnetic,
        "; speed ratio",speed_ratio,flush=True)


if __name__=="__main__":main()
