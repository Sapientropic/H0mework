#!/usr/bin/env python3
"""Source Ward identities consumed by actual free external legs and tree exchange."""
import argparse
import itertools
import json
from pathlib import Path
import sys
import sympy as s
from sympy.polys.matrices import DomainMatrix

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
sys.path.insert(0,str(HERE.parent/"nonlinear-contact"))
import exact_readout as source
from slice_checks import GAMMA, PAIRS


def clean(matrix):return s.SparseMatrix(matrix).applyfunc(s.expand)


def decode(record):
    return s.SparseMatrix(*record["shape"],{(i,j):s.sympify(v) for i,j,v in record["entries"]})


def encode(matrix):
    return {"shape":list(matrix.shape),"entries":[[int(i),int(j),str(s.simplify(v))]
        for (i,j),v in sorted(s.SparseMatrix(matrix).todok().items())]}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root",type=Path,required=True)
    parser.add_argument("--out",type=Path,required=True)
    args=parser.parse_args()
    base=args.root/"Verification/physics/low-energy-phenomenology"
    vertices=json.loads((base/"matter-vertices/receipt.json").read_text())
    exchange=json.loads((base/"matter-vertices/exchange.json").read_text())
    active=json.loads((base/"active-gauge/receipt.json").read_text())
    phase=json.loads((base/"full-phase/receipt.json").read_text())
    modes=json.loads((base/"matter-modes/source.json").read_text())
    p=s.symbols("p0 p1 p2 p3",real=True)
    transfer=s.symbols("r0 r1 r2 r3",real=True)
    exchange_p=s.symbols("p0 p1 p2 p3")
    substitute=dict(zip(exchange_p,transfer))
    n=s.sympify(phase["source_lapse"]);omega=s.sympify(phase["source_frequency"])
    D=decode(vertices["full_stationary_Dirac_operator"])
    # JSON symbols have no reality assumptions; align all external-derivative variables explicitly.
    D=D.subs(dict(zip(exchange_p,p)))
    V=[decode(item["operator"]).subs(dict(zip(exchange_p,p))) for item in vertices["primitive_vertices"]]
    active_v={item["field"]:decode(item["operator"]).subs(dict(zip(exchange_p,p)))
        for item in vertices["active_289_bosonic_source_operators"]}
    ordering=exchange["source_field_indices"]
    Q=decode(phase["phase_generator"])
    S=clean(s.kronecker_product(GAMMA[0]*s.diag(-1,-1,1,1),s.eye(63)))
    assert all(clean(Q*S*v-S*v*Q)==s.zeros(252) for v in V)
    print("PASS: every original Hermitian source vertex preserves the full graded phase charge",flush=True)
    native=source.generators([(0,1,2),(3,4)])
    rho=[]
    for _,imaginary,matrix in native:
        internal=s.diag(*[s.SparseMatrix(source.exterior_action(matrix,degree))*(s.I if imaginary else 1)
            for degree in [6,2,4]])
        rho.append(clean(s.kronecker_product(s.eye(4),internal)))
    color=[[s.sympify(x) for x in row] for row in active["actual_background"]["source_color_generators"]]
    null_generators=[clean(sum((row[i]*rho[i] for i in range(12)),s.zeros(252))) for row in color]
    null_generators += [clean(s.kronecker_product(GAMMA[a]*GAMMA[b]/2,s.eye(63))) for a,b in PAIRS]
    broken=[rho[i] for i in active["Ward_constraint_elimination"]["broken_parameter_columns"]]
    null_map=decode(exchange["local_source_compatibility_map"]).subs(substitute)
    scalar_entry=next(item for item in exchange["source_contact_terms"] if item["groups"]==["scalar_Ward"])
    scalar_map=decode(scalar_entry["source_map"]).subs(substitute)
    shifted=D.subs(dict(zip(p,[p[i]-transfer[i] for i in range(4)])),simultaneous=True)
    for label,source_map,generators in [("local-null",null_map,null_generators),("scalar-contact",scalar_map,broken)]:
        for row,T in enumerate(generators):
            lhs=s.MutableSparseMatrix(252,252,{})
            for col in range(97):
                if source_map[row,col]:lhs+=source_map[row,col]*active_v[ordering[col]]
            assert clean(lhs-n*(T*D-shifted*T))==s.zeros(252)
        print("PASS:",label,"all nine source rows factor through the two original matter equations",flush=True)
    F=decode(modes["source_isometry"])
    Pfree=decode(modes["free_projection"])
    H0=decode(modes["original_H_constant"])
    Hspace=list(map(decode,modes["original_H_spatial"]))
    time_scale=s.sympify(modes["time_scale"])
    # Two distinct exterior sectors give actual elastic source legs without a flavor-exchange vertex.
    sigma=[s.Matrix([[0,1],[1,0]]),s.Matrix([[0,-s.I],[s.I,0]]),s.diag(1,-1)]
    def leg(degree,direction):
        block=next(item for item in modes["blocks"] if item["chirality"]==1 and item["degree"]==degree and item["kind"]=="singlet")
        frame=F[:,block["first_column"]:block["first_column"]+2]
        direction=s.Matrix(direction)
        projector=(s.eye(2)+sum((direction[i]*sigma[i] for i in range(3)),s.zeros(2)))/2
        column=next(i for i in range(2) if projector[:,i]!=s.zeros(2,1))
        spin=projector[:,column];spin=spin/s.sqrt((spin.H*spin)[0])
        vector=clean(frame*spin)
        momentum=s.sqrt(2)*direction/2
        energy=2*time_scale
        stationary=energy-omega*block["phase_charge"]
        derivative=s.Matrix([-s.I*stationary,*[s.I*x for x in momentum]])
        symbol=D.subs(dict(zip(p,derivative)))
        h=clean(time_scale*(H0+sum((momentum[i]/s.sqrt(2)*Hspace[i] for i in range(3)),s.zeros(252))))
        assert clean(symbol*vector)==s.zeros(252,1)
        assert clean(vector.H*S*symbol)==s.zeros(1,252)
        assert clean(h*vector-energy*vector)==s.zeros(252,1)
        assert (vector.H*vector)[0]==1 and Pfree*vector==vector
        return {"degree":degree,"vector":vector,"momentum":momentum,"frequency":energy,
            "stationary_frequency":stationary,"phase_charge":block["phase_charge"],"derivative":derivative}
    legs=[leg(4,[0,0,1]),leg(4,[1,0,0]),leg(2,[0,0,-1]),leg(2,[-1,0,0])]
    def current(outgoing,incoming):
        answer=[]
        pin=dict(zip(p,incoming["derivative"]));pout=dict(zip(p,outgoing["derivative"]))
        for field in ordering:
            a=active_v[field].subs(pin);b=active_v[field].subs(pout)
            value=s.sqrt(2)*(outgoing["vector"].H*(S*a+b.H*S)*incoming["vector"])[0]/2
            answer.append(s.simplify(value))
        return s.Matrix(answer)
    j1=current(legs[1],legs[0]);j2=current(legs[3],legs[2])
    r1=legs[0]["derivative"]-legs[1]["derivative"]
    r2=legs[2]["derivative"]-legs[3]["derivative"]
    assert r1+r2==s.zeros(4,1) and r1[0]==0
    assert sum((item["momentum"] for item in [legs[0],legs[2]]),s.zeros(3,1))==sum((item["momentum"] for item in [legs[1],legs[3]]),s.zeros(3,1))
    assert j1!=s.zeros(97,1) and j2!=s.zeros(97,1)
    for j,rvalue in [(j1,r1),(j2,r2)]:
        sub=dict(zip(transfer,rvalue))
        assert clean(null_map.subs(sub)*j)==s.zeros(9,1)
        assert clean(scalar_map.subs(sub)*j)==s.zeros(9,1)
        assert clean(decode(exchange["independent_dual_source_map"])*j)==s.zeros(24,1)
    assert current(legs[3],legs[0])==current(legs[1],legs[2])==s.zeros(97,1)
    print("PASS: actual unit free legs generate nonzero compatible currents; all scalar contacts and complementary source vanish",flush=True)
    # Consume the complete original dynamic block, not a selected gauge-only exchange.
    sub=dict(zip(exchange_p,r1));negative_sub=dict(zip(exchange_p,-r1))
    A=decode(exchange["canonical_operator"]).subs(sub).applyfunc(s.simplify)
    J79=decode(exchange["canonical_source_map"])
    f1=clean(J79.subs(sub)*j1);f2=clean(J79.subs(negative_sub)*j2)
    domain=s.QQ.algebraic_field(s.sqrt(2),s.sqrt(15),s.I)
    Am=DomainMatrix.from_Matrix(A).convert_to(domain)
    fm=DomainMatrix.from_Matrix(f1).convert_to(domain)
    response_num,response_den=Am.solve_den(fm,method="rref")
    assert Am*response_num==fm*response_den
    response=(response_num.to_Matrix()/domain.to_sympy(response_den)).applyfunc(s.simplify)
    assert clean(A*response-f1)==s.zeros(79,1)
    contact=decode(exchange["total_contact_kernel"]).subs(sub)
    dynamic=s.simplify((f2.T*response)[0])
    local=s.simplify((j2.T*contact*j1)[0])
    field_response=clean(decode(exchange["contact_field_response"]).subs(sub)*j1+
        decode(exchange["canonical_field_lift"]).subs(sub)*response)
    H=s.MutableSparseMatrix(289,289,{})
    for i,j,powers,value in active["Fourier_Jacobi_entries"]:
        H[i,j]+=s.sympify(value)*s.prod(r1[mu]**power for mu,power in enumerate(powers))
    injected=s.MutableSparseMatrix(289,1,{})
    for i,field in enumerate(ordering):injected[field]=j1[i]
    assert clean(H*field_response-injected)==s.zeros(289,1)
    # Cross term of -1/2 jGj: the two assignments sum to the symmetric bilinear coefficient.
    direct=s.simplify(-dynamic-local)
    print("source elastic direct kernel:",direct,"; dynamic",dynamic,"; contact",local,flush=True)
    result={
        "scope":"GENERATED_FREE_ON_SHELL_MATTER_SOURCES_AND_ORIGINAL_ELASTIC_TREE_KERNEL",
        "all_158_real_vertices_preserve_phase_charge":True,
        "all_nine_source_compatibility_rows_factor_through_Dirac_equations":True,
        "all_nine_scalar_contact_sources_factor_through_Dirac_equations":True,
        "Ward_identity":"SourceMap(r)*V(p)=N[T D(p)-D(p-r)T]",
        "on_shell_transfer":"r=p_in-p_out; p0=-I*stationary_frequency, pj=I*k_j",
        "phase_readback":"nonzero vertices require equal Qcharge, so original and stationary energy transfers agree",
        "legs":[{key:(encode(value) if isinstance(value,s.MatrixBase) else str(value))
            for key,value in item.items()} for item in legs],
        "first_transition_current":encode(j1),"second_transition_current":encode(j2),
        "opposite_transfer":encode(r1),"current_sources_are_nonzero_and_compatible":True,
        "cross_species_exchange_vertices_zero":True,
        "canonical_dynamic_response":encode(response),"full_289_positive_green_response":encode(field_response),
        "all_original_289_rows_with_actual_on_shell_source":True,
        "dynamic_bilinear":str(dynamic),"local_bilinear":str(local),"elastic_direct_tree_kernel":str(direct),
        "external_residue_LSZ_or_empirical_cross_section_identified":False}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+"\n")


if __name__=="__main__":main()
