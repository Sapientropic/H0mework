#!/usr/bin/env python3
"""Independent source second-variation probes and polynomial equivalence audit.

Does not import active-gauge/compute.py or its Jet/Number arithmetic. The four
action blocks are differentiated as matrix bilinears, using cofactor Taylor
coefficients and the defining Hodge intertwining equation.
"""
from __future__ import annotations
import argparse
from collections import defaultdict
import importlib.util
import itertools
import json
from pathlib import Path
import random
import re
import sympy as s

F=s.QQ.algebraic_field(s.sqrt(2),s.sqrt(15))
P0=(0,0,0,0)
PAIRS=[(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)]

def coeff(value):
    return F.from_sympy(s.sympify(value))

def polynomial(rows):
    return {(i,j,tuple(power)):coeff(value) for i,j,power,value in rows}

def cleaned(values):
    return {key:value for key,value in values.items() if value}

def product(left,right):
    rows=defaultdict(list)
    for (i,j,p),v in right.items(): rows[i].append((j,p,v))
    answer=defaultdict(lambda:F.zero)
    for (i,k,p),v in left.items():
        for j,q,w in rows[k]:
            answer[i,j,tuple(a+b for a,b in zip(p,q))]+=v*w
    return cleaned(answer)

def same(left,right):
    assert cleaned(left)==cleaned(right)

def identity(indices):
    return {(i,i,P0):F.one for i in indices}

def adjoint(matrix):
    return {(j,i,p):(-1)**sum(p)*v for (i,j,p),v in matrix.items()}

def wedge(e):
    return s.Matrix(6,6,lambda i,j:e[PAIRS[i][0],PAIRS[j][0]]*e[PAIRS[i][1],PAIRS[j][1]]-
        e[PAIRS[i][0],PAIRS[j][1]]*e[PAIRS[i][1],PAIRS[j][0]])

def unpack(value):
    return s.SparseMatrix(*value['shape'],{(i,j):s.sympify(v) for i,j,v in value['entries']})

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    args=parser.parse_args(); root=args.root.resolve()
    directory=root/'Verification/physics/low-energy-phenomenology'
    receipt=json.loads((directory/'active-gauge/receipt.json').read_text())
    replay=json.loads(Path('/tmp/active-gauge-audit-replay.json').read_text())
    for data in (receipt,replay): data.pop('elapsed_seconds',None)
    assert receipt==replay
    core=root/'Lean/SaturationMonoid/PhysicsCore'
    spec=importlib.util.spec_from_file_location('certified_exterior_audit',directory/'mixed-symbol/audit/independent_check.py')
    exterior_audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(exterior_audit)
    exterior,realify=exterior_audit.exterior,exterior_audit.realify
    sector=json.loads((directory/'active-sector/receipt.json').read_text())
    names=receipt['basis_names']
    text=(core/'SU7ExteriorYukawaMassSpectrum.lean').read_text()
    block=text.split('def finiteGenerationScalarSubset :',1)[1].split('\ndef ',1)[0]
    terms=re.findall(r'\|\s*[01],\s*[01]\s*=>\s*\{([^}]+)\}',block)
    vacuum={tuple(sorted(names.index(x.strip()) for x in term.split(','))):1 for term in terms}
    b4=list(itertools.combinations(range(7),4))
    v=s.Matrix([vacuum.get(word,0) for word in b4]).col_join(s.zeros(35,1))
    fundamental=[]
    for group in ((0,1,2),(3,4)):
        for a,b in itertools.combinations(group,2):
            fundamental.extend([s.SparseMatrix(7,7,{(a,b):1,(b,a):-1}),s.SparseMatrix(7,7,{(a,b):s.I,(b,a):s.I})])
        for a in group[:-1]: fundamental.append(s.SparseMatrix(7,7,{(a,a):s.I,(group[-1],group[-1]):-s.I}))
    fundamental.append(s.diag(0,0,0,0,0,s.I,-s.I))
    rho=[realify(exterior(t,4)) for t in fundamental]
    orbit=s.Matrix.hstack(*[a*v for a in rho]); E=orbit[:,receipt['J_independent_columns']]
    assert E==unpack(sector['J_basis']) and E.rank()==9
    gram=s.Matrix(12,12,lambda i,j:s.re(-s.trace(fundamental[i]*fundamental[j])))
    native=gram.copy(); native[-1,-1]=1
    assert gram[-1,-1]==2
    inverse_gram=gram.inv()
    gamma=[]
    text=(core/'DiracCliffordRepresentation.lean').read_text()
    for name in ('Zero','One','Two','Three'):
        body=re.search(r'def diracGamma'+name+r'\s*:.*?:=\s*!!\[(.*?)\]',text,re.S).group(1)
        gamma.append(s.Matrix([[s.sympify(x.strip().replace('Complex.I','I')) for x in row.split(',')] for row in body.split(';')]))
    n=3*s.sqrt(30)/25; sigma=s.Rational(1,2); spin=s.sqrt(2); alpha=3*spin/5
    frequency=3*n*(spin-alpha)/2
    e0=s.diag(n,1,1,1); inverse_e0=e0.inv(); E0=wedge(e0)
    star=s.zeros(6); W=s.zeros(6); eta=s.diag(-1,1,1,1)
    for i in range(3): star[i,i+3]=1; star[i+3,i]=-1; W[i,i+3]=W[i+3,i]=1
    star0=E0.inv()*star*E0
    color=[s.Matrix([[0,s.I/2],[s.I/2,0]]),s.Matrix([[0,s.Rational(1,2)],[-s.Rational(1,2),0]]),s.diag(s.I/2,-s.I/2)]
    A0=[s.zeros(7)]+[alpha*s.diag(t,s.zeros(5)) for t in color]
    O=[]
    for a,b in PAIRS:
        t=s.zeros(4);t[a,b]=eta[a,a];t[b,a]=-eta[b,b];O.append(t)
    omega0=[s.zeros(4)]+[spin*O[mu+2] for mu in range(1,4)]
    def lie_coordinates(matrix):
        return inverse_gram*s.Matrix([s.re(-s.trace(t*matrix)) for t in fundamental])
    F0=s.Matrix.vstack(*[lie_coordinates(A0[mu]*A0[nu]-A0[nu]*A0[mu]).T for mu,nu in PAIRS])
    gaugeB0=-star0*F0/sigma
    R0=s.Matrix(6,6,lambda i,j:eta[PAIRS[i][0],PAIRS[i][0]]*
        (omega0[PAIRS[j][0]]*omega0[PAIRS[j][1]]-omega0[PAIRS[j][1]]*omega0[PAIRS[j][0]])[PAIRS[i][0],PAIRS[i][1]])
    B0=star*E0; signs=s.diag(-1,-1,-1,1,1,1); multiplier0=star*B0-signs*R0
    prepared=s.Matrix([0,1,0,-1,0,0,0,1,0,-1,0,0]); dual0=spin*prepared.T
    G=[s.kronecker_product(g,s.eye(3)) for g in gamma]; gamma5=s.kronecker_product(s.diag(-1,-1,1,1),s.eye(3))
    Hacts=[t[:3,:3]+t[5,5]*s.eye(3) for t in fundamental]
    fields=receipt['fields']; jets=receipt['jet_coordinates']
    indices={(item['group'],tuple(item['coordinate'])):i for i,item in enumerate(fields)}
    jet_indices={(item['field'],item['derivative']):j for j,item in enumerate(jets)}
    assert len(fields)==289 and len(jets)==637
    raw_blocks={name:[(pair,coeff(value)) for pair,value in entries] for name,entries in receipt['quadratic_action_blocks'].items()}
    phase_controls=[]; native_controls=[]; contact_controls=[]
    # Dense rational 1-jets exercise every value/derivative and all four action blocks.
    for seed in (17,31,47,71):
        randomizer=random.Random(seed); values=[randomizer.randrange(-2,3) for _ in jets]
        def q(group,*coordinate,derivative=-1):
            j=jet_indices.get((indices[group,coordinate],derivative));return 0 if j is None else values[j]
        h=s.Matrix(4,4,lambda i,j:q('coframe',i,j)); deformation=inverse_e0*h
        tr=s.trace(deformation); det2=(tr**2-s.trace(deformation*deformation))/2
        E1=wedge(e0+h)-E0-wedge(h); E2=wedge(h)
        star1=E0.inv()*(star*E1-E1*star0)
        star2=E0.inv()*(star*E2-E1*star1-E2*star0)
        A=[sum((q('gauge_A',mu,c)*fundamental[c] for c in range(12)),s.zeros(7)) for mu in range(4)]
        F1=s.Matrix.vstack(*[lie_coordinates(
            sum(((q('gauge_A',nu,c,derivative=mu)-q('gauge_A',mu,c,derivative=nu))*fundamental[c] for c in range(12)),s.zeros(7))+
            A0[mu]*A[nu]+A[mu]*A0[nu]-A0[nu]*A[mu]-A[nu]*A0[mu]).T for mu,nu in PAIRS])
        F2=s.Matrix.vstack(*[lie_coordinates(A[mu]*A[nu]-A[nu]*A[mu]).T for mu,nu in PAIRS])
        gb=s.Matrix(6,12,lambda i,j:q('gauge_B',i,j))
        gauge_terms=gb.T*W*F1+gaugeB0.T*W*F2-sigma/2*(gb.T*W*star0*gb+
            gb.T*W*star1*gaugeB0+gaugeB0.T*W*star1*gb+gaugeB0.T*W*star2*gaugeB0)
        gauge_q2=sum(native[i,j]*gauge_terms[i,j] for i,j in itertools.product(range(12),repeat=2))
        native_controls.append(coeff(s.expand(gauge_terms[11,11])))
        contact_controls.append(coeff(s.expand(sum(native[i,j]*(gaugeB0.T*W*F2)[i,j] for i,j in itertools.product(range(12),repeat=2)))))
        z=s.Matrix([q('scalar_J',i) for i in range(9)]); scalar_q2=-n*(E*z).dot(E*z)
        for mu in range(4):
            D1=E*s.Matrix([q('scalar_J',i,derivative=mu) for i in range(9)])
            a0=lie_coordinates(A0[mu])
            D1+=sum((rho[c]*(a0[c]*E*z+q('gauge_A',mu,c)*v) for c in range(12)),s.zeros(70,1))
            scalar_q2+=n*s.Rational(1,2)*(-1/n**2 if mu==0 else 1)*D1.dot(D1)
        omega=[sum((q('Lorentz',mu,i)*O[i] for i in range(6)),s.zeros(4)) for mu in range(4)]
        R1=s.zeros(6);R2=s.zeros(6)
        for pair,(mu,nu) in enumerate(PAIRS):
            linear=omega0[mu]*omega[nu]+omega[mu]*omega0[nu]-omega0[nu]*omega[mu]-omega[nu]*omega0[mu]
            square=omega[mu]*omega[nu]-omega[nu]*omega[mu]
            for internal,(a,b) in enumerate(PAIRS):
                R1[internal,pair]=eta[a,a]*linear[a,b]+q('Lorentz',nu,internal,derivative=mu)-q('Lorentz',mu,internal,derivative=nu)
                R2[internal,pair]=eta[a,a]*square[a,b]
        bg=s.Matrix(6,6,lambda i,j:q('gravity_B',i,j)); multiplier=s.Matrix(6,6,lambda i,j:q('multiplier',i,j))
        gravity_q2=(s.trace(bg*W*R1.T+B0*W*R2.T)-s.trace(signs*bg*W*(star*bg).T)/2+
            s.trace(signs*multiplier*W*(bg-star*E1).T)-s.trace(signs*multiplier0*W*(star*E2).T))
        xi=s.Matrix([q('primal_H',0,i//3,i%3)+s.I*q('primal_H',1,i//3,i%3) for i in range(12)])
        zeta=s.Matrix([[q('dual_H',0,i//3,i%3)+s.I*q('dual_H',1,i//3,i%3) for i in range(12)]])
        momenta=[n*inverse_e0,n*(tr*inverse_e0-inverse_e0*h*inverse_e0),
                 n*(det2*inverse_e0-tr*inverse_e0*h*inverse_e0+inverse_e0*h*inverse_e0*h*inverse_e0)]
        dirac_q2=0; phase_difference=0
        for mu in range(4):
            connection0=sum((s.kronecker_product(gamma[a]*gamma[b]/2,s.eye(3))*
                (spin if mu>0 and pair==mu+2 else 0) for pair,(a,b) in enumerate(PAIRS)),s.zeros(12))
            a0=lie_coordinates(A0[mu])
            connection0+=sum((a0[c]*s.kronecker_product(s.eye(4),Hacts[c]) for c in range(12)),s.zeros(12))
            connection1=sum((q('Lorentz',mu,pair)*s.kronecker_product(gamma[a]*gamma[b]/2,s.eye(3)) for pair,(a,b) in enumerate(PAIRS)),s.zeros(12))
            connection1+=sum((q('gauge_A',mu,c)*s.kronecker_product(s.eye(4),Hacts[c]) for c in range(12)),s.zeros(12))
            derivative=s.Matrix([q('primal_H',0,i//3,i%3,derivative=mu)+s.I*q('primal_H',1,i//3,i%3,derivative=mu) for i in range(12)])
            for internal in range(4):
                K0=s.I*G[internal]*connection0*prepared
                K1=s.I*G[internal]*(derivative+connection0*xi+connection1*prepared)
                K2=s.I*G[internal]*connection1*xi
                if mu==0:
                    K0+=frequency*G[internal]*gamma5*prepared;K1+=frequency*G[internal]*gamma5*xi
                    phase_difference+=frequency*((momenta[1][mu,internal]-n*tr*inverse_e0[mu,internal])*
                        s.re((zeta*G[internal]*gamma5*prepared+dual0*G[internal]*gamma5*xi)[0])+
                        (momenta[2][mu,internal]-n*det2*inverse_e0[mu,internal])*s.re((dual0*G[internal]*gamma5*prepared)[0]))
                dirac_q2+=(momenta[0][mu,internal]*s.re((zeta*K1+dual0*K2)[0])+
                    momenta[1][mu,internal]*s.re((zeta*K0+dual0*K1)[0])+momenta[2][mu,internal]*s.re((dual0*K0)[0]))
        phase_controls.append(coeff(s.expand(phase_difference)))
        independent={'gravity':gravity_q2,'gauge':gauge_q2,'scalar':scalar_q2,'Dirac':dirac_q2}
        for name,value in independent.items():
            expected=sum((c*values[pair[0]]*values[pair[1]] for pair,c in raw_blocks[name]),F.zero)
            assert coeff(s.expand(value))==expected,(seed,name,s.simplify(value-F.to_sympy(expected)))
        print('PASS source action: independent four-block dense 1-jet',seed,flush=True)
    assert any(phase_controls) and any(native_controls) and any(contact_controls)

    H=polynomial(receipt['Fourier_Jacobi_entries']); same(H,adjoint(H))
    # Independently recover every Euler monomial from the stored four source quadratics.
    recovered=defaultdict(lambda:F.zero)
    for entries in raw_blocks.values():
        for pair,c in entries:
            for a,b in (pair,pair[::-1]):
                left,right=jets[a],jets[b];power=[0]*4
                for d in (left['derivative'],right['derivative']):
                    if d>=0:power[d]+=1
                recovered[left['field'],right['field'],tuple(power)]+=(-c if left['derivative']>=0 else c)
    same(H,recovered)
    current=H
    for step in receipt['algebraic_Schur_steps']:
        removed=set(step['eliminated_fields']); present={i for key in current for i in key[:2]};keep=present-removed
        A={key:value for key,value in current.items() if key[0] in removed and key[1] in removed}
        assert all(power==P0 for _,_,power in A)
        inverse={(i,j,P0):coeff(v) for i,j,v in step['algebraic_block_inverse']}
        same(product(A,inverse),identity(removed));same(product(inverse,A),identity(removed))
        write=polynomial(step['write_back_auxiliary_from_retained'])
        lift={**identity(keep),**write}; transformed=product(current,lift)
        assert all(row not in removed for row,_,_ in transformed)
        current={key:value for key,value in transformed.items() if key[0] in keep}
        same(current,adjoint(current)); assert len(keep)==step['remaining_real_coordinates']
        print('PASS independent two-sided inverse and exact write-back:',step['eliminated_groups'],len(keep),flush=True)
    same(current,polynomial(receipt['primitive_121_Fourier_Jacobi_entries']))
    T=polynomial(receipt['source_primitive_gauge_tangent'])
    torque=polynomial(receipt['H_p_times_T_p']);same(product(H,T),torque)
    expected=-2*n*E.T*orbit
    same(torque,{(i,j,P0):coeff(expected[i,j]) for i in range(9) for j in range(12) if expected[i,j]})
    assert expected.rank()==9
    broken=receipt['Ward_constraint_elimination']['broken_parameter_columns'];scalar=set(range(9));retained=set(range(9,121))
    L=identity(retained)
    for (field,column,power),value in T.items():
        if field<121 and column in broken:L[broken.index(column),field,power]=(-1)**sum(power)*value
    off={key:v for key,v in L.items() if not(key[0]==key[1] and key[2]==P0)}
    inverseL={**identity(range(121)),**{key:-v for key,v in off.items()}}
    same(product(L,inverseL),identity(range(121)));same(product(inverseL,L),identity(range(121)))
    transformed=product(L,current); generated={key:v for key,v in transformed.items() if key[0] in scalar}
    same(generated,polynomial(receipt['Ward_constraint_elimination']['generated_scalar_constraint_rows']))
    assert all(col in scalar and power==P0 for _,col,power in generated)
    inverseTorque=s.Matrix(receipt['Ward_constraint_elimination']['scalar_constraint_inverse']).applyfunc(s.sympify)
    torqueMatrix=s.Matrix(9,9,lambda i,j:F.to_sympy(generated.get((i,j,P0),F.zero)))
    assert (torqueMatrix*inverseTorque).applyfunc(s.simplify)==s.eye(9)
    final={key:v for key,v in transformed.items() if key[0] in retained and key[1] in retained}
    same(final,polynomial(receipt['equivalent_112_Fourier_Jacobi_entries']))
    assert len({i for key in final for i in key[:2]})==112
    print('PASS independent Ward torque, polynomial invertible row operation and 112-row equivalence',flush=True)
    # Read the source's already kernel-checked seven-state Jacobian on indices 0,1,2,3,6.
    jacobian=s.Matrix([[0,n,0,0,0],[-12*n,0,0,0,0],[0,0,0,1/n,0],
                      [0,0,s.Rational(50,3)*n,0,0],[-3*n*spin,0,s.Rational(5,2)*n,0,0]])
    assert (jacobian-s.Matrix(receipt['source_homogeneous_Jacobian']).applyfunc(s.sympify)).applyfunc(s.simplify)==s.zeros(5)
    lift=s.SparseMatrix(289,5,{(i,j):s.sympify(value) for i,j,value in receipt['source_homogeneous_field_lift']})
    flows=[lift,lift*jacobian,lift*jacobian*jacobian]
    residual=defaultdict(lambda:F.zero)
    for (i,j,power),value in H.items():
        if any(power[1:]):continue
        for column in range(5):residual[i,column]+=value*coeff(s.expand(flows[power[0]][j,column]))
    assert not cleaned(residual) and lift.rank()==5
    x=s.Symbol('X');expected_char=x*(x*x+s.Rational(648,125))*(x*x-s.Rational(50,3))
    assert s.expand(jacobian.charpoly(x).as_expr()-expected_char)==0
    print('PASS original five-state Jacobian, all 289 x 5 lifted rows and exact characteristic polynomial',flush=True)
    output={'status':'PASS','four_action_dense_jet_probes':[17,31,47,71],
            'negative_controls':['native_U1_trace_substitution','delete_B0_commutator','freeze_phase_inverse_coframe'],
            'all_Euler_monomials_recovered':len(H),'Schur_dimensions':[289,217,145,121],
            'both_inverse_sides_and_writebacks':True,'Ward_torque_rank':9,
            'polynomial_row_change_inverse_verified':True,'equivalent_remaining_rows':112,
            'source_five_state_intertwining':[289,5],
            'thirteen_gauge_kernels_assumed':False,'physical_poles_certified':False}
    (directory/'active-gauge/audit/independent-receipt.json').write_text(json.dumps(output,indent=2)+'\n')

if __name__=='__main__':main()
