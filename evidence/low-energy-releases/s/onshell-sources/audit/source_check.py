#!/usr/bin/env python3
"""Independent source Ward, coframe derivatives and actual exterior-leg audit."""
import argparse
import importlib.util
import itertools
import json
from pathlib import Path
import re
import sympy as s


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True)
    root=parser.parse_args().root.resolve();base=root/'Verification/physics/low-energy-phenomenology';audit=base/'onshell-sources/audit'
    frozen=json.loads((base/'onshell-sources/receipt.json').read_text())
    assert frozen==json.loads(Path('/tmp/onshell-sources-audit-replay.json').read_text())
    vertices=json.loads((base/'matter-vertices/receipt.json').read_text());exchange=json.loads((base/'matter-vertices/exchange.json').read_text())
    active=json.loads((base/'active-gauge/receipt.json').read_text());phase=json.loads((base/'full-phase/receipt.json').read_text())
    modes=json.loads((base/'matter-modes/source.json').read_text())
    assert vertices['source_sha256']==phase['source_sha256']==modes['source_sha256']
    p=s.symbols('p0:4',real=True);r=s.symbols('r0:4',real=True);symbols={str(x):x for x in p+r}
    def decode(record):return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(v,locals=symbols) for i,j,v in record['entries']})
    def clean(matrix):return s.SparseMatrix(matrix).applyfunc(s.expand)
    def equal(left,right):assert not clean(left-right).todok()
    eye=lambda n:s.eye(n,cls=s.SparseMatrix)
    n=s.sympify(phase['source_lapse']);omega=s.sympify(phase['source_frequency']);scale=n*s.sqrt(2)
    principal=list(map(decode,phase['principal_coefficients']));Y=decode(phase['original_Y']);Q=decode(phase['phase_generator'])
    D=decode(phase['stationary_primal_constant'])+sum((a*x for a,x in zip(principal,p)),s.zeros(252,cls=s.SparseMatrix))
    equal(D,decode(vertices['full_stationary_Dirac_operator']))
    core=root/'Lean/SaturationMonoid/PhysicsCore';gamma=[];text=(core/'DiracCliffordRepresentation.lean').read_text()
    for name in ('Zero','One','Two','Three'):
        literal=re.search(r'def diracGamma'+name+r'\s*:.*?:=\s*!!\[(.*?)\]',text,re.S).group(1)
        gamma.append(s.SparseMatrix([[s.sympify(x.strip().replace('Complex.I','I')) for x in row.split(',')] for row in literal.split(';')]))
    Gamma=[s.kronecker_product(g,eye(63)) for g in gamma];S=clean(s.kronecker_product(gamma[0]*s.diag(-1,-1,1,1),eye(63)))
    equal(S.H,S);equal(Q.H,Q)
    spec=importlib.util.spec_from_file_location('independent_exterior',base/'mixed-symbol/audit/independent_check.py')
    helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
    def lift(fundamental):return s.kronecker_product(eye(4),s.diag(*(helper.exterior(fundamental,d) for d in (6,2,4)),cls=s.SparseMatrix))
    native={}
    for group in ((0,1,2),(3,4)):
        for a,b in itertools.combinations(group,2):
            native[f'A{a}{b}']=s.SparseMatrix(7,7,{(a,b):1,(b,a):-1})
            native[f'S{a}{b}']=s.SparseMatrix(7,7,{(a,b):s.I,(b,a):s.I})
        for a in group[:-1]:native[f'D{a}-{group[-1]}']=s.SparseMatrix(7,7,{(a,a):s.I,(group[-1],group[-1]):-s.I})
    native['Y']=s.diag(0,0,0,0,0,s.I,-s.I)
    rho=[clean(lift(native[label])) for label in active['native_P286_labels']]
    text=(core/'Stage9C/Material/SpinPair/ColorDoublet.lean').read_text().split('def sourceColorPauli',1)[1].split('theorem',1)[0]
    color=[s.SparseMatrix([[s.sympify(x.strip().replace('Complex.I','I')) for x in row.split(',')] for row in literal.split(';')])
        for literal in re.findall(r'!!\[(.*?)\]',text,re.S)]
    color_rho=[clean(lift(s.diag(t,s.zeros(5)))) for t in color]
    text=(core/'PointwiseDiracSpinConnectionLift.lean').read_text()
    first=[int(x) for x in re.search(r'def lorentzBivectorFirst.*?!\[(.*?)\]',text,re.S).group(1).split(',')]
    second=[int(x) for x in re.search(r'def lorentzBivectorSecond.*?!\[(.*?)\]',text,re.S).group(1).split(',')]
    pairs=list(zip(first,second));assert pairs[4]==(3,1)
    lorentz=[s.kronecker_product(gamma[a]*gamma[b]/2,eye(63)) for a,b in pairs]
    connections=[s.zeros(252,cls=s.SparseMatrix)]+[
        s.sqrt(2)*lorentz[j+3]+3*s.sqrt(2)*color_rho[j]/5 for j in range(3)]
    equal(sum((principal[mu]*connections[mu] for mu in range(4)),s.zeros(252,cls=s.SparseMatrix)),decode(phase['original_constant_B']))
    primitive=[decode(item['operator']) for item in vertices['primitive_vertices']]
    assert len(primitive)==158
    for operator in primitive:equal(Q*S*operator,S*operator*Q)
    # Fresh Jacobi derivatives of the actual coframe coefficient, including density*Y.
    inverse=s.diag(1/n,1,1,1)
    coframe={tuple(item['coordinate']):decode(item['operator']) for item in vertices['primitive_vertices'] if item['group']=='coframe'}
    for a,mu in itertools.product(range(4),repeat=2):
        h=s.SparseMatrix(4,4,{(a,mu):1});dv=n*s.trace(inverse*h)
        dp=n*(s.trace(inverse*h)*inverse-inverse*h*inverse)
        expected=dv*Y
        for direction,internal in itertools.product(range(4),repeat=2):
            if dp[direction,internal]:
                kinetic=s.I*Gamma[internal]*(p[direction]*eye(252)+connections[direction])
                if direction==0:kinetic+=omega*Gamma[internal]*Q
                expected+=dp[direction,internal]*kinetic
        equal(coframe[a,mu],expected)
    ordered=exchange['source_field_indices'];active_v={item['field']:decode(item['operator']) for item in vertices['active_289_bosonic_source_operators']}
    V=[active_v[field] for field in ordered]
    null=decode(exchange['local_source_compatibility_map']).subs(dict(zip(p,r)))
    scalar_entry=next(item for item in exchange['source_contact_terms'] if item['groups']==['scalar_Ward'])
    scalar=decode(scalar_entry['source_map']).subs(dict(zip(p,r)))
    broken=[rho[i] for i in active['Ward_constraint_elimination']['broken_parameter_columns']]
    Ts=color_rho+lorentz
    ward_reports=[]
    for label,source_map,generators in (('null',null,Ts),('scalar_contact',scalar,broken)):
        assert source_map.shape==(9,97) and len(generators)==9
        for row,T in enumerate(generators):
            lhs=sum((source_map[row,col]*V[col] for col in range(97) if source_map[row,col]),s.zeros(252,cls=s.SparseMatrix))
            # Reconstruct each of the eight independent derivative coefficients.
            rhs=n*(T*decode(phase['stationary_primal_constant'])-decode(phase['stationary_primal_constant'])*T)
            rhs+=n*sum((p[mu]*(T*principal[mu]-principal[mu]*T)+r[mu]*principal[mu]*T for mu in range(4)),s.zeros(252,cls=s.SparseMatrix))
            equal(lhs,rhs)
            assert all(s.im(value)==0 for value in source_map[row,:])
        ward_reports.append({'map':label,'rows':9,'all_eight_formal_variables':True})
    # Reversing the transfer sign changes the actual source identity.
    wrong=n*(Ts[0]*D-D.subs(dict(zip(p,[p[i]+r[i] for i in range(4)])),simultaneous=True)*Ts[0])
    right=n*(Ts[0]*D-D.subs(dict(zip(p,[p[i]-r[i] for i in range(4)])),simultaneous=True)*Ts[0])
    assert clean(wrong-right)!=s.zeros(252)
    F=decode(modes['source_isometry']);Pfree=decode(modes['free_projection'])
    scalar_count=0
    for item,operator in zip(vertices['primitive_vertices'],primitive):
        if item['group']=='scalar':equal(F.H*S*operator,s.zeros(216,252));scalar_count+=1
    assert scalar_count==70
    f24=decode(exchange['independent_dual_source_map'])
    assert all(not value.free_symbols for value in f24)
    for row in range(24):
        operator=sum((f24[row,col]*V[col] for col in range(97) if f24[row,col]),s.zeros(252,cls=s.SparseMatrix))
        assert not operator.free_symbols
        equal(S*operator+operator.H*S,s.zeros(252))
    print('PASS full252/8-variable Ward, actual coframe derivatives,158 Q charges,70 scalar and24 complement sources',flush=True)

    sigma=[s.Matrix([[0,1],[1,0]]),s.Matrix([[0,-s.I],[s.I,0]]),s.diag(1,-1)]
    spin=[-s.I*s.kronecker_product(gamma[a]*gamma[b],eye(63)) for a,b in ((2,3),(3,1),(1,2))]
    legs=[]
    for index,(degree,direction) in enumerate(((4,[0,0,1]),(4,[1,0,0]),(2,[0,0,-1]),(2,[-1,0,0]))):
        selected=next(item for item in modes['blocks'] if item['degree']==degree and item['chirality']==1 and item['kind']=='singlet')
        assert selected['dimension']==2 and selected['phase_charge']==1
        frame=F[:,selected['first_column']:selected['first_column']+2]
        equal(frame.H*frame,eye(2));equal(Q*frame,frame)
        lower,upper={2:(7,28),4:(28,63)}[degree]
        assert all(row//63 in (2,3) and lower<=row%63<upper for row,col in frame.todok())
        equal(s.kronecker_product(s.diag(-1,-1,1,1),eye(63))*frame,frame)
        for action in color_rho:equal(action*frame,s.zeros(252,2))
        for actual_sigma,pauli in zip(spin,sigma):equal(actual_sigma*frame,frame*pauli)
        direction=s.Matrix(direction);projector=(eye(2)+sum((direction[i]*sigma[i] for i in range(3)),s.zeros(2)))/2
        column=next(i for i in range(2) if projector[:,i]!=s.zeros(2,1));small=projector[:,column]
        small=small/s.sqrt((small.H*small)[0]);u=clean(frame*small)
        momentum=direction/s.sqrt(2);energy=2*scale;stationary=energy-omega
        derivative=s.Matrix([-s.I*stationary,*list(s.I*momentum)])
        equal(sum((direction[i]*spin[i]*u for i in range(3)),s.zeros(252,1)),u)
        equal(Pfree*u,u);assert (u.H*u)[0]==1
        symbol=D.subs(dict(zip(p,derivative)));equal(symbol*u,s.zeros(252,1));equal(u.H*S*symbol,s.zeros(1,252))
        original_H=n*Gamma[0]*(decode(phase['original_constant_B'])+Y)-n*sum((momentum[i]*Gamma[0]*Gamma[i+1] for i in range(3)),s.zeros(252,cls=s.SparseMatrix))
        equal(original_H*u,energy*u)
        record=frozen['legs'][index]
        for key,value in (('vector',u),('momentum',momentum),('derivative',derivative)):equal(value,decode(record[key]))
        assert degree==int(record['degree']) and s.simplify(s.sympify(record['frequency'])-energy)==0
        assert s.simplify(s.sympify(record['stationary_frequency'])-stationary)==0 and s.sympify(record['phase_charge'])==1
        legs.append((u,derivative,momentum,selected))
    def transition(outgoing,incoming,operators):
        out,pout=outgoing[:2];inside,pin=incoming[:2]
        forward=s.Matrix([s.simplify((out.H*S*op.subs(dict(zip(p,pin)))*inside)[0]) for op in operators])
        reverse=s.Matrix([s.simplify((out.H*op.subs(dict(zip(p,pout))).H*S*inside)[0]) for op in operators])
        return s.sqrt(2)*(forward+reverse)/2,forward,reverse
    j1,first1,second1=transition(legs[1],legs[0],V);j2,first2,second2=transition(legs[3],legs[2],V)
    equal(j1,decode(frozen['first_transition_current']));equal(j2,decode(frozen['second_transition_current']))
    r1=legs[0][1]-legs[1][1];r2=legs[2][1]-legs[3][1]
    equal(r1,-r2);equal(r1,decode(frozen['opposite_transfer']));assert r1[0]==0
    equal(legs[0][2]+legs[2][2],legs[1][2]+legs[3][2])
    assert j1!=s.zeros(97,1) and j2!=s.zeros(97,1)
    for j,left,right,transfer in ((j1,first1,second1,r1),(j2,first2,second2,r2)):
        for source_map in (null,scalar):
            numerical=source_map.subs(dict(zip(r,transfer)))
            equal(numerical*left,s.zeros(9,1));equal(numerical*right,s.zeros(9,1));equal(numerical*j,s.zeros(9,1))
        equal(f24*j,s.zeros(24,1))
    for outgoing,incoming in ((legs[3],legs[0]),(legs[1],legs[2])):
        cross,_,_=transition(outgoing,incoming,primitive);equal(cross,s.zeros(158,1))
    out,pout=legs[1][:2];inside,pin=legs[0][:2]
    wrong_current=s.Matrix([s.simplify(s.sqrt(2)*(out.H*(S*op.subs(dict(zip(p,pin)))+op.subs(dict(zip(p,pin))).H*S)*inside)[0]/2) for op in V])
    assert wrong_current!=j1
    wrong_ward=clean(null.subs(dict(zip(r,r1)))*wrong_current)
    assert wrong_ward!=s.zeros(9,1)
    axial=[s.sqrt(2)*S*Gamma[a]*s.kronecker_product(s.diag(-1,-1,1,1),eye(63)) for a in range(4)]
    axial1=s.Matrix([(legs[1][0].H*op*legs[0][0])[0] for op in axial])
    axial2=s.Matrix([(legs[3][0].H*op*legs[2][0])[0] for op in axial])
    contact=s.simplify((axial2.T*(3*n*s.diag(1,-1,-1,-1)/8)*axial1)[0])
    assert contact==-9*s.sqrt(30)/50
    result={'status':'PASS','replay_equal':True,'Ward_maps':ward_reports,'all158_phase_charge_commutators':True,
        'all16_coframe_density_and_external_derivative_vertices_rebuilt':True,'all70_free_scalar_vertices_zero':True,
        'all24_prepared_complement_sources_zero_as_operators':True,'four_legs_unit_original_positive_helicity_on_shell':True,
        'selected_frames_actual_right_chirality_and_exterior_support':True,
        'source_selected_columns':[legs[i][3]['first_column'] for i in range(4)],
        'each_Hermitian_half_satisfies_both_nine_row_maps':True,'all158_cross_grade_vertices_zero':True,
        'negative_controls':['reversed_transfer_sign','using_incoming_derivative_on_both_coframe_legs'],
        'independent_axial_contact':str(contact),'original_energy':'2*N*sqrt(2)','stationary_energy':'2*N*sqrt(2)-omega',
        'upstream_matter_modes_independent_certificate_required':True}
    (audit/'source-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS actual four original free legs, both Hermitian Ward halves, full cross-grade zeros and independent axial contact',flush=True)


if __name__=='__main__':main()
