#!/usr/bin/env python3
"""Source phase normalization, Neumann elimination, original action and Noether audit."""
from functools import reduce
import json
from pathlib import Path
import re

import sympy as s

HERE=Path(__file__).resolve().parent
BASE=HERE.parent
PHYSICS=BASE.parent
ROOT=next(path for path in HERE.parents if (path/'Lean/lean-toolchain').exists())
CORE=ROOT/'Lean/SaturationMonoid/PhysicsCore'
source=json.loads((PHYSICS/'active-gauge/receipt.json').read_text())
origin=json.loads((PHYSICS/'active-gauge/origin.json').read_text())
canonical=json.loads((PHYSICS/'canonical-active/receipt.json').read_text())
spectrum=json.loads((PHYSICS/'canonical-active/spectrum/receipt.json').read_text())
candidate=json.loads((BASE/'receipt.json').read_text())
fresh=json.loads(Path('/tmp/soft-phase-audit.json').read_text())
assert {k:v for k,v in candidate.items() if k!='elapsed_seconds'}=={k:v for k,v in fresh.items() if k!='elapsed_seconds'}
u,q1,q2,q3=s.symbols('u q1 q2 q3');variables=(u,q1,q2,q3)
p=s.symbols('p0 p1 p2 p3');n=s.sympify(source['source_lapse'])
substitution=dict(zip(p,(n*s.sqrt(2)*u,s.I*s.sqrt(2)*q1,s.I*s.sqrt(2)*q2,s.I*s.sqrt(2)*q3)))
negative={v:-v for v in variables};at_zero={v:0 for v in variables}
local={str(v):v for v in (*p,*variables)}


def clean(matrix):return s.SparseMatrix(matrix).applyfunc(s.expand)
def zero(matrix):return not any(s.expand(value) for value in s.SparseMatrix(matrix).todok().values())
def decode(entries,rows=None,cols=None):
    if isinstance(entries,dict):rows,cols=entries['shape'];entries=entries['entries']
    return s.SparseMatrix(rows,cols,{(i,j):s.sympify(value,locals=local) for i,j,value in entries})
def original_matrix(entries,rows,cols):
    out=s.MutableSparseMatrix(rows,cols,{})
    for i,j,powers,value in entries:
        out[i,j]+=s.sympify(value)*s.prod(substitution[v]**degree for v,degree in zip(p,powers))
    return clean(out)
def component(matrix,degree):
    values={}
    for (i,j),value in s.SparseMatrix(matrix).todok().items():
        selected=sum(coefficient*s.prod(v**a for v,a in zip(variables,powers))
            for powers,coefficient in s.Poly(value,*variables).terms() if sum(powers)==degree)
        if selected:values[i,j]=selected
    return s.SparseMatrix(matrix.rows,matrix.cols,values)
def degrees(matrix):
    return sorted({sum(powers) for value in s.SparseMatrix(matrix).todok().values()
                   for powers,coefficient in s.Poly(value,*variables).terms() if coefficient})
def trunc(matrix,order):return clean(sum((component(matrix,d) for d in range(order+1)),s.zeros(*matrix.shape)))


# Current source Gamma matrices and real independent-dual phase columns.
gamma_text=(CORE/'DiracCliffordRepresentation.lean').read_text()
def literal(body):
    return s.Matrix([[s.sympify(v.strip().replace('Complex.I','I'),locals={'I':s.I})
                      for v in row.split(',')] for row in body.split(';')])
gamma=[s.kronecker_product(literal(re.search(r'def diracGamma'+name+r'\s*:.*?:=\s*!!\[(.*?)\]',gamma_text,re.S).group(1)),s.eye(3))
       for name in ('Zero','One','Two','Three')]
g5match=re.search(r'def diracGammaFive.*?:=\s*Matrix.diagonal\s*!\[(.*?)\]',gamma_text,re.S);assert g5match
gamma5=s.kronecker_product(s.diag(*[s.sympify(v) for v in g5match.group(1).split(',')]),s.eye(3))
seed=s.Matrix([s.sympify(value) for value in source['actual_background']['primal_H']])
dual=s.sympify(source['actual_background']['dual_multiple'])*seed.T
assert dual==s.sqrt(2)*seed.T*gamma[0]*gamma5
Z=s.zeros(289,2)
for col,(primal,conjugate) in enumerate(((s.I*seed,-s.I*dual),(-s.I*gamma5*seed,-s.I*dual*gamma5))):
    for row,field in enumerate(source['fields']):
        if field['group'] not in ('primal_H','dual_H'):continue
        part,spin,color=field['coordinate'];vector=primal if field['group']=='primal_H' else conjugate
        Z[row,col]=(s.re if part==0 else s.im)(vector[3*spin+color])
assert Z==decode(origin['source_289_mode_columns'],289,5)[:,[1,3]]
assert Z==decode(candidate['source_phase_columns_289'])

scales=[]
for index in canonical['retained_canonical_fields']:
    field=source['fields'][9+index]
    value=s.sqrt(2) if field['group']=='gauge_A' else s.S.One
    if ((field['group']=='gauge_A' and field['coordinate'][0]==0) or
            (field['group']=='coframe' and field['coordinate'][1]==0)):value*=n
    scales.append(value)
assert list(map(str,scales))==candidate['field_scaling']
S=s.diag(*scales);Sinv=s.diag(*[1/value for value in scales])
C=decode(canonical['canonical_embedding_112_by_88'],112,88)
R=decode(canonical['constant_whole_equation_readback_112_by_88'],112,88)
Q=decode(canonical['quotient_readback'],79,88).subs(substitution)
section=decode(canonical['quotient_section'],88,79)
assert C*R.T*Z[9:121,:]==Z[9:121,:]
phase=clean(Sinv*Q*R.T*Z[9:121,:])
P=phase.subs(at_zero)
assert phase==decode(candidate['source_phase_section']) and P==decode(candidate['constant_phase_basis'])
heavy=candidate['heavy_indices'];pivots=candidate['phase_pivot_indices']
assert sorted(heavy+pivots)==list(range(79)) and len(heavy)==77 and len(pivots)==2
E=s.SparseMatrix(79,77,{(row,col):1 for col,row in enumerate(heavy)})
T=P.row_join(E);Tinv=decode(candidate['phase_and_heavy_basis_inverse'])
assert T*Tinv==s.eye(79) and Tinv*T==s.eye(79)
assert Tinv[:2,:]*phase==s.eye(2)
assert zero(phase-P-E*E.T*(phase-P)) and not zero(phase-P)

G=clean(S*decode(canonical['canonical_quotient_operator'],79,79).subs(substitution)*S/n)
assert degrees(G)==[0,1,2]
assert zero(G.subs(negative,simultaneous=True).T-G)
Gparts={degree:component(G,degree) for degree in (0,1,2)}
assert zero(Gparts[0]*P)
D={degree:clean(E.T*part*E) for degree,part in Gparts.items()}
B={degree:clean(E.T*part*P) for degree,part in Gparts.items()}
inverse=decode(candidate['heavy_origin_inverse'])
assert D[0]*inverse==s.eye(77) and inverse*D[0]==s.eye(77)
assert zero(B[0])
# A finite Neumann expansion applied directly to B independently reconstructs
# the recursive Taylor graph, including the order of its matrix products.
X1,X2=clean(inverse*D[1]),clean(inverse*D[2])
v1,v2=clean(inverse*B[1]),clean(inverse*B[2])
xv=clean(X1*v1);xxv=clean(X1*xv)
neumann={1:-v1,2:clean(xv-v2),3:clean(-xxv+X2*v1+X1*v2),
    4:clean(X1*xxv-X1*(X2*v1)-X2*xv-X1*(X1*v2)+X2*v2)}
for degree,value in neumann.items():
    assert degrees(value)==[degree]
    assert zero(value-decode(candidate['heavy_graph_homogeneous'][str(degree)]))
graph=clean(P+E*sum(neumann.values(),s.zeros(77,2)))
assert Tinv[:2,:]*graph==s.eye(2)
rows=clean(T.T*G*graph)
K=trunc(rows[:2,:],4)
assert K==decode(candidate['normalized_effective_operator_through_order_four'])
assert degrees(K)==[2,4]
row_lift=Tinv.T[:,:2]
remainder=clean(G*graph-row_lift*K)
assert degrees(remainder)==[5,6] and min(degrees(rows[2:,:]))==5
for degree in (5,6):assert component(remainder,degree)==decode(candidate['normalized_remainder_homogeneous'][str(degree)])
assert zero(K.subs(negative,simultaneous=True).T-K)
assert zero(trunc(graph.subs(negative,simultaneous=True).T*G*graph,4)-K)
print('PASS actual phase angles and nonzero Q(p)-Q(0) heavy shift; source D0 two-sided inverse; independent Neumann W1..W4; signed action and exact degrees 5,6 remainder',flush=True)

# Rebuild the original field and equation maps, with all nine Ward rows.
V=s.MutableSparseMatrix(289,79,{})
V[9:121,:]=clean(C*section*S)
for step in reversed(source['algebraic_Schur_steps']):
    for row,col,powers,value in step['write_back_auxiliary_from_retained']:
        V[row,:]+=s.sympify(value)*s.prod(substitution[v]**a for v,a in zip(p,powers))*V[col,:]
    V=clean(V)
assert V==decode(candidate['source_field_lift_289_by_79'])
gauge=original_matrix(source['source_primitive_gauge_tangent'],289,12)[:121,:]
broken=gauge[:,source['Ward_constraint_elimination']['broken_parameter_columns']]
assert broken[:9,:]==s.eye(9)
ward=(-broken[9:,:].subs(negative,simultaneous=True).T).col_join(s.eye(112))
J=s.MutableSparseMatrix(289,79,{})
J[:121,:]=clean(ward*R*Q.subs(negative,simultaneous=True).T*Sinv*n)
J=clean(J)
assert J==decode(candidate['source_equation_lift_289_by_79'])
H=original_matrix(source['Fourier_Jacobi_entries'],289,289)
assert zero(H*V-J*G)
# This identity pays the original action's N and 1/2 rather than assuming that
# the normalized Schur operator itself was already the original density.
assert zero(V.subs(negative,simultaneous=True).T*J-n*s.eye(79))
full=clean(V*graph);full_rem=clean(J*remainder);full_light=clean(J*row_lift)
assert full==decode(candidate['source_phase_field_through_order_four'])
assert full_rem==decode(candidate['full_equation_remainder'])
assert full_light==decode(candidate['full_equation_effective_row_lift'])
assert zero(H*full-full_light*K-full_rem)
assert min(degrees(full_rem))==5
assert zero(trunc(full.subs(negative,simultaneous=True).T*H*full,4)-n*K)
wrong_ward=(-broken[9:,:].T).col_join(s.eye(112))
wrong_J=s.zeros(289,79);wrong_J[:121,:]=clean(wrong_ward*R*Q.subs(negative,simultaneous=True).T*Sinv*n)
assert not zero(H*V-wrong_J*G)
omitted_ward=J.copy();omitted_ward[:9,:]=s.zeros(9,79)
assert not zero(H*V-omitted_ward*G)
print('PASS every original 289 row, three auxiliary lifts and restored nine Ward rows; V(-p)^T J=N I fixes the original action normalization; signed/omitted Ward countercontrols rejected',flush=True)

# Source matter kinetic term: Re chi i Gamma^mu_e D_mu psi, with volume.
# Take the local phase-gradient coefficient before any effective-action input.
kinetic=(CORE/'StageNineMatterCovariantDerivativeAffine.lean').read_text()
assert 'def matterCovariantDerivativeVariationVector' in kinetic and 'Complex.I •' in kinetic
e0=s.Matrix([[s.sympify(value) for value in row] for row in source['actual_background']['coframe']])
einv=e0.inv();cofactor=e0.det()*einv
phase_generators=(s.I*s.eye(12),-s.I*gamma5)
currents=[s.zeros(2,289) for _ in range(4)]
background_current=s.zeros(2,4)
for mu in range(4):
    weighted=sum((cofactor[mu,a]*gamma[a] for a in range(4)),s.zeros(12))
    for charge,generator in enumerate(phase_generators):
        operator=s.I*weighted*generator
        background_current[charge,mu]=s.simplify(s.re((dual*operator*seed)[0]))
        for index,field in enumerate(source['fields']):
            if field['group'] in ('primal_H','dual_H'):
                part,spin,color=field['coordinate'];basis=s.zeros(12,1);basis[3*spin+color]=s.I**part
                value=dual*operator*basis if field['group']=='primal_H' else basis.T*operator*seed
                currents[mu][charge,index]=s.simplify(s.re(value[0]))
            elif field['group']=='coframe':
                a,nu=field['coordinate'];h=s.zeros(4);h[a,nu]=1
                derivative=e0.det()*(s.trace(einv*h)*einv-einv*h*einv)
                derivative_operator=s.I*sum((derivative[mu,b]*gamma[b] for b in range(4)),s.zeros(12))*generator
                currents[mu][charge,index]=s.simplify(s.re((dual*derivative_operator*seed)[0]))
assert background_current==s.Matrix([[0,0,0,0],[4*s.sqrt(2),0,0,0]])
assert currents[0]==decode(candidate['source_phase_Noether_density_covectors'])
# The complete source current identity is tested on EVERY perturbation column,
# not inferred merely from agreement on the two soft fields.
divergence=sum((substitution[p[mu]]*currents[mu] for mu in range(4)),s.zeros(2,289))
assert zero(divergence+Z.T*H)
current_response=clean(currents[0]*full)
for degree,text in candidate['source_phase_Noether_density_response'].items():
    assert component(current_response,int(degree))==decode(text)
leading_current=component(current_response,1)
assert leading_current==s.diag(-16*s.sqrt(2)*u/11,20*s.sqrt(2)*u)
without_cofactor=currents[0].copy()
for index,field in enumerate(source['fields']):
    if field['group']=='coframe':without_cofactor[:,index]=s.zeros(2,1)
assert not zero(component(without_cofactor*full,1)-leading_current)
assert not zero(divergence+(-Z).T*H)
print('PASS Noether currents independently differentiated from original volume/coframe Dirac action; all four currents satisfy the full 2x289 Ward identity; actual time density and cofactor contribution verified',flush=True)

# Original action Fourier bookkeeping: delta field(-p) H delta field(p)/2.
K2=component(K,2);K4=component(K,4);radius=q1*q1+q2*q2+q3*q3
time_coefficients=(s.Rational(32,11),-40);space_coefficients=(s.Rational(160,67),s.Rational(2500,81))
assert K2==s.diag(time_coefficients[0]*u*u+space_coefficients[0]*radius,
                  time_coefficients[1]*u*u+space_coefficients[1]*radius)
time_L=[s.simplify(-a/(4*n)) for a in time_coefficients]
space_L=[s.simplify(n*b/4) for b in space_coefficients]
assert time_L==[-8/(11*n),10/n] and space_L==[40*n/67,625*n/81]
assert leading_current==s.diag(*[s.simplify(2*coefficient*n*s.sqrt(2)*u) for coefficient in time_L])

# Compare the quartic shells with the independently certified exact degree10/12
# source factors, including the conversion from u^2,q^2 to lambda^2,|k|^2.
x,r=s.symbols('x r');shells=[]
for index,(a,b) in enumerate(zip(time_coefficients,space_coefficients)):
    c1=-b/a
    shell4=s.Poly(K4[index,index],u)
    assert all(power[0]%2==0 for power,_ in shell4.terms())
    on_shell=s.expand(sum(coefficient*(c1*radius)**(power[0]//2) for power,coefficient in shell4.terms()))
    c2=s.cancel(-on_shell/(a*radius**2))
    assert not c2.has(*variables)
    leading=s.simplify(n*n*c1);quartic=s.simplify(n*n*c2/2)
    assert leading==s.sympify(candidate['native_lambda_squared_per_k_squared'][index])
    assert quartic==s.sympify(candidate['native_lambda_squared_per_k_fourth'][index])
    owner=next(item for item in spectrum['gapless_branch_assignments']
        if item.get('lambda_squared_leading_k_squared')==str(leading))
    assert owner['canonical_multiplicity']==1
    axial_q=s.symbols('q')
    exact=s.Poly(s.sympify(owner['factor'],locals={'u':u,'q':axial_q}),u,axial_q)
    assert all(du%2==dq%2==0 for (du,dq),_ in exact.terms())
    exact_xr=s.Poly(sum(coefficient*x**(du//2)*r**(dq//2) for (du,dq),coefficient in exact.terms()),x,r)
    derivative=exact_xr.coeff_monomial(x)
    exact_c1=-exact_xr.coeff_monomial(r)/derivative
    exact_c2=-(exact_xr.coeff_monomial(x*x)*exact_c1**2+
        exact_xr.coeff_monomial(x*r)*exact_c1+exact_xr.coeff_monomial(r*r))/derivative
    assert s.simplify(c1-exact_c1)==0 and s.simplify(c2-exact_c2)==0
    shells.append({'phase':candidate['source_phase_names'][index],'exact_source_factor_degree':exact.total_degree(),
        'leading_lambda_squared_coefficient':str(leading),'quartic_lambda_squared_coefficient':str(quartic),
        'off_axis_on_shell_quartic_is_radius_squared_only':True})
assert not zero(K4-K4.subs({q1:q2,q2:q1},simultaneous=True))
print('PASS original L2 sign/factor N and actual charge-density response; both all-direction quartic shells agree with the exact certified source factors despite non-manifest off-shell isotropy',flush=True)

result={'scope':candidate['scope'],'source_phases_match_original_columns_1_3':True,
    'phase_section_minus_origin_is_nonzero_heavy_only':True,'light_angle_readback_identity':True,
    'heavy_origin_inverse_both_sides':True,'neumann_graph_degrees_verified':[1,2,3,4],
    'normalized_remainder_degrees':degrees(remainder),'full_remainder_degrees':degrees(full_rem),
    'original_289_field_and_equation_lifts_verified':True,'original_action_readback_Vminus_T_J':'N*I79',
    'source_Noether_derivation':'coefficient of local phase gradient in Vol*Re chi*i*Gamma_e^mu*D_mu psi',
    'Noether_all_four_current_Ward_identity':'sum p_mu*dJ^mu + Z^T*H289 = 0 (all 289 columns)',
    'source_Noether_background':[[str(value) for value in row] for row in background_current.tolist()],
    'source_time_current_first_order':[[str(value) for value in row] for row in leading_current.tolist()],
    'native_L2_time_coefficients':list(map(str,time_L)),'native_L2_spatial_coefficients':list(map(str,space_L)),
    'exact_source_shell_crosschecks':shells,
    'negative_controls_rejected':['equate_source_phase_with_P0_without_heavy_shift','omit_negative_momentum_in_Ward_restore',
        'erase_nine_original_scalar_rows','omit_axial_coframe_cofactor','reverse_Noether_source_phase_sign',
        'assert_off_shell_K4_manifest_isotropy'],
    'fresh_receipt_equal_except_elapsed_seconds':True}
(HERE/'independent-receipt.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print('PASS exact independent source/effective-action/Noether/shell receipt written',flush=True)
