#!/usr/bin/env python3
"""Independent raw metric differential, source Schur equations and rational response."""
from collections import defaultdict
import itertools
import json
from pathlib import Path
import re

import sympy as s
from sympy.polys.matrices import DomainMatrix

HERE=Path(__file__).resolve().parent
BASE=HERE.parent
ACTIVE=BASE.parent/'active-gauge'
ROOT=next(path for path in HERE.parents if (path/'Lean/lean-toolchain').exists())
CORE=ROOT/'Lean/SaturationMonoid/PhysicsCore'
raw=json.loads((ACTIVE/'receipt.json').read_text())
quotient=json.loads((ACTIVE/'quotient.json').read_text())
propagation=json.loads((ACTIVE/'propagation.json').read_text())
symmetry=json.loads((ACTIVE/'symmetries.json').read_text())
candidate=json.loads((BASE/'receipt.json').read_text())
fresh=json.loads(Path('/tmp/metric-response-audit.json').read_text())
assert {k:v for k,v in candidate.items() if k!='elapsed_seconds'}=={k:v for k,v in fresh.items() if k!='elapsed_seconds'}
q=s.symbols('q',real=True)
n=s.sympify(raw['source_lapse'])
groups=defaultdict(dict)
for i,field in enumerate(raw['fields']):groups[field['group']][tuple(field['coordinate'])]=i
pairs=list(itertools.combinations_with_replacement(range(4),2))
assert [list(pair) for pair in pairs]==candidate['metric_pairs']
e0=s.Matrix([[s.sympify(value) for value in row] for row in raw['actual_background']['coframe']])
assert e0==s.diag(n,1,1,1) and n.is_positive

source=(CORE/'RawLorentzianMetricHodgeRecovery.lean').read_text()
assert 'coframe.transpose * minkowskiInternalMetric * coframe' in source
eta_match=re.search(r'def minkowskiInternalMetric.*?:=\s*Matrix.diagonal\s*!\[(.*?)\]',source,re.S)
assert eta_match
eta=s.diag(*[s.sympify(value) for value in eta_match.group(1).split(',')])
assert eta==s.diag(-1,1,1,1)
epsilon=s.symbols('epsilon',real=True)
metric=s.zeros(10,289)
for (internal,coordinate),index in groups['coframe'].items():
    h=s.zeros(4);h[internal,coordinate]=1
    differential=((e0+epsilon*h).T*eta*(e0+epsilon*h)).diff(epsilon).subs(epsilon,0)
    for row,(mu,nu) in enumerate(pairs):metric[row,index]=differential[mu,nu]


def decode(payload):
    rows,columns=payload['shape'];out=s.MutableSparseMatrix(rows,columns,{})
    for row,col,text in payload['entries']:
        assert out[row,col]==0
        out[row,col]=s.sympify(text,locals={'q':q})
    return s.SparseMatrix(out)


assert metric[:,:121]==decode(candidate['metric_variation_map'])
assert metric[:,121:]==s.zeros(10,168)
assert metric[0,groups['coframe'][(0,0)]]==-2*n
assert sum(value!=0 for value in metric[0,:])==1
injection=metric.T

# All four momentum monomials retained; no local diffeomorphism columns added.
terms={}
for row,col,power,value in symmetry['source_symmetry_tangents_112']:
    assert 0<=col<9
    for target in range(10):
        if metric[target,row]:
            key=(target,col,tuple(power))
            terms[key]=terms.get(key,0)+metric[target,row]*s.sympify(value)
assert all(s.simplify(value)==0 for value in terms.values())


def static_operator(entries,size):
    out=s.MutableSparseMatrix(size,size,{})
    for row,col,power,value in entries:
        if not any(power[:3]):out[row,col]+=s.sympify(value)*(s.I*s.sqrt(2)*q)**power[3]
    return s.SparseMatrix(out)


constant_field=s.QQ.algebraic_field(s.sqrt(2),s.sqrt(15),s.I)
domain=constant_field.frac_field(q)
def dm(matrix):return DomainMatrix.from_Matrix(matrix).convert_to(domain)
def zero(matrix):return all(not value for row in matrix.to_list() for value in row)
def eye(size):return dm(s.eye(size))

full=decode(candidate['full_289_field_green_columns'])
H=dm(static_operator(raw['Fourier_Jacobi_entries'],289))
F=dm(full);I=dm(injection);M=dm(metric)
assert zero(H.matmul(F)-I)
assert zero(H.matmul(-F)+I)
assert not zero(H.matmul(F)+I)
print('PASS actual metric differential and pure J00 normalization; all-four-momentum compatibility; every original 289 equation and induced-field sign',flush=True)

# Reconstruct the successive ORIGINAL block equations, verifying both sides of
# each algebraic inverse and the actual forward Schur matrix. The frozen full
# solution is checked against the independently reconstructed unique writeback.
active=list(range(289));current=H;stages=[]
for step in raw['algebraic_Schur_steps']:
    eliminated=step['eliminated_fields'];remaining=[index for index in active if index not in eliminated]
    erows=[active.index(index) for index in eliminated]
    rrows=[active.index(index) for index in remaining]
    d=current.extract(erows,erows)
    dinverse=s.zeros(len(eliminated))
    eindex={index:i for i,index in enumerate(eliminated)}
    rindex={index:i for i,index in enumerate(remaining)}
    for row,col,value in step['algebraic_block_inverse']:
        dinverse[eindex[row],eindex[col]]=s.sympify(value)
    dinverse=dm(dinverse)
    assert zero(d.matmul(dinverse)-eye(len(eliminated)))
    assert zero(dinverse.matmul(d)-eye(len(eliminated)))
    writeback=-dinverse.matmul(current.extract(erows,rrows))
    recorded=s.MutableSparseMatrix(len(eliminated),len(remaining),{})
    for row,col,power,value in step['write_back_auxiliary_from_retained']:
        assert row in eindex and col in rindex
        if not any(power[:3]):recorded[eindex[row],rindex[col]]+=s.sympify(value)*(s.I*s.sqrt(2)*q)**power[3]
    assert zero(writeback-dm(recorded))
    assert zero(F.extract(eliminated,list(range(10)))-writeback.matmul(F.extract(remaining,list(range(10)))))
    current=current.extract(rrows,rrows)+current.extract(rrows,erows).matmul(writeback)
    stages.append({'groups':step['eliminated_groups'],'actual_two_sided_inverse':True,
        'writeback_derived_from_original_equations':True,'actual_ten_columns_obey_writeback':True})
    active=remaining
assert active==list(range(121))
assert zero(current-dm(static_operator(raw['primitive_121_Fourier_Jacobi_entries'],121)))
kept=quotient['retained_original_fields']
K=current.extract(kept,kept)
lam,k=s.symbols('lam k',real=True)
recorded_K=s.SparseMatrix(103,103,{(i,j):s.sympify(text.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs({lam:0,k:s.sqrt(2)*q})
                                 for i,j,text in quotient['quotient_operator_103_by_103']})
assert zero(K-dm(recorded_K))
primitive=F.extract(kept,list(range(10)))
assert zero(K.matmul(primitive)-dm(metric[:,kept].T))
assert zero(F.extract(list(range(9))+quotient['fixed_section_removed_original_fields'],list(range(10))))
sources_by_block=[]
for block in propagation['blocks']:
    selected=[row for row in range(10) if any(metric[row,kept[index]] for index in block['quotient_indices'])]
    if selected:sources_by_block.append([block['dimension'],len(selected)])
assert sources_by_block==[[30,4],[33,6]]
print('PASS independently reconstructed 289->217->145->121 source Schur equations, all three reverse writebacks and actual 103 source block equations',flush=True)

# Rebuild the prepared relation from the source adjoint instead of a chosen dual.
adjoint_source=(CORE/'StageNineFullDiracAdjointMaterial.lean').read_text()
match=re.search(r'def diracAdjointSpinSwap.*?:=\s*!!\[(.*?)\]',adjoint_source,re.S);assert match
swap=s.Matrix([[s.sympify(value.strip()) for value in row.split(',')] for row in match.group(1).split(';')])
swap12=s.kronecker_product(swap,s.eye(3))
L=s.sympify(raw['actual_background']['dual_multiple'])*s.diag(swap12,-swap12)
primal=list(groups['primal_H'].values());dual=list(groups['dual_H'].values())
assert zero(F.extract(dual,list(range(10)))-dm(L).matmul(F.extract(primal,list(range(10)))))

response=decode(candidate['metric_inverse_response'])
assert zero(M.matmul(F)-dm(response))
assert zero(dm(decode(candidate['induced_metric_response']))+dm(response))
assert zero(dm(response-response.subs(q,-q).T))
static=s.zeros(10);regular=[]
for i in range(10):
    for j in range(10):
        numerator,denominator=s.fraction(s.cancel(response[i,j]))
        num=s.Poly(numerator,q,extension=[s.sqrt(30),s.I])
        den=s.Poly(denominator,q,extension=[s.sqrt(30),s.I])
        assert s.gcd(num,den).degree()==0
        assert den.eval(0)!=0
        static[i,j]=s.simplify(num.eval(0)/den.eval(0))
        regular.append([i,j,str(den.eval(0))])
assert zero(dm(static-decode(candidate['metric_zero_limit'])))
assert decode(candidate['q_squared_metric_response_limit'])==s.zeros(10)
expected=n**3*(625*q**6+7800*q**4+15984*q**2-31104)/(625*q**8+2550*q**6+7704*q**4+23328*q**2-93312)
assert zero(dm(s.Matrix([[response[0,0]-expected]])))
assert s.simplify(static[0,0]-n**3/3)==0
num,den=map(lambda value:s.Poly(value,q,extension=s.sqrt(30)),s.fraction(s.cancel(response[0,0])))
assert num.degree()+2==den.degree()
uv=s.simplify(num.LC()/den.LC())
assert uv==n**3 and s.sympify(candidate['q_squared_g00_response_ultraviolet_limit'])==uv
assert s.sympify(candidate['original_k_squared_g00_response_ultraviolet_limit'])==2*uv
print('PASS current canonical adjoint condition, all 100 reduced metric entries regular, signed reciprocity and exact IR/UV coefficient readback',flush=True)

# The complete field is stronger data than its metric observable. Keep its poles.
field_poles=[];residue=s.zeros(289,10)
for row,col,text in candidate['full_289_field_green_columns']['entries']:
    numerator,denominator=s.fraction(s.cancel(s.sympify(text,locals={'q':q})))
    pnum=s.Poly(numerator,q,extension=[s.sqrt(2),s.sqrt(15),s.I])
    pden=s.Poly(denominator,q,extension=[s.sqrt(2),s.sqrt(15),s.I])
    numerator_order=min(power[0] for power,_ in pnum.terms())
    denominator_order=min(power[0] for power,_ in pden.terms())
    pole=denominator_order-numerator_order
    if pole>0:
        field_poles.append({'row':row,'column':col,'group':raw['fields'][row]['group'],'pole_order':pole})
        assert pole==1
        residue[row,col]=s.simplify(pnum.nth(numerator_order)/pden.nth(denominator_order))
assert len(field_poles)==8 and {entry['column'] for entry in field_poles}=={3}
assert zero(dm(metric*residue))

# Negative controls: a half-normalized diagonal metric source and frozen feedback
# cannot satisfy the actually solved original equations.
wrong_injection=injection.copy();wrong_injection[groups['coframe'][(0,0)],0]=-n
assert not zero(H.matmul(F)-dm(wrong_injection))
coframe_only=s.zeros(289,10)
for row in groups['coframe'].values():coframe_only[row,:]=full[row,:]
assert not zero(H.matmul(dm(coframe_only))-I)
without_gauge_auxiliary=full.copy()
for row in groups['gauge_B'].values():without_gauge_auxiliary[row,:]=s.zeros(1,10)
assert not zero(H.matmul(dm(without_gauge_auxiliary))-I)

# Conditional normalization to the explicit conventional stress-variation formula.
# This is algebraic bookkeeping, not a new physical stress producer.
Jvars=s.symbols('J0:10');Tvars=s.symbols('T0:10');hvars=s.symbols('h0:16')
h=s.Matrix(4,4,hvars);dg=e0.T*eta*h+h.T*eta*e0
stress=s.zeros(4)
for value,(mu,nu) in zip(Tvars,pairs):stress[mu,nu]=stress[nu,mu]=value
standard=s.Rational(1,2)*n*sum(stress[mu,nu]*dg[mu,nu] for mu in range(4) for nu in range(4))
readback=sum((n*s.Rational(1,2) if mu==nu else n)*stress[mu,nu]*dg[mu,nu] for mu,nu in pairs)
assert s.expand(standard-readback)==0
assert s.simplify(n*s.Rational(1,2)/n**2-1/(2*n))==0
print('PASS field/observable distinction: eight simple J03 matter poles invisible to metric; source-sign, factor-two and frozen-feedback negative controls rejected',flush=True)

result={'scope':candidate['scope'],'source_metric_differential_rebuilt':True,
    'metric_source_count':10,'metric_source_pure_J00_coframe_entry':str(-2*n),
    'all_four_momentum_nine_symmetry_compatibility':True,'original_289_equation_identity_exact':True,
    'source_schur_steps':stages,'actual_source_blocks':sources_by_block,'canonical_relation_from_original_adjoint':True,
    'all_100_reduced_denominators_nonzero_at_origin':regular,
    'g00_exact_response':str(s.factor(expected)),'g00_zero_limit':str(n**3/3),
    'q_squared_g00_UV':str(uv),'original_k_squared_g00_UV':str(2*uv),
    'full_field_origin_poles':field_poles,'metric_annihilates_full_field_simple_pole_residue':True,
    'stress_normalization_conditional_on_definition':{
        'definition':'delta S_ext=(1/2)*N*sum_(all mu,nu) T^(mu,nu) delta g_(mu,nu)',
        'diagonal':'J_(mu,mu)=N*T^(mu,mu)/2','off_diagonal':'J_(mu,nu)=N*T^(mu,nu), mu<nu',
        'pure_rest_density':'if T^00=rho/N^2, then J00=rho/(2*N)',
        'actual_matter_stress_or_physical_units_identified':False},
    'negative_controls_rejected':['wrong_induced_sign','half_metric_diagonal_source','coframe_only_solution',
        'omit_gauge_B_writeback','claim_full_field_regular_from_metric_regular'],
    'fresh_receipt_equal_except_elapsed_seconds':True}
(HERE/'independent-receipt.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print('PASS conditional densitized-stress normalization and exact independent receipt written',flush=True)
