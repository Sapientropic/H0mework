#!/usr/bin/env python3
"""Independent original Gauss100/full504 normal ordering and Heisenberg ports."""
from collections import defaultdict
from functools import lru_cache
from itertools import product
import hashlib
import json
import time
import sympy as s
from dynamic import HERE,ROOT,ROOT_ID
from source_joint_form_hamiltonian import read_bound
from source_coframe_live_ordering import full
from source_quantum_temporal_symbol import N
import source_joint_ccr_car_ports as candidate


def normalized(values):return {w:s.expand(c)for w,c in values.items()if s.expand(c)!=0}
def equal_states(a,b):assert normalized(add((1,a),(-1,b)))=={}
def add(*terms):
    out=defaultdict(lambda:s.S.Zero)
    for c,state in terms:
        for w,v in state.items():out[w]+=c*v
    return dict(out)
def mask(word):return sum(1<<int(i)for i in word)
def decode(rows):return {mask(word):s.sympify(c)for word,c in rows}
def bits(w):
    while w:
        bit=w&-w;yield bit.bit_length()-1;w-=bit
def step(w,j,creation):
    occupied=(w>>j)&1
    if occupied==int(creation):return None,0
    return w^(1<<j),(-1)**((w&((1<<j)-1)).bit_count())
def car(j,state,creation=False):
    out={}
    for w,c in state.items():
        v,sign=step(w,j,creation)
        if sign:out[v]=out.get(v,0)+sign*c
    return normalized(out)

_columns={}
def columns(M):
    key=id(M)
    if key not in _columns:
        cols=defaultdict(list)
        for(i,j),c in s.SparseMatrix(M).todok().items():
            if c:cols[int(j)].append((int(i),c))
        _columns[key]=(M,cols)
    return _columns[key][1]
def current(M,state):
    out=defaultdict(lambda:s.S.Zero);cols=columns(M)
    for w,c in state.items():
        for j in bits(w):
            a,s1=step(w,j,False)
            for i,v in cols[j]:
                b,s2=step(a,i,True)
                if s2:out[b]+=c*s1*s2*v
    return normalized(out)
def normal(A,B,state):
    out=defaultdict(lambda:s.S.Zero);ac,bc=columns(A),columns(B)
    for w,c in state.items():
        for j in bits(w):
            u,s1=step(w,j,False)
            for ell in bits(u):
                v,s2=step(u,ell,False)
                for k,b in bc[ell]:
                    t,s3=step(v,k,True)
                    if not s3:continue
                    for i,a in ac[j]:
                        z,s4=step(t,i,True)
                        if s4:out[z]+=c*a*b*s1*s2*s3*s4
    return normalized(out)
def apply_symbol(symbol,state):
    return normalized(add((symbol.scalar,state),(1,current(symbol.one_body,state)),
        *((c,normal(A,B,state))for c,A,B in symbol.pairs)))


def generic_CAR_and_Leibniz():
    def canonical(t):
        names={};return tuple(names.setdefault(x,len(names))for x in t)
    patterns=[t for t in product(range(5),repeat=5)if canonical(t)==t]
    assert len(patterns)==52
    def word_action(word,w):
        state={w:s.S.One}
        for kind,j in reversed(word):state=car(j,state,bool(kind))
        return state
    checks=0
    for i,j,k,l,m in patterns:
        q=((1,i),(0,j));r=((1,k),(0,l));quartic=((1,i),(1,k),(0,l),(0,j))
        for creation in(False,True):
            g=((int(creation),m),);terms=[]
            if creation:
                if j==m:terms.append((1,((1,i),)+r))
                if l==m:terms.append((1,((1,k),)+q))
            else:
                if i==m:terms.append((-1,r+((0,j),)))
                if k==m:terms.append((-1,q+((0,l),)))
            for w in range(1<<(max(i,j,k,l,m)+1)):
                left=add((1,word_action(quartic+g,w)),(-1,word_action(g+quartic,w)))
                right=add(*((c,word_action(word,w))for c,word in terms));equal_states(left,right)
            checks+=1
    z=s.Symbol('independent_live_coefficient',real=True)
    A=s.SparseMatrix([[1,z,0],[s.I,0,z*z],[0,1,2]])
    B=s.SparseMatrix([[0,1,s.I*z],[z,2,0],[0,z,1]])
    sym=candidate.NormalSymbol(z*z,s.eye(3)*z,((1+z*z,A,B),))
    state={mask((0,2)):s.S.One};image=apply_symbol(sym,state)
    derived=sym.derivative(z,{z:s.Rational(2,3)},negative=True)
    exact={w:-s.diff(c,z).subs(z,s.Rational(2,3))for w,c in image.items()}
    equal_states(apply_symbol(derived,state),exact)
    wrong=candidate.NormalSymbol(-2*z,-s.eye(3),((-2*z,A,B),))
    assert normalized(add((1,exact),(-1,{w:c.subs(z,s.Rational(2,3))for w,c in apply_symbol(wrong,state).items()})))
    return {'all104_equality_patterns_independent_bit_replay':checks,
        'actual_Lean_generic_ports_bound_separately':True,'both_live_current_matrix_derivatives_required':True,
        'no_Hermitian_or_extra_half_premise':True}


def actual_source(target):
    model=candidate.SourceJointCCRCarPorts()
    configuration=tuple(map(s.sympify,target['configuration100']));p=tuple(map(s.sympify,target['configuration_momenta100']))
    phase=configuration+p;d=model.coefficients(configuration);symbol=model.symbol(phase)
    assert model.time_point==(N,0,0,0)and target['time']==list(map(str,model.time_point))
    assert len(symbol.pairs)==target['CAR']['quartic_factors']==119
    assert symbol.one_body.shape==(504,504)and all(A.shape==B.shape==(504,504)for _,A,B in symbol.pairs)
    at=model.at_time;principal=d['principal'];I=s.SparseMatrix(s.eye(504))
    q=configuration[:6];volume=d['volume'];mom=s.Matrix(p)
    # Rebuildtheactualsourcecurrent products before normal ordering.
    qsub=dict(zip(model.leaf.weyl.native.joint.coframe.q,q))
    cf=d['coframe'];coframe_one=at(full(cf['one_body']+cf['correction']))
    cf_curr=[s.SparseMatrix(full(J))for J in cf['J']]
    cf_linear=[at(full(M.subs(qsub)))for M in model.leaf.pairing['Mh']]
    charges=model.leaf.charges
    expected_pairs=[(N*s.Rational(3,16)/volume,I,I)]
    body=at(d['matter']['matter_CAR'])+coframe_one+N*s.Rational(21,16)/volume*I
    scalar=N*(s.Rational(5,4)/volume+3*volume)
    for data in(d['scalar'],d['gauge']):
        scalar+=at(sum(data[k]for k in('classical_zero','half_density_potential','weyl_correction')))
        for a,c in enumerate(at(data['linear_current'])):body+=c*charges[a]
        for(a,b),c in at(data['square_current']).todok().items():body+=c*(charges[a]*charges[b]);expected_pairs.append((c,charges[a],charges[b]))
    expected_pairs.extend((c,cf_curr[a],cf_curr[b])for(a,b),c in cf['W'].todok().items())
    assert len(expected_pairs)==119
    for(c,A,B),(v,C,D)in zip(expected_pairs,symbol.pairs):
        assert s.expand(c-v)==0
        assert not s.SparseMatrix(A-C).applyfunc(s.expand).todok()and not s.SparseMatrix(B-D).applyfunc(s.expand).todok()
    for j in range(100):body+=p[j]*d['linear_current'][j]
    scalar+=(mom.T*principal*mom)[0]+(mom.T*d['linear_identity'])[0]
    assert s.expand(symbol.scalar-scalar)==0 and not s.SparseMatrix(symbol.one_body-body).applyfunc(s.expand).todok()
    number=s.Symbol('occupation_number',integer=True,nonnegative=True)
    assert s.expand(s.Rational(5,4)+s.Rational(21,16)*number+s.Rational(3,16)*number*(number-1)-(3*number**2+18*number+20)/16)==0
    divergence=s.zeros(100,1);divergence[:6,:]=at(model.leaf.pairing['divergence'].subs(qsub))
    divergence[6:,:]=at(d['scalar']['div_principal']+d['gauge']['div_principal'])
    divdiv=at(sum(s.diff(model.leaf.pairing['K'][i,j],model.leaf.weyl.native.joint.coframe.q[i],model.leaf.weyl.native.joint.coframe.q[j])for i in range(6)for j in range(6)).subs(qsub))
    divdiv+=at(d['scalar']['divdiv_principal']+d['gauge']['divdiv_principal'])
    divlinear=at(d['scalar']['div_momentum_identity']+d['gauge']['div_momentum_identity'])
    weights=at(d['scalar']['div_momentum_current']+d['gauge']['div_momentum_current'])
    divmatrix=s.SparseMatrix(sum((c*Q for c,Q in zip(weights,charges)),s.SparseMatrix(504,504,{})))
    correction=-s.I*(divergence.T*mom)[0]-divdiv/4-s.I*divlinear/2
    @lru_cache(None)
    def H(w):return apply_symbol(symbol,{w:s.S.One})
    for row in target['actual_full_H_images']:
        w=mask(row['input']);image=H(w);equal_states(image,decode(row['symbol_image']))
        quantized=add((1,image),(correction,{w:s.S.One}),(-s.I/2,current(divmatrix,{w:s.S.One})))
        equal_states(quantized,decode(row['unchanged_differential_H']))
    # Thefull100 CCR identity isexactforquadratic Weyl symbols; compareall
    # sourcecoefficients andtheactualnonzero countwithitsquantizedreadout.
    state={mask((144,396)):s.S.One};nonzero=0
    for j in range(100):
        port=model.velocity(j,phase)
        assert port.pairs==()and port.one_body==d['linear_current'][j]
        assert s.expand(port.scalar-2*(principal[j,:]*mom)[0]-d['linear_identity'][j])==0
        readout=normalized(add((1,apply_symbol(port,state)),(-s.I*divergence[j],state)))
        nonzero+=bool(readout)
    assert nonzero==target['CCR']['actual_position_nonzero']==93
    actual_ports=[];cubic=0
    for row in target['actual_CAR_ports']:
        w=mask(row['word']);mode=row['mode'];creation=row['creation'];value={w:s.S.One}
        first=car(mode,value,creation)
        acted=add(*((c,H(v))for v,c in first.items()))
        port=normalized(add((s.I,acted),(-s.I,car(mode,H(w),creation))))
        equal_states(port,decode(row['symbol_image']))
        one=current(symbol.one_body,value)
        linear=add((s.I,current(symbol.one_body,first)),(-s.I,car(mode,one,creation)))
        defect=normalized(add((1,port),(-1,linear)));equal_states(defect,decode(row['cubic']));cubic+=bool(defect)
        D=-s.I*divmatrix/2
        extra=add((s.I,current(D,first)),(-s.I,car(mode,current(D,value),creation)))
        equal_states(add((1,port),(1,extra)),decode(row['original_differential_port']))
        actual_ports.append((row['word'],mode,creation))
    assert len(actual_ports)==24 and cubic==target['CAR']['nonzero_actual_cubic_checks']==21
    # Independentformal adjointretainsYdaggeronlyinHsharp.
    Yraw=d['matter']['matter']['Y'];Einv=d['matter']['matter']['inverse_E']
    Yp=at(-s.I*d['matter']['e'].det()*Einv*Yraw);Y=s.SparseMatrix(s.diag(Yp,-Yp.conjugate()))
    sharp=apply_symbol(symbol.adjoint(),state)
    equal_states(sharp,decode(target['actual_force']['original_Hsharp_image']))
    equal_states(sharp,add((1,H(mask((144,396)))),(1,current(Y.H-Y,state))))
    assert normalized(current(Y.H-Y,state))
    return model,phase,{'actual_configuration_nonzero_quartic_factors':119,
        'all_normal_coefficient_sources_and_ordered_matrices_rebuilt':True,
        'full_occupation_number_polynomial_identity':True,'original_four_CAR_sector_images_rebuilt':[0,1,2,3],
        'all100_position_ports_and_ordering_terms':True,'actual_nonzero_position_ports':nonzero,
        'all24_actualCAR_ports_independent_full504_bits':True,'actual_nonzero_cubic_ports':cubic,
        'original_differential_divergence_terms_preserved':True,'independent_Hsharp_with_original_Y_once':True}


def force_scope_and_actual(model,phase,target):
    # Payoneactualsource derivative; thefull100 mixedderivative mainreceipt
    # remainsbound,notrepresented asreexecutedhere.
    force=model.force(0,phase);state={mask((144,396)):s.S.One}
    image=apply_symbol(force,state);equal_states(image,decode(target['actual_force']['image']))
    for creation,row in zip((False,True),target['actual_force']['CAR_mixed_Jacobi']):
        first=car(144,state,creation)
        comm=add((s.I,apply_symbol(force,first)),(-s.I,car(144,apply_symbol(force,state),creation)))
        equal_states(comm,decode(row))
    return {'actual_source_coframe_force0_recomputed':True,'both_actual_force_CAR_ports_rebuilt':True,
        'all100_mixed_velocity_source_main_binding':target['actual_force']['mixed_velocity_nonzero'],
        'mixed_velocity_main_replayed_in_this_audit':False,
        'CCR_proof':'For the originalquadratic canonicalWeyl symbol,commutationwithlinear z_j andp_j truncates theMoyal expansionexactly: i[H,z_j]=OpW(d_pj sigma), i[H,p_j]=-OpW(d_zj sigma). Allsourceprincipal/linear/currentcoefficients areretained; thezeroCAR commutatorpartincludesitsWeyl currentdivergence. These100 canonicalconfigurationmomenta arenotphysicalspatialk.',
        'Leibniz_and_mixed_proof':'NormalSymbol.derivative differentiates scalar,one-bodymatrix,andallthree factors c,A,B in eachactualnormalproduct. Theexplicitnonconstantmatrix control rejectsweights-only differentiation. ExactCAR algebraisindependentofconfiguration,so differentiatingitcommuteswiththe CCR derivation; theactualcoframeforceandbothmode144 ports areindependentlyrecomputed.',
        'adjoint_and_core_scope':'The sourceCc-infinity Gauss100 chart tensorfullCAR504 ispreservedby thefinite-ordersmooth differential coefficients. Weylformaladjoint istheconjugate scalar,onebodydagger,and reversed Bdagger/Adagger normalpair. ItgivesindependentHsharp; noHnative selfadjointness,globalextension,unitaryevolutionorphysicalk-splice follows.'}


def main():
    start=time.monotonic();target=read_bound('source_joint_ccr_car_ports')
    assert target['scope']=='ACTUAL_LOCAL_GAUSS100_FULL504_CCR_CAR_HEISENBERG_PORTS'
    lean=json.loads((HERE/'JointCCRCarPorts.audit.json').read_text());assert lean['verdict']=='CERTIFIED'
    for path,digest in lean['input_sha256'].items():assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    generic=generic_CAR_and_Leibniz();print('PASS independent complete104 CAR patterns and live-matrix Leibniz control',flush=True)
    model,phase,actual=actual_source(target);print('PASS original119 source factors, four H images,100 CCR and24 CAR ports',flush=True)
    forces=force_scope_and_actual(model,phase,target)
    names=('source_joint_ccr_car_ports.py','source_joint_ccr_car_ports.json','independent_source_joint_ccr_car_ports.py',
        'JointCCRCarPorts.lean','JointCCRCarPorts.audit.json','source_common_weyl_symbol.json',
        'source_joint_form_hamiltonian.json','source_full_quantum_adjoint.json',
        'source_clock_symbol_recursion.py','source_scalar_weyl_symbol.py','source_gauss_quantum_current.py')
    out={'root':ROOT_ID,'verdict':'CERTIFIED','scope':target['scope'],
        'input_sha256':{str((HERE/n).relative_to(ROOT)):hashlib.sha256((HERE/n).read_bytes()).hexdigest()for n in names},
        'source_sha256':target['source_sha256'],'generic_exact_CAR_and_Leibniz':generic,
        'actual_full_source_ports':actual,'actual_force_and_domain_scope':forces,
        'scope_readback':'Theunchangedfour-energy Weyl leaf atoriginaltime(N,0,0,0)generatesfullGauss100/CAR504 Heisenbergports withgenuinecubicfeedback. The119 countbelongs totherecordednontrivialconfiguration; theparameterfamily retainsallsourcecoefficients. OriginalWeyl/divergence termsandindependentHsharpremain. Fullspatialfield/physicalk/four-block quantumsplice,physicalparticlespectrumandlifetime arenotclaimed.',
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-start,3)}
    (HERE/'independent_source_joint_ccr_car_ports.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('PASS independent source joint CCR/CAR ports, live force and independent Hsharp',out['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
