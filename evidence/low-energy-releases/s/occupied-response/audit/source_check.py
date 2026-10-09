#!/usr/bin/env python3
"""Independent source gauge pulse and full-symbol independent-dual construction."""
import argparse
import importlib.util
import itertools
import json
from pathlib import Path
import re
import sympy as s


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True)
    root=parser.parse_args().root.resolve();base=root/'Verification/physics/low-energy-phenomenology';audit=base/'occupied-response/audit'
    frozen=json.loads((base/'occupied-response/receipt.json').read_text())
    replay=json.loads(Path('/tmp/occupied-response-audit-replay.json').read_text())
    assert {k:v for k,v in frozen.items() if k!='elapsed_seconds'}=={k:v for k,v in replay.items() if k!='elapsed_seconds'}
    phase=json.loads((base/'full-phase/receipt.json').read_text());vertices=json.loads((base/'matter-vertices/receipt.json').read_text())
    original=json.loads((base/'active-gauge/receipt.json').read_text())
    assert phase['source_sha256']==vertices['source_sha256']==frozen['source_sha256']
    core=root/'Lean/SaturationMonoid/PhysicsCore'
    p=s.symbols('p0:4',real=True);energy=s.Symbol('E',real=True);ks=s.symbols('k1:4',real=True)
    symbols={str(x):x for x in (*p,energy,*ks)}
    def decode(record):return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(value,locals=symbols) for i,j,value in record['entries']})
    def clean(matrix):return s.SparseMatrix(matrix).applyfunc(s.expand)
    def equal(left,right):assert not clean(left-right).todok()
    def realify(matrix):
        real=matrix.applyfunc(s.re);imag=matrix.applyfunc(s.im)
        return clean(real.row_join(-imag).col_join(imag.row_join(real)))
    def realcolumn(matrix):return clean(matrix.applyfunc(s.re).col_join(matrix.applyfunc(s.im)))
    eye=lambda n:s.eye(n,cls=s.SparseMatrix)
    n=s.sympify(phase['source_lapse']);omega=s.sympify(phase['source_frequency']);spin=s.sqrt(2)
    assert s.sympify(frozen['source_lapse'])==n and s.sympify(frozen['source_frequency'])==omega
    assert s.sympify(original['actual_background']['dual_multiple'])==spin
    gamma=[];text=(core/'DiracCliffordRepresentation.lean').read_text()
    for name in ('Zero','One','Two','Three'):
        literal=re.search(r'def diracGamma'+name+r'\s*:.*?:=\s*!!\[(.*?)\]',text,re.S).group(1)
        gamma.append(s.SparseMatrix([[s.sympify(v.strip().replace('Complex.I','I')) for v in row.split(',')] for row in literal.split(';')]))
    g5=s.kronecker_product(s.diag(-1,-1,1,1),eye(63));Gamma=[s.kronecker_product(g,eye(63)) for g in gamma]
    fullS=clean(Gamma[0]*g5);fullQ=decode(phase['phase_generator'])
    b2=list(itertools.combinations(range(7),2))
    indices=[j*63+7+b2.index((color,5)) for j in range(4) for color in range(3)]
    assert indices==frozen['occupied_full_indices_zero_based']
    F=s.SparseMatrix(252,12,{(row,col):1 for col,row in enumerate(indices)})
    equal(F,decode(frozen['occupied_frame']));equal(F.T*F,eye(12))
    S=clean(F.T*fullS*F);Q=clean(F.T*fullQ*F)
    equal(S,decode(frozen['occupied_adjoint_swap']));equal(Q,decode(frozen['occupied_phase_charge']))
    equal(fullS*F,F*S);equal(fullQ*F,F*Q);equal(g5*F,F*Q);equal(S*S,eye(12))
    C=list(map(decode,phase['principal_coefficients']));constant=decode(phase['stationary_primal_constant'])
    fullD=constant+sum((C[mu]*p[mu] for mu in range(4)),s.zeros(252,cls=s.SparseMatrix))
    d=clean(F.T*fullD*F);equal(fullD*F,F*d)
    c0=clean(F.T*C[0]*F);inverse=clean(n*n*c0)
    equal(c0*inverse,eye(12));equal(inverse*c0,eye(12))
    h0=clean(-s.I*inverse*(F.T*constant*F))
    hj=[clean(inverse*F.T*C[j+1]*F) for j in range(3)]
    equal(h0,decode(frozen['stationary_H_constant']))
    for generated,saved in zip(hj,frozen['H_spatial_coefficients']):equal(generated,decode(saved))
    for h in [h0]+hj:equal(h.H,h);equal(h*Q,Q*h)
    originalH=clean(n*Gamma[0]*(decode(phase['original_constant_B'])+decode(phase['original_Y'])))
    equal(originalH*F,F*(h0+omega*Q));equal(h0+omega*Q,decode(frozen['original_H_constant']))
    assert h0!=s.zeros(12) and h0+omega*Q!=omega*Q
    # Parse actual SpinPair's original two-column coefficient table.
    text=(core/'Stage9C/Material/SpinPair/Spinor.lean').read_text()
    literal=re.search(r'def spinPairCoefficients.*?!!\[(.*?)\]',text,re.S).group(1)
    coefficients=s.Matrix([[s.sympify(v.strip(),locals={'upper':1,'lower':1}) for v in row.split(',')] for row in literal.split(';')])
    seed=s.zeros(12,1)
    for j in range(4):
        for color in range(2):seed[j*3+color]=coefficients[j,color]
    equal(seed,s.Matrix(original['actual_background']['primal_H']).applyfunc(s.sympify))
    w=seed/2;equal(w,decode(frozen['source_prepared']));assert (w.H*w)[0]==1
    equal(h0*w,s.zeros(12,1));equal(d.subs(dict.fromkeys(p,0))*seed,s.zeros(12,1))
    dual=spin*seed.H*S;equal(dual,decode(frozen['source_independent_dual_row']))
    equal(dual*d.subs(dict.fromkeys(p,0)),s.zeros(1,12))
    for i,sign in enumerate((-1,1)):
        branch=(eye(12)+sign*Q)*w/2;equal(branch,decode(frozen['source_prepared_phase_branches'][i]))
        equal((h0+omega*Q)*branch,sign*omega*branch);assert (branch.H*branch)[0]==s.Rational(1,2)
    spec=importlib.util.spec_from_file_location('independent_exterior',base/'mixed-symbol/audit/independent_check.py')
    helper=importlib.util.module_from_spec(spec);spec.loader.exec_module(helper)
    native={}
    for group in ((0,1,2),(3,4)):
        for a,b in itertools.combinations(group,2):
            native[f'A{a}{b}']=s.SparseMatrix(7,7,{(a,b):1,(b,a):-1})
            native[f'S{a}{b}']=s.SparseMatrix(7,7,{(a,b):s.I,(b,a):s.I})
        for a in group[:-1]:native[f'D{a}-{group[-1]}']=s.SparseMatrix(7,7,{(a,a):s.I,(group[-1],group[-1]):-s.I})
    native['Y']=s.diag(0,0,0,0,0,s.I,-s.I)
    rho=[s.kronecker_product(eye(4),s.diag(*(helper.exterior(native[label],degree) for degree in (6,2,4)),cls=s.SparseMatrix))
        for label in original['native_P286_labels']]
    vertex_records=[row for row in vertices['primitive_vertices'] if row['group']=='gauge_A']
    T=[];B=[];smallV=[]
    for col,(mu,index) in enumerate(itertools.product(range(4),range(12))):
        record=vertex_records[col];assert record['coordinate']==[mu,index]
        V=clean(n*C[mu]*rho[index]);equal(V,decode(record['operator']))
        force=clean(Gamma[0]*V);read=clean(spin*(fullS*V+V.H*fullS)/2)
        equal(force.H,force);equal(read.H,read);equal(fullQ*force,force*fullQ)
        t=clean(F.T*force*F);b=clean(F.T*read*F)
        equal(force*F,F*t);equal(read*F,F*b);equal(b,-spin*Q*t)
        equal(t,decode(frozen['gauge_Hamiltonian_forces'][col]));equal(b,decode(frozen['original_current_readers'][col]))
        T.append(t);B.append(b);smallV.append(clean(F.T*V*F))
    Tseed=s.SparseMatrix.hstack(*(t*seed for t in T));Bseed=s.SparseMatrix.hstack(*(b*seed for b in B))
    forcing=realcolumn(-s.I*Tseed)
    equal(Tseed,decode(frozen['T_times_original_background']));equal(Bseed,decode(frozen['B_times_original_background']))
    equal(forcing,decode(frozen['original_real_forcing']))
    assert any(b!=t for b,t in zip(B,T))
    print('PASS direct full252 gauge vertices, actual source seed/clock and all48 distinct force/current operators',flush=True)
    fields=original['fields'];primal=[i for i,row in enumerate(fields) if row['group']=='primal_H']
    dualrows=[i for i,row in enumerate(fields) if row['group']=='dual_H'];matter=primal+dualrows
    gauge=[i for i,row in enumerate(fields) if row['group']=='gauge_A']
    expected=[list(x) for x in itertools.product(range(2),range(4),range(3))]
    assert [fields[i]['coordinate'] for i in primal]==[fields[i]['coordinate'] for i in dualrows]==expected
    H=s.MutableSparseMatrix(289,289,{})
    for row,col,powers,value in original['Fourier_Jacobi_entries']:
        H[row,col]+=s.sympify(value)*s.prod(p[j]**degree for j,degree in enumerate(powers))
    M=H.extract(matter,matter);HmA=H.extract(matter,gauge);HAm=H.extract(gauge,matter)
    conjugation=s.diag(eye(12),-eye(12),cls=s.SparseMatrix)
    minus=dict(zip(p,[-x for x in p]))
    generated=s.SparseMatrix.vstack(s.SparseMatrix.hstack(s.zeros(24),n*realify(d.subs(minus)).T*conjugation),
        s.SparseMatrix.hstack(n*conjugation*realify(d),s.zeros(24)))
    equal(M,generated);equal(M,decode(frozen['actual_real_matter_operator']))
    direct_forcing=[]
    for V in smallV:
        bilinear=conjugation*realify(V)
        direct_forcing.append((bilinear.T*realcolumn(dual.T)).col_join(bilinear*realcolumn(seed)))
    equal(HmA,s.SparseMatrix.hstack(*direct_forcing));equal(HAm,HmA.T)
    L=eye(24).col_join(spin*realify(S)*conjugation);equal(L,decode(frozen['canonical_dual_graph_real']))
    drift=clean(p[0]*eye(12)+s.I*h0+sum((p[j+1]*hj[j] for j in range(3)),s.zeros(12)))
    equal(d,c0*drift);KR=realify(drift);equal(KR,decode(frozen['original_real_drift']))
    embedding=M.diff(p[0])*L;equal(embedding,decode(frozen['real_time_equation_embedding']))
    assert embedding.rank()==24
    equal(M*L,embedding*KR);equal(HmA,-embedding*forcing)
    split=eye(12).row_join(s.I*eye(12)).col_join(eye(12).row_join(-s.I*eye(12)))
    unsplit=split.H/2;equal(split*unsplit,eye(24));equal(unsplit*split,eye(24))
    equal(split,decode(frozen['real_to_double_complex']));equal(unsplit,decode(frozen['double_complex_to_real']))
    equal(HAm*L,Bseed.H.row_join(Bseed.T)*split)
    equal(split*forcing,(-s.I*Tseed).col_join((s.I*Tseed.conjugate())))
    h=clean(h0+sum((ks[j]*hj[j] for j in range(3)),s.zeros(12)))
    hm=h.subs(dict(zip(ks,[-x for x in ks])),simultaneous=True)
    plus=energy*eye(12)-h;negative=energy*eye(12)+hm
    equal(plus,decode(frozen['positive_resolvent_denominator']));equal(negative,decode(frozen['negative_resolvent_denominator']))
    fourier=dict(zip(p,[-s.I*energy,*[s.I*x for x in ks]]))
    equal(split*KR.subs(fourier)*unsplit,s.diag(-s.I*plus,-s.I*negative.T,cls=s.SparseMatrix))
    equal(split*KR.subs(minus).subs(fourier)*unsplit,s.diag(s.I*negative,s.I*plus.T,cls=s.SparseMatrix))
    equal(realify(inverse)*realify(c0),eye(24));equal(realify(c0)*realify(inverse),eye(24))
    wrong=realify(drift.subs(fourier))
    assert clean(wrong-KR.subs(fourier))!=s.zeros(24)
    graph_wrong=eye(24).col_join(spin*realify(S))
    assert clean(M*graph_wrong-embedding*KR)!=s.zeros(48,24)
    output={'status':'PASS','replay_equal_except_runtime':True,'full252_vertices_independently_rebuilt':48,
        'actual_H12_frame_and_source_seed':True,'actual_preparation_norm_squared':1,'phase_branch_norms_squared':['1/2','1/2'],
        'whole_original_H_not_identified_with_phase_clock':True,'force_current_relation':'B=-s Q T',
        'original_independent_dual48_operator_rebuilt':True,'original48_forcing_bilinears_rebuilt':True,
        'all_symbol_graph_and_current_readback':True,'both_p_and_negative_p_resolvent_factorizations':True,
        'negative_controls':['realifying_after_Fourier_changes_operator','omitting_internal_conjugation_changes_dual_graph',
            'force_is_not_original_current','clock_identity_not_whole_operator_identity']}
    (audit/'source-receipt.json').write_text(json.dumps(output,indent=2)+'\n')
    print('PASS all4 formal derivatives, actual48 dual/primal rows, all48 forcing/current readbacks and ordered p/-p factors',flush=True)


if __name__=='__main__':main()
