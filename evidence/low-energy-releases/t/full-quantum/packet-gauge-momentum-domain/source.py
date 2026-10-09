#!/usr/bin/env python3
"""Generate the original complete112 for all axial q and physical frequency."""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import time
import sympy as s

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
FQ=HERE.parent;BASE=FQ.parent;ROOT=HERE.parents[4]
x,q=s.symbols('x q',real=True)
p=s.symbols('p0:4',real=True)
N=3*s.sqrt(30)/25;c=N*s.sqrt(2)


def read(path):return json.loads(path.read_text())


def clean(M):
    return s.SparseMatrix(M.rows,M.cols,{ij:v for ij,raw in s.SparseMatrix(M).todok().items()
        if (v:=s.expand(raw))!=0})


def encode(M):
    return {'shape':list(M.shape),'entries':[[i,j,str(v)] for (i,j),v in sorted(s.SparseMatrix(M).todok().items())]}


def matrix(record,names=None):
    return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(v,locals=names or {'x':x,'q':q}) for i,j,v in record['entries']})


def operator(entries,rows=289,cols=289,values=None):
    values=[c*x,0,0,s.I*s.sqrt(2)*q] if values is None else values
    out=s.MutableSparseMatrix(rows,cols,{})
    for i,j,exponents,value in entries:
        out[i,j]+=s.sympify(value)*s.prod(v**n for v,n in zip(values,exponents))
    return clean(out)


def main():
    began=time.monotonic()
    raw=read(BASE/'active-gauge/receipt.json')
    quotient=read(BASE/'active-gauge/quotient.json')
    propagation=read(BASE/'active-gauge/propagation.json')
    ward=read(FQ/'packet-gauge-kernel/ward.json')
    causal=read(FQ/'packet-gauge-causal/source.json')
    for name,digest in raw['source_sha256'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    assert s.simplify(s.sympify(raw['source_lapse'])-N)==0
    H=operator(raw['Fourier_Jacobi_entries'])
    original=H;indices=list(range(289));steps=[]
    for step in raw['algebraic_Schur_steps']:
        eliminated=step['eliminated_fields'];kept=[i for i in indices if i not in eliminated]
        ei=[indices.index(i) for i in eliminated];ki=[indices.index(i) for i in kept]
        inverse=s.SparseMatrix(len(eliminated),len(eliminated),
            {(eliminated.index(i),eliminated.index(j)):s.sympify(v) for i,j,v in step['algebraic_block_inverse']})
        assert clean(H.extract(ei,ei)*inverse)==s.eye(len(ei))
        assert clean(inverse*H.extract(ei,ei))==s.eye(len(ei))
        left=H.extract(ki,ei);back=clean(-inverse*H.extract(ei,ki))
        steps.append({'eliminated':eliminated,'kept':kept,'inverse':encode(inverse),
                      'left':encode(left),'back':encode(back)})
        H=clean(H.extract(ki,ki)+left*back);indices=kept
    assert indices==list(range(121))
    primitive=operator(raw['primitive_121_Fourier_Jacobi_entries'])[:121,:121]
    assert clean(H-primitive)==s.zeros(121)
    removed=quotient['fixed_section_removed_original_fields']
    retained=quotient['retained_original_fields'];keep=list(range(9))+retained
    K=matrix(ward['K0'],{str(v):v for v in p}).subs(dict(zip(p,[c*x,0,0,s.I*s.sqrt(2)*q])))
    K=clean(K)
    assert clean(original*K)==s.zeros(289,9)
    minor=K.extract(removed,range(9));minor_inv=minor.inv(method='DM')
    assert not any(v.has(x,q) for v in minor.todok().values())
    Tg=operator(raw['source_primitive_gauge_tangent'],cols=12)
    T=Tg[:,raw['J_independent_columns']]
    T=clean(T-K*minor_inv*T.extract(removed,range(9)))
    assert T[:9,:]==s.eye(9) and T.extract(removed,range(9))==s.zeros(9)
    G=clean((H*T[:121,:])[:9,:])
    assert not any(v.has(x,q) for v in G.todok().values())
    assert G.det()!=0 and G==matrix(causal['scalar_block'])
    torque=s.zeros(121,9);torque[:9,:]=G
    assert clean(H*T[:121,:]-torque)==s.zeros(121,9)
    E=s.SparseMatrix(121,103,{(row,j):1 for j,row in enumerate(retained)})
    C=clean(T[:121,:].row_join(E).extract(keep,range(112)))
    minus=C.conjugate().subs({x:-x})
    # q is real and appears in the source through i*q.  Coefficient conjugation
    # flips that spatial derivative; the separate x reflection flips time.
    M=clean(H.extract(keep,keep));Q=H.extract(retained,retained)
    assert C.det()==1 and minus.det()==1
    assert clean(minus.T*M*C-s.diag(G,Q))==s.zeros(112)
    legacy={'lam':c*x,'k':s.sqrt(2)*q}
    oldQ=s.SparseMatrix(103,103,{(i,j):s.sympify(v.replace('lambda','lam'),locals=legacy)
                              for i,j,v in quotient['quotient_operator_103_by_103']})
    assert clean(Q-oldQ)==s.zeros(103)
    scale103=list(map(s.sympify,propagation['constant_diagonal_field_scaling']))
    D=s.diag(*([s.Integer(1)]*9+scale103));A=clean(D*M*D/N)
    for value in A.todok().values():s.Poly(value,x,q,domain=s.QQ_I)
    assert clean(M.subs(q,s.Rational(1,131072))-matrix(causal['complete112']))==s.zeros(112)
    print('PASS true all-q168/121/112 source, constant minor/G9, exact separation and original103 readback',flush=True)

    # Replay the native finite rotation polynomial identities, using every
    # original momentum monomial.  No angle samples or isotropy premise.
    path=BASE/'active-gauge/rotation/finite.py'
    spec=importlib.util.spec_from_file_location('momentum_native_rotation',path)
    finite=importlib.util.module_from_spec(spec);sys.modules[spec.name]=finite;spec.loader.exec_module(finite)
    cert=read(BASE/'active-gauge/rotation/finite.json')
    coefficient_denominator,coefficients=finite.source_integer_coefficients(raw)
    assert coefficient_denominator==cert['source_coefficient_common_denominator']
    rotations=[]
    for data in cert['certificates']:
        field={(i,j):tuple(v) for i,j,v in data['field_numerator']}
        spatial={(i,j):tuple(v) for i,j,v in data['spatial_numerator']}
        finite.field_inverse(field,data['field_constant_denominator'])
        slots=finite.finite_congruence(coefficients,spatial,data['field_constant_denominator'],field)
        assert slots==data['exact_zero_congruence_coefficient_slots']
        rows=[s.Rational(0)]*289
        for (i,j),values in field.items():rows[i]+=sum(abs(v) for v in values)/s.Integer(data['field_constant_denominator'])
        rotations.append({'axis':data['axis'],'all_momentum_zero_slots':slots,
                          'uniform_infinity_norm_for_abs_parameter_le1':str(max(rows)),
                          'inverse_same_bound':True})
    radius_path=ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/LightModes/Source.lean'
    text=radius_path.read_text()
    matched=re.search(r'def momentumRadius\s*:\s*ℝ\s*:=\s*(\d+)\s*/\s*(\d+)',text)
    assert matched
    light=s.Rational(int(matched[1]),int(matched[2]));R=s.Rational(1,32768);rho=s.Rational(1,131072)
    assert light==s.Rational(5234375,294988800512)
    assert light+rho/2<R and 3*light/2<R and 3*rho/2<light
    print('PASS native all-angle/all-momentum covariance and actual light-ball plus external-transfer coverage',flush=True)
    inputs=[BASE/'active-gauge/receipt.json',BASE/'active-gauge/propagation.json',
        BASE/'active-gauge/quotient.json',FQ/'packet-gauge-kernel/ward.json',
        FQ/'packet-gauge-causal/source.json',BASE/'active-gauge/rotation/finite.json',
        BASE/'active-gauge/rotation/finite.py',radius_path,
        ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/LightSpace/Radial.lean',
        ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/PacketPairResponse/Band.lean']
    factors=[]
    for block in propagation['blocks']:
        factors.append({'indices':block['quotient_indices'],'constant':block['constant'],
            'factors':[{'polynomial':str(s.sympify(v['polynomial'],locals={'u':x,'q':q})),
                        'multiplicity':v['multiplicity']} for v in block['factors']]})
    result={'scope':'STRIKE_ORIGINAL_ALL_SMALL_MOMENTUM_COMPLETE112_SOURCE_AND_NATIVE_COVARIANCE',
        'source_sha256':raw['source_sha256'],
        'input_sha256':{str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in inputs},
        'clock':'lambda=c*x, c=N*sqrt(2)=6*sqrt(15)/25; original time',
        'physical_axis':'k=(0,0,sqrt(2)*q); p3=i*sqrt(2)*q',
        'all_q_including_zero':True,'removed':removed,'keep112':keep,
        'auxiliary_steps':steps,'primitive121':encode(H),'complete112':encode(M),
        'scales112':encode(D),'normalized112':encode(A),'scalar_G9':encode(G),
        'symmetry_minor':encode(minor),'symmetry_minor_inverse':encode(minor_inv),
        'polynomial_separation':encode(C),'scalar_torque_graph':encode(T[:121,:]),
        'all_source_factors':factors,'native_rotation_checks':rotations,
        'all_direction_section':'Transport the original axial section and its whole289 backwrite with the actual native field circle; do not assume a fixed world coordinate removed9 chart.',
        'q_radius':str(R),'actual_light_q_radius':str(light),
        'original_incoming_q':str(rho),'external_q_magnitude':str(rho/2),'outgoing_q':str(3*rho/2),
        'light_plus_fixed_external_strict_margin':str(R-light-rho/2),
        'whole_light_one_and_half_strict_margin':str(R-3*light/2),
        'elapsed_seconds':round(time.monotonic()-began,3)}
    (HERE/'source.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS source momentum construction',result['elapsed_seconds'],flush=True)


if __name__=='__main__':main()
