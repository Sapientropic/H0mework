#!/usr/bin/env python3
"""Primitive A1=S01 family of the original active 289-field action.

Only the connection changes. In particular the primitive B, coframe, phase
clock, scalar value and independent dual background are held fixed. The scalar
completion is constructed before comparison with the old theta-class reader.
"""
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
FQ=HERE.parent
BASE=FQ.parent
ROOT=HERE.parents[4]


def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec)
    sys.modules[name]=module
    spec.loader.exec_module(module)
    return module


def clean(matrix):
    return s.SparseMatrix(matrix.rows,matrix.cols,{key:value for key,raw in s.SparseMatrix(matrix).todok().items()
        if (value:=s.expand(raw))!=0})


def encode(matrix):
    return {'shape':[matrix.rows,matrix.cols],
        'entries':[[i,j,str(v)] for (i,j),v in sorted(s.SparseMatrix(matrix).todok().items())]}


def build():
    start=time.monotonic()
    original=json.loads((BASE/'active-gauge/receipt.json').read_text())
    for path,digest in original['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    native=load(FQ/'vertex-tensor/compute.py','gauge_primitive_vertices')
    _,_,N,_,context=native.source_tables(False)
    jet=load(BASE/'active-gauge/compute.py','gauge_primitive_jet')
    J=jet.Jet
    coordinates=jet.Coordinates()
    for group,shape in [('scalar_J',(9,)),('gauge_A',(4,12)),('coframe',(4,4)),
        ('primal_H',(2,4,3)),('dual_H',(2,4,3)),('Lorentz',(4,6)),
        ('gravity_B',(6,6)),('multiplier',(6,6)),('gauge_B',(6,12))]:
        coordinates.group(group,shape)
    assert coordinates.fields==original['fields']
    q=coordinates.value
    fundamental=context['fundamental']
    assert original['native_P286_labels'][1]=='S01'
    generator=fundamental[1]
    assert generator[:2,:2]==s.Matrix([[0,s.I],[s.I,0]])
    e0=context['coframe']
    e=jet.matrix(4,4,lambda i,j:e0[i,j]+q('coframe',i,j))
    adj=jet.adjugate(e)
    primal=jet.matrix(12,1,lambda i,j:context['primal'][i]+s.I*context['primal'][i+12]+
        q('primal_H',0,i//3,i%3)+s.I*q('primal_H',1,i//3,i%3))
    dual=jet.matrix(1,12,lambda i,j:context['dual'][j]+s.I*context['dual'][j+12]+
        q('dual_H',0,j//3,j%3)+s.I*q('dual_H',1,j//3,j%3))
    # Literal original Dirac insertion: epsilon times adj(e) chi i Gamma rho(a) psi.
    matter=J()
    for internal in range(4):
        block=context['blocks'][1,internal]
        # Convert the literal independent real bilinear back to its full complex
        # matrix; the first real-real block is Re and the imag-real is -Im.
        vertex=block[:12,:12]-s.I*block[12:,:12]
        matter+=adj[1][internal]*jet.multiply(dual,jet.multiply(jet.fixed(vertex),primal))[0][0].real_part()

    pairs=context['pairs'];abar=s.Matrix(original['actual_background']['gauge_connection']).applyfunc(s.sympify)
    gram=s.Matrix(12,12,lambda i,j:s.re(-s.trace(fundamental[i]*fundamental[j])))
    gram_inv=gram.inv();native_gram=gram.copy();native_gram[11,11]=1
    brackets={}
    for a,b in itertools.product(range(12),repeat=2):
        comm=fundamental[a]*fundamental[b]-fundamental[b]*fundamental[a]
        coeff=gram_inv*s.Matrix([s.re(-s.trace(g*comm)) for g in fundamental])
        assert sum((coeff[c]*fundamental[c] for c in range(12)),s.zeros(7))==comm
        for c in range(12):
            if coeff[c]:brackets[a,b,c]=coeff[c]
    F0=s.Matrix(6,12,lambda pair,c:sum(abar[pairs[pair][0],a]*abar[pairs[pair][1],b]*v
        for (a,b,out),v in brackets.items() if out==c))
    sigma=s.sympify(original['source_coupling'])
    # The source Hodge is live-coframe conjugated, even at this fixed background.
    exterior0=native.load(BASE/'nonlinear-contact/slice_checks.py','gauge_primitive_slice').wedge_matrix(e0)
    B0=-exterior0.inv()*s.Matrix(jet.J)*exterior0*F0/sigma
    connection=jet.matrix(4,12,lambda mu,c:abar[mu,c]+q('gauge_A',mu,c))
    auxiliary=jet.matrix(6,12,lambda pair,c:B0[pair,c]+q('gauge_B',pair,c))
    curvature_first=jet.matrix(6,12,lambda pair,c:
        sum((v*connection[pairs[pair][1]][b] for (a,b,out),v in brackets.items()
             if pairs[pair][0]==1 and a==1 and out==c),J())+
        sum((v*connection[pairs[pair][0]][a] for (a,b,out),v in brackets.items()
             if pairs[pair][1]==1 and b==1 and out==c),J()))
    # The only external one-form component is 1, hence [a_mu,a_nu] is identically zero.
    gauge=J()
    for i,j,a,b in itertools.product(range(6),range(6),range(12),range(12)):
        if jet.W[i,j] and native_gram[a,b]:
            gauge+=jet.W[i,j]*native_gram[a,b]*auxiliary[i][a]*curvature_first[j][b]

    _,vacuum,_,_=jet.source.parse_source(ROOT)
    basis4=list(itertools.combinations(range(7),4))
    vc=s.Matrix([vacuum.get(word,0) for word in basis4]);v=vc.col_join(s.zeros(35,1))
    rho=[jet.active.realify(jet.active.exterior(g,4)) for g in fundamental]
    orbit=s.Matrix.hstack(*(r*v for r in rho))
    inclusion=orbit[:,original['J_independent_columns']]
    assert (rho[1]*v).is_zero_matrix
    jaction=(inclusion.T*inclusion).inv()*inclusion.T*rho[1]*inclusion
    assert rho[1]*inclusion==inclusion*jaction
    eta=jet.multiply(jet.fixed(inclusion),jet.matrix(9,1,lambda i,j:q('scalar_J',i)))
    dphi=jet.multiply(jet.fixed(inclusion),jet.matrix(9,1,lambda i,j:q('scalar_J',i,derivative=1)))
    for c in range(12):
        dphi=jet.add(dphi,jet.multiply(jet.fixed(rho[c]),jet.add(
            jet.scale(abar[1,c],eta),jet.scale(q('gauge_A',1,c),jet.fixed(v)))))
    changed=jet.multiply(jet.fixed(rho[1]),eta)
    scalar_first=N*sum((a[0]*b[0] for a,b in zip(dphi,changed)),J())
    scalar_second=N*s.Rational(1,2)*sum((a[0]*a[0] for a in changed),J())
    # D_(A+epsilon a)(v+eta)=D_A(v+eta)+epsilon rho(a)eta.
    # D_A v=0 on the complete primitive family, so the displayed first jet
    # produces the exact quadratic field part for every epsilon, not a scalar deletion.
    first=matter+gauge+scalar_first
    assert not first.terms.get((),jet.ZERO)
    assert all(not n.imag for n in first.terms.values())
    H1=jet.fourier_hessian(coordinates,first)
    H2=jet.fourier_hessian(coordinates,scalar_second)
    HS=jet.fourier_hessian(coordinates,scalar_first)
    bare=jet.fourier_hessian(coordinates,matter+gauge)
    prior=json.loads((FQ/'packet-field/current-data.json').read_text())
    expected={(i,j,(0,0,0,0)):jet.number(s.sympify(value)) for i,j,value in prior['selected']['entries']}
    assert bare==expected
    assert HS and H2
    # A separate finite-epsilon real 70-coordinate covariant-gradient expansion
    # checks the scalar differential Hessian before any Fourier specialization.
    p1,epsilon=s.symbols('p1 epsilon',real=True)
    scalar_map=s.zeros(70,289)
    scalar_map[:,:9]=p1*inclusion+sum((abar[1,c]*rho[c]*inclusion for c in range(12)),s.zeros(70,9))
    for c in range(12):scalar_map[:,coordinates.groups['gauge_A'][1,c]]=rho[c]*v
    scalar_delta=s.zeros(70,289);scalar_delta[:,:9]=rho[1]*inclusion
    scalar_direct=clean(N*((scalar_map.subs(p1,-p1)+epsilon*scalar_delta).T*
        (scalar_map+epsilon*scalar_delta)-scalar_map.subs(p1,-p1).T*scalar_map))
    scalar_generated=s.zeros(289)
    for (i,j,power),value in HS.items():
        assert not any(power[k] for k in [0,2,3])
        scalar_generated[i,j]+=epsilon*jet.F.to_sympy(value.real)*p1**power[1]
    for (i,j,power),value in H2.items():
        assert not any(power)
        scalar_generated[i,j]+=epsilon**2*jet.F.to_sympy(value.real)
    assert clean(scalar_direct-scalar_generated)==s.zeros(289)
    assert scalar_generated[0,0].coeff(epsilon,1)==36*s.sqrt(15)/125
    assert 2*scalar_generated[0,0].coeff(epsilon,2)==12*s.sqrt(30)/25
    E1=s.zeros(289,1)
    for key,value in first.terms.items():
        if len(key)==1:
            field,derivative=coordinates.jets[key[0]]
            if derivative==-1:E1[field]+=jet.F.to_sympy(value.real)
    pzero=s.zeros(289,289)
    for i,j,power,value in original['Fourier_Jacobi_entries']:
        if not any(power):pzero[i,j]+=s.sympify(value)
    a=s.zeros(289,1);a[coordinates.groups['gauge_A'][1,1]]=1
    assert E1==pzero*a and E1!=s.zeros(289,1)
    assert all(coordinates.fields[i]['group']!='scalar_J' for i,j in s.SparseMatrix(E1).todok())
    for operator in [H1,H2,HS]:
        for (i,j,power),value in operator.items():
            assert operator.get((j,i,power),jet.ZERO)==(-1)**sum(power)*value
    print('PASS primitive family H1, H2 and reader derivative with full scalar completion',flush=True)
    print('PASS old188 comparison only after literal action differentiation; E1 nonzero',len(s.SparseMatrix(E1).todok()),flush=True)
    scalar_null=all(not scalar_second.terms.get((i,),jet.ZERO) for i in range(len(coordinates.jets)))
    assert scalar_null
    data={'scope':'STRIKE_PRIMITIVE_A1_S01_FULL289_HESSIAN_FAMILY',
        'source_sha256':original['source_sha256'],'fields':coordinates.fields,
        'external_family':'A_epsilon=Abar+epsilon*(d x1) S01; all other primitive fields fixed, including B; real epsilon',
        'phase':'Same original physical time and fixed original FullPhase transformation; no changed frequency.',
        'action_identity':'S_epsilon-S_0=epsilon*current_full+epsilon^2*scalar_square (through degree2 in all original field jets)',
        'Hessian_identity':'H_epsilon(p)=H0(p)+epsilon*H1(p)+epsilon^2*H2(p)',
        'reader_identity':'Q_a(epsilon,p)=H1(p)+2*epsilon*H2(p); Q_a_prime=2*H2',
        'H1':jet.encoded_operator(H1),'H2':jet.encoded_operator(H2),
        'scalar_H1_completion':jet.encoded_operator(HS),'bare188':jet.encoded_operator(bare),
        'E1':encode(E1),'E_family':'E_epsilon=epsilon*E1; E0=0; no epsilon2 background Euler term',
        'external_direction':encode(a),'scalar_J_inclusion':encode(inclusion),'scalar_v':encode(v),
        'scalar_rho':list(map(encode,rho)),'scalar_selected_J_action':encode(jaction),
        'fundamental':list(map(encode,fundamental)),'native_pairing':encode(native_gram),
        'gauge_background':encode(abar),'gauge_auxiliary_background':encode(B0),
        'independent_primal_background':encode(context['primal']),
        'independent_dual_background':encode(context['dual']),
        'reader_contact_nonzero':True,'scalar_background_second_order_Euler_zero':scalar_null,
        'finite_epsilon_scalar_gradient_identity_all_p1':True,
        'negative_controls':{'old188_full_H1_missing_entry_00':'36*sqrt(15)/125',
            'drop_native_reader_contact_missing_entry_00':'12*sqrt(30)/25'},
        'original_188_is_not_full_H1':True,'elapsed_seconds':round(time.monotonic()-start,3)}
    (HERE/'source.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('PASS primitive source jets',data['elapsed_seconds'],flush=True)


if __name__=='__main__':build()
