#!/usr/bin/env python3
"""Independent audit of source matter vertices and the active exchange frame.

The candidate programs are not imported. Clifford data are read from Lean,
exterior actions use the earlier independent bit implementation, coframe
derivatives use Jacobi's inverse formula, and auxiliary inverses are recomputed
directly from H289. All identities retain four formal momenta.
"""
from __future__ import annotations

import argparse
from collections import Counter
import importlib.util
import itertools
import json
from pathlib import Path
import re
import sympy as s


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def equal(left, right):
    assert left.shape == right.shape
    assert all(s.cancel(value) == 0 for value in s.SparseMatrix(left-right).todok().values())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    base = root/'Verification/physics/low-energy-phenomenology'
    core = root/'Lean/SaturationMonoid/PhysicsCore'
    folder = base/'matter-vertices'
    vertices = json.loads((folder/'receipt.json').read_text())
    exchange = json.loads((folder/'exchange.json').read_text())
    assert vertices == json.loads(Path('/tmp/matter-vertices-audit-replay.json').read_text())
    assert exchange == json.loads(Path('/tmp/matter-exchange-audit-replay.json').read_text())
    original = json.loads((base/'active-gauge/receipt.json').read_text())
    full_phase = json.loads((base/'full-phase/receipt.json').read_text())
    p = s.symbols('p0:4', real=True)
    r = s.symbols('r0:4', real=True)
    symbols = {str(x): x for x in p+r}

    def decode(record):
        return s.SparseMatrix(*record['shape'], {(i,j):s.sympify(value, locals=symbols)
            for i,j,value in record['entries']})

    def entries(record, rows, cols):
        return decode({'shape':[rows,cols], 'entries':record})

    def polynomial(record, rows, cols):
        matrix = s.MutableSparseMatrix(rows, cols, {})
        for i,j,powers,value in record:
            matrix[i,j] += s.sympify(value)*s.prod(x**power for x,power in zip(p,powers))
        return clean(matrix)

    def reverse(matrix):
        return matrix.subs(dict(zip(p,[-x for x in p])), simultaneous=True)

    spec = importlib.util.spec_from_file_location('certified_bit_exterior',
        base/'mixed-symbol/audit/independent_check.py')
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    gamma = []
    text = (core/'DiracCliffordRepresentation.lean').read_text()
    for name in ('Zero','One','Two','Three'):
        literal = re.search(r'def diracGamma'+name+r'\s*:.*?:=\s*!!\[(.*?)\]', text, re.S).group(1)
        gamma.append(s.SparseMatrix([[s.sympify(v.strip().replace('Complex.I','I'))
            for v in row.split(',')] for row in literal.split(';')]))
    text = (core/'PointwiseDiracSpinConnectionLift.lean').read_text()
    first = [int(x) for x in re.search(r'def lorentzBivectorFirst.*?!\[(.*?)\]',text,re.S).group(1).split(',')]
    second = [int(x) for x in re.search(r'def lorentzBivectorSecond.*?!\[(.*?)\]',text,re.S).group(1).split(',')]
    pairs = list(zip(first,second))
    assert pairs == [(0,1),(0,2),(0,3),(2,3),(3,1),(1,2)]
    eta = s.diag(-1,1,1,1)
    for a,b in itertools.product(range(4),repeat=2):
        equal(gamma[a]*gamma[b]+gamma[b]*gamma[a], 2*eta[a,b]*s.eye(4))
    basis = {degree:list(itertools.combinations(range(7),degree)) for degree in (6,2,4)}
    internal = [(degree,word) for degree in (6,2,4) for word in basis[degree]]
    names = ['colorZeroIndex','colorOneIndex','colorTwoIndex','weakZeroIndex',
        'weakOneIndex','hyperPlusIndex','hyperMinusIndex']
    text = (core/'SU7ExteriorYukawaMassSpectrum.lean').read_text()
    text = text.split('def finiteGenerationScalarSubset :',1)[1].split('\ndef ',1)[0]
    vacuum = {tuple(sorted(names.index(x.strip()) for x in term.split(','))):1
        for term in re.findall(r'\|\s*[01],\s*[01]\s*=>\s*\{([^}]+)\}',text)}
    assert len(vacuum) == 4

    def yukawa(scalar):
        small = s.MutableSparseMatrix(7,21,{})
        for col,two in enumerate(basis[2]):
            for four,value in scalar.items():
                if not set(two).intersection(four):
                    small[basis[6].index(tuple(sorted(two+four))),col] += value*(-1)**sum(a>b for a in two for b in four)
        inside = s.MutableSparseMatrix(63,63,{})
        inside[:7,7:28] = small
        return clean(s.kronecker_product(s.diag(0,0,1,1),inside))

    fundamental = {}
    for group in ((0,1,2),(3,4)):
        for a,b in itertools.combinations(group,2):
            fundamental[f'A{a}{b}'] = s.SparseMatrix(7,7,{(a,b):1,(b,a):-1})
            fundamental[f'S{a}{b}'] = s.SparseMatrix(7,7,{(a,b):s.I,(b,a):s.I})
        for a in group[:-1]:
            fundamental[f'D{a}-{group[-1]}'] = s.SparseMatrix(7,7,{(a,a):s.I,(group[-1],group[-1]):-s.I})
    fundamental['Y'] = s.diag(0,0,0,0,0,s.I,-s.I)
    labels = list(fundamental)
    assert labels == original['native_P286_labels']
    rho = [clean(s.kronecker_product(s.eye(4),
        s.diag(*[helper.exterior(matrix,degree) for degree in (6,2,4)])))
        for matrix in fundamental.values()]
    gamma5 = s.diag(-1,-1,1,1)
    Sspin = gamma[0]*gamma5
    S = clean(s.kronecker_product(Sspin,s.eye(63)))
    Gamma = [clean(s.kronecker_product(g,s.eye(63))) for g in gamma]
    spin = [clean(s.kronecker_product(gamma[a]*gamma[b]/2,s.eye(63))) for a,b in pairs]
    n = s.sqrt(s.Rational(54,125))
    kappa = s.sqrt(2)
    alpha = 3*kappa/5
    omega = s.simplify(3*n*(kappa-alpha)/2)
    assert n > 0 and n**2 == s.Rational(54,125)
    assert n == s.sympify(original['source_lapse']) == s.sympify(vertices['source_lapse'])
    assert omega == s.sympify(original['source_frequency']) == s.sympify(vertices['source_frequency'])
    Q = clean(s.kronecker_product(gamma5,s.eye(63))+
        2*s.kronecker_product(s.eye(4),s.diag(*[int(degree==6) for degree,_ in internal])))
    equal(Q,decode(full_phase['phase_generator']))
    text = (core/'Stage9C/Material/SpinPair/ColorDoublet.lean').read_text().split('def sourceColorPauli',1)[1].split('theorem',1)[0]
    color = [s.SparseMatrix([[s.sympify(v.strip().replace('Complex.I','I'))
        for v in row.split(',')] for row in literal.split(';')])
        for literal in re.findall(r'!!\[(.*?)\]',text,re.S)]
    connection = [s.zeros(252)]
    for j in range(3):
        crho = s.diag(*[helper.exterior(s.diag(color[j],s.zeros(5)),degree) for degree in (6,2,4)])
        connection.append(clean(kappa*spin[j+3]+alpha*s.kronecker_product(s.eye(4),crho)))
    from_receipt_A = s.Matrix(original['actual_background']['gauge_connection']).applyfunc(s.sympify)
    from_receipt_O = s.Matrix(original['actual_background']['lowered_Lorentz_connection']).applyfunc(s.sympify)
    for mu in range(4):
        equal(connection[mu],sum((from_receipt_A[mu,a]*rho[a] for a in range(12)),s.zeros(252))+
            sum((from_receipt_O[mu,a]*spin[a] for a in range(6)),s.zeros(252)))
    Y = yukawa(vacuum)
    equal(Y,decode(full_phase['original_Y']))
    C = [s.I*Gamma[mu]/(n if mu==0 else 1) for mu in range(4)]
    B = clean(sum((C[mu]*connection[mu] for mu in range(4)),s.zeros(252)))
    D = clean(sum((C[mu]*p[mu] for mu in range(4)),s.zeros(252))+B+Y+omega/n*Gamma[0]*Q)
    equal(D,decode(vertices['full_stationary_Dirac_operator']))
    equal(B,decode(full_phase['original_constant_B']))
    seed = s.MutableSparseMatrix(252,1,{})
    for sp,word,value in ((0,(1,5),1),(1,(0,5),-1),(2,(1,5),1),(3,(0,5),-1)):
        seed[sp*63+internal.index((2,word)),0] = value
    dual = kappa*seed.T*S
    zero = dict.fromkeys(p,0)
    equal(D.subs(zero)*seed,s.zeros(252,1))
    equal(dual*D.subs(zero),s.zeros(1,252))

    actual = {}
    for mu in range(4):
        for a in range(12):actual['gauge_A',(mu,a)] = clean(n*C[mu]*rho[a])
        for a in range(6):actual['Lorentz',(mu,a)] = clean(n*C[mu]*spin[a])
    e = s.diag(n,1,1,1)
    ei = e.inv()
    jets = [[clean(s.I*Gamma[a]*(p[mu]*s.eye(252)+connection[mu])+
        (omega*Gamma[a]*Q if mu==0 else s.zeros(252))) for a in range(4)] for mu in range(4)]
    coframe_controls = []
    frozen_derivatives = {tuple(item['coordinate']):item
        for item in vertices['coframe_actual_adjugate_and_volume_derivatives']}
    for a,nu in itertools.product(range(4),repeat=2):
        h = s.zeros(4);h[a,nu]=1
        # Jacobi's formula: d(det e * e^-1), independent of polynomial adjugate differentiation.
        dvol = n*s.trace(ei*h)
        dadj = clean(dvol*ei-n*ei*h*ei)
        equal(dadj,decode(frozen_derivatives[a,nu]['adjugate_derivative']))
        assert dvol == s.sympify(frozen_derivatives[a,nu]['volume_derivative'])
        value = clean(sum((dadj[mu,b]*jets[mu][b] for mu,b in itertools.product(range(4),repeat=2)),s.zeros(252))+dvol*Y)
        actual['coframe',(a,nu)] = value
        phase_piece = clean(sum((dadj[0,b]*omega*Gamma[b]*Q for b in range(4)),s.zeros(252)))
        if phase_piece != s.zeros(252):coframe_controls.append([a,nu])
    assert coframe_controls and dvol*Y != s.zeros(252)
    for im in range(2):
        for col,word in enumerate(basis[4]):actual['scalar',(im,col)] = clean(n*s.I**im*yukawa({word:1}))
    assert len(actual) == 158
    for item in vertices['primitive_vertices']:
        equal(actual[item['group'],tuple(item['coordinate'])],decode(item['operator']))
    assert Counter(item['group'] for item in vertices['primitive_vertices']) == {'gauge_A':48,'Lorentz':24,'coframe':16,'scalar':70}
    print('PASS all158 full252 vertices from source gamma/exterior data;16 independent Jacobi coframe derivatives',flush=True)

    H = polynomial(original['Fourier_Jacobi_entries'],289,289)
    equal(reverse(H).T,H)
    fields = original['fields']
    v = s.Matrix([vacuum.get(word,0) for word in basis[4]])
    orbit = [helper.exterior(matrix,4)*v for matrix in fundamental.values()]
    source_operators = {}
    for i,field in enumerate(fields):
        key = field['group'],tuple(field['coordinate'])
        if key in actual:source_operators[i]=actual[key]
        elif field['group']=='scalar_J':
            a=original['J_independent_columns'][field['coordinate'][0]]
            source_operators[i]=clean(n*yukawa({word:value for word,value in zip(basis[4],orbit[a]) if value}))
    assert len(source_operators)==97
    for item in vertices['active_289_bosonic_source_operators']:
        equal(source_operators[item['field']],decode(item['operator']))
    matched=0
    for boson,V in source_operators.items():
        left=clean(dual*V);right=clean(V.subs(zero)*seed)
        for matter,field in enumerate(fields):
            if field['group'] not in ('primal_H','dual_H'):continue
            im,sp,color=field['coordinate']
            coord=sp*63+internal.index((2,(color,5)))
            value=(left[coord] if field['group']=='primal_H' else right[coord])*s.I**im
            assert s.expand(s.re(value)-H[boson,matter])==0
            assert s.expand(s.re(value).subs(dict(zip(p,[-x for x in p])))-H[matter,boson])==0
            matched+=1
    assert matched==97*48
    # Independent complex-linear dual evaluation has [[Re V,-Im V],[-Im V,-Re V]].
    testV=actual['scalar',(1,0)]
    dual_real=s.diag(s.eye(252),-s.eye(252),cls=s.SparseMatrix)*helper.realify(testV)
    R,I=testV.as_real_imag()
    equal(dual_real,s.SparseMatrix.vstack(s.SparseMatrix.hstack(R,-I),s.SparseMatrix.hstack(-I,-R)))
    assert dual_real!=helper.realify(testV)
    shifted=D.subs(dict(zip(p,[p[i]+r[i] for i in range(4)])),simultaneous=True)
    for a,T in enumerate(rho):
        var=clean(n*yukawa({word:value for word,value in zip(basis[4],orbit[a]) if value}))
        for mu in range(4):var+=n*C[mu]*(T*connection[mu]-connection[mu]*T-r[mu]*T)
        equal(var+n*shifted*T-n*T*D,s.zeros(252))
    for a,(i,j) in enumerate(pairs):
        L=s.zeros(4);L[i,j]=eta[i,i];L[j,i]=-eta[j,j]
        h=L*e;T=spin[a]
        var=sum((h[b,nu]*actual['coframe',(b,nu)] for b,nu in itertools.product(range(4),repeat=2)),s.zeros(252))
        for mu in range(4):var+=n*C[mu]*(T*connection[mu]-connection[mu]*T-r[mu]*T)
        equal(var+n*shifted*T-n*T*D,s.zeros(252))
    print('PASS97 actual occupied source legs, both Hessian orientations, independent dual pairing and18 full local Ward identities',flush=True)

    # Reconstruct each Schur step directly, rather than adopting its supplied inverse/write-back.
    current=H
    F=s.SparseMatrix(s.eye(289))
    Finv=s.SparseMatrix(s.eye(289))
    auxiliary=[]
    for step in original['algebraic_Schur_steps']:
        ids=step['eliminated_fields'];outside=[i for i in range(289) if i not in ids]
        block=current[ids,ids]
        inverse=clean(block.inv(method='DM'))
        equal(block*inverse,s.eye(len(ids)));equal(inverse*block,s.eye(len(ids)))
        equal(inverse,entries(step['algebraic_block_inverse'],289,289)[ids,ids])
        W=s.MutableSparseMatrix(289,289,{})
        response=clean(-inverse*current[ids,outside])
        for row,i in enumerate(ids):
            for col,j in enumerate(outside):
                if response[row,col]:W[i,j]=response[row,col]
        equal(W,polynomial(step['write_back_auxiliary_from_retained'],289,289))
        equal(W*W,s.zeros(289))
        change=s.eye(289)+W
        current=clean(reverse(change).T*current*change)
        F=clean(F*change);Finv=clean((s.eye(289)-W)*Finv)
        equal(current[ids,outside],s.zeros(len(ids),len(outside)))
        equal(current[outside,ids],s.zeros(len(outside),len(ids)))
        auxiliary.append((ids,block,inverse,step['eliminated_groups']))
    equal(current[:121,:121],polynomial(original['primitive_121_Fourier_Jacobi_entries'],121,121))
    broken=original['Ward_constraint_elimination']['broken_parameter_columns']
    tangent=polynomial(original['source_primitive_gauge_tangent'],289,12)[:121,broken]
    equal(tangent[:9,:],s.eye(9))
    change=s.MutableSparseMatrix(s.eye(289));change[9:121,:9]=tangent[9:,:]
    inverse=s.MutableSparseMatrix(s.eye(289));inverse[9:121,:9]=-tangent[9:,:]
    current=clean(reverse(change).T*current*change)
    F=clean(F*change);Finv=clean(inverse*Finv)
    M=current[:9,:9];Minv=clean(M.inv(method='DM'))
    equal(M*Minv,s.eye(9));equal(Minv*M,s.eye(9))
    equal(current[:9,9:121],s.zeros(9,112));equal(current[9:121,:9],s.zeros(112,9))
    frozenF=decode(exchange['full_polynomial_field_change'])
    final=clean(Finv*frozenF)
    assert all(i in range(9,121) and j in range(9,121)
        for i,j in clean(final-s.eye(289)).todok())
    frame=final[9:121,9:121]
    inverse_frame=clean(frame.inv(method='DM'))
    equal(frame*inverse_frame,s.eye(112));equal(inverse_frame*frame,s.eye(112))
    lastinv=s.MutableSparseMatrix(s.eye(289));lastinv[9:121,9:121]=inverse_frame
    Finv=clean(lastinv*Finv)
    equal(Finv,decode(exchange['full_polynomial_inverse']))
    equal(frozenF*Finv,s.eye(289));equal(Finv*frozenF,s.eye(289))
    F=frozenF
    normal=clean(reverse(F).T*H*F)
    A=decode(exchange['canonical_operator']);Bcomp=decode(exchange['independent_dual_operator'])
    expected=s.MutableSparseMatrix(289,289,{})
    expected[:9,:9]=M;expected[9:88,9:88]=A;expected[88:112,88:112]=Bcomp
    for ids,block,_,_ in auxiliary:
        for i,row in enumerate(ids):
            for j,col in enumerate(ids):
                if block[i,j]:expected[row,col]=block[i,j]
    equal(normal,expected)
    assert all(s.denom(s.cancel(value)).free_symbols.isdisjoint(set(p)) for value in F.todok().values())
    assert all(s.denom(s.cancel(value)).free_symbols.isdisjoint(set(p)) for value in Finv.todok().values())
    assert clean(F.T*H*F-normal)!=s.zeros(289)
    print('PASS direct original auxiliary inverses, scalar Ward contact and all-four-momentum two-sided289 polynomial frame',flush=True)

    ids=list(source_operators)
    assert ids==exchange['source_field_indices']
    injection=s.SparseMatrix(289,97,{(row,col):1 for col,row in enumerate(ids)})
    f=clean(reverse(F).T*injection)
    rowlift=clean(reverse(Finv).T)
    equal(rowlift,decode(exchange['equation_row_lift']))
    for key,interval in [('canonical_source_map',(9,88)),('independent_dual_source_map',(88,112)),('local_source_compatibility_map',(112,121))]:
        equal(f[interval[0]:interval[1],:],decode(exchange[key]))
    contact=s.zeros(97);response=s.zeros(289,97)
    contact_blocks=auxiliary+[(list(range(9)),M,Minv,['scalar_Ward'])]
    for (indices,block,inv,groups),record in zip(contact_blocks,exchange['source_contact_terms']):
        fmap=f[indices,:]
        kernel=clean(reverse(fmap).T*inv*fmap)
        equal(kernel,decode(record['kernel']));equal(fmap,decode(record['source_map']))
        assert groups==record['groups']
        response+=F[:,indices]*inv*fmap
        contact+=kernel
    response=clean(response);contact=clean(contact)
    equal(response,decode(exchange['contact_field_response']))
    equal(contact,decode(exchange['total_contact_kernel']))
    equal(reverse(contact).T,contact)
    equal(H*response+rowlift[:,9:88]*f[9:88,:]+rowlift[:,88:112]*f[88:112,:]+rowlift[:,112:121]*f[112:121,:],injection)
    equal(H*F[:,9:88],rowlift[:,9:88]*A)
    equal(H*F[:,88:112],rowlift[:,88:112]*Bcomp)
    equal(H*F[:,112:121],s.zeros(289,9))
    equal(F[:,9:88],decode(exchange['canonical_field_lift']))
    equal(F[:,88:112],decode(exchange['independent_dual_field_lift']))
    assert f[112:121,:]!=s.zeros(9,97)
    assert clean(H*response)!=s.zeros(289,97)
    assert clean(H*response+injection-rowlift[:,9:88]*f[9:88,:]-rowlift[:,88:112]*f[88:112,:]-rowlift[:,112:121]*f[112:121,:])!=s.zeros(289,97)
    weak=json.loads((base/'weak-exchange/spatial/receipt.json').read_text())
    weak_sub={s.Symbol('lam'):p[0],**{s.Symbol('k'+str(i)):-s.I*p[i] for i in range(1,4)}}
    for record in weak['generators']:
        lift=decode(record['original_289_field_lift']).subs(weak_sub)
        operator=decode(record['actual_five_field_operator']).subs(weak_sub)
        coordinates=clean(Finv*lift)
        equal(F*coordinates,lift)
        equal(reverse(coordinates).T*normal*coordinates,operator)
        selected=[ids.index(i) for i in record['original_fields']]
        equal(f[112:121,selected],s.zeros(9,5));equal(f[88:112,selected],s.zeros(24,5))
    print('PASS all97 source maps/contact coefficients, all289 forced equations and both actual weak5 consumers',flush=True)

    complement=f[88:112,:]
    assert complement!=s.zeros(24,97)
    assert all(fields[ids[col]]['group']=='Lorentz' for row,col in complement.todok())
    assert not set().union(*(value.free_symbols for value in complement.todok().values()))
    nonzero=[]
    for row in range(24):
        V=clean(sum((complement[row,col]*source_operators[ids[col]] for col in range(97)),s.zeros(252)))
        equal(V,decode(exchange['actual_complementary_source_vertices'][row]))
        equal(kappa*(S*V+V.H*S)/2,s.zeros(252))
        if V!=s.zeros(252):nonzero.append(row)
    assert nonzero
    # Hilbert-Schmidt projection is independent of the candidate's bilinear flattening inverse.
    axial=[clean(kappa*Sspin*g*gamma5) for g in gamma]
    for a in range(4):
        equal(axial[a].H,axial[a]);equal(axial[a],decode(exchange['canonical_axial_bilinear_spin_operators'][a]))
    gram=s.Matrix(4,4,lambda i,j:s.trace(axial[i].H*axial[j]))
    assert gram.det()!=0
    spin_fields=auxiliary[-1][0]
    assert all(fields[i]['group']=='Lorentz' for i in spin_fields)
    spin_map=[]
    reality_controls=[]
    for i in spin_fields:
        V=source_operators[i]
        small=V.extract([0,63,126,189],[0,63,126,189])
        equal(V,s.kronecker_product(small,s.eye(63)))
        real=clean(kappa*(Sspin*small+small.H*Sspin)/2)
        coeff=clean(gram.inv()*s.Matrix([s.trace(a.H*real) for a in axial]))
        equal(sum((coeff[a]*axial[a] for a in range(4)),s.zeros(4)),real)
        spin_map.append(list(coeff))
        if real!=s.zeros(4):
            assert kappa*(Sspin*small+small.H*Sspin)!=real
            reality_controls.append(i)
    spin_map=s.Matrix(spin_map)
    assert spin_map.rank()==4
    equal(spin_map,decode(exchange['canonical_spin_source_axial_map']))
    Domega=auxiliary[-1][1]
    Domega_inv=clean(Domega.inv(method='DM'))
    equal(Domega*Domega_inv,s.eye(24));equal(Domega_inv*Domega,s.eye(24))
    K=clean(spin_map.T*Domega_inv*spin_map)
    equal(K,3*n/8*s.diag(1,-1,-1,-1))
    equal(K,decode(exchange['canonical_spin_contact_kernel']))
    aa=s.Matrix(s.symbols('a0:4',real=True))
    j=spin_map*aa
    induced=-Domega_inv*j
    equal(Domega*induced+j,s.zeros(24,1))
    action=s.expand((induced.T*Domega*induced)[0]/2+(j.T*induced)[0])
    assert s.expand(action-3*n/16*(aa.T*eta*aa)[0])==0
    assert s.expand(action-(j.T*Domega_inv*j)[0]/2)!=0
    print('PASS nonzero independent-dual spin source; all24 canonical real cancellations; actual axial rank4 and3N/16 eta contact',flush=True)

    output={
        'status':'PASS',
        'replay_exact_json_equal':True,
        'source':'positiveSmoothUnifiedSource / Dirac-dual form-native / SpinPair.actual',
        'runtime':'visit10 / tick16 / materialEntry -> visit11 / tick17; unchanged',
        'classification':'subordinate classical source and active tree exchange consumer',
        'primitive_vertex_counts':{'gauge_A':48,'Lorentz':24,'coframe':16,'scalar':70},
        'source_matter_complex_dimension':252,
        'oriented_pairs':[list(pair) for pair in pairs],
        'all16_adjugate_derivatives_from_Jacobi_formula':True,
        'live_coframe_phase_nonzero_directions':coframe_controls,
        'all97_source_operators_and_4656_occupied_cross_entries':True,
        'both_Hessian_orientations_checked':True,
        'independent_complex_linear_dual_pairing':True,
        'gauge_Ward_identities':12,
        'Lorentz_Ward_identities':6,
        'all_momenta':'p0,p1,p2,p3 formal; no axis or momentum specialization',
        'auxiliary_inverses':'computed directly from original289, both sides checked',
        'F_and_inverse_polynomial':True,
        'source_contact_and_forced_row_identity':True,
        'null_source_compatibility_nonzero_and_retained':True,
        'both_actual_weak5_consumers':True,
        'nonzero_raw_complementary_vertices':nonzero,
        'all24_actual_real_complementary_vertices_zero':True,
        'canonical_real_normalization':'sqrt(2)/2 * (S V + V^dagger S)',
        'canonical_axial_source_rank':4,
        'canonical_axial_kernel':'(3*N/8)*diag(1,-1,-1,-1)',
        'canonical_axial_action':'(3*N/16)*[-a0^2+a1^2+a2^2+a3^2]',
        'negative_controls':['omit graded live-coframe phase','omit Yukawa volume derivative',
            'replace independent dual by Hermitian pairing','drop -p transpose',
            'reverse induced-field sign','remove canonical Hermitian factor1/2','reverse spin contact sign'],
        'dynamic_inverse_scope':'A79/B24 inverse interface away from poles and compatible97-source rows',
        'peripheral_61_scalar_exchange_included':False,
        'complete_physical_external_states_or_units_claimed':False,
        'new_Lean_theorem_for_all_computed_matrices_claimed':False}
    (folder/'audit/independent-receipt.json').write_text(json.dumps(output,indent=2)+'\n')


if __name__=='__main__':main()
