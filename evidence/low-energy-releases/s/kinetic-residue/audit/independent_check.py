#!/usr/bin/env python3
"""Independent action kernel, signed resolvent and normalized source audit."""
import argparse
from collections import Counter
import json
from pathlib import Path
import re
import sympy as s


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True)
    root=parser.parse_args().root.resolve();base=root/'Verification/physics/low-energy-phenomenology';audit=base/'kinetic-residue/audit'
    frozen=json.loads((base/'kinetic-residue/receipt.json').read_text())
    assert frozen==json.loads(Path('/tmp/kinetic-residue-audit-replay.json').read_text())
    phase=json.loads((base/'full-phase/receipt.json').read_text());modes=json.loads((base/'matter-modes/source.json').read_text())
    spectrum=json.loads((base/'matter-modes/spectral.json').read_text());vertices=json.loads((base/'matter-vertices/receipt.json').read_text())
    exchange=json.loads((base/'matter-vertices/exchange.json').read_text());external=json.loads((base/'onshell-sources/receipt.json').read_text())
    original=json.loads((base/'active-gauge/receipt.json').read_text())
    assert frozen['source_sha256']==phase['source_sha256']==modes['source_sha256']==vertices['source_sha256']
    E=s.Symbol('E',real=True);k=s.symbols('k1:4',real=True);p=s.symbols('p0:4')
    nx,ny,nz,r,t,x=s.symbols('nx ny nz r t x',real=True)
    symbols={str(value):value for value in (E,*k,*p,nx,ny,nz,r,t,x)}
    def decode(record):return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(value,locals=symbols) for i,j,value in record['entries']})
    def clean(matrix):return s.SparseMatrix(matrix).applyfunc(s.expand)
    def equal(left,right):assert all(s.simplify(value)==0 for value in s.SparseMatrix(left-right).todok().values())
    eye=lambda n:s.eye(n,cls=s.SparseMatrix)
    text=(root/'Lean/SaturationMonoid/PhysicsCore/DiracCliffordRepresentation.lean').read_text()
    gamma=[]
    for name in ('Zero','One','Two','Three'):
        literal=re.search(r'def diracGamma'+name+r'\s*:.*?:=\s*!!\[(.*?)\]',text,re.S).group(1)
        gamma.append(s.SparseMatrix([[s.sympify(v.strip().replace('Complex.I','I')) for v in row.split(',')] for row in literal.split(';')]))
    diagonal=re.search(r'def diracGammaFive.*?Matrix.diagonal !\[(.*?)\]',text,re.S).group(1)
    g5=s.diag(*[s.sympify(value.strip()) for value in diagonal.split(',')])
    gamma5=s.kronecker_product(g5,eye(63));S=s.kronecker_product(gamma[0]*g5,eye(63))
    n=s.sympify(phase['source_lapse']);omega=s.sympify(phase['source_frequency']);spin=s.sqrt(2);theta=2**s.Rational(-1,4)
    assert s.sympify(original['actual_background']['dual_multiple'])==spin
    assert s.simplify(s.sympify(frozen['right_normalization_factor'])-theta)==0
    assert theta>0 and s.simplify(theta**2-1/spin)==0 and theta**4==s.Rational(1,2)
    C=list(map(decode,phase['principal_coefficients']));B=decode(phase['original_constant_B'])+decode(phase['original_Y'])
    Q=decode(phase['phase_generator']);G=spin*gamma5;BQ=clean(G*Q)
    equal(S*s.kronecker_product(gamma[0],eye(63)),gamma5);equal(S*S,eye(252))
    equal(n*spin*S*C[0],s.I*G)
    H0=decode(modes['original_H_constant']);Hj=list(map(decode,modes['original_H_spatial']));scale=n*s.sqrt(2)
    H=clean(scale*(H0+sum((k[j]*Hj[j]/s.sqrt(2) for j in range(3)),s.zeros(252,cls=s.SparseMatrix))))
    D=clean(-s.I*E*C[0]+B+sum((s.I*k[j]*C[j+1] for j in range(3)),s.zeros(252,cls=s.SparseMatrix)))
    kernel=clean(n*spin*S*D)
    equal(kernel,G*(E*eye(252)-H))
    equal(decode(frozen['kinetic_pair_matrix']),G);equal(decode(frozen['original_time_principal']),s.I*G)
    F=decode(modes['source_isometry']);P=decode(modes['free_projection'])
    equal(F.H*F,eye(216));equal(F*F.H,P)
    chirality=clean(F.H*gamma5*F);charge=clean(F.H*Q*F)
    signs=[chirality[i,i] for i in range(216)];charges=[charge[i,i] for i in range(216)]
    equal(chirality,s.diag(*signs));equal(charge,s.diag(*charges))
    equal(gamma5*F,F*chirality);equal(Q*F,F*charge)
    assert Counter(signs)=={-1:106,1:110}
    weights=[a*b for a,b in zip(signs,charges)];assert Counter(weights)=={1:202,3:14}
    equal(F.H*G*F,decode(frozen['free_kinetic_pair']));equal(F.H*BQ*F,decode(frozen['free_Noether_phase_charge_gram']))
    equal(BQ,decode(frozen['Noether_phase_charge_matrix']))
    assert all(value>0 for value in weights)
    right=[i for i in range(216) if signs[i]==1];left=[i for i in range(216) if signs[i]==-1]
    R=theta*F[:,right];equal(R,decode(frozen['positive_normalized_frame']))
    equal(R.H*G*R,eye(110));equal(R*R.H,F[:,right]*F[:,right].H/spin)
    # This is a separate positive pairing. It does not replace the signed G.
    FQ=F*s.diag(*[1/s.sqrt(spin*value) for value in weights],cls=s.SparseMatrix)
    RQ=clean(FQ.H*BQ)
    equal(FQ,decode(frozen['Noether_isometric_frame']));equal(RQ,decode(frozen['Noether_full_readback']))
    equal(RQ*FQ,eye(216));equal(FQ*RQ,P)
    equal(FQ.H*G*FQ,s.diag(*[1/value for value in charges]))
    assert FQ.H*G*FQ!=eye(216)
    for h,saved in zip([H0]+Hj,frozen['Noether_positive_pullback_H_coefficients']):
        equal((h*G-G*h)*P,s.zeros(252));equal((h*BQ-BQ*h)*P,s.zeros(252))
        small=clean(RQ*h*FQ);equal(small.H,small);equal(h*FQ,FQ*small);equal(small,decode(saved))
    equal(n*spin*S*decode(phase['generated_live_time_shift']),omega*BQ)
    # Original H consists of all four spin copies of the same three Lambda2 modes.
    b2=list(__import__('itertools').combinations(range(7),2))
    indices=[j*63+7+b2.index((color,5)) for j in range(4) for color in range(3)]
    activeH=s.SparseMatrix(252,252,{(i,i):1 for i in indices})
    equal(BQ*activeH,spin*S*S*activeH)
    for block in modes['blocks']:
        start=block['first_column'];frame=F[:,start:start+block['dimension']];chi=block['chirality']
        assert signs[start:start+block['dimension']]==[chi]*block['dimension']
        h0=decode(modes[block['kind']+'_constant']);hj=list(map(decode,modes[block['kind']+'_spatial']))
        expected=spin*chi*(E*eye(frame.cols)-scale*chi*(h0+sum((k[j]*hj[j]/s.sqrt(2) for j in range(3)),s.zeros(frame.cols))))
        equal(frame.H*kernel*frame,expected)
    assert len(modes['blocks'])==79
    print('PASS original full252 action kernel, all79 source copies, signed216 Gram and separate positive Q interface',flush=True)

    real_hessian_checks=0
    for kind in ('singlet','doublet'):
        for chi in (-1,1):
            block=next(item for item in modes['blocks'] if item['kind']==kind and item['chirality']==chi)
            start=block['first_column'];frame=F[:,start:start+block['dimension']]
            K=clean(frame.H*kernel*frame);equal(K.H,K)
            size=K.rows;coords=s.symbols('z0:'+str(2*size),real=True)
            u=s.Matrix([coords[i]+s.I*coords[size+i] for i in range(size)])
            density=s.expand((u.H*K*u)[0]);assert s.simplify(s.im(density))==0
            # Read quadratic monomial coefficients rather than calling Hessian.
            hessian=s.Matrix(2*size,2*size,lambda i,j:
                2*density.coeff(coords[i],2) if i==j else density.coeff(coords[i],1).coeff(coords[j],1))
            real_part=K.applyfunc(s.re);imag_part=K.applyfunc(s.im)
            realify=real_part.row_join(-imag_part).col_join(imag_part.row_join(real_part))
            equal(hessian,2*realify);assert hessian!=realify
            real_hessian_checks+=1
    relations=s.groebner([nx*nx+ny*ny+nz*nz-1,t*t-r*r-s.Rational(9,25)],t,nz,ny,nx,r,x,domain=s.QQ_I)
    def spectral_zero(matrix):
        for value in s.SparseMatrix(matrix).todok().values():
            num=s.together(value).as_numer_denom()[0]
            assert relations.reduce(s.expand(num))[1]==0
    branches=0
    for kind,family in spectrum['universal_families'].items():
        h=decode(family['hamiltonian'])
        for chi in (-1,1):
            A=chi*x*eye(h.rows)-h;inverse=s.zeros(h.rows)
            for branch in family['projectors']:
                Pi=decode(branch['matrix']);e=s.sympify(branch['scaled_frequency'],locals=symbols)
                spectral_zero(A*Pi-chi*(x-chi*e)*Pi)
                inverse+=chi*Pi/(x-chi*e)
                equal((spin*chi)*((chi/spin)*Pi),Pi)
                branches+=1
            spectral_zero(A*inverse-eye(h.rows));spectral_zero(inverse*A-eye(h.rows))
            origin=chi*x*eye(h.rows)-decode(modes[kind+'_constant']);origin_inverse=s.zeros(h.rows)
            for branch in spectrum['origin_resolution'][kind]:
                Pi=decode(branch['matrix']);e=s.sympify(branch['scaled_frequency'])
                equal(origin*Pi,chi*(x-chi*e)*Pi)
                origin_inverse+=chi*Pi/(x-chi*e);branches+=1
            equal(origin*origin_inverse,eye(h.rows));equal(origin_inverse*origin,eye(h.rows))
    assert branches==18
    negative=F[:,left[0]];left_energy=-3*scale/2
    negative_kernel=s.simplify((negative.H*kernel.subs(dict.fromkeys(k,0))*negative)[0])
    assert s.simplify(negative_kernel+spin*(E-left_energy))==0
    assert s.limit((E-left_energy)/negative_kernel,E,left_energy)==-1/spin
    equal(decode(frozen['actual_left_line_pole']['source_vector']),negative)
    assert s.simplify((theta*negative).H*G*(theta*negative))[0]==-1
    assert s.simplify((theta*negative).H*BQ*(theta*negative))[0]==1
    print('PASS all18 signed residue branches and independently assembled two-sided action inverses, real Hessian factor2 and negative source line',flush=True)

    stationary=decode(vertices['full_stationary_Dirac_operator']);normalized=[]
    for old,record in zip(external['legs'],frozen['normalized_original_on_shell_legs']):
        u=decode(old['vector']);momentum=decode(old['momentum']);energy=s.sympify(old['frequency'])
        nu=theta*u;equal(nu,decode(record['normalized_vector']))
        equal(nu.H*G*nu,s.ones(1));equal(nu.H*BQ*nu,s.ones(1))
        assert s.simplify((nu.H*nu)[0]-1/spin)==0
        equal(nu*nu.H,u*u.H/spin)
        value=kernel.subs(dict(zip(k,momentum)))
        ku=s.simplify((u.H*value*u)[0]);kn=s.simplify((nu.H*value*nu)[0])
        assert s.simplify(ku-spin*(E-energy))==0 and s.simplify(kn-(E-energy))==0
        assert s.limit((E-energy)/ku,E,energy)==1/spin
        derivative=decode(old['derivative']);at=stationary.subs(dict(zip(p,derivative)))
        equal(at*nu,s.zeros(252,1));equal(nu.H*S*at,s.zeros(1,252))
        normalized.append((nu,derivative))
    operators={row['field']:decode(row['operator']) for row in vertices['active_289_bosonic_source_operators']}
    ordering=exchange['source_field_indices']
    def current(outgoing,incoming):
        out,po=outgoing;inside,pi=incoming
        return s.Matrix([s.simplify(spin*(out.H*(S*operators[field].subs(dict(zip(p,pi)))+
            operators[field].subs(dict(zip(p,po))).H*S)*inside)[0]/2) for field in ordering])
    j1=current(normalized[1],normalized[0]);j2=current(normalized[3],normalized[2])
    equal(j1,decode(frozen['actual_normalized_first_current']));equal(j2,decode(frozen['actual_normalized_second_current']))
    equal(j1,decode(external['first_transition_current'])/spin);equal(j2,decode(external['second_transition_current'])/spin)
    equal(current(normalized[3],normalized[0]),s.zeros(97,1));equal(current(normalized[1],normalized[2]),s.zeros(97,1))
    transfer=decode(external['opposite_transfer']);sub=dict(zip(p,transfer));minus=dict(zip(p,-transfer))
    full=s.MutableSparseMatrix(289,289,{})
    for row,col,powers,value in original['Fourier_Jacobi_entries']:
        full[row,col]+=s.sympify(value)*s.prod(transfer[j]**degree for j,degree in enumerate(powers))
    injection=s.SparseMatrix(289,97,{(field,col):1 for col,field in enumerate(ordering)})
    f=decode(exchange['canonical_source_map']);f1=clean(f.subs(sub)*j1);f2=clean(f.subs(minus)*j2)
    response=decode(external['canonical_dynamic_response'])/spin
    equal(decode(exchange['canonical_operator']).subs(sub)*response,f1)
    field_response=decode(exchange['contact_field_response']).subs(sub)*j1+decode(exchange['canonical_field_lift']).subs(sub)*response
    equal(full*field_response,injection*j1);equal(field_response,decode(frozen['actual_normalized_289_green_response']))
    dynamic=s.simplify((f2.T*response)[0]);contact=s.simplify((j2.T*decode(exchange['total_contact_kernel']).subs(sub)*j1)[0])
    tree=s.simplify(-dynamic-contact)
    for new,old,value in (('normalized_dynamic_bilinear','dynamic_bilinear',dynamic),
                          ('normalized_local_bilinear','local_bilinear',contact),
                          ('normalized_elastic_direct_tree_kernel','elastic_direct_tree_kernel',tree)):
        assert s.simplify(value-s.sympify(frozen[new]))==0
        assert s.simplify(value-s.sympify(external[old])/2)==0
    assert tree!=s.sympify(external['elastic_direct_tree_kernel'])
    receipt={'status':'PASS','replay_equal':True,'all_source_copies':79,'signed_projector_branches':branches,
        'generic_and_origin_action_resolvents_verified_both_sides':True,
        'kinetic_free_signature':{'negative':106,'positive':110},'phase_charge_positive_weights':{'s':202,'3s':14},
        'real_Hessian_monomial_checks':real_hessian_checks,'real_Hessian_factor':2,
        'positive_charge_frame_readback_both_sides':True,'all_H_coefficients_Hermitian_and_intertwining':True,
        'kinetic_Gram_in_positive_charge_frame':'diag(1/Qcharge): -1[106], +1[96], +1/3[14]',
        'four_actual_legs_action_unit_pole_limit':'1/s','original_left_line_pole_limit':'-1/s',
        'old_Fock_one_particle_pair_factor':'1/s','actual_97_sources_factor':'1/s',
        'original_289_normalized_source_rows':289,'dynamic_contact_and_tree_factor':'1/2',
        'normalized_contact':str(contact),'normalized_tree':str(tree),
        'negative_controls':['unsigned_left_residue','real_Hessian_without_factor2','old_Fock_pair_renamed_unit',
            'kinetic_pair_replaced_by_positive_phase_charge','unchanged_four_leg_tree'],
        'full_quantum_LSZ_or_global_no_go_claimed':False}
    (audit/'independent-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('PASS actual action-normalized four legs, all97 original sources, full289 readback and separate dynamic/contact/tree factor1/2',flush=True)


if __name__=='__main__':main()
