#!/usr/bin/env python3
"""Full original independent-dual current: both Fourier legs, primitive contact, CAR readback."""
from functools import lru_cache
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import time
import sympy as s
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]; BASE=HERE.parents[1]
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module
probe=load('fullcurrent_state_response',HERE.parent/'state-response/compute.py')
native=load('fullcurrent_vertices',BASE/'matter-vertices/compute.py')
clean,zero,decode,encode,normalized=probe.clean,probe.zero,probe.decode,probe.encode,probe.normalized
@lru_cache(None)
def scalar(value): return s.radsimp(s.simplify(value))
def assertzero(matrix): zero(normalized(matrix))
def real_parts(matrix):
    return clean(matrix.applyfunc(s.re)),clean(matrix.applyfunc(s.im))
def split_internal(value,bar): return clean((value+bar)/2).col_join(clean((value-bar)/(2*s.I)))
def subset_indices(group,vertices): return [i for i,row in enumerate(vertices) if row['group']==group]
def block_inverse(matrix): return probe.source.source.block_inverse(matrix,probe.source.source.components(matrix))

def main():
    started=time.monotonic()
    probe.source.source.source.source_matrices(ROOT)
    _,vacuum,degrees,hashes=native.source.parse_source(ROOT)
    phase=json.loads((BASE/'full-phase/receipt.json').read_text())
    full=json.loads((HERE.parent/'receipt.json').read_text())
    active=json.loads((BASE/'active-gauge/receipt.json').read_text())
    vertices=json.loads((BASE/'matter-vertices/receipt.json').read_text())
    occ=json.loads((BASE/'occupied-response/receipt.json').read_text())
    for record in [phase,full,vertices,occ]: assert record['source_sha256']==hashes
    for path,digest in active['source_sha256'].items(): assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    n,omega,spin=s.sympify(phase['source_lapse']),s.sympify(phase['source_frequency']),s.sqrt(2)
    p=s.symbols('p0:4',real=True);symbols={str(x):x for x in p};p0=dict.fromkeys(p,0)
    z=(3+s.I)*omega;k=[0,0,omega/(2*n)]
    pv=dict(zip(p,[-s.I*z,*[s.I*x for x in k]]));mv={x:-v for x,v in pv.items()}
    D=decode(vertices['full_stationary_Dirac_operator'],**symbols)
    C=[decode(item) for item in phase['principal_coefficients']];CI=decode(full['time_principal_inverse'])
    gamma=[clean(n*C[0]/s.I)]+[clean(C[j]/s.I) for j in range(1,4)]
    gamma5=clean(s.kronecker_product(s.diag(-1,-1,1,1),s.eye(63)))
    S=clean(gamma[0]*gamma5);Q=decode(phase['phase_generator']);Y=decode(phase['original_Y'])
    frame=decode(occ['occupied_frame']);w=clean(frame*decode(occ['source_prepared']));psi=2*w;chi=clean(spin*psi.H*S)
    K=clean(-s.I*n*spin*S*C[0]);assertzero(K*CI+s.I*n*spin*S)
    original_lower=clean(decode(phase['original_constant_B'])+Y)
    assertzero(D-sum((p[mu]*C[mu] for mu in range(4)),s.SparseMatrix.zeros(252))-
        original_lower+s.I*omega*C[0]*Q)
    assertzero(w.H*w-s.ones(1));assertzero(D.subs(p0)*psi);assertzero(chi*D.subs(p0))
    rows=vertices['primitive_vertices'];V=[decode(row['operator'],**symbols) for row in rows]
    assert len(V)==158
    V0=[clean(value.subs(p0)) for value in V]
    Vp=[clean(value.subs(pv)) for value in V];Vm=[clean(value.subs(mv)) for value in V]
    Vbp=[clean(value.conjugate().subs(pv)) for value in V]
    Vbm=[clean(value.conjugate().subs(mv)) for value in V]
    F=clean(s.SparseMatrix.hstack(*[value*psi for value in V0]))
    Lp=clean(s.SparseMatrix.vstack(*[chi*value for value in Vp]))
    Lm=clean(s.SparseMatrix.vstack(*[chi*value for value in Vm]))
    Lbp=clean(s.SparseMatrix.vstack(*[chi.conjugate()*value for value in Vbp]))
    Lbm=clean(s.SparseMatrix.vstack(*[chi.conjugate()*value for value in Vbm]))
    dp,dm,dbp,dbm=[clean(value) for value in [D.subs(pv),D.subs(mv),D.conjugate().subs(pv),D.conjugate().subs(mv)]]
    Gp,Gm,Gbp,Gbm=[block_inverse(value) for value in [dp,dm,dbp,dbm]]
    I=s.SparseMatrix.eye(252)
    for d,g in zip([dp,dm,dbp,dbm],[Gp,Gm,Gbp,Gbm]): assertzero(d*g-I);assertzero(g*d-I)
    X=normalized(-Gp*F/n);Xb=normalized(-Gbp*F.conjugate()/n)
    Z=normalized(-Lm*Gm/n);Zb=normalized(-Lbm*Gbm/n)
    assertzero(dp*X+F/n);assertzero(dbp*Xb+F.conjugate()/n)
    assertzero(Z*dm+Lm/n);assertzero(Zb*dbm+Lbm/n)
    response=clean(split_internal(X,Xb).col_join(split_internal(Z.T,Zb.T)))
    BM=clean(((Lp+Lbp)/2).row_join(s.I*(Lp-Lbp)/2).row_join((F.T+F.conjugate().T)/2).row_join(s.I*(F.T-F.conjugate().T)/2))
    induced=normalized(BM*response)
    complex_induced=normalized(Lp*X+(Z*F).T)
    barred_induced=normalized(Lbp*Xb+(Zb*F.conjugate()).T)
    assertzero(induced-(complex_induced+barred_induced)/2)
    conjugation=s.diag(s.eye(252),-s.eye(252))
    Dr=probe.occ.realify(D);DRp=clean(Dr.subs(pv));DRm=clean(Dr.subs(mv))
    # Verify every original realified primal/dual row, with the adjoint p sign before substitution.
    MB=clean(s.SparseMatrix.vstack(((Lm+Lbm)/2).T,(s.I*(Lm-Lbm)/2).T,
        ((F.T+F.conjugate().T)/2).T,(s.I*(F.T-F.conjugate().T)/2).T))
    assertzero(n*DRm.T*conjugation*response[504:,:]+MB[:504,:])
    assertzero(n*conjugation*DRp*response[:504,:]+MB[504:,:])
    print('PASS full252 four original inverses, all158 forcing, all1008 independent real matter rows',flush=True)

    # The original 97 active bosonic coordinates embed in all158 actual primitive directions.
    bosons=[i for i,row in enumerate(active['fields']) if row['group'] in ['gauge_A','Lorentz','coframe','scalar_J']]
    matter=[i for i,row in enumerate(active['fields']) if row['group'] in ['primal_H','dual_H']]
    index={(row['group'],tuple(row['coordinate'])):i for i,row in enumerate(rows)}
    bases4=list(itertools.combinations(range(7),4));v=s.Matrix([vacuum.get(word,0) for word in bases4])
    generators=native.source.generators([(0,1,2),(3,4)])
    orbit=[clean(s.SparseMatrix(native.source.exterior_action(matrix,4))*(s.I if imaginary else 1)*v)
        for _,imaginary,matrix in generators]
    E=s.MutableSparseMatrix(158,len(bosons),{})
    for column,field in enumerate(bosons):
        row=active['fields'][field]
        if row['group']!='scalar_J': E[index[row['group'],tuple(row['coordinate'])],column]=1
        else:
            o=orbit[active['J_independent_columns'][row['coordinate'][0]]]
            for a in range(35):
                E[index['scalar',(0,a)],column]=s.re(o[a]);E[index['scalar',(1,a)],column]=s.im(o[a])
    E=clean(E)
    activeR=probe.occ.realify(frame)
    restrict=s.diag(activeR.T,activeR.T)
    response48=normalized(restrict*response*E)
    assertzero(response*E-s.diag(activeR,activeR)*response48)
    equations=clean(probe.occ.field_matrix(active,p).subs(pv))
    assertzero(equations.extract(matter,matter)*response48+equations.extract(matter,bosons))
    assertzero(equations.extract(bosons,matter)*response48-E.T*induced*E)
    embedded=s.MutableSparseMatrix(289,len(bosons),{})
    for (i,j),value in response48.todok().items(): embedded[matter[i],j]=value
    replay=normalized(equations*embedded)
    for i in range(289):
        if i in matter: assertzero(replay[i,:]+equations[i,bosons])
        elif i in bosons: assertzero(replay[i,:]-(E.T*induced*E)[bosons.index(i),:])
        else: assertzero(replay[i,:])
    print('PASS all289 original Hessian rows; full97x97 matter Schur readback',flush=True)

    # Real primitive two-jet at the same held original fields: only coframe enters nonlinearly.
    rho=[]
    for _,imaginary,matrix in generators:
        internal=s.SparseMatrix.diag(*[s.SparseMatrix(native.source.exterior_action(matrix,d))*(s.I if imaginary else 1) for d in degrees])
        rho.append(clean(s.kronecker_product(s.eye(4),internal)))
    spins=[clean(s.kronecker_product(native.GAMMA[a]*native.GAMMA[b]/2,s.eye(63))) for a,b in native.PAIRS]
    gauge=s.Matrix(active['actual_background']['gauge_connection']).applyfunc(s.sympify)
    lorentz=s.Matrix(active['actual_background']['lowered_Lorentz_connection']).applyfunc(s.sympify)
    connections=[clean(sum((gauge[mu,a]*rho[a] for a in range(12)),s.SparseMatrix.zeros(252))+
        sum((lorentz[mu,a]*spins[a] for a in range(6)),s.SparseMatrix.zeros(252))) for mu in range(4)]
    jets=[[clean(s.I*gamma[a]*connections[mu]+(omega*gamma[a]*Q if mu==0 else s.SparseMatrix.zeros(252))) for a in range(4)] for mu in range(4)]
    jetpair=s.Matrix(4,4,lambda mu,a:scalar((chi*jets[mu][a]*psi)[0]))
    e0=s.diag(n,1,1,1);eps,delta=s.symbols('eps delta',real=True)
    coframes=subset_indices('coframe',rows)
    contact=s.MutableSparseMatrix(158,158,{})
    complex_contact=s.MutableSparseMatrix(158,158,{})
    for b in coframes:
        a,nu=rows[b]['coordinate'];direction=s.zeros(4);direction[a,nu]=1
        dAdj=(e0+eps*direction).adjugate().diff(eps).subs(eps,0)
        for c,row in enumerate(rows):
            value=0
            if row['group'] in ['gauge_A','Lorentz']:
                mu,j=row['coordinate'];g=(rho if row['group']=='gauge_A' else spins)[j]
                value=sum((dAdj[mu,a]*(chi*(s.I*gamma[a]*g)*psi)[0] for a in range(4)),s.S.Zero)
            elif row['group']=='coframe':
                a,nu=row['coordinate'];d2=s.zeros(4);d2[a,nu]=1
                second=(e0+eps*direction+delta*d2).adjugate().diff(eps,delta).subs({eps:0,delta:0})
                value=sum((second[mu,a]*jetpair[mu,a] for mu,a in itertools.product(range(4),repeat=2)),s.S.Zero)
            elif row['group']=='scalar':
                dvol=(e0+eps*direction).det().diff(eps).subs(eps,0)
                value=dvol*(chi*(V0[c]/n)*psi)[0]
            value=scalar(value)
            if value:
                complex_contact[b,c]=value;complex_contact[c,b]=value
                contact[b,c]=s.re(value);contact[c,b]=s.re(value)
    contact=clean(contact);complex_contact=clean(complex_contact)
    dirac=s.MutableSparseMatrix(289,289,{})
    for key,value in active['quadratic_action_blocks']['Dirac']:
        left,right=key
        for r,c in [(left,right),(right,left)]:
            jr,jc=active['jet_coordinates'][r],active['jet_coordinates'][c]
            val=s.sympify(value)
            if jr['derivative']>=0: val*=-pv[p[jr['derivative']]]
            if jc['derivative']>=0: val*=pv[p[jc['derivative']]]
            dirac[jr['field'],jc['field']]+=val
    dirac=clean(dirac)
    assertzero(dirac.extract(bosons,bosons)-E.T*contact*E)
    assertzero(dirac.extract(bosons,matter)-equations.extract(bosons,matter))
    assertzero(dirac.extract(matter,bosons)-equations.extract(matter,bosons))
    combined=normalized(induced+contact)
    actual_embedding=s.SparseMatrix(embedded)
    for j,i in enumerate(bosons): actual_embedding[i,j]=1
    returned=normalized(dirac*actual_embedding)
    for i in range(289):
        if i in bosons: assertzero(returned[i,:]-(E.T*combined*E)[bosons.index(i),:])
        else: assertzero(returned[i,:])
    print('PASS primitive coframe/gauge/Lorentz/scalar second contacts and original complete Dirac Hessian',flush=True)

    # The original p0 acts on the incoming primal to its right. Resolving that
    # derivative generates two local contacts, one on each independent leg.
    Hplus=clean(-s.I*CI*(D.subs(p0)+sum((s.I*k[j]*C[j+1] for j in range(3)),s.SparseMatrix.zeros(252))))
    Hminus=clean(-s.I*CI*(D.subs(p0)-sum((s.I*k[j]*C[j+1] for j in range(3)),s.SparseMatrix.zeros(252))))
    Pjets=[clean(value.diff(p[0])) for value in V]
    shellp=[clean(V0[b]-s.I*Pjets[b]*Hplus+sum((s.I*k[j]*V[b].diff(p[j+1]) for j in range(3)),s.SparseMatrix.zeros(252))) for b in range(158)]
    shellm=[clean(V0[b]-s.I*Pjets[b]*Hminus-sum((s.I*k[j]*V[b].diff(p[j+1]) for j in range(3)),s.SparseMatrix.zeros(252))) for b in range(158)]
    for b in range(158):
        assertzero(Vp[b]*Gp-shellp[b]*Gp-Pjets[b]*CI)
        assertzero(Vm[b]*Gm-shellm[b]*Gm-Pjets[b]*CI)
    leftshellp=clean(s.SparseMatrix.vstack(*[chi*value for value in shellp]))
    leftshellm=clean(s.SparseMatrix.vstack(*[chi*value for value in shellm]))
    principal_rows=clean(s.SparseMatrix.vstack(*[chi*value for value in Pjets]))
    reader_contact=normalized(-principal_rows*CI*F/n)
    dual_contact=clean(reader_contact.T)
    shell_induced=normalized(leftshellp*X-(leftshellm*Gm*F).T/n)
    assertzero(complex_induced-shell_induced-reader_contact-dual_contact)
    # Independent momentum is varied with the same densitized C0, including
    # the local conversion back to chi. K' is independently tied to the
    # already generated primitive coframe family.
    momentum_response=clean(-s.I*(n*Z*C[0]+principal_rows))
    momentum_dual=clean(s.I*momentum_response*CI/n)
    assertzero(Z-momentum_dual+principal_rows*CI/n)
    coframe_receipt=json.loads((HERE.parent/'coframe-response/receipt.json').read_text())
    dK=[]
    for b in range(158):
        entry=clean(-s.I*spin*S*Pjets[b]);dK.append(entry)
        if rows[b]['group']=='coframe':
            old=next(row for row in coframe_receipt['coefficients'] if row['coordinate']==rows[b]['coordinate'])
            assertzero(entry-decode(old['canonical_initial_weight_first_variation']))
        else: assertzero(entry)
    weight_rows=clean(s.SparseMatrix.vstack(*[w.H*value for value in dK]))
    density_force_columns=clean(s.SparseMatrix.hstack(*[(-s.I/n)*CI*value*w for value in V0]))
    assertzero(4*(weight_rows*density_force_columns).T-dual_contact)
    assert normalized(reader_contact+dual_contact).todok()
    print('PASS both true p0 contacts, independent momentum conversion and same primitive K-prime',flush=True)

    # All transfer words are evaluated on one actual prepared state at incoming0.
    # K stays at the boundary, with the raw C0 inverse immediately on its right.
    prepared={(i,):value for i,value in enumerate(w) if value}
    Ktransfer=probe.transfer_block(K,0,0)
    Gptransfer=probe.transfer_block(Gp,1,1);Gmtransfer=probe.transfer_block(Gm,2,2)
    forceplus=[probe.transfer_block(value,1,0) for value in V0]
    forceminus=[probe.transfer_block(value,2,0) for value in V0]
    plus_states=[];minus_states=[]
    for positive,negative in zip(forceplus,forceminus):
        plus_states.append(probe.number_action(Gptransfer,probe.number_action(positive,prepared)))
        minus_states.append(probe.number_action(Gmtransfer,probe.number_action(negative,prepared)))
    leftplus=[probe.transfer_block(clean(CI*value),0,1) for value in Vp]
    leftminus=[probe.transfer_block(clean(CI*value),0,2) for value in Vm]
    carplus=s.MutableSparseMatrix(158,158,{});carminus=s.MutableSparseMatrix(158,158,{})
    for b in range(158):
        for c in range(158):
            first=probe.read(prepared,probe.number_action(Ktransfer,probe.number_action(leftplus[b],plus_states[c])))
            second=probe.read(prepared,probe.number_action(Ktransfer,probe.number_action(leftminus[c],minus_states[b])))
            if first: carplus[b,c]=first
            if second: carminus[b,c]=second
    car_complex=normalized((-4*s.I/n**2)*(carplus+carminus))
    assertzero(car_complex-complex_induced)
    assert normalized(K*Gp-Gp*K).todok()
    # Separate internal conjugate algebra is required before external Fourier substitution.
    # It is not complex conjugation of the already continued positive-frequency value.
    scalarids=subset_indices('scalar',rows)
    assertzero(induced[scalarids,:]);assertzero(induced[:,scalarids]);assertzero(contact[scalarids,:]);assertzero(contact[:,scalarids])
    assert X[:,scalarids].todok()
    assert normalized(induced-induced.conjugate()).todok()
    contact_counts={group:sum(1 for (b,c) in contact.todok() if rows[b]['group']==group) for group in ['gauge_A','Lorentz','coframe','scalar']}
    result={'scope':'ALL158_ORIGINAL_INDEPENDENT_DUAL_CURRENT_AND_ORIGINAL289_MATTER_SCHUR',
        'source_sha256':hashes,'background_source_sha256':active['source_sha256'],
        'energy':str(z),'spatial_momentum':list(map(str,k)),
        'source_preparation':'actual.matter(0)/2; common incoming0 only','original_physical_time':True,
        'frequency_representation':'original FullPhase co-rotation, p0=-i z; p and -p preserve their source order',
        'vertices':[{'group':row['group'],'coordinate':row['coordinate']} for row in rows],
        'full252_original_inverses':4,'full_real_matter_rows':1008,'primitive_channels':158,
        'full158_complex_raw_induced':encode(complex_induced),'full158_real_field_induced':encode(induced),
        'primitive_complex_contact':encode(complex_contact),'primitive_real_contact':encode(contact),
        'on_shell_two_leg_complex_response':encode(shell_induced),
        'primal_reader_time_contact':encode(reader_contact),'independent_dual_time_contact':encode(dual_contact),
        'all16_boundary_variations_match_original_primitive_family':True,
        'dual_time_contact_equals_original_boundary_variation_CAR':True,
        'original_independent_momentum_variation_recovered':True,
        'full158_total_real_current_response':encode(combined),
        'original289_boson_indices':bosons,'original289_matter_indices':matter,
        'original97_inclusion':encode(E),'original97_matter_response':encode(response48),
        'original97_induced_current':encode(normalized(E.T*induced*E)),
        'original97_full_Dirac_current':encode(normalized(E.T*combined*E)),
        'original289_all_rows_replayed':True,'original289_Dirac_second_jet_replayed':True,
        'complete_CAR_ordered_products':2*158**2,'CAR_operators_per_leg':8,'common_transfer_carrier':756,
        'boundary_K_order':'K C0^-1 V_b(p) D(p)^-1 V_c(0); K C0^-1 V_c(-p) D(-p)^-1 V_b(0)',
        'source_CAR_coefficient':str(-4*s.I/n**2),'scalar_raw_current_all_rows_columns_zero':True,
        'scalar_open_primal_nnz':len(X[:,scalarids].todok()),'contact_nonzero_rows_by_group':contact_counts,
        'internal_realification_before_external_Fourier':True,'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ['scope','complete_CAR_ordered_products','scalar_open_primal_nnz','contact_nonzero_rows_by_group','elapsed_seconds']},indent=2),flush=True)
if __name__=='__main__':main()
