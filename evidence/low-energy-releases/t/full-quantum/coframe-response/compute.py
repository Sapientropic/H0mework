#!/usr/bin/env python3
"""Actual primitive coframes generate temporal forces, boundary weights and contacts."""
from functools import lru_cache
import importlib.util
import hashlib
import itertools
import json
from pathlib import Path
import time
import sympy as s
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1];ROOT=HERE.parents[4]
spec=importlib.util.spec_from_file_location('state_response',HERE.parent/'state-response/compute.py')
probe=importlib.util.module_from_spec(spec);spec.loader.exec_module(probe)
specv=importlib.util.spec_from_file_location('native_vertices',BASE/'matter-vertices/compute.py')
native=importlib.util.module_from_spec(specv);specv.loader.exec_module(native)
clean,zero,decode,encode,normalized=probe.clean,probe.zero,probe.decode,probe.encode,probe.normalized

def main():
    started=time.monotonic()
    probe.source.source.source.source_matrices(ROOT)
    _,_,degrees,hashes=native.source.parse_source(ROOT)
    phase=json.loads((BASE/'full-phase/receipt.json').read_text())
    full=json.loads((HERE.parent/'receipt.json').read_text())
    active=json.loads((BASE/'active-gauge/receipt.json').read_text())
    vertices=json.loads((BASE/'matter-vertices/receipt.json').read_text())
    triangle=json.loads((HERE.parent/'triangular/receipt.json').read_text())
    occupied=json.loads((BASE/'occupied-response/receipt.json').read_text())
    assert all(record['source_sha256']==hashes for record in [phase,full,vertices,triangle,occupied])
    assert all(active['source_sha256'][key]==value for key,value in hashes.items() if key in active['source_sha256'])
    for path,digest in active['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest, path
    n,omega=s.sympify(phase['source_lapse']),s.sympify(phase['source_frequency'])
    gamma=[s.SparseMatrix(g) for g in native.GAMMA]
    Gamma=[clean(s.kronecker_product(g,s.eye(63))) for g in gamma]
    S=clean(Gamma[0]*s.kronecker_product(s.diag(-1,-1,1,1),s.eye(63)))
    Q=decode(phase['phase_generator']);Y=decode(phase['original_Y'])
    C=[decode(value) for value in phase['principal_coefficients']]
    CI=decode(full['time_principal_inverse']);L=clean(decode(phase['original_constant_B'])+Y)
    H=decode(full['original_H_full']);Hco=clean(H-omega*Q)
    rho=[]
    for _,imaginary,matrix in native.source.generators([(0,1,2),(3,4)]):
        internal=s.SparseMatrix.diag(*[s.SparseMatrix(native.source.exterior_action(matrix,d))*(s.I if imaginary else 1) for d in degrees])
        rho.append(clean(s.kronecker_product(s.eye(4),internal)))
    spins=[clean(s.kronecker_product(gamma[a]*gamma[b]/2,s.eye(63))) for a,b in native.PAIRS]
    gauge=s.Matrix(active['actual_background']['gauge_connection']).applyfunc(s.sympify)
    lorentz=s.Matrix(active['actual_background']['lowered_Lorentz_connection']).applyfunc(s.sympify)
    connections=[clean(sum((gauge[mu,a]*rho[a] for a in range(12)),s.SparseMatrix.zeros(252))+
        sum((lorentz[mu,a]*spins[a] for a in range(6)),s.SparseMatrix.zeros(252))) for mu in range(4)]
    zero(sum((C[mu]*connections[mu] for mu in range(4)),s.SparseMatrix.zeros(252))+Y-L)
    w=clean(decode(occupied['occupied_frame'])*decode(occupied['source_prepared']))
    psi=2*w;chi=clean(s.sqrt(2)*psi.H*S);prepared={(i,):value for i,value in enumerate(w) if value}
    K=clean(-s.I*n*s.sqrt(2)*S*C[0]);zero(K-s.sqrt(2)*s.kronecker_product(s.diag(-1,-1,1,1),s.eye(63)))
    zero(-s.I*n*chi*C[0]-psi.H*K)
    p=s.symbols('p0:4',real=True);k=s.symbols('k1:4',real=True);eps=s.symbols('epsilon',real=True)
    e0=s.diag(n,1,1,1);einverse=e0.inv();zero_p=dict.fromkeys(p,0)
    symbols={str(value):value for value in p}
    fullH=clean(H+sum((-n*Gamma[0]*C[j+1]/s.I*k[j] for j in range(3)),s.SparseMatrix.zeros(252)))
    fullL=clean(L+sum((s.I*k[j]*C[j+1] for j in range(3)),s.SparseMatrix.zeros(252)))
    case=next(case for case in triangle['cases'] if case['momentum']==['0','0','0'])
    assert all(term['time_power']==0 for term in case['time']['coefficients'])
    t=s.pi/(4*omega)
    def evolution(time):
        return normalized(sum((s.expand_complex(s.exp(-s.I*s.sympify(term['rate'])*time))*decode(term['matrix'])
            for term in case['time']['coefficients']),s.SparseMatrix.zeros(252)))
    U,Ui=evolution(t),evolution(-t);psi_t=clean(U*psi);chi_t=clean(chi*C[0]*Ui*CI)
    assert normalized(K*Ui-Ui*K).todok()
    coefficients=[];symbol_vertices=[];contacts=[];current_words=[]
    raw_operator=clean(sum((p[mu]*C[mu] for mu in range(4)),s.SparseMatrix.zeros(252))+L)
    all_vertices=[row for row in vertices['primitive_vertices'] if row['group']=='coframe']
    for row in all_vertices:
        a,b=row['coordinate'];direction=s.zeros(4);direction[a,b]=1
        curve=e0+eps*direction
        delta_inverse=clean(curve.inv().diff(eps).subs(eps,0))
        zero(delta_inverse+einverse*direction*einverse)
        dC=[clean(s.I*sum((delta_inverse[mu,c]*Gamma[c] for c in range(4)),s.SparseMatrix.zeros(252))) for mu in range(4)]
        dL=clean(sum((dC[mu]*connections[mu] for mu in range(4)),s.SparseMatrix.zeros(252)))
        dvol=s.diff(curve.det(),eps).subs(eps,0)
        C0curve=s.I*sum((curve.inv()[0,c]*gamma[c] for c in range(4)),s.zeros(4))
        dCI=clean(s.kronecker_product(C0curve.inv().diff(eps).subs(eps,0),s.eye(63)))
        zero(dCI+CI*dC[0]*CI)
        dLk=clean(dL+sum((s.I*k[j]*dC[j+1] for j in range(3)),s.SparseMatrix.zeros(252)))
        T=clean(-s.I*(dCI*fullL+CI*dLk))
        zero(T+CI*dC[0]*fullH+s.I*CI*dLk)
        on_shell=clean(dLk-s.I*dC[0]*fullH)
        zero(T+s.I*CI*on_shell)
        dP=clean(dvol*C[0]+n*dC[0]);dLd=clean(dvol*fullL+n*dLk)
        V=decode(row['operator'],**symbols)
        native_vertex=clean(dvol*raw_operator+n*(sum((p[mu]*dC[mu] for mu in range(4)),s.SparseMatrix.zeros(252))+dL)-s.I*omega*dP*Q)
        zero(native_vertex-V)
        on_shell_density=clean(V.subs(zero_p)+V.diff(p[0])*(-s.I*(fullH-omega*Q))+
            sum((s.I*k[j]*V.diff(p[j+1]) for j in range(3)),s.SparseMatrix.zeros(252)))
        zero(Gamma[0]*on_shell_density-T)
        dK=clean(-s.I*s.sqrt(2)*S*dP)
        direct_weight=-s.I*s.sqrt(2)*curve.det()*s.kronecker_product(gamma[0]*s.diag(-1,-1,1,1)*C0curve,s.eye(63))
        zero(clean(direct_weight.diff(eps).subs(eps,0))-dK)
        T0=clean(T.subs(dict.fromkeys(k,0)));A0=clean(on_shell.subs(dict.fromkeys(k,0)))
        word_matrix=normalized(Ui*T0*U);current_words.append(word_matrix)
        source_word=probe.read(prepared,probe.number_action(K,probe.number_action(word_matrix,prepared)))
        raw=normalized(n*chi_t*A0*psi_t)[0]
        assert probe.canonical(raw+4*source_word)==0
        coefficients.append({'coordinate':[a,b],'hamiltonian_first_variation':encode(T),
            'raw_temporal_principal_first_variation':encode(dC[0]),'densitized_temporal_first_variation':encode(dP),
            'canonical_initial_weight_first_variation':encode(dK),'raw_complex_current_at_physical_time':str(raw)})
        symbol_vertices.append((dC[0],dLk,dP,dLd,on_shell))
    print('PASS all16 raw coframes -> dC0, dH(k), original158 vertices and initial -i Vol chi C0',flush=True)
    for label,kv in [('zero',[0,0,0]),('spatial',[0,0,omega/(2*n)])]:
        values=dict(zip(k,kv));Hv=clean(fullH.subs(values));z=(3+s.I)*omega
        R=probe.source.source.block_inverse(z*s.SparseMatrix.eye(252)-Hv,probe.source.source.components(Hv))
        G=clean(s.I*R*CI);zero(normalized((-s.I*z*C[0]+fullL.subs(values))*G-s.SparseMatrix.eye(252)))
        counts={'raw_nonzero':0,'density_nonzero':0}
        for dC0,dLk,dP,dLd,on_shell in symbol_vertices:
            dLvalue=clean(dLk.subs(values));raw_vertex=clean(dLvalue-s.I*z*dC0)
            raw_contact=clean(dC0*CI)
            zero(normalized(raw_vertex*G-on_shell.subs(values)*G-raw_contact))
            density_vertex=clean(dLd.subs(values)-s.I*z*dP)
            density_on=clean(dLd.subs(values)-s.I*dP*Hv)
            density_contact=clean(dP*CI/n)
            zero(normalized(density_vertex*(G/n)-density_on*(G/n)-density_contact))
            counts['raw_nonzero']+=bool(raw_contact.todok());counts['density_nonzero']+=bool(density_contact.todok())
        assert counts=={'raw_nonzero':4,'density_nonzero':6}
        contacts.append({'label':label,'momentum':list(map(str,kv)),'spectral_parameter':str(z),**counts,
            'all16_true_Dirac_Green_contacts_match':True})
        print('PASS',label,'positive-damped full252 Dirac Green; all16 derivative/current contacts',flush=True)
    result={'scope':'ORIGINAL_COFRAME_TEMPORAL_VARIATION_BOUNDARY_MOMENTUM_AND_DIRAC_CONTACT',
        'source_sha256':hashes,'background_source_sha256':active['source_sha256'],'momentum_symbols':list(map(str,k)),'source_lapse':str(n),'source_frequency':str(omega),
        'all16_Hamiltonian_variations_from_actual_inverse_coframe':True,
        'force_formula':'dH=-C0^-1 dC0 H-i C0^-1 dL; right action retained',
        'original_densitized_vertices_all16_recovered':True,'source_occupation':'w=actual.matter(0)/2',
        'boundary_weight':'K(C)=-i Vol(C) spinScale S C0(C); actual K=spinScale gamma5',
        'original_momentum':'pi0=-i Vol chi0 C0=psi0† K(C)',
        'source_matter_amplitude_squared':4,'physical_time':str(t),
        'all16_raw_independent_dual_current_equals_weighted_full_CAR':True,
        'boundary_K_cannot_be_commuted_through_full_U':True,
        'coefficients':coefficients,'contacts':contacts,'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({key:result[key] for key in ['scope','all16_Hamiltonian_variations_from_actual_inverse_coframe',
        'all16_raw_independent_dual_current_equals_weighted_full_CAR','elapsed_seconds']},indent=2))

if __name__=='__main__':main()
