#!/usr/bin/env python3
"""Source-P connected words and incoming-zero / intermediate +/-k response.

The state is the actual normalized source.  Momentum labels are common finite
transfer channels, not independent vacua or a continuum occupation prescription.
"""
from __future__ import annotations
from functools import lru_cache
import importlib.util
import itertools
import json
from pathlib import Path
import time
import sympy as s

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
BASE=HERE.parents[1]
spec=importlib.util.spec_from_file_location('state_source',HERE.parent/'state-green/compute.py')
source=importlib.util.module_from_spec(spec)
spec.loader.exec_module(source)
decode,clean,zero=source.decode,source.clean,source.zero
encode=source.source.encode
occ_spec=importlib.util.spec_from_file_location('occupied_equations',BASE/'occupied-response/compute.py')
occ=importlib.util.module_from_spec(occ_spec)
occ_spec.loader.exec_module(occ)

@lru_cache(None)
def canonical(value): return s.radsimp(s.simplify(value))

def normalized(matrix): return clean(matrix).applyfunc(canonical)

COLUMNS={}
def number_action(matrix,state):
    columns=COLUMNS.get(id(matrix))
    if columns is None:
        columns={}
        for (i,j),coefficient in matrix.todok().items(): columns.setdefault(j,[]).append((i,coefficient))
        COLUMNS[id(matrix)]=columns
    result={}
    for occupied,amplitude in state.items():
        for j in occupied:
            annihilated=source.annihilate_field([(j,1)],{occupied:amplitude})
            term=source.create_field(columns.get(j,[]),annihilated)
            for out,value in term.items(): source.add(result,out,value)
    return {key:canonical(value) for key,value in result.items() if value}

def read(prepared,state): return canonical(source.pairing(prepared,state))

def transfer_block(matrix, target, incoming):
    return s.SparseMatrix(756,756,{(252*target+i,252*incoming+j):value
        for (i,j),value in matrix.todok().items()})

def main():
    started=time.monotonic()
    source.source.source.source_matrices(ROOT)
    _,_,_,hashes=source.source.source.source.parse_source(ROOT)
    phase=json.loads((BASE/'full-phase/receipt.json').read_text())
    original=json.loads((HERE.parent/'receipt.json').read_text())
    occupied=json.loads((BASE/'occupied-response/receipt.json').read_text())
    vertices=json.loads((BASE/'matter-vertices/receipt.json').read_text())
    assert phase['source_sha256']==original['source_sha256']==occupied['source_sha256']==vertices['source_sha256']==hashes
    n,omega,spin=s.sympify(phase['source_lapse']),s.sympify(phase['source_frequency']),s.sqrt(2)
    C=[decode(item) for item in phase['principal_coefficients']]
    gamma0=clean(n*C[0]/s.I)
    gamma5=clean(s.kronecker_product(s.diag(-1,-1,1,1),s.eye(63)))
    swap=clean(gamma0*gamma5)
    Q=decode(phase['phase_generator'])
    h=clean(decode(original['original_H_full'])-omega*Q)
    spatial=[clean(-n*gamma0*C[j+1]/s.I) for j in range(3)]
    w=s.zeros(252,1)
    basis2=list(itertools.combinations(range(7),2))
    for spin_index,pair,value in [(0,(1,5),1),(1,(0,5),-1),(2,(1,5),1),(3,(0,5),-1)]:
        w[63*spin_index+7+basis2.index(pair)]=s.Rational(value,2)
    w=s.SparseMatrix(w);P=clean(w*w.H)
    zero(w.H*w-s.ones(1));zero(h*w);zero(w.H*h);zero(h*Q-Q*h)
    prepared={(i,):value for i,value in enumerate(w) if value}
    frame=decode(occupied['occupied_frame']);P12=clean(frame*frame.T)
    p=s.symbols('p0:4',real=True);symbols={str(x):x for x in p}
    zero_p=dict.fromkeys(p,0)
    gauge=[];readers=[];forces=[];groups={};derivative_channels=[]
    for row_index,row in enumerate(vertices['primitive_vertices']):
        V=decode(row['operator'],**symbols)
        B=clean(spin*(swap*V.subs(zero_p)+V.subs(zero_p).H*swap)/2)
        # The temporal derivative acts on the incoming primal on its right.
        on_shell=clean(V.subs(zero_p)+V.diff(p[0])*(-s.I*h))
        T=clean(gamma0*on_shell)
        key=row['group']; groups.setdefault(key,[]).append(len(readers))
        readers.append(B);forces.append(T)
        zero(B.H-B)
        if V.diff(p[0]).todok(): derivative_channels.append([key,row['coordinate']])
        if key=='gauge_A':
            zero(V-on_shell);zero(T.H-T);zero(Q*T-T*Q);zero(Q*B-B*Q)
            zero(B+spin*gamma5*T)
            zero((B+spin*Q*T)*frame)
            zero((s.SparseMatrix.eye(252)-P12)*T*frame);zero((s.SparseMatrix.eye(252)-P12)*B*frame)
            gauge.append((T,B))
        if row_index % 40 == 39: print('source vertices',row_index+1,flush=True)
    assert len(gauge)==48 and len(readers)==158
    print('PASS all158 original vertices; actual incoming P, source Q, all48 gauge H12 closure',flush=True)
    # Literal c_i a_j words are evaluated in full finite Fock space, before read.
    force_states=[number_action(T,prepared) for T in forces]
    reader_states=[number_action(B,prepared) for B in readers]
    force_reads=[read(prepared,state) for state in force_states]
    reader_reads=[read(prepared,state) for state in reader_states]
    fw=s.SparseMatrix.hstack(*[T*w for T in forces])
    wb=s.SparseMatrix.vstack(*[w.H*B for B in readers])
    bw=s.SparseMatrix.hstack(*[B*w for B in readers])
    wt=s.SparseMatrix.vstack(*[w.H*T for T in forces])
    connected=normalized(wb*(s.SparseMatrix.eye(252)-P)*fw)
    reverse=normalized(wt*(s.SparseMatrix.eye(252)-P)*bw).T
    for b,B in enumerate(readers):
        for c,T in enumerate(forces):
            direct=read(prepared,number_action(B,force_states[c]))-reader_reads[b]*force_reads[c]
            backward=read(prepared,number_action(T,reader_states[b]))-force_reads[c]*reader_reads[b]
            assert canonical(direct-connected[b,c])==0
            assert canonical(backward-reverse[b,c])==0
    print('PASS 49928 complete four-CAR words and their source-P connected contractions',flush=True)
    # All48 transfer channels use the same incoming P at momentum zero.
    Ts=s.SparseMatrix.hstack(*[T*w for T,B in gauge])
    Bs=s.SparseMatrix.vstack(*[w.H*B for T,B in gauge])
    Tw=s.SparseMatrix.vstack(*[w.H*T for T,B in gauge])
    Bw=s.SparseMatrix.hstack(*[B*w for T,B in gauge])
    active=json.loads((BASE/'active-gauge/receipt.json').read_text())
    full_equations=occ.field_matrix(active,p)
    matter_indices=[i for i,row in enumerate(active['fields']) if row['group'] in ['primal_H','dual_H']]
    gauge_indices=[i for i,row in enumerate(active['fields']) if row['group']=='gauge_A']
    h12=decode(occupied['stationary_H_constant'])
    h12space=[decode(value) for value in occupied['H_spatial_coefficients']]
    eta=s.symbols('eta',positive=True)
    samples=[]
    for sample in occupied['samples']:
        E=s.sympify(sample['energy']);k=list(map(s.sympify,sample['momentum']))
        hk=clean(h+sum((k[j]*spatial[j] for j in range(3)),s.SparseMatrix.zeros(252)))
        hm=clean(h-sum((k[j]*spatial[j] for j in range(3)),s.SparseMatrix.zeros(252)))
        # Positive damping is valid on the complete carrier, including other sectors' real poles.
        z=E+s.I*omega
        rp=source.source.block_inverse(z*s.SparseMatrix.eye(252)-hk,source.source.components(hk))
        rm=source.source.block_inverse(z*s.SparseMatrix.eye(252)+hm,source.source.components(hm))
        zero(normalized((z*s.SparseMatrix.eye(252)-hk)*rp-s.SparseMatrix.eye(252)))
        zero(normalized((z*s.SparseMatrix.eye(252)+hm)*rm-s.SparseMatrix.eye(252)))
        plus=normalized(Bs*rp*Ts);minus=normalized(Tw*rm*Bw).T
        pi=normalized(4*(plus-minus))
        hk12=clean(h12+sum((k[j]*h12space[j] for j in range(3)),s.SparseMatrix.zeros(12)))
        hm12=clean(h12-sum((k[j]*h12space[j] for j in range(3)),s.SparseMatrix.zeros(12)))
        zero(hk*frame-frame*hk12);zero(hm*frame-frame*hm12)
        R12plus=source.source.block_inverse(z*s.eye(12)-hk12,source.source.components(hk12))
        R12minus=source.source.block_inverse(z*s.eye(12)+hm12,source.source.components(hm12))
        zero(normalized(rp*frame-frame*R12plus));zero(normalized(rm*frame-frame*R12minus))
        p_values=dict(zip(p,[-s.I*z,*[s.I*value for value in k]]))
        equations=clean(full_equations.subs(p_values))
        response=occ.solve_actual(equations.extract(matter_indices,matter_indices),
            -equations.extract(matter_indices,gauge_indices))
        zero(normalized(equations.extract(gauge_indices,matter_indices)*response-pi))
        zero(normalized(equations[matter_indices,:][:,matter_indices]*response+
            equations.extract(matter_indices,gauge_indices)))
        # The source-open legs have a genuine eta-down-to-zero limit even when
        # a complementary full252 sector has a pole at this real energy.
        RetaPlus=source.source.block_inverse((E+s.I*eta)*s.eye(12)-hk12,source.source.components(hk12))
        RetaMinus=source.source.block_inverse((E+s.I*eta)*s.eye(12)+hm12,source.source.components(hm12))
        zero(normalized(RetaPlus.subs(eta,0)-decode(sample['twelve_mode_positive_resolvent'])))
        zero(normalized(RetaMinus.subs(eta,0)-decode(sample['twelve_mode_negative_resolvent'])))
        for expression in set(RetaPlus.todok().values())|set(RetaMinus.todok().values()):
            assert canonical(s.limit(expression,eta,0,dir='+')-expression.subs(eta,0))==0
        real_pi=normalized(4*(Bs*frame*RetaPlus.subs(eta,0)*frame.T*Ts-
            (Tw*frame*RetaMinus.subs(eta,0)*frame.T*Bw).T))
        zero(normalized(real_pi-decode(sample['induced_current_response'])))
        # The all-mode formula is exactly the two ordered products in the common carrier.
        # R has (+,0),(0,-); B has (0,+),(-,0). No per-k occupied state is inserted.
        Wp=transfer_block(rp,1,1);Wm=transfer_block(rm,2,2)
        w0=s.SparseMatrix.vstack(w,s.zeros(504,1))
        test_c=0;R=transfer_block(gauge[test_c][0],1,0)+transfer_block(gauge[test_c][0],0,2)
        for b in range(48):
            B=transfer_block(gauge[b][1],0,1)+transfer_block(gauge[b][1],2,0)
            first=(w0.H*B*Wp*R*w0)[0]
            second=(w0.H*R*Wm*B*w0)[0]
            assert canonical(4*(first-second)-pi[b,test_c])==0
        samples.append({'label':sample['label'],'all_48_by_48_matches_original_Pi_and_Schur':True,
            'incoming':'one P=|actual.matter(0)/2><actual.matter(0)/2| at 0',
            'intermediate_momenta':list(map(str,k)),'common_carrier_dimension':756,
            'positive_damping':str(omega),'upper_half_plane_current_response':encode(pi),
            'real_limit_matches_original_receipt':True,'real_limit_current_response':encode(real_pi)})
        print('PASS',sample['label'],'full252 causal +/-k, all48x48 complex Schur, original real Pi limit',flush=True)
    scalar_ids=groups['scalar'];coframe_ids=groups['coframe']
    raw_scalar=s.SparseMatrix.hstack(*[forces[c]*w for c in scalar_ids])
    scalar_response=connected.extract(scalar_ids,scalar_ids)
    assert raw_scalar.todok() and scalar_response.todok()
    raw_closed=sum(s.trace(forces[c]*forces[d]) for c in scalar_ids for d in scalar_ids)
    assert raw_closed==0
    report={'scope':'SOURCE_PREPARED_CONNECTED_CAR_AND_ORIGINAL_OCCUPIED_GAUGE_RESPONSE',
        'source_sha256':hashes,'source_occupation':'actual.matter(0)/2; rank1 norm1, common incoming zero',
        'full_four_CAR_words_checked':2*158**2,'reader_force_order':'B_b before T_c and reversed; distinct source maps',
        'connected_equal_time_static_jet':encode(connected),'reverse_connected_equal_time_static_jet':encode(reverse),
        'vertex_groups':{key:len(value) for key,value in groups.items()},
        'source_gauge_weight':'B=-sqrt(2) gamma5 T on full252; Q=gamma5 on original H12','source_amplitude_squared':4,
        'momentum_rule':'incoming0; plus leg k, minus leg -k; one shared source preparation',
        'samples':samples,'source_scalar_open_force_nnz':len(raw_scalar.todok()),
        'source_scalar_canonical_reader_connected_nnz':len(scalar_response.todok()),
        'closed_raw_scalar_trace':str(raw_closed),
        'coframe_time_derivative_channels':derivative_channels,
        'coframe_force_rule':'gamma0 [V0+Vp0*(-i h0)] at incoming zero; derivative-current contact is retained responsibility',
        'scalar_reader_scope':'canonical real current B; independent-dual variational scalar response is not identified by this probe',
        'finite_transfer_not_continuum_covariance':True,'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({key:report[key] for key in ['scope','full_four_CAR_words_checked','vertex_groups',
        'source_scalar_open_force_nnz','source_scalar_canonical_reader_connected_nnz','elapsed_seconds']},indent=2))

if __name__=='__main__':main()
