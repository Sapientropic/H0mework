#!/usr/bin/env python3
"""Independent causal response using nullspace projectors and harmonic coefficients.

The frozen builder generates polynomial projectors. This checker independently
obtains each eigenspace from the source matrix and constructs its Gram projector.
Positive-time equations, source jumps and reality are checked per harmonic.
"""
import argparse
import json
from pathlib import Path
import sympy as s


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True)
    root=parser.parse_args().root.resolve();base=root/'Verification/physics/low-energy-phenomenology'
    folder=base/'occupied-response/causal';audit=folder/'audit'
    frozen=json.loads((folder/'receipt.json').read_text())
    replay=json.loads(Path('/tmp/occupied-causal-audit-replay.json').read_text())
    assert {k:v for k,v in frozen.items() if k!='elapsed_seconds'}=={k:v for k,v in replay.items() if k!='elapsed_seconds'}
    source=json.loads((base/'occupied-response/receipt.json').read_text());active=json.loads((base/'active-gauge/receipt.json').read_text())
    assert source['source_sha256']==frozen['source_sha256']
    for name in ('source-receipt.json','response-receipt.json'):
        assert json.loads((base/'occupied-response/audit'/name).read_text())['status']=='PASS'
    phase=s.Symbol('phase',nonzero=True);z=s.Symbol('z');p=s.symbols('p0:4',real=True)
    symbols={str(value):value for value in (phase,z,*p)}
    def decode(record):return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(value,locals=symbols) for i,j,value in record['entries']})
    def clean(matrix):return s.SparseMatrix(matrix).applyfunc(s.expand)
    def equal(left,right):assert all(s.cancel(value)==0 for value in s.SparseMatrix(left-right).todok().values())
    eye=lambda n:s.eye(n,cls=s.SparseMatrix)
    omega=s.sympify(source['source_frequency']);spin=s.sympify(source['source_dual_multiple'])
    assert omega>0 and spin==s.sqrt(2)
    h=decode(source['stationary_H_constant']);small=clean(h/omega)
    w=decode(source['source_prepared']);seed=2*w;equal(w,decode(frozen['source_prepared']))
    T=list(map(decode,source['gauge_Hamiltonian_forces']));B=list(map(decode,source['original_current_readers']))
    ts=s.SparseMatrix.hstack(*(a*seed for a in T));bs=s.SparseMatrix.hstack(*(b*seed for b in B))
    equal(ts,decode(source['T_times_original_background']));equal(bs,decode(source['B_times_original_background']))
    equal(h.H,h);equal(h*w,s.zeros(12,1));assert (w.H*w)[0]==1
    lam=s.Symbol('lam');characteristic=small.charpoly(lam).as_expr();roots=s.roots(characteristic,lam)
    assert sum(roots.values())==12 and len(roots)==5
    rates=sorted(roots);assert all(rate.is_Rational for rate in rates)
    saved={s.sympify(item['scaled_rate']):item for item in frozen['generated_spectrum']}
    assert set(saved)==set(rates)
    P={};forward={};backward={}
    for rate in rates:
        basis=s.Matrix.hstack(*(small-rate*eye(12)).nullspace())
        assert basis.cols==roots[rate]
        projector=clean(basis*(basis.H*basis).inv()*basis.H)
        equal(projector.H,projector);equal(projector*projector,projector);equal(small*projector,rate*projector)
        equal(projector,decode(saved[rate]['projector']))
        assert projector.rank()==saved[rate]['multiplicity']==int(roots[rate])
        P[rate]=projector
        forward[rate]=clean(bs.H*projector*ts)
        backward[rate]=clean(ts.H*projector*bs).T
        equal(forward[rate],decode(saved[rate]['forward_current_weight']))
        equal(backward[rate],decode(saved[rate]['backward_current_weight']))
        equal(backward[rate],forward[rate].conjugate())
    equal(sum(P.values(),s.zeros(12)),eye(12))
    for a in rates:
        for b in rates:equal(P[a]*P[b],P[a] if a==b else s.zeros(12))
    flow=sum((P[rate]*phase**(2*rate) for rate in rates),s.zeros(12))
    equal(flow,decode(frozen['source_unitary_flow']))
    # Spectral multiplication supplies both unitary products and the generator.
    equal(flow*flow.subs(phase,1/phase),eye(12));equal(flow.subs(phase,1/phase)*flow,eye(12))
    equal(flow.conjugate().T.subs(s.conjugate(phase),1/phase),flow.subs(phase,1/phase))
    equal(flow*w,w)
    equal((-s.I*omega*phase/2)*flow.diff(phase),-s.I*h*flow)
    Q=decode(source['occupied_phase_charge']);h_original=decode(source['original_H_constant'])
    for sign,branch in zip((-1,1),source['source_prepared_phase_branches']):
        u=decode(branch);equal(h_original*u,sign*omega*u);equal(Q*u,sign*u)
    print('PASS source nullspace/Gram five-projector resolution, all-time unitary harmonics and original clock branches',flush=True)

    fields=active['fields'];matter=[i for group in ('primal_H','dual_H') for i,row in enumerate(fields) if row['group']==group]
    gauge=[i for i,row in enumerate(fields) if row['group']=='gauge_A']
    H=s.MutableSparseMatrix(289,289,{})
    for row,col,powers,value in active['Fourier_Jacobi_entries']:
        H[row,col]+=s.sympify(value)*s.prod(p[j]**degree for j,degree in enumerate(powers))
    M=H.extract(matter,matter);mg=H.extract(matter,gauge);gm=H.extract(gauge,matter)
    M0=M.subs(dict.fromkeys(p,0));M1=M.diff(p[0])
    equal(M.subs(dict.fromkeys(p[1:],0)),M0+p[0]*M1)
    assert not mg.free_symbols and not gm.free_symbols
    graph=decode(source['canonical_dual_graph_real']);unsplit=decode(source['double_complex_to_real'])
    complex_pulse={rate:clean(-s.I*P[rate]*ts) for rate in rates}
    real_pulse={rate:clean(graph*unsplit*complex_pulse[rate].col_join(complex_pulse[-rate].conjugate())) for rate in rates}
    residues={rate:clean(forward[rate]-backward[-rate]) for rate in rates}
    current={rate:clean(-s.I*residues[rate]) for rate in rates}
    ranks=[]
    for rate in rates:
        equal(residues[rate],decode(saved[rate]['merged_retarded_residue']))
        actual_rank=residues[rate].rank();assert actual_rank==saved[rate]['merged_residue_rank']
        ranks.append((str(rate),actual_rank))
        equal((M0-s.I*omega*rate*M1)*real_pulse[rate],s.zeros(48,48))
        equal(gm*real_pulse[rate],current[rate])
        equal(real_pulse[rate].conjugate(),real_pulse[-rate])
        equal(current[rate].conjugate(),current[-rate])
    assert ranks==[('-2',6),('-3/2',4),('0',0),('3/2',4),('2',6)]
    pulse=sum((real_pulse[rate]*phase**(2*rate) for rate in rates),s.zeros(48))
    response=sum((current[rate]*phase**(2*rate) for rate in rates),s.zeros(48))
    equal(pulse,decode(frozen['source_retarded_matter_positive_time']))
    equal(response,decode(frozen['source_retarded_current_positive_time']))
    pulse_jump=clean(sum(real_pulse.values(),s.zeros(48)))
    equal(pulse_jump,decode(frozen['original_matter_right_jump']));equal(M1*pulse_jump+mg,s.zeros(48))
    assert M1.det()!=0 and pulse_jump!=s.zeros(48)
    jump=clean(sum(current.values(),s.zeros(48)));equal(jump,decode(frozen['current_right_jump']))
    direct_jump=s.Matrix(48,48,lambda b,c:s.expand(s.I*(seed.H*(T[c]*B[b]-B[b]*T[c])*seed)[0]))
    equal(jump,direct_jump);assert len(jump.todok())==frozen['current_jump_nonzero_entries']==44
    equal(residues[0],s.zeros(48));assert P[0].rank()==2
    # A vanishing merged current pole does not erase the underlying zero modes
    # or their actual static matter excitation.
    equal(P[0]*w,w);assert complex_pulse[0]!=s.zeros(12,48) and real_pulse[0]!=s.zeros(48)
    assert forward[0]!=s.zeros(48) and backward[0]!=s.zeros(48)
    assert clean(response-current[-2]*phase**(-4)-current[2]*phase**4)!=s.zeros(48)
    assert clean(M1*(-pulse_jump)+mg)!=s.zeros(48)
    print('PASS all48 matter harmonics, canonical dual, delta jump and2304 currents;44 nonzero current jumps and retained source zero modes',flush=True)

    resolvent_plus=sum((P[rate]/(z-omega*rate) for rate in rates),s.zeros(12))
    resolvent_minus=sum((P[rate]/(z+omega*rate) for rate in rates),s.zeros(12))
    equal((z*eye(12)-h)*resolvent_plus,eye(12));equal(resolvent_plus*(z*eye(12)-h),eye(12))
    equal((z*eye(12)+h)*resolvent_minus,eye(12));equal(resolvent_minus*(z*eye(12)+h),eye(12))
    meromorphic=sum((residues[rate]/(z-omega*rate) for rate in rates),s.zeros(48))
    equal(meromorphic,bs.H*resolvent_plus*ts-bs.T*resolvent_minus.T*ts.conjugate())
    energy=s.Symbol('E',real=True);eta=s.Symbol('eta',positive=True,real=True)
    # Entrywise application of the certified finite_retarded_transform: each
    # harmonic coefficient is current[rate], with the original real frequency.
    integrals={rate:s.I/(energy+s.I*eta-omega*rate) for rate in rates}
    transformed=sum((current[rate]*integrals[rate] for rate in rates),s.zeros(48))
    equal(transformed,meromorphic.subs(z,energy+s.I*eta))
    for rate in rates:
        assert s.im(energy+s.I*eta-omega*rate)==eta
        equal(residues[rate].T,-residues[-rate])
    equal(meromorphic.subs(z,-z).T,meromorphic)
    # The frequency-space matter solution follows from the actual time pulse.
    laplace_matter=sum((real_pulse[rate]*integrals[rate] for rate in rates),s.zeros(48))
    equal((M0-s.I*(energy+s.I*eta)*M1)*laplace_matter+mg,s.zeros(48))
    equal(gm*laplace_matter,transformed)
    regulated=s.sympify(frozen['regulated_consumer']['energy']);assert s.simplify(regulated-omega*(3+s.I))==0
    at=clean(M0-s.I*regulated*M1)
    inv=at.inv(method='DM');equal(at*inv,eye(48));equal(inv*at,eye(48))
    matter_response=clean(-inv*mg);current_response=clean(gm*matter_response)
    equal(matter_response,decode(frozen['regulated_consumer']['original_matter_response']))
    equal(current_response,decode(frozen['regulated_consumer']['original_current_response']))
    equal(current_response,meromorphic.subs(z,regulated))
    equal(matter_response,laplace_matter.subs({energy:3*omega,eta:omega}))
    equal(meromorphic.subs(z,3*omega),decode(source['samples'][0]['induced_current_response']))
    opposite_damping=transformed.subs(eta,-eta)
    assert s.simplify(opposite_damping[0,0]-transformed[0,0])!=0
    # Direct scalar harmonic coefficients, independently of sine simplification.
    assert current[-2][0,0]==-4*s.I*spin and current[2][0,0]==4*s.I*spin
    assert all(current[rate][0,0]==0 for rate in rates if abs(rate)!=2)
    target=-16*spin*omega/(z*z-4*omega*omega)
    assert s.cancel(meromorphic[0,0]-target)==0
    assert s.cancel(target-s.sympify(frozen['source_diagonal_transform'],locals={'z':z}))==0
    output={'status':'PASS','replay_equal_except_runtime':True,'projector_algorithm':'eigenspace nullspaces and Gram inverses',
        'spectrum_and_merged_current_ranks':ranks,'source_zero_mode_dimension':2,
        'zero_mode_static_matter_pulse_nonzero':True,'zero_current_residue_is_cancellation_of_nonzero_weights':True,
        'time_coefficients_checked_per_harmonic':True,'all48_positive_time_matter_and_delta_source_rows':True,
        'current_jump_nonzero_entries':44,'all2304_current_and_positive_damping_transform_entries':True,
        'full_positive_damping_matter_Laplace_equation':True,'regulated_original48_inverse_verified_both_sides':True,
        'source_diagonal_time':'8*sqrt(2)*sin(2*omega*t)','source_diagonal_transform':str(target),
        'negative_controls':['reversed_matter_jump','discarded_zero_mode_matter_pulse','reversed_damping_half_plane'],
        'scope':'k=0, positive damping; original prepared response','distributional_eta_zero_limit_or_vacuum_added':False}
    (audit/'independent-receipt.json').write_text(json.dumps(output,indent=2)+'\n')
    print('PASS full positive-damping Laplace matter equation, both12 inverses, all2304 ordered responses and actual complex-energy48 inverse',flush=True)


if __name__=='__main__':main()
