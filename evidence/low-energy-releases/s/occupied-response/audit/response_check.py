#!/usr/bin/env python3
"""Independent block inverse, complete Euler residual and spectral response audit."""
import argparse
from collections import Counter
import json
from pathlib import Path
import sympy as s


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True)
    root=parser.parse_args().root.resolve();base=root/'Verification/physics/low-energy-phenomenology';audit=base/'occupied-response/audit'
    assert json.loads((audit/'source-receipt.json').read_text())['status']=='PASS'
    frozen=json.loads((base/'occupied-response/receipt.json').read_text());original=json.loads((base/'active-gauge/receipt.json').read_text())
    phase=json.loads((base/'full-phase/receipt.json').read_text())
    p=s.symbols('p0:4',real=True);E=s.Symbol('E',real=True);ks=s.symbols('k1:4',real=True);z=s.Symbol('z',real=True)
    symbols={str(x):x for x in (*p,E,*ks,z)}
    def decode(record):return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(value,locals=symbols) for i,j,value in record['entries']})
    def clean(matrix):return s.SparseMatrix(matrix).applyfunc(s.expand)
    def equal(left,right):assert all(s.cancel(value)==0 for value in s.SparseMatrix(left-right).todok().values())
    def realify(matrix):
        real=matrix.applyfunc(s.re);imag=matrix.applyfunc(s.im)
        return clean(real.row_join(-imag).col_join(imag.row_join(real)))
    eye=lambda n:s.eye(n,cls=s.SparseMatrix)
    n=s.sympify(frozen['source_lapse']);omega=s.sympify(frozen['source_frequency'])
    L=decode(frozen['canonical_dual_graph_real']);split=decode(frozen['real_to_double_complex']);unsplit=decode(frozen['double_complex_to_real'])
    Tseed=decode(frozen['T_times_original_background']);Bseed=decode(frozen['B_times_original_background'])
    Pplus=decode(frozen['positive_resolvent_denominator']);Pminus=decode(frozen['negative_resolvent_denominator'])
    F=decode(frozen['occupied_frame']);c0=F.T*decode(phase['principal_coefficients'][0])*F;c0inv=n*n*c0
    c=s.diag(eye(12),-eye(12),cls=s.SparseMatrix)
    H=s.MutableSparseMatrix(289,289,{})
    for row,col,powers,value in original['Fourier_Jacobi_entries']:
        H[row,col]+=s.sympify(value)*s.prod(p[j]**degree for j,degree in enumerate(powers))
    fields=original['fields'];matter=[i for group in ('primal_H','dual_H') for i,row in enumerate(fields) if row['group']==group]
    gauge=[i for i,row in enumerate(fields) if row['group']=='gauge_A']
    M=H.extract(matter,matter);HmA=H.extract(matter,gauge);HAm=H.extract(gauge,matter)
    samples=[];pis=[]
    for sample in frozen['samples']:
        energy=s.sympify(sample['energy']);momentum=list(map(s.sympify,sample['momentum']))
        sub=dict(zip((E,*ks),(energy,*momentum)));fourier=dict(zip(p,[-s.I*energy,*[s.I*x for x in momentum]]))
        plus=Pplus.subs(sub);minus=Pminus.subs(sub)
        # Invert only the two independently source-derived 12-mode factors,
        # then build a full 48 inverse using the original off-diagonal action.
        rp=plus.inv(method='DM');rm=minus.inv(method='DM')
        equal(plus*rp,eye(12));equal(rp*plus,eye(12));equal(minus*rm,eye(12));equal(rm*minus,eye(12))
        equal(rp,decode(sample['twelve_mode_positive_resolvent']));equal(rm,decode(sample['twelve_mode_negative_resolvent']))
        kr_inv=unsplit*s.diag(s.I*rp,s.I*rm.T,cls=s.SparseMatrix)*split
        kr_neg_inv=unsplit*s.diag(-s.I*rm,-s.I*rp.T,cls=s.SparseMatrix)*split
        dr_inv=kr_inv*realify(c0inv);dr_neg_inv=kr_neg_inv*realify(c0inv)
        original_inverse=s.SparseMatrix.vstack(s.SparseMatrix.hstack(s.zeros(24),dr_inv*c/n),
            s.SparseMatrix.hstack(c*dr_neg_inv.T/n,s.zeros(24)))
        original_at=M.subs(fourier);equal(original_at*original_inverse,eye(48));equal(original_inverse*original_at,eye(48))
        response=clean(-original_inverse*HmA.subs(fourier))
        equal(response,decode(sample['original_matter_response']))
        complex_response=(rp*Tseed).col_join(-rm.T*Tseed.conjugate())
        equal(response,L*unsplit*complex_response)
        pi=clean(Bseed.H*rp*Tseed-Bseed.T*rm.T*Tseed.conjugate())
        equal(pi,HAm.subs(fourier)*response);equal(pi,decode(sample['induced_current_response']))
        equal(pi,-HAm.subs(fourier)*original_inverse*HmA.subs(fourier))
        residual=clean(H[:,matter].subs(fourier)*response+H[:,gauge].subs(fourier))
        equal(residual,decode(sample['all_289_rows_after_gauge_injection_and_generated_matter']))
        equal(residual[matter,:],s.zeros(48,48));assert residual!=s.zeros(289,48)
        equal(residual[gauge,:],H.extract(gauge,gauge).subs(fourier)+pi)
        equal(pi/4,(Bseed/2).H*rp*(Tseed/2)-(Bseed/2).T*rm.T*(Tseed/2).conjugate())
        assert pi!=pi/4
        no_backward=clean(Bseed.H*rp*Tseed)
        assert no_backward!=pi
        wrong_b=clean(Tseed.H*rp*Tseed-Tseed.T*rm.T*Tseed.conjugate())
        assert wrong_b!=pi
        wrong_response=clean(original_inverse*HmA.subs(fourier))
        assert clean(original_at*wrong_response+HmA.subs(fourier))!=s.zeros(48,48)
        row_groups=Counter(fields[row]['group'] for row in sorted({row for row,col in residual.todok()}))
        samples.append({'label':sample['label'],'full48_left_and_right_inverse':True,
            'all2304_current_entries':True,'all289_residual_rows_retained':True,'nonzero_residual_row_counts':dict(row_groups),
            'original_amplitude_squared_factor':4})
        pis.append(pi)
        print('PASS',sample['label'],': independent full48 inverse,2304 Schur entries and full289 residual with nonmatter rows',flush=True)
    equal(pis[1].T,pis[2])
    pole={E:3*omega,ks[0]:0,ks[1]:0,ks[2]:omega/n}
    pole_matrix=clean(Pplus.subs(pole)/omega)
    null=pole_matrix.nullspace();assert len(null)==1 and pole_matrix.rank()==11
    equal(pole_matrix*null[0],s.zeros(12,1));assert null[0]!=s.zeros(12,1)
    # Derive the reported scalar rational function by spectral interpolation,
    # independently of the candidate's symbolic 12x12 rational inverse.
    h0=decode(frozen['stationary_H_constant'])/omega
    lam=s.Symbol('lambda');characteristic=s.factor(h0.charpoly(lam).as_expr())
    assert s.expand(characteristic-s.sympify(frozen['zero_momentum_scaled_stationary_characteristic_polynomial'].replace('lambda','lam'),locals={'lam':lam}))==0
    eigenvalues=[-2,-s.Rational(3,2),0,s.Rational(3,2),2]
    projectors=[]
    for value in eigenvalues:
        projection=eye(12)
        for other in eigenvalues:
            if other!=value:projection=projection*(h0-other*eye(12))/(value-other)
        projection=clean(projection);equal(projection**2,projection);equal(h0*projection,value*projection)
        projectors.append(projection)
    equal(sum(projectors,s.zeros(12)),eye(12))
    resolvent_plus=sum((Pi/(z-value) for Pi,value in zip(projectors,eigenvalues)),s.zeros(12))
    resolvent_minus=sum((Pi/(z+value) for Pi,value in zip(projectors,eigenvalues)),s.zeros(12))
    equal((z*eye(12)-h0)*resolvent_plus,eye(12));equal((z*eye(12)+h0)*resolvent_minus,eye(12))
    pi00=s.factor((Bseed[:,0].H*resolvent_plus*Tseed[:,0]-Bseed[:,0].T*resolvent_minus.T*Tseed[:,0].conjugate())[0]/omega)
    expected=-200*s.sqrt(30)/(27*(z*z-4))
    assert s.cancel(pi00-expected)==0
    assert s.cancel(pi00-s.sympify(frozen['source_diagonal_response_E_equals_z_omega'],locals={'z':z}))==0
    assert s.simplify(pi00.subs(z,3)+40*s.sqrt(30)/27)==0
    assert s.limit((z-2)*pi00,z,2)==-50*s.sqrt(30)/27
    assert s.limit((z+2)*pi00,z,-2)==50*s.sqrt(30)/27
    equal(pis[0][0:1,0:1],s.Matrix([[pi00.subs(z,3)]]))
    result={'status':'PASS','inverse_algorithm':'12-mode direct inverses plus original independent-dual off-diagonal inverse',
        'samples':samples,'opposite_frequency_momentum_signed_transpose':True,
        'excluded_source_pole_rank':11,'excluded_source_pole_kernel_dimension':1,
        'zero_momentum_response_spectral_projector_derivation':str(pi00),
        'actual_z_plus2_residue':str(-50*s.sqrt(30)/27),'actual_z_minus2_residue':str(50*s.sqrt(30)/27),
        'negative_controls':['dropping_backward_resolvent','force_substituted_for_current',
            'reversing_matter_response_sign','unit_seed_substituted_for_original_amplitude'],
        'full_bosonic_solution_or_vacuum_loop_claimed':False}
    (audit/'response-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS independent Pi00 spectral derivation, actual pole residues and rank11 excluded denominator',flush=True)


if __name__=='__main__':main()
