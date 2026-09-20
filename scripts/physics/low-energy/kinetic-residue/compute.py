#!/usr/bin/env python3
"""Original action time pairing, pole residues, and source-normalized tree legs."""
from __future__ import annotations
import argparse
from collections import Counter
import json
from pathlib import Path
import sys
import sympy as s

HERE=Path(__file__).resolve().parent
BASE=HERE.parent
sys.path.insert(0,str(BASE/'matter-modes'))
from compute import clean,decode,encode,zero,source as native_source


def simple(matrix):return s.SparseMatrix(matrix).applyfunc(s.simplify)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    phase=json.loads((BASE/'full-phase/receipt.json').read_text())
    modes=json.loads((BASE/'matter-modes/source.json').read_text())
    spectrum=json.loads((BASE/'matter-modes/spectral.json').read_text())
    peripheral=json.loads((BASE/'canonical-peripheral/generator.json').read_text())
    active=json.loads((BASE/'active-gauge/receipt.json').read_text())
    vertices=json.loads((BASE/'matter-vertices/receipt.json').read_text())
    exchange=json.loads((BASE/'matter-vertices/exchange.json').read_text())
    external=json.loads((BASE/'onshell-sources/receipt.json').read_text())
    hashes=native_source.parse_source(args.root)[3]
    assert phase['source_sha256']==modes['source_sha256']==vertices['source_sha256']==hashes
    N=s.sympify(phase['source_lapse']);omega=s.sympify(phase['source_frequency'])
    spin=s.sympify(active['actual_background']['dual_multiple'])
    assert spin==s.sqrt(2) and spin.is_positive and spin**2==2
    factor=1/s.sqrt(spin)
    assert s.simplify(spin*factor**2)==1 and s.simplify(factor**4)==s.Rational(1,2)
    C=list(map(decode,phase['principal_coefficients']))
    gamma0=clean(N*C[0]/s.I)
    gamma5=s.kronecker_product(s.diag(-1,-1,1,1),s.eye(63))
    S=clean(gamma0*gamma5);Q=decode(phase['phase_generator'])
    kinetic=clean(spin*gamma5);charge=clean(kinetic*Q)
    zero(S*gamma0-gamma5)
    zero(N*spin*S*C[0]-s.I*kinetic)
    F=decode(modes['source_isometry']);P=decode(modes['free_projection'])
    h0=decode(modes['original_H_constant']);hspace=list(map(decode,modes['original_H_spatial']))
    time_scale=s.sympify(modes['time_scale'])
    B=decode(phase['original_constant_B'])+decode(phase['original_Y'])
    zero(N*spin*S*B+kinetic*time_scale*h0)
    for j in range(3):zero(N*spin*S*(s.I*C[j+1])+kinetic*N*hspace[j])
    # The complex sesquilinear coefficient and real-coordinate Hessian differ by2.
    e_symbol=s.symbols('E_kernel',real=True);q_symbols=s.symbols('q1:4',real=True)
    hessian_checks=0
    for kind in ['singlet','doublet']:
        small0=decode(modes[kind+'_constant'])
        smallspace=list(map(decode,modes[kind+'_spatial']))
        dimension=small0.rows
        coordinates=s.symbols('a0:'+str(2*dimension),real=True)
        amplitude=s.Matrix([coordinates[j]+s.I*coordinates[dimension+j] for j in range(dimension)])
        for chirality in [-1,1]:
            h=time_scale*chirality*(small0+sum((q_symbols[j]*smallspace[j] for j in range(3)),s.zeros(dimension)))
            kernel=clean(spin*chirality*(e_symbol*s.eye(dimension)-h))
            real,imag=kernel.applyfunc(s.re),kernel.applyfunc(s.im)
            realified=real.row_join(-imag).col_join(imag.row_join(real))
            density=s.expand(s.re((amplitude.H*kernel*amplitude)[0]))
            zero(s.hessian(density,coordinates)-2*realified)
            hessian_checks+=1
    signs=[block['chirality'] for block in modes['blocks'] for _ in range(block['dimension'])]
    charges=[block['phase_charge'] for block in modes['blocks'] for _ in range(block['dimension'])]
    zero(gamma5*F-F*s.diag(*signs));zero(Q*F-F*s.diag(*charges))
    gram=clean(F.H*kinetic*F);noether=clean(F.H*charge*F)
    zero(gram-spin*s.diag(*signs));zero(noether-spin*s.diag(*[a*b for a,b in zip(signs,charges)]))
    assert Counter(signs)=={-1:106,1:110}
    assert Counter(a*b for a,b in zip(signs,charges))=={1:202,3:14}
    charge_scale=s.SparseMatrix(s.diag(*[1/s.sqrt(spin*a*b) for a,b in zip(signs,charges)]))
    charge_frame=clean(F*charge_scale)
    charge_readback=clean(charge_frame.H*charge)
    zero(charge_readback*charge_frame-s.eye(216))
    zero(charge_frame*charge_readback-P)
    charge_H=[]
    for h in [h0]+hspace:
        written=clean(charge_readback*h*charge_frame)
        zero(written.H-written)
        zero(h*charge_frame-charge_frame*written)
        charge_H.append(written)
    # Consume the certified spectral projectors in the original action kernel.
    nx,ny,nz,r,t,x=s.symbols('nx ny nz r t x',real=True)
    relations=s.groebner([nx*nx+ny*ny+nz*nz-1,t*t-r*r-s.Rational(9,25)],
        t,nz,ny,nx,r,x,domain=s.QQ_I)

    def spectral_zero(matrix):
        for value in s.SparseMatrix(matrix).todok().values():
            numerator=s.together(value).as_numer_denom()[0]
            assert relations.reduce(s.expand(numerator))[1]==0

    spectral_count=0
    for kind,family in spectrum['universal_families'].items():
        h=decode(family['hamiltonian'],nx=nx,ny=ny,nz=nz,r=r,t=t)
        for chirality in [-1,1]:
            kernel=chirality*x*s.eye(h.rows)-h
            for branch in family['projectors']:
                projector=decode(branch['matrix'],nx=nx,ny=ny,nz=nz,r=r,t=t)
                energy=s.sympify(branch['scaled_frequency'],locals={'r':r,'t':t})
                spectral_zero(kernel*projector-chirality*(x-chirality*energy)*projector)
                pole=s.cancel(time_scale*(x-chirality*energy)/(spin*time_scale*chirality*(x-chirality*energy)))
                assert s.simplify(pole-chirality/spin)==0
                spectral_count+=1
            for branch in spectrum['origin_resolution'][kind]:
                projector=decode(branch['matrix']);energy=s.sympify(branch['scaled_frequency'])
                origin=chirality*x*s.eye(h.rows)-decode(modes[kind+'_constant'])
                zero(origin*projector-chirality*(x-chirality*energy)*projector)
                spectral_count+=1
    assert spectral_count==18
    for block in modes['blocks']:
        first=block['first_column'];frame=F[:,first:first+block['dimension']]
        small0=decode(modes[block['kind']+'_constant'])
        smallspace=list(map(decode,modes[block['kind']+'_spatial']))
        zero(frame.H*(N*spin*S*B)*frame+spin*time_scale*small0)
        for j in range(3):zero(frame.H*(N*spin*S*(s.I*C[j+1]))*frame+spin*N*smallspace[j])
    for h in [h0]+hspace:
        zero((h*kinetic-kinetic*h)*P)
        zero((h*charge-charge*h)*P)
    shift=decode(phase['generated_live_time_shift'])
    zero(F.H*(N*spin*S*shift)*F-omega*noether)
    interacting=decode(peripheral['primal_interacting_frame'])
    interacting_left=clean((interacting.H*interacting).inv(method='DM')*interacting.H)
    H=clean(s.eye(252)-P-interacting*interacting_left)
    assert s.trace(H)==12
    zero((gamma5*Q-s.eye(252))*H)
    right_columns=[i for i,value in enumerate(signs) if value==1]
    left_columns=[i for i,value in enumerate(signs) if value==-1]
    right=clean(factor*F[:,right_columns]);left=clean(factor*F[:,left_columns])
    zero(right.H*kinetic*right-s.eye(110));zero(left.H*kinetic*left+s.eye(106))
    zero(right*right.H-F[:,right_columns]*F[:,right_columns].H/spin)
    source_leg_results=[];legs=[]
    D=decode(vertices['full_stationary_Dirac_operator'])
    p=s.symbols('p0:4')
    frequency=s.symbols('E',real=True)
    for leg in external['legs']:
        vector=decode(leg['vector']);normalized=clean(factor*vector)
        derivative=decode(leg['derivative']);sub=dict(zip(p,derivative))
        zero(P*vector-vector);zero(gamma5*vector-vector);zero(Q*vector-vector)
        zero(simple(vector.H*vector-s.ones(1)))
        zero(simple(normalized.H*kinetic*normalized-s.ones(1)))
        zero(simple(normalized.H*charge*normalized-s.ones(1)))
        zero(simple(D.subs(sub)*normalized));zero(simple(normalized.H*S*D.subs(sub)))
        zero(normalized*normalized.H-vector*vector.H/spin)
        momentum=decode(leg['momentum']);energy=s.sympify(leg['frequency'])
        original_symbol=-s.I*frequency*C[0]+B+sum((s.I*momentum[j]*C[j+1] for j in range(3)),s.zeros(252))
        original_entry=s.simplify(N*spin*(vector.H*S*original_symbol*vector)[0])
        normalized_entry=s.simplify(N*spin*(normalized.H*S*original_symbol*normalized)[0])
        assert s.simplify(original_entry-spin*(frequency-energy))==0
        assert s.simplify(normalized_entry-(frequency-energy))==0
        pole=s.limit((frequency-energy)/original_entry,frequency,energy)
        assert s.simplify(pole-1/spin)==0
        legs.append({'vector':normalized,'derivative':derivative})
        source_leg_results.append({'degree':leg['degree'],'original_frequency':leg['frequency'],
            'stationary_frequency':leg['stationary_frequency'],'normalized_vector':encode(normalized),
            'kinetic_norm':1,'phase_charge_norm':1,'right_pole_line_residue_outer_product':True,
            'original_action_line_frequency_kernel':str(original_entry),
            'normalized_action_line_frequency_kernel':str(normalized_entry),
            'original_action_inverse_line_pole_limit':str(pole)})
    left_vector=F[:,left_columns[0]];left_energy=-s.Rational(3,2)*time_scale
    left_entry=s.simplify(N*spin*(left_vector.H*S*(-s.I*frequency*C[0]+B)*left_vector)[0])
    assert s.simplify(left_entry+spin*(frequency-left_energy))==0
    left_pole=s.limit((frequency-left_energy)/left_entry,frequency,left_energy)
    assert s.simplify(left_pole+1/spin)==0
    ordering=exchange['source_field_indices']
    operators={row['field']:decode(row['operator']) for row in vertices['active_289_bosonic_source_operators']}

    def current(outgoing,incoming):
        pin=dict(zip(p,incoming['derivative']));pout=dict(zip(p,outgoing['derivative']))
        answer=[]
        for field in ordering:
            a=operators[field].subs(pin);b=operators[field].subs(pout)
            answer.append(s.simplify(spin*(outgoing['vector'].H*(S*a+b.H*S)*incoming['vector'])[0]/2))
        return s.SparseMatrix(answer)

    j1=current(legs[1],legs[0]);j2=current(legs[3],legs[2])
    zero(j1-decode(external['first_transition_current'])/spin)
    zero(j2-decode(external['second_transition_current'])/spin)
    zero(current(legs[3],legs[0]));zero(current(legs[1],legs[2]))
    transfer=decode(external['opposite_transfer']);sub=dict(zip(p,transfer));minus=dict(zip(p,-transfer))
    fmatrix=decode(exchange['canonical_source_map'])
    f1=clean(fmatrix.subs(sub)*j1);f2=clean(fmatrix.subs(minus)*j2)
    response=clean(decode(external['canonical_dynamic_response'])/spin)
    zero(simple(decode(exchange['canonical_operator']).subs(sub)*response-f1))
    contact=decode(exchange['total_contact_kernel']).subs(sub)
    dynamic=s.simplify((f2.T*response)[0]);local=s.simplify((j2.T*contact*j1)[0])
    tree=s.simplify(-dynamic-local)
    assert s.simplify(dynamic-s.sympify(external['dynamic_bilinear'])/2)==0
    assert s.simplify(local-s.sympify(external['local_bilinear'])/2)==0
    assert s.simplify(tree-s.sympify(external['elastic_direct_tree_kernel'])/2)==0
    field_response=clean(decode(external['full_289_positive_green_response'])/spin)
    full=s.MutableSparseMatrix(289,289,{})
    for i,j,powers,value in active['Fourier_Jacobi_entries']:
        full[i,j]+=s.sympify(value)*s.prod(transfer[mu]**exponent for mu,exponent in enumerate(powers))
    injected=s.MutableSparseMatrix(289,1,{})
    for i,field in enumerate(ordering):injected[field]=j1[i]
    zero(simple(full*field_response-injected))
    # Each certified Hermitian projector has a fixed original chirality and phase charge.
    residues=[]
    for group in modes['groups']:
        residues.append({'chirality':group['chirality'],'degree':group['degree'],
            'phase_charge':group['phase_charge'],'pole_residue_factor':str(group['chirality']/spin),
            'kinetic_weight':str(group['chirality']*spin),
            'phase_charge_weight':str(group['chirality']*group['phase_charge']*spin)})
    result={'scope':'ORIGINAL_ACTION_KINETIC_PAIRING_FREE_POLE_RESIDUES_AND_NORMALIZED_SOURCE_TREE',
        'source_sha256':modes['source_sha256'],'source_spin_scale':str(spin),'source_lapse':str(N),
        'temporal_density':'s Re(i psi^dagger gamma5 dot(psi)) from original holonomic affine density',
        'original_time_principal':encode(s.I*kinetic),'kinetic_pair_matrix':encode(kinetic),
        'free_kinetic_pair':encode(gram),'signature':{'positive':110,'negative':106},
        'sesquilinear_frequency_kernel':'K(E,k)=s gamma5 (E-H_original(k)); original density=Re(psi^dagger K psi)',
        'real_coordinate_frequency_Hessian':'2*Realify(K) on the Hermitian free restriction; complex kernel and real Hessian kept distinct',
        'actual_source_block_real_Hessian_checks':hessian_checks,
        'action_resolvent':'G_K(E,k)=G_H(E,k)*gamma5/s=sum_b (chi_b/s)*Pi_b(k)/(E-E_b(k))',
        'coincident_frequency_residue':'sum_b with E_b=E0 of (chi_b/s)*Pi_b, not a single unsigned projector',
        'all_source_copy_action_kernel_readbacks':len(modes['blocks']),
        'all_generic_and_origin_projector_action_residue_identities':spectral_count,
        'residue_groups':residues,'positive_normalized_frame':encode(right),
        'right_normalization_factor':str(factor),'right_normalized_kinetic_gram_identity':True,
        'Noether_phase_charge_matrix':encode(charge),'free_Noether_phase_charge_gram':encode(noether),
        'free_Noether_positive_weights':{'s':202,'3s':14},
        'Noether_isometric_frame':encode(charge_frame),'Noether_full_readback':encode(charge_readback),
        'Noether_frame_left_inverse_identity':True,'Noether_frame_right_inverse_is_original_Pfree':True,
        'Noether_positive_pullback_H_coefficients':list(map(encode,charge_H)),
        'Noether_positive_H_readback':'H_original(k)=N*sqrt(2)*(Hcoeff[0]+sum_j (k_j/sqrt(2))*Hcoeff[j+1])',
        'Noether_source_time_generator_Hermitian_and_intertwining_all_k':True,
        'actual_FullPhase_time_shift_equals_omega_times_charge_pair':True,
        'original_occupied_H_charge_equals_original_canonical_S_density':True,
        'normalized_original_on_shell_legs':source_leg_results,
        'actual_left_line_pole':{'source_vector':encode(left_vector),'original_frequency':str(left_energy),
            'frequency_kernel':str(left_entry),'inverse_pole_limit':str(left_pole),
            'kinetic_norm':str((left_vector.H*kinetic*left_vector)[0]),
            'phase_charge_norm':str((left_vector.H*charge*left_vector)[0])},
        'actual_normalized_first_current':encode(j1),'actual_normalized_second_current':encode(j2),
        'actual_normalized_289_green_response':encode(field_response),
        'normalized_dynamic_bilinear':str(dynamic),'normalized_local_bilinear':str(local),
        'normalized_elastic_direct_tree_kernel':str(tree),
        'actual_all_289_rows_with_normalized_original_source':True,
        'per_bilinear_factor':str(1/spin),'four_leg_tree_factor':'1/2',
        'Fock_coordinate_pairing_not_redefined':True,'full_quantum_LSZ_or_cross_section_claimed':False,
        'left_signature_not_promoted_to_whole_theory_no_go':True}
    args.out.parent.mkdir(parents=True,exist_ok=True)
    args.out.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print('PASS original action K=s gamma5(E-H), free signature +110/-106, source phase-charge +202s/+14(3s)',flush=True)
    print('PASS all4 source external legs action-unit; original97 currents scale1/s; full289 Green source rewrite',flush=True)
    print('PASS actual normalized tree =',tree,'; exact factor1/2',flush=True)


if __name__=='__main__':main()
