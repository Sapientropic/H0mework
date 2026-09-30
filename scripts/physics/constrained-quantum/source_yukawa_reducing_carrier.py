#!/usr/bin/env python3
"""Largest canonical reducing carrier annihilated by all original Yukawas.

The initial kernel is generated from every actual Hamiltonian Y and adjoint.
The original canonical158 coefficients then generate the minimal reducing
closure of its excluded range. The original Dirac action uses the same-E dual
companion projector; a separate common-raw-projector comparison is retained. This is a source field-sector construction, unrelated
to the momentum-dependent Ward compatibility constraint on external currents.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from dynamic import HERE,BASE,ROOT,ROOT_ID,decode
from source_spatial_active_phase_splice import dm
from source_common_hamiltonian import SourceCommonHamiltonian
from source_lorentz_contact import clean,equal,encode,GAMMA
from source_quantum_gauss_section import SourceQuantumGaussSection
from source_gauss_quantum_current import apply_superposition,encode_state
from source_quantum_ordered_temporal import OrderedTemporalCoefficients


def coefficient_matrices(matrix):
    variables=tuple(sorted(matrix.free_symbols,key=str))
    if not variables:return [matrix]
    terms={}
    for key,value in matrix.todok().items():
        for powers,coefficient in s.Poly(value,*variables).terms():
            if coefficient:terms.setdefault(powers,{})[key]=coefficient
    return [s.SparseMatrix(*matrix.shape,entries)for _,entries in sorted(terms.items())]


def common_kernel(yukawa):
    gram=clean(sum((Y.H*Y+Y*Y.H for Y in yukawa),s.zeros(252)))
    assert gram.is_diagonal()
    excluded=[i for i in range(252)if gram[i,i]!=0]
    assert all(gram[i,i]>0 for i in excluded)
    P=s.SparseMatrix(252,252,{(i,i):1 for i in range(252)if i not in excluded})
    for Y in yukawa:
        equal(Y*P,s.zeros(252));equal(Y.H*P,s.zeros(252))
    equal(P.H,P);equal(P*P,P)
    return P,excluded,gram


def reducing_closure(excluded,generators):
    """Actual generated column spans, with a paid coordinate basis at each step."""
    current=set(excluded);chain=[];leaks=[]
    for _ in range(253):
        candidates=[];seen=set();next_support=set(current)
        for label,A in generators:
            for adjoint,B in ((False,A),(True,A.H)):
                entries=B.todok();by_column={}
                for (i,j),value in entries.items():
                    if j in current:by_column.setdefault(j,{})[i]=value
                for j,column in by_column.items():
                    if set(column)<=current:continue
                    signature=tuple(sorted(column.items()))
                    if signature in seen:continue
                    seen.add(signature)
                    candidates.append(s.SparseMatrix(252,1,{(i,0):v for i,v in column.items()}))
                    next_support.update(column)
                    if not leaks:leaks.append({'generator':label,'adjoint':adjoint,'incoming':j,
                        'outgoing_entries':[[i,str(v)]for i,v in sorted(column.items())if i not in current]})
        if not candidates:
            chain.append({'dimension':len(current),'generated_new_dimension':0})
            break
        old=s.SparseMatrix(252,len(current),{(i,j):1 for j,i in enumerate(sorted(current))})
        span=s.SparseMatrix.hstack(old,*candidates)
        generated_rank=len(dm(span).rref()[1])
        # This identity proves the coordinate frame is the actual span of
        # original generated vectors, rather than a support overapproximation.
        assert generated_rank==len(next_support)
        chain.append({'dimension':len(current),'generated_new_dimension':generated_rank-len(current),
                      'actual_original_new_columns':len(candidates)})
        current=next_support
    else:raise AssertionError('finite original reducing closure failed to stabilize')
    P=s.SparseMatrix(252,252,{(i,i):1 for i in range(252)if i not in current})
    for _,A in generators:
        equal(clean(P*A-A*P),s.zeros(252))
        equal(clean(P*A.H-A.H*P),s.zeros(252))
    return P,chain,leaks


def actual_quantum_consumer(P):
    section=SourceQuantumGaussSection();native=section.native;joint=native.joint
    fullP=s.diag(P,P.conjugate());kept={i for i in range(504)if fullP[i,i]}
    # This stronger source carrier has chirality-dependent exterior support.
    # Pay every actual generic spin coefficient; arbitrary spin matrices would
    # not commute with it. Tensor identity63 is evaluated entrywise exactly.
    cf=joint.coframe
    spin_matrices=cf.J+cf.T+cf.M+[cf.correction,cf.one_body]
    spin_matrices +=[M for row in cf.dT for M in row]
    for spin in spin_matrices:
        for (i,j),value in spin.todok().items():
            for color in range(63):
                assert s.cancel((fullP[63*i+color,63*i+color]-fullP[63*j+color,63*j+color])*value)==0
    gamma5=s.diag(-1,-1,1,1)
    for gamma in GAMMA:equal(gamma5*gamma+gamma*gamma5,s.zeros(4))
    for left in GAMMA:
        for right in GAMMA:equal(gamma5*left*right-left*right*gamma5,s.zeros(4))
    for M in joint.common.rho:
        equal(clean(P*M-M*P),s.zeros(252))
    for Q in native.Q_b+native.Q_s:
        equal(clean(fullP*Q-Q*fullP),s.zeros(504))
    for R in section.R:
        equal(clean(fullP*R-R*fullP),s.zeros(504))
    for quaternion in ((s.Rational(3,5),s.Rational(4,5),0,0),(-1,0,0,0)):
        U=section.matter_group(section.group(s.Matrix(quaternion)))
        equal(clean(fullP*U-U*fullP),s.zeros(504))
    q=(s.Rational(7,6),s.Rational(1,11),s.Rational(9,8),s.Rational(-1,13),s.Rational(1,17),s.Rational(11,10))
    x=s.Matrix([s.Rational((3*j+1)%7-3,1000)for j in range(61)])
    A=section.A0.copy();A[0,2]+=s.Rational(1,17);A[1,7]+=s.Rational(1,19)
    data=joint.coefficients(q,x,A)
    Y=clean(-s.I*data['e'].det()*data['matter']['inverse_E']*data['matter']['Y'])
    Y=clean(s.diag(Y,-Y.conjugate()))
    equal(Y*fullP,s.zeros(504));equal(Y.H*fullP,s.zeros(504))
    equal(clean(fullP*data['matter_CAR']-data['matter_CAR']*fullP),s.zeros(504))
    candidates=sorted(i for i in kept if i<252)
    incoming=next(word for word in itertools.combinations(candidates,2)
                  if apply_superposition(data['matter_CAR'],{word:1}))
    gradient=s.Matrix([s.I*s.Rational(j%11+1,67)for j in range(103)])
    v=s.Matrix([s.Rational(j%7-3,53)for j in range(103)])
    parts,image=joint.action(data,incoming,gradient,v*v.T-s.eye(103))
    assert all(parts.values())
    for part in parts.values():
        assert all(len(word)==2 and set(word)<=kept for word in part)
    assert not apply_superposition(Y,{incoming:1})
    # The original local Gauss extension and every derivative retain the
    # same CAR carrier, including words with zero value and nonzero jets.
    grad=s.Matrix([s.Rational(j%3-1,41)for j in range(100)])
    jet=section.extend_jet({incoming:1},{incoming:grad},{incoming:grad*grad.T-s.eye(100)})
    Gauss=section.verify_Gauss_jet(jet)
    assert all(set(word)<=kept for word in jet)
    ordered=OrderedTemporalCoefficients();_,energy,_=ordered.generate(3)
    discarded=[sum(13 in word for word in coefficient)for coefficient in energy]
    retained=[sum(13 not in word for word in coefficient)for coefficient in energy]
    assert discarded[1]>0 and retained[1]>0
    return {'real_CAR_dimension':len(kept),'complete_native_broken_stabilizer_current_reducing':True,
        'generic_live_spin_coefficients_and_all_derivatives_reducing':{'actual_q_generic_spin_matrices_checked':len(spin_matrices),'all_matrix_entries_and63_internal_slots_checked':True,'generic_four_time_extension':'Each original E^-1 C_mu Gamma_ab is even Clifford, as is E^-1 C_mu. The actual Gamma5 anticommutators and all even products are checked. The only odd Hamiltonian factor is Y, killed in both directions on this generated carrier.'},
        'actual_finite_native_group_and_center_reduce_carrier':True,
        'actual_two_particle_input':list(incoming),
        'all4_original_Hamiltonian_components_nonzero':True,
        'complete_four_component_action':{name:encode_state(part)for name,part in parts.items()},
        'complete_Hamiltonian_image':encode_state(image),
        'actual_complete_local_Gauss_extension':Gauss,
        'all_Gauss_jet_words_remain_in_carrier':True,
        'original_whole_Y_and_adjoint_annihilate_carrier':True,
        'actual_ordered_energy_words_with_Y_vanish':[int(v)for v in discarded],
        'remaining_ordered_energy_word_counts':[int(v)for v in retained],
        'Fock_lift':'Outside(P) occupation has binary one-particle charge. Every original one-body coefficient commutes with this charge, as do its adjoint, normal products and all boson derivatives. Its zero-charge eigenspace is the full algebraic Fock(P), preserved in both directions by the entire four-energy family and every ordered temporal coefficient.',
        'Lean_direct_consumers':['LowEnergy/Fermion/Charge.lean: occupationCharge_quantize',
            'LowEnergy/Fermion/Charge.lean: occupationCharge_normalProduct',
            'LowEnergy/Fermion/Charge.lean: occupationCharge_preserves_eigenstate'],
        'whole_boson_coframe_scalar61_gauge36_fields_retained':True,
        'formal_symmetry_or_positive_spectrum_of_restriction_proved':False}


def main():
    started=time.monotonic();common=SourceCommonHamiltonian()
    source=json.loads((BASE/'matter-vertices/receipt.json').read_text())
    phase=json.loads((BASE/'full-phase/receipt.json').read_text())
    for record in(source,phase):
        for group in('source_sha256','input_sha256'):
            for name,digest in record.get(group,{}).items():
                assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    background=common.scalar.exchange.active['actual_background']
    e=s.Matrix(background['coframe']).applyfunc(s.sympify)
    A=s.Matrix(background['gauge_connection']).applyfunc(s.sympify)
    E=common.matter_data(e,common.scalar.vacuum,A)['E']
    prefactor=clean(-s.I*e.det()*E.inv())
    yukawa=[clean(prefactor*(s.I**imaginary)*Y)for imaginary in range(2)for Y in common.yukawa_basis]
    assert len(yukawa)==70
    kernel,excluded,gram=common_kernel(yukawa)
    print('PASS actual all70 Hamiltonian Yukawa/adjoint common kernel',int(s.trace(kernel))*2,'real CAR modes',flush=True)
    generators=[];raw_vertex_count=0;raw_coefficient_count=0
    for j,row in enumerate(source['primitive_vertices']):
        raw_vertex_count+=1
        for k,coefficient in enumerate(coefficient_matrices(decode(row['operator']))):
            generators.append((f'raw_vertex{j}:{row["group"]}:coefficient{k}',coefficient))
            raw_coefficient_count+=1
    assert raw_vertex_count==158
    for j,row in enumerate(phase['principal_coefficients']):
        for k,coefficient in enumerate(coefficient_matrices(decode(row))):
            generators.append((f'original_principal{j}:coefficient{k}',coefficient))
    for k,coefficient in enumerate(coefficient_matrices(decode(source['full_stationary_Dirac_operator']))):
        generators.append((f'full_stationary_Dirac:coefficient{k}',coefficient))
    for j,gamma in enumerate(GAMMA):generators.append((f'original_Clifford{j}',clean(s.kronecker_product(gamma,s.eye(63)))))
    Einverse=clean(E.inv())
    canonical_generators=[(label,clean(-s.I*Einverse*V))for label,V in generators]
    P,chain,leaks=reducing_closure(excluded,canonical_generators)
    dual=clean(E*P*Einverse)
    equal(dual*dual,dual);equal(dual.H,dual)
    for Y in yukawa:
        equal(Y*P,s.zeros(252));equal(Y.H*P,s.zeros(252))
    for _,V in generators:
        equal(clean(V*P-dual*V),s.zeros(252))
    print('PASS actual canonical158 closure and same-E raw primal/dual intertwining',chain,'remaining',int(s.trace(P))*2,flush=True)
    rawP,raw_chain,raw_leaks=reducing_closure(excluded,generators)
    print('PASS separate common-raw-projector comparison',raw_chain,'remaining',int(s.trace(rawP))*2,flush=True)
    # Identify source exterior/chirality support only after both actual spans.
    from source_gauge_legendre import source as original_source
    _,_,degrees,_=original_source.parse_source(ROOT)
    inventory=[(degree,word)for degree in degrees for word in itertools.combinations(range(7),degree)]
    support_by_spin=[{str(degree):sum(bool(P[63*spin+i,63*spin+i])for i,(k,_)in enumerate(inventory)if k==degree)for degree in degrees}for spin in range(4)]
    for i in range(252):
        degree=inventory[i%63][0];spin=i//63
        assert bool(P[i,i])==(degree==4 or(degree==2 and spin<2)or(degree==6 and spin>=2))
        assert bool(rawP[i,i])==(degree==4)
    consumer=actual_quantum_consumer(P)
    print('PASS complete interacting Fock reducing carrier, nonzero four-energy action and all ordered time coefficients',flush=True)
    paths=[HERE/name for name in('source_yukawa_reducing_carrier.py','source_common_hamiltonian.py',
        'source_quantum_grade_structure.json','source_quantum_ordered_temporal.py','source_quantum_ordered_temporal.json',
        'source_quantum_gauss_section.py','source_quantum_stabilizer.py','source_coframe_live_ordering.py')]
    paths +=[BASE/'matter-vertices/receipt.json',BASE/'full-phase/receipt.json',
        ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/Fermion/Charge.lean']
    result={'root':ROOT_ID,'scope':'SOURCE_GENERATED_MAXIMAL_CANONICAL_YUKAWA_NULL_REDUCING_CARRIER_SAME_E_RAW_DUAL_AND_FULL_FOCK_CLOSURE',
        'source_sha256':common.source_hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},
        'all70_original_Hamiltonian_Yukawa_and_adjoint_kernel':{'complex_dimension':int(s.trace(kernel)),
            'real_CAR_dimension':2*int(s.trace(kernel)),'positive_Gram':encode(gram),'projector':encode(kernel)},
        'original_canonical_vertex_closure':{'raw_vertex_count':raw_vertex_count,'independent_momentum_coefficient_matrices':raw_coefficient_count,
            'first_canonical_leak_of_initial_kernel_complement':leaks,'minimal_excluded_span_chain':chain,
            'maximality':'Start with the exact range of sum(YdagY+YYdag). At every step the actual images under all canonical -i E^-1 V source coefficients and adjoints span the recorded enlarged carrier; its final reducing closure is minimal. Its orthogonal complement is therefore the largest canonical reducing carrier killed by all Y and Ydag.',
            'raw_and_canonical_ports':'All158 raw V matrices are checked coefficientwise in every momentum monomial, together with original principals and Clifford matrices. The canonical projector commutes with -i E^-1 V. The raw action instead satisfies V Pprimal=Pdual V with Pdual=E Pprimal E^-1; no artificial equality of these two restrictions is imposed.'},
        'generated_raw_dual_companion':encode(dual),
        'raw_independent_dual_restriction':'psi=Pprimal psi, p=p Pprimal and chi=i p E^-1 imply chi=chi Pdual. Every original raw Dirac/principal/vertex intertwines this same-source pair.',
        'common_raw_projector_comparison':{'projector':encode(rawP),'complex_dimension':int(s.trace(rawP)),'real_CAR_dimension':2*int(s.trace(rawP)),'excluded_span_chain':raw_chain,'first_leak':raw_leaks,'meaning':'Adding the unnecessary requirement that one identical projector commute with every raw Dirac vertex yields the smaller Lambda4 carrier. It is not the maximal canonical physical subtheory.'},
        'generated_reducing_projector_complex252':encode(P),'generated_reducing_projector_real504':encode(s.diag(P,P.conjugate())),
        'generated_complex_dimension':int(s.trace(P)),'generated_real_CAR_dimension':2*int(s.trace(P)),
        'generated_original_support_by_spin':support_by_spin,
        'identified_carrier':'(left chirality tensor Lambda2) direct_sum (right chirality tensor Lambda6) direct_sum (all spin tensor Lambda4), doubled on the independent-real CAR branches',
        'complete_Fock_consumer':consumer,
        'scope_separation':'This is a source-generated interacting reducing subtheory. The original complementary matter carrier and all bosonic fields remain in the full theory. This is not the external-current Ward compatibility kernel, a B/L/hadron/proton identification, or a proton no-go.',
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'source_yukawa_reducing_carrier.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS source Yukawa reducing carrier',result['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
