#!/usr/bin/env python3
"""Independent static source residue and all-direction charge readback audit.

No candidate program is imported. The two-dimensional residue is generated
from the actual canonical operator's Schur coefficient. The twelve-source
response is checked in all original289 rows, with independent block inverses.
"""
import argparse
import json
from pathlib import Path
import sympy as s


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def equal(left,right):
    assert left.shape==right.shape
    assert all(s.cancel(x)==0 for x in s.SparseMatrix(left-right).todok().values())


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    root=parser.parse_args().root.resolve()
    base=root/'Verification/physics/low-energy-phenomenology'
    folder=base/'charge-response'
    frozen=json.loads((folder/'receipt.json').read_text())
    assert frozen==json.loads(Path('/tmp/charge-response-audit-replay.json').read_text())
    original=json.loads((base/'active-gauge/receipt.json').read_text())
    exchange=json.loads((base/'matter-vertices/exchange.json').read_text())
    canonical=json.loads((base/'canonical-active/receipt.json').read_text())
    soft=json.loads((base/'soft-phase/receipt.json').read_text())
    quotient=json.loads((base/'active-gauge/quotient.json').read_text())
    propagation=json.loads((base/'active-gauge/propagation.json').read_text())
    finite=json.loads((base/'active-gauge/rotation/finite.json').read_text())
    p=s.symbols('p0:4');q=s.Symbol('q',real=True)
    qs=s.symbols('q1:4',real=True)
    z=s.Symbol('z',real=True)
    lam,k=s.symbols('lam k',real=True)
    locals_={str(x):x for x in (*p,*qs,q,z,lam,k)}
    def decode(record,rows=None,cols=None):
        if isinstance(record,dict):rows,cols=record['shape'];record=record['entries']
        return s.SparseMatrix(rows,cols,{(i,j):s.sympify(v.replace('lambda','lam'),locals=locals_) for i,j,v in record})
    def polynomial(record,rows,cols):
        out=s.MutableSparseMatrix(rows,cols,{})
        for i,j,powers,v in record:
            out[i,j]+=s.sympify(v)*s.prod(x**degree for x,degree in zip(p,powers))
        return clean(out)
    def homogeneous(matrix,degree):
        out={}
        for position,value in s.SparseMatrix(matrix).todok().items():
            terms=sum(coefficient*s.prod(v**a for v,a in zip(qs,powers))
                for powers,coefficient in s.Poly(value,*qs).terms() if sum(powers)==degree)
            if terms:out[position]=terms
        return s.SparseMatrix(*matrix.shape,out)
    n=s.sympify(original['source_lapse'])
    assert n>0 and n**2==s.Rational(54,125)
    at_zero=dict.fromkeys(p,0)
    static=dict(zip(p,(0,0,0,s.I*s.sqrt(2)*q)))
    spatial=dict(zip(p,(0,*[s.I*s.sqrt(2)*v for v in qs])))
    H=polynomial(original['Fourier_Jacobi_entries'],289,289)
    F=decode(exchange['full_polynomial_field_change'])
    Fi=decode(exchange['full_polynomial_inverse'])
    A79=decode(canonical['canonical_quotient_operator'],79,79)
    equal(A79,decode(exchange['canonical_operator']))
    S=s.diag(*[s.sympify(x) for x in soft['field_scaling']])
    P=decode(soft['constant_phase_basis'])
    heavy=soft['heavy_indices']
    assert len(heavy)==77
    E=s.SparseMatrix(79,77,{(row,col):1 for col,row in enumerate(heavy)})
    T=P.row_join(E)
    Tinv=decode(soft['phase_and_heavy_basis_inverse'])
    equal(T*Tinv,s.eye(79));equal(Tinv*T,s.eye(79))
    G=clean(S*A79.subs(spatial)*S/n)
    G0=G.subs(dict.fromkeys(qs,0))
    equal(G0*P,s.zeros(79,2))
    D0=E.T*G0*E
    Dinv=decode(soft['heavy_origin_inverse'])
    equal(D0*Dinv,s.eye(77));equal(Dinv*D0,s.eye(77))
    LL=clean(P.T*G*P);C=clean(P.T*G*E);B=clean(E.T*G*P)
    equal(homogeneous(LL,0),s.zeros(2));equal(homogeneous(LL,1),s.zeros(2))
    equal(homogeneous(C,0),s.zeros(2,77));equal(homogeneous(B,0),s.zeros(77,2))
    leading=clean(homogeneous(LL,2)-homogeneous(C,1)*Dinv*homogeneous(B,1))
    h2=s.diag(s.Rational(160,67),s.Rational(2500,81))
    equal(leading,sum(v*v for v in qs)*h2)
    assert h2.det()!=0
    # D0 invertible and T invertible prove exactly two soft directions.
    equal(T.T*G0*T,s.diag(s.zeros(2),D0))
    source_indices=exchange['source_field_indices']
    I97=s.SparseMatrix(289,97,{(row,col):1 for col,row in enumerate(source_indices)})
    Z=decode(soft['source_phase_columns_289'])
    assert all(original['fields'][i]['group'] in ('primal_H','dual_H') for i,j in Z.todok())
    U0=clean(F[:,9:88].subs(at_zero)*S*P)
    shift=clean(Fi.subs(at_zero)*(U0-Z))
    equal(shift[:112,:],s.zeros(112,2));equal(shift[121:,:],s.zeros(168,2))
    Bnull=shift[112:121,:]
    equal(Bnull,decode(frozen['source_null_phase_shift']))
    assert Bnull.todok()=={(2,0):2,(2,1):2}
    Cnull=decode(exchange['local_source_compatibility_map'])
    equal(U0-Z,F[:,112:121].subs(at_zero)*Bnull)
    equal(Z.T*I97,s.zeros(2,97))
    source_light=clean(P.T*S*F[:,9:88].subs(at_zero).T*I97)
    equal(source_light,U0.T*I97)
    equal(source_light,Bnull.T*Cnull.subs(at_zero))
    # The Schur inverse's q^-2 coefficient has only its light-light block:
    # cross blocks vanish at0, D^-1 is analytic and the light leading form is invertible.
    R9=clean(Bnull*h2.inv()*Bnull.T/n)
    assert R9.todok()=={(2,2):s.Rational(9023,5000)/n}
    residue=clean(source_light.T*h2.inv()*source_light/n)
    equal(R9,decode(frozen['canonical_residue_factor_through_null_constraints']))
    equal(residue,decode(frozen['canonical_q_squared_source_inverse_residue']))
    equal(residue,Cnull.subs(at_zero).T*R9*Cnull.subs(at_zero))
    nullspace=s.Matrix(Cnull.subs(at_zero)).nullspace()
    nullbasis=s.SparseMatrix.hstack(*nullspace)
    equal(Cnull.subs(at_zero)*nullbasis,s.zeros(9,len(nullspace)))
    equal(residue*nullbasis,s.zeros(97,len(nullspace)))
    assert residue!=s.zeros(97)
    print('PASS actual all-spatial Schur leading form, exactly2 soft directions, original null phase shift and97-source residue',flush=True)

    fields=[i for i,f in enumerate(original['fields']) if f['group']=='gauge_A' and f['coordinate'][0]==0]
    assert fields==frozen['source_fields'] and len(fields)==12
    columns=[source_indices.index(i) for i in fields]
    equal(Cnull[:,columns].subs(static),s.zeros(9,12))
    equal(decode(exchange['independent_dual_source_map'])[:,columns],s.zeros(24,12))
    equal(residue[:,columns],s.zeros(97,12))
    kept=quotient['retained_original_fields']
    K=decode(quotient['quotient_operator_103_by_103'],103,103).subs({lam:0,k:s.sqrt(2)*q})
    scalings=[s.sympify(v) for v in propagation['constant_diagonal_field_scaling']]
    scale=s.diag(*scalings)
    normalized=clean(scale*K*scale/n)
    rows=[kept.index(i) for i in fields]
    expected=s.zeros(103,12)
    active_blocks=[]
    for block in propagation['blocks']:
        indices=block['quotient_indices']
        selected=[col for col,row in enumerate(rows) if row in indices]
        if not selected:continue
        outside=[i for i in range(103) if i not in indices]
        equal(K[indices,outside],s.zeros(len(indices),len(outside)))
        equal(K[outside,indices],s.zeros(len(outside),len(indices)))
        # Direct inverse differs from the candidate's polynomial solve_den method.
        raw=normalized[indices,indices]
        inverse=raw.inv(method='DM').applyfunc(s.cancel)
        equal(raw*inverse,s.eye(len(indices)));equal(inverse*raw,s.eye(len(indices)))
        for col in selected:
            for j,row in enumerate(indices):
                expected[row,col]=s.cancel(scalings[row]*inverse[j,indices.index(rows[col])]*scalings[rows[col]]/n)
        active_blocks.append([len(indices),len(selected)])
        print('PASS independent static block inverse',len(indices),'sources',len(selected),flush=True)
    assert active_blocks==[[2,1],[2,1],[16,2],[16,2],[30,2],[33,4]]
    I103=s.SparseMatrix(103,12,{(row,col):1 for col,row in enumerate(rows)})
    equal(K*expected,I103)
    full=decode(frozen['full_289_field_green_columns'])
    equal(full[kept,:],expected)
    injection=s.SparseMatrix(289,12,{(row,col):1 for col,row in enumerate(fields)})
    Haxis=H.subs(static)
    equal(Haxis*full,injection)
    assert clean(Haxis*full+injection)!=s.zeros(289,12)
    # Each source-free auxiliary equation independently fixes the auxiliary response.
    for step in original['algebraic_Schur_steps']:
        indices=step['eliminated_fields']
        equal(Haxis[indices,:]*full,s.zeros(len(indices),12))
    R=full[fields,:].applyfunc(s.cancel)
    equal(R,decode(frozen['static_charge_inverse_response']))
    equal(R.subs(q,-q).T,R)
    denominators=sorted(set(str(s.factor(s.denom(value))) for value in R))
    assert all(s.sympify(den,locals=locals_).subs(q,0)!=0 for den in denominators)
    R0=R.subs(q,0)
    equal(R0,decode(frozen['static_charge_zero_limit']))
    equal((q*q*R).applyfunc(lambda value:s.limit(value,q,0)),s.zeros(12))
    assert any(s.degree(s.denom(value),q)>0 for value in R)
    print('PASS complete original289 forced rows, original12-source normalization,144 regular readouts and retained finite-momentum denominators',flush=True)

    positions={row:i for i,row in enumerate(fields)}
    U=[];bounds=[]
    for entry,output,bound_output in zip(finite['certificates'],frozen['finite_charge_rotations'],frozen['uniform_entrywise_rotation_bounds']):
        current=s.zeros(12);bound=s.zeros(12)
        d=s.sympify(entry['field_constant_denominator']);assert d>0
        for i,j,coeffs in entry['field_numerator']:
            assert (i in positions)==(j in positions)
            if i not in positions:continue
            assert len(coeffs)<=9
            current[positions[i],positions[j]]=sum(s.sympify(c)*z**m for m,c in enumerate(coeffs))/(d*(1+z*z)**4)
            bound[positions[i],positions[j]]=sum(abs(s.sympify(c)) for c in coeffs)/d
        equal(current,decode(output));equal(bound,decode(bound_output))
        equal(current*current.subs(z,-z),s.eye(12));equal(current.subs(z,-z)*current,s.eye(12))
        assert all(value>=0 for value in bound)
        U.append(current);bounds.append(bound)
    # The source slice is invariant in both directions, so the field congruence
    # transports the physical source readout as U R U^T, with the same +/-p frame.
    oblique=U[1].subs(z,s.Rational(1,2))
    difference=clean(oblique*R0*oblique.T-R0)
    equal(difference,decode(frozen['nonzero_directional_difference_of_finite_charge_limit']))
    assert difference!=s.zeros(12)
    # The two-circle field order is Sz(z) Sy(y); these bounds are independent of y,z.
    composed_bound=bounds[2]*bounds[1]
    worst=max(composed_bound)
    assert worst>0
    witness=next(((i,j,str(value)) for (i,j),value in difference.todok().items()))
    print('PASS actual12-source invariant slice, finite inverse rotations, degree8 uniform bound and nonzero angular finite-limit control',flush=True)
    result={
        'status':'PASS','fresh_frozen_JSON_equal':True,
        'classification':'subordinate original-background classical static source response',
        'unchanged_root':'positiveSmoothUnifiedSource / Dirac-dual / actual / visit10 tick16 -> visit11 tick17',
        'exact_soft_dimension':2,'heavy_origin_dimension':77,
        'all_spatial_Schur_leading':'N*(q1^2+q2^2+q3^2)*diag(160/67,2500/81)',
        'heavy_light_cross_at_zero':False,'source_pure_matter_Z_annihilates_I97':True,
        'null_shift_nonzero_entries':[[2,0,2],[2,1,2]],
        'R9_only_entry':'R9[2,2]=9023/(5000*N)',
        'canonical_source_residue_factors_through_original_null_constraint':True,
        'null_compatible_origin_source_dimension':len(nullspace),
        'regular_compatible_source_quantifier':'j(q) has a finite limit and Cnull(q)j(q)=0 near0; only q^-2 canonical residue asserted zero',
        'original_static_gauge_source_count':12,'independent_dual_complement_source_zero':True,
        'independently_inverted_source_blocks':active_blocks,
        'all289_forced_equations':True,'source_sign':'plus j*A0 gives induced field minus FieldGreen*j',
        'all144_charge_readout_entries_regular_at_zero':True,
        'charge_readout_denominators':denominators,
        'finite_k_denominators_retained':True,
        'all3_finite_rotations_and_reverse_checked':True,
        'entry_bound':'sum(abs(coefficients))/positive_constant; abs(z^m)/(1+z^2)^4<=1 for0<=m<=8',
        'two_circle_composed_entry_bound':str(worst),
        'angular_finite_limit_is_not_constant_witness':list(witness),
        'all_real_direction_radial_squared_charge_residue_zero':True,
        'physical_modes_or_quantum_no_go_claimed':False}
    (folder/'audit/independent-receipt.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
