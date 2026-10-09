#!/usr/bin/env python3
"""Independent source-to-original-action solve and both tree permutations."""
import argparse
import json
from pathlib import Path
import sympy as s
from sympy.polys.matrices import DomainMatrix


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True)
    root=parser.parse_args().root.resolve();base=root/'Verification/physics/low-energy-phenomenology';audit=base/'onshell-sources/audit'
    assert json.loads((audit/'source-receipt.json').read_text())['status']=='PASS'
    frozen=json.loads((base/'onshell-sources/receipt.json').read_text())
    exchange=json.loads((base/'matter-vertices/exchange.json').read_text());source=json.loads((base/'active-gauge/receipt.json').read_text())
    p=s.symbols('p0:4');symbols={str(x):x for x in p}
    def decode(record):return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(v,locals=symbols) for i,j,v in record['entries']})
    def clean(matrix):return s.SparseMatrix(matrix).applyfunc(s.expand)
    def equal(left,right):assert not clean(left-right).todok()
    j1=decode(frozen['first_transition_current']);j2=decode(frozen['second_transition_current'])
    transfer=decode(frozen['opposite_transfer']);ordered=exchange['source_field_indices']
    plus=dict(zip(p,transfer));minus=dict(zip(p,-transfer))
    def at(record,sub):return decode(record).subs(sub).applyfunc(s.simplify)
    def action(momentum):
        result=s.MutableSparseMatrix(289,289,{})
        for i,j,powers,value in source['Fourier_Jacobi_entries']:
            result[i,j]+=s.sympify(value)*s.prod(momentum[mu]**power for mu,power in enumerate(powers))
        return clean(result)
    Hp=action(transfer);Hm=action(-transfer);equal(Hm.T,Hp)
    Lp=at(exchange['canonical_field_lift'],plus);Lm=at(exchange['canonical_field_lift'],minus)
    # Reconstruct the dynamic operator from the original full action and its
    # already-certified actual field lift, rather than importing a target A.
    A=clean(Lm.T*Hp*Lp);Aminus=clean(Lp.T*Hm*Lm)
    equal(A,at(exchange['canonical_operator'],plus));equal(Aminus,at(exchange['canonical_operator'],minus))
    equal(Aminus.T,A)
    injection=s.SparseMatrix(289,97,{(row,col):1 for col,row in enumerate(ordered)})
    f1=clean(Lm.T*injection*j1);f2=clean(Lp.T*injection*j2)
    equal(f1,at(exchange['canonical_source_map'],plus)*j1)
    equal(f2,at(exchange['canonical_source_map'],minus)*j2)
    assert f1!=s.zeros(79,1) and f2!=s.zeros(79,1)

    # A nonzero determinant image certifies nonsingularity over the exact
    # original number field. The rational denominators are checked invertible.
    prime=1000000009
    assert s.isprime(prime)
    rt2=int(s.sqrt_mod(2,prime));rt15=int(s.sqrt_mod(15,prime));imag=int(s.sqrt_mod(-1,prime))
    assert rt2*rt2%prime==2 and rt15*rt15%prime==15 and imag*imag%prime==prime-1
    replacement={s.sqrt(2):rt2,s.sqrt(15):rt15,s.sqrt(30):rt2*rt15,s.I:imag}
    def residue(value):
        rational=s.sympify(s.expand(value).xreplace(replacement))
        assert rational.is_Rational,rational
        numerator,denominator=map(int,rational.as_numer_denom())
        assert denominator%prime!=0
        return numerator*pow(denominator,-1,prime)%prime
    matrix=[[residue(A[i,j]) for j in range(79)] for i in range(79)]
    determinant=1
    for col in range(79):
        row=next((row for row in range(col,79) if matrix[row][col]),None)
        assert row is not None
        if row!=col:matrix[row],matrix[col]=matrix[col],matrix[row];determinant=-determinant
        pivot=matrix[col][col];determinant=determinant*pivot%prime;inverse=pow(pivot,-1,prime)
        for row in range(col+1,79):
            coefficient=matrix[row][col]*inverse%prime
            if coefficient:
                for j in range(col+1,79):matrix[row][j]=(matrix[row][j]-coefficient*matrix[col][j])%prime
            matrix[row][col]=0
    assert determinant!=0
    x1=decode(frozen['canonical_dynamic_response']);equal(A*x1,f1)
    # Solve the other actual source at opposite transfer, which the candidate
    # does not store. This directly checks its second tree assignment.
    field=s.QQ.algebraic_field(s.sqrt(2),s.sqrt(15),s.I)
    dm=DomainMatrix.from_Matrix(Aminus).convert_to(field);rhs=DomainMatrix.from_Matrix(f2).convert_to(field)
    numerator,denominator=dm.solve_den(rhs,method='rref')
    assert denominator!=field.zero and dm*numerator==rhs*denominator
    x2=(numerator.to_Matrix()/field.to_sympy(denominator)).applyfunc(s.simplify)
    equal(Aminus*x2,f2)
    Cp=at(exchange['total_contact_kernel'],plus);Cm=at(exchange['total_contact_kernel'],minus);equal(Cm.T,Cp)
    Rp=at(exchange['contact_field_response'],plus);Rm=at(exchange['contact_field_response'],minus)
    response1=clean(Rp*j1+Lp*x1);response2=clean(Rm*j2+Lm*x2)
    equal(response1,decode(frozen['full_289_positive_green_response']))
    equal(Hp*response1,injection*j1);equal(Hm*response2,injection*j2)
    equal(Hp*(-response1)+injection*j1,s.zeros(289,1))
    assert clean(Hp*response1+injection*j1)!=s.zeros(289,1)
    d12=s.simplify((f2.T*x1)[0]);d21=s.simplify((f1.T*x2)[0])
    c12=s.simplify((j2.T*Cp*j1)[0]);c21=s.simplify((j1.T*Cm*j2)[0])
    assert d12==d21 and c12==c21
    assert d12==s.sympify(frozen['dynamic_bilinear']) and c12==s.sympify(frozen['local_bilinear'])
    direct=s.simplify(-(d12+d21+c12+c21)/2)
    assert direct==s.sympify(frozen['elastic_direct_tree_kernel'])
    assert s.simplify((j2.T*injection.T*response1)[0]-d12-c12)==0
    assert s.simplify((j1.T*injection.T*response2)[0]-d21-c21)==0
    half_only=-(d12+c12)/2;assert s.simplify(direct-half_only)!=0
    wrong_adjoint=s.simplify((f2.H*x1)[0]+(j2.H*Cp*j1)[0]);assert wrong_adjoint!=d12+c12
    pieces=[]
    for item in exchange['source_contact_terms']:
        value=s.simplify((j2.T*at(item['kernel'],plus)*j1)[0])
        pieces.append({'groups':item['groups'],'value':str(value)})
        if item['groups']!=['Lorentz']:assert value==0
    assert c12==-9*s.sqrt(30)/50
    assert c12==s.sympify(json.loads((audit/'source-receipt.json').read_text())['independent_axial_contact'])
    result={'status':'PASS','original_289_reconstructed_canonical_operator':True,
        'exact_number_field':'QQ(sqrt(2),sqrt(15),I)',
        'nonsingular_determinant_witness':{'prime':prime,'sqrt2':rt2,'sqrt15':rt15,'sqrt_minus1':imag,'determinant_image':int(determinant)},
        'both_nonzero_sources_solved':True,'both_original_289_source_responses_verified':True,
        'signed_transpose_reciprocity':True,'first_dynamic':str(d12),'second_dynamic':str(d21),
        'first_contact':str(c12),'second_contact':str(c21),'contact_pieces':pieces,'full_direct_coefficient':str(direct),
        'negative_controls':['positive_source_requires_negative_induced_field','one_assignment_leaves_wrong_half',
            'conjugate_transpose_cannot_replace_Fourier_signed_transpose'],
        'external_LSZ_normalization_identified':False}
    (audit/'exchange-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS original79 nonsingular number-field solve, both actual opposite-transfer sources and all289 rows',flush=True)
    print('PASS both -1/2 tree assignments, independent axial contact and signs; direct coefficient:',direct,flush=True)


if __name__=='__main__':main()
