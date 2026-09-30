#!/usr/bin/env python3
"""Actual nonaxial theta-source propagation derivative with Noether completion.

The source derivative is generated from E1 and the field symmetry before the
whole-row response check. The primitive background is off shell; the source
on the nine complementary rows therefore varies. All other source coordinates
of the original theta projection are held fixed in the transported old slice.
"""
import hashlib
from functools import lru_cache
import json
from pathlib import Path
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix
import source
import ward

HERE=Path(__file__).resolve().parent
FQ=HERE.parent;BASE=FQ.parent
clean,encode=source.clean,source.encode
u,q,U=s.symbols('u q U',real=True)


def read(path):return json.loads(path.read_text())


def matrix(record,names=None):
    return s.SparseMatrix(*record['shape'],{(i,j):s.sympify(value,locals=names or {})
        for i,j,value in record['entries']})


def circle(certificate,parameter):
    L=s.SparseMatrix(289,289,{(i,j):sum(s.sympify(c)*parameter**n for n,c in enumerate(poly))/
        ((1+parameter**2)**4*certificate['field_constant_denominator'])
        for i,j,poly in certificate['field_numerator']})
    R=s.SparseMatrix(4,4,{(i,j):sum(s.sympify(c)*parameter**n for n,c in enumerate(poly))/
        (1+parameter**2)**2 for i,j,poly in certificate['spatial_numerator']})
    return clean(L),clean(R)


def components(M):
    neighbors=[set() for _ in range(M.rows)]
    for i,j in M.todok():
        if i!=j:neighbors[i].add(j);neighbors[j].add(i)
    seen=set();result=[]
    for i in range(M.rows):
        if i in seen:continue
        stack=[i];part=[];seen.add(i)
        while stack:
            j=stack.pop();part.append(j)
            for k in neighbors[j]-seen:seen.add(k);stack.append(k)
        result.append(sorted(part))
    return result


def rational_inverse(M):
    inverse=s.MutableSparseMatrix(M.rows,M.cols,{})
    blocks=components(M)
    for part in blocks:
        block=M.extract(part,part)
        domain=DomainMatrix.from_Matrix(block).convert_to(s.QQ_I)
        generated=domain.inv().to_Matrix()
        for i,row in enumerate(part):
            for j,col in enumerate(part):
                if generated[i,j]:inverse[row,col]=generated[i,j]
    result=s.SparseMatrix(inverse)
    assert clean(M*result-s.eye(M.rows))==s.zeros(M.rows)
    assert clean(result*M-s.eye(M.rows))==s.zeros(M.rows)
    return result,list(map(len,blocks))


def main():
    start=time.monotonic()
    actual=read(BASE/'active-gauge/receipt.json')
    primitive=read(HERE/'source.json');off=read(HERE/'ward.json')
    quotient=read(BASE/'active-gauge/quotient.json')
    propagation=read(BASE/'active-gauge/propagation.json')
    pole=read(FQ/'packet-field/pole-source.json')
    fields=read(FQ/'light-modes/field-receipt.json')
    rotation=read(BASE/'active-gauge/rotation/finite.json')
    for path,digest in actual['source_sha256'].items():
        assert hashlib.sha256((source.ROOT/path).read_bytes()).hexdigest()==digest
    rho=s.Rational(1,131072)
    y,z=s.Rational(1,5),s.Rational(1,3)
    Ly,Ry=circle(rotation['certificates'][1],y)
    Lz,Rz=circle(rotation['certificates'][2],z)
    L,rotation_space=clean(Lz*Ly),clean(Ry*Rz)
    V=clean(circle(rotation['certificates'][1],-y)[0]*circle(rotation['certificates'][2],-z)[0])
    assert clean(V*L)==s.eye(289) and clean(L*V)==s.eye(289)
    k=rotation_space.T*s.Matrix([0,0,0,s.sqrt(2)*rho])
    assert all(k[i]!=0 for i in [1,2,3]) and s.expand(sum(k[i]**2 for i in [1,2,3]))==2*rho**2
    N=s.sympify(actual['source_lapse']);clock=N*s.sqrt(2)
    lam=clock*(1-s.I)
    axis=[lam,0,0,s.I*s.sqrt(2)*rho]
    world=[lam,*[s.I*k[i] for i in [1,2,3]]]
    removed=quotient['fixed_section_removed_original_fields']
    retained=[i for i in range(289) if i not in removed]
    keep121=[i for i in range(121) if i not in removed]
    P=s.SparseMatrix(289,len(retained),{(i,j):1 for j,i in enumerate(retained)})
    assert keep121==list(range(9))+quotient['retained_original_fields']
    names={str(v):v for v in ward.p}
    Kformal=matrix(off['K0'],names);K1formal=matrix(off['K1'],names);Cformal=matrix(off['C1'],names)
    Hplus=ward.operator(actual['Fourier_Jacobi_entries'],values=axis)
    Hworld=ward.operator(actual['Fourier_Jacobi_entries'],values=world)
    assert clean(L.T*Hworld*L-Hplus)==s.zeros(289)
    Kaxis=clean(Kformal.subs(dict(zip(ward.p,axis))))
    Kworld=clean(Kformal.subs(dict(zip(ward.p,world))))
    K1world=clean(K1formal.subs(dict(zip(ward.p,world))))
    minor=Kaxis.extract(removed,range(9))
    minor_inv=minor.inv(method='DM')
    M=clean(minor_inv*(V*Kworld).extract(removed,range(9)))
    Mi=clean(M.inv(method='DM'))
    assert clean(V*Kworld-Kaxis*M)==s.zeros(289,9)
    K1hat=clean(V*K1world*Mi)
    Chat=clean(L.T*Cformal*Mi)
    H1hat=clean(L.T*ward.operator(primitive['H1'],values=world)*L)
    H2hat=clean(L.T*ward.operator(primitive['H2'],values=world)*L)
    scalarhat=clean(L.T*ward.operator(primitive['scalar_H1_completion'],values=world)*L)
    assert clean(H1hat*Kaxis+Hplus*K1hat+Chat)==s.zeros(289,9)

    F=s.Poly(s.sympify(fields['axial_source_factor'],locals={'u':u,'q':q}),u,q)
    assert all(a%2==0 and b%2==0 for (a,b),_ in F.terms())
    Fhat=s.Poly(sum(c*U**(a//2)*rho**b for (a,b),c in F.terms()),U,domain=s.QQ)
    radial=s.symbols('r',real=True)
    Fr=s.Poly(Fhat.as_expr().subs(U,rho**2*radial),radial)
    assert Fr.count_roots(s.Rational(3,4),s.Rational(4,5))==1
    assert s.gcd(Fhat,Fhat.diff()).degree()==0
    degree=Fhat.degree()
    print('PASS same-frame nonaxial source and complete theta-root domain',flush=True)

    def even(expression):
        polynomial=s.Poly(s.expand(expression),u)
        assert all(n%2==0 for (n,),_ in polynomial.terms())
        return sum(c*U**(n//2) for (n,),c in polynomial.terms())

    def coefficient_columns(record,sign):
        terms={}
        for i,_,value in record['entries']:
            expression=even(s.sympify(value,locals={'u':u,'q':q}).subs(q,sign*rho))
            for (power,),coefficient in s.Poly(expression,U,domain=s.EX).terms():terms[i,power]=coefficient
        return reduce_columns(s.SparseMatrix(289,1+max(j for i,j in terms),terms))

    @lru_cache(None)
    def power_remainder(power):
        remainder=s.Poly(U**power,U,domain=s.QQ).rem(Fhat)
        return {n:c for (n,),c in remainder.terms()}

    def reduce_columns(columns):
        result=s.MutableSparseMatrix(columns.rows,degree,{})
        for (i,power),coefficient in s.SparseMatrix(columns).todok().items():
            for n,c in power_remainder(power).items():result[i,n]+=coefficient*c
        return clean(result)

    D=even(s.sympify(pole['factor_D'],locals={'u':u,'q':q}).subs(q,rho))
    theta_den=s.expand(D*(lam**2-clock**2*U))
    assert s.gcd(s.Poly(theta_den,U,extension=s.I),Fhat).degree()==0
    # Every column below is a coefficient of U^j; common theta_den is retained.
    family_results=[];cache_inverse=None;family_columns=[]
    source_scalings=list(map(s.sympify,propagation['constant_diagonal_field_scaling']))
    scale_map=dict(zip(quotient['retained_original_fields'],source_scalings))
    scales=s.diag(*[s.Integer(1) if i<9 else scale_map[i] for i in keep121])
    for sign in [1,-1]:
        ax=[sign*v for v in axis];wv=[sign*v for v in world]
        H0=ward.operator(actual['Fourier_Jacobi_entries'],values=ax)
        H1=clean(L.T*ward.operator(primitive['H1'],values=wv)*L)
        H2=H2hat
        K0=clean(Kformal.subs(dict(zip(ward.p,ax))))
        Km=clean(Kformal.subs(dict(zip(ward.p,[-v for v in ax]))))
        Kworld0=clean(Kformal.subs(dict(zip(ward.p,wv))))
        assert clean(V*Kworld0-K0*M)==s.zeros(289,9)
        assert clean(H0*K0)==s.zeros(289,9)
        assert clean(H1*K0+H0*K1hat+Chat)==s.zeros(289,9)
        A=coefficient_columns(pole['pair_numerator_linear'],sign)
        B=coefficient_columns(pole['pair_numerator_constant'],sign)
        Z=coefficient_columns(pole['source_projection_numerator'],sign)
        X0=clean(sign*lam*A+B)
        Iraw=s.zeros(289,degree+1)
        Iraw[:,:degree]=lam**2*Z
        Iraw[:,1:]+= -clock**2*Z
        I0=reduce_columns(Iraw)
        assert clean(H0*X0-I0)==s.zeros(289,degree)
        assert X0.extract(removed,range(degree))==s.zeros(9,degree)
        assert clean(scalarhat*X0)==s.zeros(289,degree)
        assert clean(H2*X0)==s.zeros(289,degree)
        print('PASS original theta source and full scalar completion at sign',sign,flush=True)
        # Generate I1 from Noether E1 contact and original I0, not H1*X0.
        contact_rhs=clean(-K1hat.T*I0-Chat.T*X0)
        I1=s.zeros(289,degree)
        contact_values=clean(Km.extract(removed,range(9)).T.inv(method='DM')*contact_rhs)
        for i,row in enumerate(removed):I1[row,:]=contact_values[i,:]
        I1=clean(I1)
        assert I1.todok()
        assert clean(Km.T*I1+K1hat.T*I0+Chat.T*X0)==s.zeros(9,degree)
        force=clean(-H1*X0)
        current=H0;rhs=force;indices=list(range(289));steps=[]
        # Paid constant auxiliary inverses, with their nonzero source terms retained.
        for old in actual['algebraic_Schur_steps']:
            eliminated=old['eliminated_fields']
            erows=[indices.index(i) for i in eliminated]
            kept=[i for i in indices if i not in eliminated];krows=[indices.index(i) for i in kept]
            inverse=s.SparseMatrix(len(eliminated),len(eliminated),
                {(eliminated.index(i),eliminated.index(j)):s.sympify(value)
                 for i,j,value in old['algebraic_block_inverse']})
            assert clean(current.extract(erows,erows)*inverse)==s.eye(len(eliminated))
            right=current.extract(erows,krows);left=current.extract(krows,erows)
            particular=clean(inverse*rhs.extract(erows,range(degree)))
            back=clean(-inverse*right)
            steps.append((eliminated,kept,particular,back))
            rhs=clean(rhs.extract(krows,range(degree))-left*particular)
            current=clean(current.extract(krows,krows)+left*back)
            indices=kept
        assert indices==list(range(121))
        expected121=ward.operator(actual['primitive_121_Fourier_Jacobi_entries'],rows=289,cols=289,values=ax)[:121,:121]
        assert clean(current-expected121)==s.zeros(121)
        slice_matrix=current.extract(keep121,keep121)
        rational=clean(scales*slice_matrix*scales/N)
        print('generated paid auxiliary elimination and actual112 section',sign,flush=True)
        if sign==1:
            cache_inverse,block_sizes=rational_inverse(rational)
        else:
            assert clean(rational-original_rational.T)==s.zeros(112)
            cache_inverse=original_inverse.T
        invslice=clean(scales*cache_inverse*scales/N)
        assert clean(slice_matrix*invslice)==s.eye(112)
        reduced=clean(invslice*rhs.extract(keep121,range(degree)))
        X1=s.MutableSparseMatrix(289,degree,{})
        for i,row in enumerate(keep121):X1[row,:]=reduced[i,:]
        for eliminated,kept,particular,back in reversed(steps):
            values=clean(particular+back*X1.extract(kept,range(degree)))
            for i,row in enumerate(eliminated):X1[row,:]=values[i,:]
        X1=clean(X1)
        assert clean(H0*X1+H1*X0-I1)==s.zeros(289,degree)
        assert clean(H0*X1+H1*X0).todok() # Fixed old full source fails by exactly I1.
        assert clean(L.T*ward.operator(actual['Fourier_Jacobi_entries'],values=wv)*L-H0)==s.zeros(289)
        Xw0,Xw1,Iw0,Iw1=map(clean,[L*X0,L*X1,V.T*I0,V.T*I1])
        Hw0=ward.operator(actual['Fourier_Jacobi_entries'],values=wv)
        Hw1=ward.operator(primitive['H1'],values=wv)
        assert clean(Hw0*Xw1+Hw1*Xw0-Iw1)==s.zeros(289,degree)
        assert clean(ward.operator(primitive['scalar_H1_completion'],values=wv)*Xw0)==s.zeros(289,degree)
        assert clean(ward.operator(primitive['H2'],values=wv)*Xw0)==s.zeros(289,degree)
        if sign==1:original_rational=rational;original_inverse=cache_inverse
        family_columns.append((X0,X1,H1,I1))
        family_results.append({'frequency_sign':sign,'X0_numerator_coefficients':encode(Xw0),
            'X1_numerator_coefficients':encode(Xw1),'I0_numerator_coefficients':encode(Iw0),
            'I1_numerator_coefficients':encode(Iw1),
            'all289_first_variation_zero':True,'fixed_source_failure_equals_I1':True,
            'scalar_completion_and_reader_contact_annihilate_actual_theta_input':True,
            'nonzero_X1_rows':len(set(i for i,j in Xw1.todok())),
            'nonzero_I1_rows':len(set(i for i,j in Iw1.todok()))})
        print('PASS actual nonaxial theta propagation derivative, original289 rows',sign,
            'fieldrows',family_results[-1]['nonzero_X1_rows'],'source derivative rows',family_results[-1]['nonzero_I1_rows'],flush=True)

    xp,dp,Qp,_=family_columns[0];xm,dm,Qm,_=family_columns[1]
    assert clean(Qm-Qp.T)==s.zeros(289)
    def polynomial_pair(left,M,right):
        product=clean(left.T*M*right)
        values=s.zeros(1,2*degree-1)
        for (i,j),v in product.todok().items():values[0,i+j]+=v
        reduced=reduce_columns(values)
        return s.expand(sum(reduced[0,j]*U**j for j in range(degree)))
    first_leg=polynomial_pair(dm,Qp,xp)/2
    second_leg=polynomial_pair(xm,Qp,dp)/2
    contact=polynomial_pair(xm,2*H2hat,xp)/2
    total=s.expand(first_leg+second_leg+contact)
    assert contact==0 and total!=0
    # The generated reader has a single real radical factor. Remove it before
    # the rational-complex gcd; avoid reconstructing an algebraic number field
    # for huge, already expanded rational coefficients.
    radical=next(factor for factor in [s.Integer(1),s.sqrt(2),s.sqrt(15),s.sqrt(30)]
        if all(s.expand(coefficient/factor).is_number and
            s.re(s.expand(coefficient/factor)).is_Rational and s.im(s.expand(coefficient/factor)).is_Rational
            for _,coefficient in s.Poly(total,U,domain=s.EX).terms()))
    assert s.Poly(s.expand(total/radical),U,domain=s.QQ_I).gcd(Fhat).degree()==0
    print('PASS two propagation legs give nonzero actual scalar response; native reader contact zero on this theta input',flush=True)
    result={'scope':'STRIKE_NONAXIAL_THETA_SOURCE_PROPAGATION_DERIVATIVE_WITH_OFF_SHELL_NOETHER_COMPLETION',
        'source_sha256':actual['source_sha256'],'rho':str(rho),'quarterY':str(y),'quarterZ':str(z),
        'physical_momentum':list(map(str,k[1:,0])),'physical_lambda':str(s.expand(lam)),
        'positive_damping':str(s.re(lam)),'physical_energy':str(-s.im(lam)),
        'theta_root':'U=rho^2*r; complete original Fhat(U)=0; unique r in(3/4,4/5)',
        'complete_Fhat':str(Fhat.as_expr()),'common_theta_denominator':str(theta_den),
        'denominator_coprime_with_complete_factor':True,
        'scalar_column_convention':'row j is coefficient of U^j; all columns divided by common_theta_denominator',
        'transported_old_slice_removed_axis_coordinates':removed,
        'actual_normalized112_inverse_block_sizes':block_sizes,
        'source_definition':'all retained primitive source coordinates are held fixed in transported old slice; complementary9 source coordinates are generated by the off-shell Noether identity',
        'I1_generation':'K0(-p)^T I1=-K1(-p)^T I0-C1(-p)^T X0; I1_retained=0',
        'finite_family':'X_epsilon=P*(P^T H_epsilon P)^-1*P^T I0 locally; full source is the independently Noether-completed retained source, not frozen I0',
        'true_local_inverse_domain':'det(P^T H0 P)!=0 from actual paid168 and constructed112 double inverses; polynomial continuity generates a real epsilon neighborhood',
        'families':family_results,
        'two_leg_reader_response':{'first_numerator':str(s.expand(first_leg)),
            'second_numerator':str(s.expand(second_leg)),'contact_numerator':str(contact),
            'total_numerator':str(total),'denominator':'common_theta_denominator^2',
            'nonzero_on_complete_factor':True,'gcd_degree':0,
            'independent_minus_leg_not_Hilbert_conjugation':True},
        'scope_limits':'Finite primitive gauge/current propagation derivative with original Noether source completion; the quantum noise derivative is a separate same-source consumer.',
        'elapsed_seconds':round(time.monotonic()-start,3)}
    (HERE/'propagation.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS complete finite gauge kernel construction',result['elapsed_seconds'],flush=True)


if __name__=='__main__':main()
