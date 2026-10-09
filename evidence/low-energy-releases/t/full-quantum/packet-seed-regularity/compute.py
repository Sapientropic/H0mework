#!/usr/bin/env python3
"""Construct the source seed's frame-free polynomial and regularity bounds.

Strike producer only: finite source identities plus the explicit analytic
readout. It does not certify its own result or modify upstream data.
"""
import hashlib
import json
from math import isqrt
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
BASE=ROOT/'Verification/physics/low-energy-phenomenology'
FQ=BASE/'full-quantum'
u,q,U,T,r,nx,ny,nz,kx,ky,kz,y,z=s.symbols('u q U T r nx ny nz kx ky kz y z',real=True)


def read(path):return json.loads(path.read_text())


def matrix(record):
    entries={(i,j):s.sympify(value,locals={'u':u,'q':q}) for i,j,value in record['entries']}
    assert len(entries)==len(record['entries'])
    return s.SparseMatrix(*record['shape'],entries)


def clean(M):
    M=s.SparseMatrix(M)
    return s.SparseMatrix(M.rows,M.cols,{ij:value for ij,raw in M.todok().items()
        if (value:=s.expand(raw))!=0})


def ceiling(value):
    scalar,radical=s.expand(value).as_coeff_Mul()
    assert scalar.is_Rational
    if radical==1:return abs(scalar)
    square=s.expand(radical**2)
    assert square.is_Integer and square>0 and radical.is_positive
    top=isqrt(int(square))
    if top*top<square:top+=1
    return abs(scalar)*top


def abs_bound(value):
    real,imag=s.expand_complex(value).as_real_imag()
    return ceiling(s.expand(real))+ceiling(s.expand(imag))


def rounded(value):
    return s.ceiling(value*10**6)/10**6


def sqrt_upper(value):
    value=s.Rational(value)
    scale=10**6
    upper=isqrt(int(value.p)*scale*scale//int(value.q))
    if upper*upper*value.q<value.p*scale*scale:upper+=1
    answer=s.Rational(upper,scale)
    assert answer**2>=value
    return answer


def main():
    started=time.monotonic()
    paths={'actual':BASE/'active-gauge/receipt.json',
        'field':FQ/'light-modes/field-receipt.json',
        'circles':FQ/'packet-field/circle-data.json',
        'pole':FQ/'packet-field/pole-source.json',
        'generators':BASE/'active-gauge/rotation/generators.json',
        'finite':BASE/'active-gauge/rotation/finite.json',
        'bounds':FQ/'packet-field/field-data.json'}
    data={name:read(path) for name,path in paths.items()}
    actual=data['actual']
    for path,digest in actual['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    V=matrix(data['field']['axial_original289_pole_leg'])
    F=s.Poly(s.sympify(data['field']['axial_source_factor'],locals={'u':u,'q':q}),u,q,domain=s.QQ)
    clock=s.simplify(s.sqrt(2)*s.sympify(actual['source_lapse']))
    cf=F.coeff_monomial(u**2)
    odd=clean((V-V.subs(u,-u)).applyfunc(lambda expression:s.cancel(expression/(2*u))))
    A=clean(-clock/cf*odd)
    assert A==matrix(data['pole']['pair_numerator_linear'])
    D=s.cancel(s.diff(F.as_expr(),u)/(2*cf*u))
    C=[[matrix(entry) for entry in circle['coefficients']] for circle in data['circles']['circles']]
    G=[s.SparseMatrix(289,289,{(i,j):s.sympify(value) for i,j,value in row['field_generator']})
        for row in data['generators']['generators']]
    spatial=[s.Matrix([[s.sympify(value) for value in row] for row in entry['spatial_matrix']])
        for entry in data['generators']['generators']]
    eye=s.eye(289);zero=s.zeros(289,1)
    assert all(C[i][1]==4*G[i] for i in range(3))
    flip=sum(C[1],s.zeros(289))/16
    assert clean(flip*V-V.subs(q,-q))==zero
    assert clean(flip*A-A.subs(q,-q))==zero
    for degree,coefficient in enumerate(C[2]):
        expected=s.binomial(4,degree//2) if degree%2==0 else 0
        assert clean(coefficient*V-expected*V)==zero
        assert clean(coefficient*A-expected*A)==zero
    print('PASS actual Ly(1) reflection and all nine Lz stabilizer coefficients',flush=True)

    casimir=clean(-sum((generator*generator for generator in G),s.zeros(289)))
    assert clean(casimir*(casimir-2*eye)*(casimir-6*eye)*A)==zero
    projectors=[(casimir-2*eye)*(casimir-6*eye)/12,
        -casimir*(casimir-6*eye)/8,casimir*(casimir-2*eye)/24]
    Aj=[clean(P*A) for P in projectors]
    assert clean(sum(Aj,zero)-A)==zero
    B=[];descriptions=[]
    for j,part in enumerate(Aj):
        assert clean((casimir-j*(j+1)*eye)*part)==zero
        assert clean(G[2]*part)==zero
        entries={};count=0
        for (index,_),value in part.todok().items():
            terms=s.Poly(value,u,q).terms()
            assert all(a%2==0 and b>=j and (b-j)%2==0 for (a,b),_ in terms)
            entries[index,0]=s.expand(sum(c*U**(a//2)*T**((b-j)//2) for (a,b),c in terms))
            assert s.expand(q**j*entries[index,0].subs({U:u*u,T:q*q})-value)==0
            count+=len(terms)
        B.append(s.SparseMatrix(289,1,entries))
        descriptions.append({'j':j,'casimir_eigenvalue':j*(j+1),'nonzero_rows':len(entries),
            'source_terms':count,'exact_divisor':f'q^{j}',
            'remaining_variables':['U=u^2','T=q^2'],'zero_z_weight':True})
    assert all(clean(generator*B[0])==zero for generator in G)
    print('PASS source Casimir0/2/6 and exact q^j divisibility; no angular singular terms',flush=True)

    # Homogeneous sphere harmonics generated from the actual source zero-weight vectors.
    B0,B1,B2=B
    T1=clean(nz*B1+nx*G[1]*B1-ny*G[0]*B1)
    quadrupole=clean((G[1]*G[1]*B2+3*B2)/2)
    cross=clean(G[2]*quadrupole)
    T2=clean((2*nz*nz-nx*nx-ny*ny)/2*B2+nx*nz*G[1]*B2-
        ny*nz*G[0]*B2+(nx*nx-ny*ny)*quadrupole+nx*ny*cross)
    assert clean(T1.subs({nx:0,ny:0,nz:1})-B1)==zero
    assert clean(T2.subs({nx:0,ny:0,nz:1})-B2)==zero
    assert clean(sum((T2.diff(v,2) for v in [nx,ny,nz]),zero))==zero
    infinitesimal=[]
    normal=s.Matrix([nx,ny,nz])
    for axis in range(3):
        tangent=spatial[axis].extract([1,2,3],[1,2,3]).T*normal
        for j,tensor in enumerate([B0,T1,T2]):
            directional=sum((tangent[i]*tensor.diff(v) for i,v in enumerate([nx,ny,nz])),zero)
            assert clean(directional-G[axis]*tensor)==zero,(axis,j)
            infinitesimal.append({'axis':axis,'j':j,'entire_polynomial_identity':True})
    print('PASS all nine full polynomial generator-equivariance identities',flush=True)

    # Literal source-circle identity, independently retaining every native coefficient.
    n=s.Matrix([0,0,0,1])
    finite=data['finite']['certificates']
    def spatial_numerator(axis,parameter):
        return s.SparseMatrix(4,4,{(i,j):sum(c*parameter**power for power,c in enumerate(poly))
            for i,j,poly in finite[axis]['spatial_numerator']})
    Rnum=spatial_numerator(1,y)*spatial_numerator(2,z)
    nnum=(Rnum.T*n)[1:4,0]
    denominator=(1+y*y)**2*(1+z*z)**2
    n1,n2,n3=map(s.expand,nnum)
    expected=clean(denominator**2*B0+q*denominator*(n3*B1+n1*G[1]*B1-n2*G[0]*B1)+
        q*q*((2*n3*n3-n1*n1-n2*n2)/2*B2+n1*n3*G[1]*B2-
            n2*n3*G[0]*B2+(n1*n1-n2*n2)*quadrupole+n1*n2*cross))
    expected=expected.subs({U:u*u,T:q*q})
    lhs={}
    yvectors=[coefficient*A for coefficient in C[1]]
    for iz,cz in enumerate(C[2]):
        for iy,ay in enumerate(yvectors):
            vector=clean(cz*ay)
            for (index,_),value in vector.todok().items():lhs[index,iy,iz]=value
    slots=0
    for index in range(289):
        coefficients=s.Poly(s.expand(expected[index]),y,z).as_dict()
        assert all(iy<9 and iz<9 for iy,iz in coefficients)
        for iy in range(9):
            for iz in range(9):
                left=lhs.get((index,iy,iz),0)
                right=coefficients.get((iy,iz),0)
                assert s.expand(left-right)==0,(index,iy,iz)
                if left!=0 or right!=0:slots+=1
    print('PASS actual two-circle all-parameter equality to homogeneous direction polynomials',slots,flush=True)

    # Seed uses ell(-k): odd spatial terms change sign. Absorb every q^j n^j.
    seed_numerator=clean(B0-
        (kz*B1+kx*G[1]*B1-ky*G[0]*B1)/s.sqrt(2)+
        (2*kz*kz-kx*kx-ky*ky)/4*B2+(kx*kz/2)*G[1]*B2-
        (ky*kz/2)*G[0]*B2+(kx*kx-ky*ky)/2*quadrupole+(kx*ky/2)*cross)
    # Along the actual negative axial momentum this is precisely A/D's numerator.
    assert clean(seed_numerator.subs({kx:0,ky:0,kz:s.sqrt(2)*q,U:u*u,T:q*q})-A.subs(q,-q))==zero
    assert clean(s.conjugate(seed_numerator)-seed_numerator.subs({kx:-kx,ky:-ky,kz:-kz},simultaneous=True))==zero
    denominator_poly=s.Poly(D,u,q,domain=s.QQ)
    assert all(a%2==b%2==0 for (a,b),_ in denominator_poly.terms())
    Dhat=s.Poly(sum(c*U**(a//2)*T**(b//2) for (a,b),c in denominator_poly.terms()),U,T,domain=s.QQ)
    assert Dhat.eval({U:0,T:0})==1
    origin=clean(seed_numerator.subs({kx:0,ky:0,kz:0,U:0,T:0}))
    center=-F.coeff_monomial(q*q)/cf
    orientation=s.symbols('orientation',real=True)
    pole_origin=s.zeros(289,1)
    for (index,_),expression in V.todok().items():
        first_degree=[(a,b,c) for (a,b),c in s.Poly(expression,u,q).terms() if a+b==1]
        pole_origin[index]=s.simplify(-sum(clock*c*(sigma*s.sqrt(center))**a*orientation**b/
            (2*cf*sigma*s.sqrt(center)) for sigma in [1,-1] for a,b,c in first_degree))
    assert clean(origin-pole_origin)==zero
    assert all(clean(generator*origin)==zero for generator in G)
    print('PASS frame-free full-ball seed formula, physical k factors, Fourier reality and origin extension',flush=True)

    source_bounds=data['bounds']['root']
    eps=s.Rational(source_bounds['epsilon'])
    low,high=map(s.Rational,source_bounds['window'])
    P=s.Poly(s.sympify(source_bounds['root_remainder'],locals={'r':r,'w':T}),r,T,domain=s.QQ)
    # The source remainder also changes explicitly with T; retain P+T*P_T.
    root_derivative_numerator=s.Poly(P.as_expr()+T*P.diff(T).as_expr(),r,T,domain=s.QQ)
    root_derivative_bound=s.Rational(40,39)*sum(abs(c)*eps**(2*j)
        for (i,j),c in root_derivative_numerator.terms())
    U_derivative_bound=high+eps**2*root_derivative_bound
    assert U_derivative_bound<1
    Fhat=s.Poly(sum(c*U**(a//2)*T**(b//2) for (a,b),c in F.terms()),U,T,domain=s.QQ)
    # The two implicit derivative formulae agree after the original root equation.
    original_root=s.expand(r-center+T*P.as_expr())
    cleared=s.expand(Dhat.as_expr().subs(U,T*r)*r-
        T*root_derivative_numerator.as_expr()+Fhat.diff(T).as_expr().subs(U,T*r)/cf)
    assert s.expand(cleared-original_root)==0
    assert s.expand(Dhat.as_expr()-Fhat.diff(U).as_expr()/cf)==0
    kbound=2*eps # rational upper bound for sqrt(2)*eps
    variables=(kx,ky,kz,U,T)
    def polynomial_bound(expression):
        return sum(abs_bound(c)*kbound**(a+b+d)*eps**(2*(e+f))
            for (a,b,d,e,f),c in s.Poly(s.expand(expression),*variables).terms())
    den_U=sum(abs(c)*eps**(2*(a+b)) for (a,b),c in Dhat.diff(U).terms())
    den_T=sum(abs(c)*eps**(2*(a+b)) for (a,b),c in Dhat.diff(T).terms())
    den_gradient=kbound*(U_derivative_bound*den_U+den_T)
    field_rows=[];value_square=gradient_square=0
    for (index,_),expression in seed_numerator.todok().items():
        bound=polynomial_bound(expression)
        value_bound=rounded(s.Rational(40,39)*bound)
        radial_u=polynomial_bound(s.diff(expression,U))
        radial_t=polynomial_bound(s.diff(expression,T))
        gradient_bounds=[]
        for coordinate in [kx,ky,kz]:
            deriv_bound=polynomial_bound(s.diff(expression,coordinate))+kbound*(U_derivative_bound*radial_u+radial_t)
            result=rounded(s.Rational(40,39)*deriv_bound+s.Rational(40,39)**2*bound*den_gradient)
            gradient_bounds.append(result)
        value_square+=value_bound**2
        gradient_square+=sum(v*v for v in gradient_bounds)
        field_rows.append({'index':index,'field':actual['fields'][index],
            'numerator':str(expression),'value_uniform_bound':str(value_bound),
            'physical_k_gradient_uniform_bounds':list(map(str,gradient_bounds))})
    # Omitting the signed-q flip is a real seam error on the actual source root.
    seam_error=clean(flip*A-A)
    assert seam_error==clean(-2*Aj[1])
    sample=s.Rational(1,131072)
    Fs=s.Poly(F.as_expr().subs(q,sample),u,domain=s.QQ)
    assert Fs.count_roots(4*sample/5,sample)==1 and s.gcd(Fs,Fs.diff()).degree()==0
    seam_witness=None
    for (index,_),expression in seam_error.todok().items():
        candidate=s.Poly(s.expand(expression.subs(q,sample)),u)
        leading=candidate.LC()
        rational={power:s.cancel(s.radsimp(coefficient/leading)) for power,coefficient in candidate.terms()}
        if all(coefficient.is_Rational for coefficient in rational.values()):
            reduced=s.Poly.from_dict(rational,u,domain=s.QQ)
            if s.gcd(reduced,Fs).degree()==0:
                seam_witness=index
                break
    assert seam_witness is not None
    result={'scope':'STRIKE_ORIGINAL_SEED_FRAME_FREE_SMOOTH_EXTENSION_AND_INNER_BALL_H1',
        'source_sha256':actual['source_sha256'],
        'input_sha256':{str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in paths.values()},
        'source_seed':'W(k)=-sum_sigma ell_sigma(-k)=transported A/D, A=-c/cF*Vodd',
        'exact_reflection':{'Ly_1_V_equals_V_at_minus_q':True,'Ly_1_A_equals_A_at_minus_q':True,
            'all_nine_Lz_stabilizer_coefficients':True},
        'angular_source_decomposition':descriptions,'generator_equivariance':infinitesimal,
        'two_circle_finite_identity':{'all_field_slots':289*81,'nontrivial_slots':slots,
            'angle_parameters':'all real y,z','field_order':'Lz(z)Ly(y)',
            'spatial_direction':'(Ry(y)Rz(z))^T e3',
            'frame_free_polynomial_degree':2},
        'actual_seed_formula':{'physical_variables':['kx','ky','kz'],'T':'|k|^2/2',
            'U':'T*sourceRoot.axialPhase.root(T)', 'denominator':str(Dhat.as_expr()),
            'numerator_variables':['kx','ky','kz','U','T'],
            'own_clock':str(clock),'source_coefficient':str(cf),
            'opposite_momentum_already_in_numerator':True,
            'entire_seed_Fourier_reality_checked':True,'origin_denominator':1,
            'origin_equals_actual_cancelled_two_pole_value_for_every_orientation':True,
            'origin_fixed_by_all_three_generators':True,
            'origin_nonzero_entries':[[i,str(value)] for (i,_),value in sorted(origin.todok().items())]},
        'source_root_control':{'epsilon':str(eps),'r_window':[str(low),str(high)],
            'D_lower':'39/40','D_upper':'41/40',
            'r_prime_formula':'-(P(r,T)+T*P_T(r,T))/(1+T*P_r(r,T))',
            'r_prime_numerator':str(root_derivative_numerator.as_expr()),
            'r_prime_uniform_bound':str(root_derivative_bound),
            'U_prime_formula':'r+T*r_prime','U_prime_uniform_bound':str(U_derivative_bound),
            'complete_F_implicit_derivative_identity':'U_prime=-Fhat_T/Fhat_U on the same original root',
            'complete_F_derivative_identity_checked':True,
            'U_prime_uniform_bound_less_than_one':True},
        'field_dimension':289,'unlisted_seed_rows_are_identically_zero':True,
        'fields':field_rows,'nonzero_frame_free_rows':len(field_rows),
        'uniform_bounds':{'sum_component_value_bounds_squared':str(value_square),
            'sum_physical_gradient_bounds_squared':str(gradient_square),
            'euclidean_W_bound':str(sqrt_upper(value_square)),
            'physical_jacobian_Frobenius_bound':str(sqrt_upper(gradient_square)),
            'inner_ball_global_Lipschitz_W_bound':str(sqrt_upper(gradient_square)),
            'maximum_value_coordinate':str(max(s.Rational(row['value_uniform_bound']) for row in field_rows)),
            'maximum_gradient_coordinate':str(max(s.Rational(v) for row in field_rows for v in row['physical_k_gradient_uniform_bounds']))},
        'negative_control':{'omitted_signed_q_flip_equals_minus_twice_j1':True,
            'actual_q':str(sample),'source_root_unique_and_simple':True,
            'witness_row':seam_witness,'gcd_with_complete_source_factor':0,
            'wrong_pair_gluing_differs_on_every_source_root_at_sample':True},
        'regularity_consequence':'The same source root is analytic locally by its generated simple derivative; the explicit numerator and nonzero denominator therefore make W analytic on a neighborhood of the closed light ball, including the origin. It is independent of Borel frame choices. In particular W and all physical first derivatives are bounded and W belongs to H1 of the inner ball.',
        'window_scope':'Multiplication by the sharp ball indicator is not claimed to preserve whole-space H1; the boundary trace is retained for the separate window responsibility.',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS source seed regularity construction',result['elapsed_seconds'],
        'rows',len(field_rows),'bounds',result['uniform_bounds'],flush=True)


if __name__=='__main__':main()
