#!/usr/bin/env python3
"""Original contact/quotient jets, actual moments, and a direct 3D lens integral."""
from fractions import Fraction as F
from math import comb,factorial,isqrt
import hashlib
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode=True
sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
CANDIDATE=HERE.parent
FQ=CANDIDATE.parent


def read(p):return json.loads(p.read_bytes())
def matrix(r):return s.Matrix(*r['shape'],lambda i,j:next((s.sympify(v) for a,b,v in r['entries'] if a==i and b==j),0))
def clean(v):return s.expand(v)


def main():
    began=time.monotonic()
    manifest=read(CANDIDATE/'construction.json')
    for name,digest in manifest['candidate_sha256'].items():
        assert hashlib.sha256((CANDIDATE/name).read_bytes()).hexdigest()==digest,name
    data=read(CANDIDATE/'bounds.json');shape=read(CANDIDATE/'shape.json')
    source=read(FQ/'packet-gauge-global-transfer/source.json')
    contact=read(FQ/'packet-gauge-reduced-contact/contact.json')
    probe=read(FQ/'packet-gauge-probe-laplace/bounds.json')
    quantum=read(FQ/'packet-gauge-probe-moments/integrals.json')
    grams={row['name']:row for row in quantum['all_two_probe_Gram_jets']}
    for i in range(3):
        for side in ['left','right']:
            assert all(F(v)==0 for part in ['real','imaginary']
                       for v in grams[f'N0_{side}_{i}']['raw'][part]['rational'])
        assert grams[f'N0_mixed_{i}{i}']['raw']==grams['N0_mixed_00']['raw']
        for j in range(3):
            if i!=j:
                assert all(F(v)==0 for part in ['real','imaginary']
                           for v in grams[f'N0_mixed_{i}{j}']['raw'][part]['rational'])
    k=s.Matrix(s.symbols('kx ky kz',real=True));d=s.Matrix(s.symbols('d1:4',real=True))
    U,T=s.symbols('U T',real=True);c=s.sympify(source['physical_clock']);z=6*c*(1-s.I)
    p=s.symbols('p0:4',real=True);q=s.symbols('q0:4',real=True);r=s.symbols('r0:4',real=True)
    chosen=next(v for v in contact['readers'] if v['reader']==[1,1])
    ids=data['active_original_coframe_fields'];idx={v:i for i,v in enumerate(ids)}
    native=s.zeros(len(ids));sub=dict(zip(p,[z,*[-s.I*(k[i]+d[i]) for i in range(3)]]))
    sub|=dict(zip(q,[0,*[s.I*d[i] for i in range(3)]]));sub|=dict(zip(r,[-s.conjugate(z)-z,0,0,0]))
    for i,j,text in chosen['native_contact_complete']['entries']:
        if i in idx and j in idx:
            native[idx[i],idx[j]]=s.expand(s.sympify(text,locals={str(v):v for v in [*p,*q,*r]}).subs(sub))
    Q0=native.subs(dict.fromkeys(d,0));Qj=[native.diff(v) for v in d]
    assert Q0==matrix(data['Q0']) and Qj==list(map(matrix,data['Q_physical_external_derivatives']))
    assert native==Q0+sum((d[i]*Qj[i] for i in range(3)),s.zeros(len(ids)))
    assert not any(v.has(*k) for v in native)
    assert Q0.H==Q0 and all(Q.H==-Q for Q in Qj)

    # Full source rational quotient, composed before extracting the jet.
    names={str(v):v for v in [*k,U,T]}
    sourceF=s.sympify(source['complete_Fhat'],locals=names)
    r0=s.cancel(-s.diff(sourceF,T)/s.diff(sourceF,U)).subs({U:0,T:0})
    assert r0==s.Rational(125,162)
    den=s.sympify(source['denominator_D'],locals=names)*(z*z-c*c*U)
    tables={name:{i:s.sympify(v,locals=names) for i,_,v in source['columns'][name]['global_numerator']['entries']} for name in ['A','B']}
    first=matrix(data['coframe_first_jet']);second=matrix(data['coframe_second_jet'])
    tau=s.Symbol('tau',real=True)
    directions=[s.eye(3)[:,i] for i in range(3)]+[s.eye(3)[:,i]+s.eye(3)[:,j] for i,j in [(0,1),(0,2),(1,2)]]
    for n in directions:
        t2=tau*tau*n.dot(n)/2
        comp={k[i]:tau*n[i] for i in range(3)}|{U:r0*t2,T:t2}
        denominator=s.Poly(s.expand(den.subs(comp,simultaneous=True)),tau)
        for j,row in enumerate(ids):
            raw=z*tables['A'].get(row,0)+tables['B'].get(row,0)
            numerator=s.Poly(s.expand(s.sympify(raw).subs(comp,simultaneous=True)),tau)
            coeff=[]
            for order in range(3):
                coeff.append(s.simplify((numerator.nth(order)-sum(denominator.nth(a)*coeff[order-a] for a in range(1,order+1)))/denominator.nth(0)))
            assert coeff[0]==0
            assert s.simplify(coeff[1]-(first*n)[j])==0
            target=sum(n[i]*n[l]*second[j,3*i+l] for i in range(3) for l in range(3))
            assert s.simplify(2*coeff[2]-target)==0
    actualT=(first.H*Q0*first).applyfunc(s.simplify)
    tau0=32041*s.sqrt(30)/31492800
    assert actualT==s.diag(-2*tau0,-tau0,-tau0)
    print('PASS original 12-variable contact and six quotient-generated coframe jets',flush=True)

    moments=probe['source_moment_upper_bounds']
    M,H=[list(map(s.Rational,moments[key])) for key in ['psi','Hpsi']]
    Nu,alpha=map(s.Rational,[moments['N'],moments['alpha']])
    timevar=s.Symbol('time',nonnegative=True);radius=s.Rational(1,20000)
    paid=[]
    for order in [2,3]:
        P=lambda m,v:sum(comb(m,j)*(Nu*timevar)**(m-j)*v[j] for j in range(m+1))
        B=s.Poly(s.expand(alpha*(2*P(order,H)+Nu*radius*P(order,M)+order*Nu*P(order-1,M))),timevar)
        integral=sum(value*s.factorial(a[0])/5**(a[0]+1) for a,value in B.terms())
        assert integral==s.Rational(probe['derivative_bounds'][order]['eta_ge5_probe_ball_B_bound'])
        assert integral==s.Rational(data['packet_vector_bounds'][order])
        assert integral>B.nth(0)/5
        paid.append({'order':order,'actual_position_moment_Laplace_bound':str(integral),'t0_over_damping_strictly_too_small':True})

    # A genuine non-axis 3D ball-lens integral. The polynomial uses the
    # original F1 and the actual b0/bi Gram form G+M x.y; G,M remain symbols.
    # This is an exact source-tangent control, not a substitute for the full
    # source whose remainder is bounded in the candidate.
    Hrotate=s.Matrix([[3,6,2],[6,-2,-3],[2,-3,6]])/7
    assert Hrotate.T*Hrotate==s.eye(3)
    n=Hrotate[:,2]
    xx,yy,zz,shift,R,hh=s.symbols('x y z shift R h',real=True)
    Gm,Mm=s.symbols('G M',real=True)
    coordinate=s.Matrix([xx,yy,zz]);physical=Hrotate*coordinate
    Qn=sum((n[i]*Qj[i] for i in range(3)),s.zeros(len(ids)))
    def pair(left,right,Q):
        field=((first*left).H*Q*(first*right))[0]
        return s.expand(s.re(s.expand(field*(Gm+Mm*left.dot(right)))))
    centred=pair(physical-shift*n/2,physical+shift*n/2,Q0+shift*Qn)
    assert s.expand(centred-centred.subs(shift,-shift))==0
    def lens(poly):
        result=0
        for (a,b,j,e),value in s.Poly(poly,xx,yy,zz,shift).terms():
            if a%2 or b%2 or j%2:continue
            angle=2*s.gamma(s.Rational(a+1,2))*s.gamma(s.Rational(b+1,2))/s.gamma(s.Rational(a+b+2,2))
            radial=hh*(R*R-hh*hh)**((a+b)//2)*2*(hh-shift/2)**(j+1)/(j+1)
            result+=value*shift**e*angle*s.integrate(s.expand(radial),(hh,shift/2,R))
        return s.expand(result/(2*s.pi)**3)
    def ball(poly):
        result=0
        for powers,value in s.Poly(poly,xx,yy,zz).terms():
            if any(e%2 for e in powers):continue
            m=sum(powers)//2
            moment=4*s.pi*R**(2*m+3)*s.prod(s.factorial2(e-1) for e in powers)/((2*m+3)*s.factorial2(2*m+1))
            result+=value*moment
        return s.expand(result/(2*s.pi)**3)
    actual=s.expand(lens(centred)/2)
    generated=s.Poly(actual,shift).nth(2)
    biform0=pair(physical,physical+tau*n,Q0)
    biform1=pair(physical,physical+tau*n,Qn)
    target=ball(s.diff(biform0,tau,2).subs(tau,0)/4+s.diff(biform1,tau).subs(tau,0)/2)
    assert s.simplify(generated-target)==0
    assert generated.subs(Mm,0)==0 and s.diff(generated,Mm)!=0
    body=ball(s.diff(centred,shift,2).subs(shift,0)/4)
    assert body.subs(Mm,0)!=0
    cusp=s.Poly(actual,shift).nth(1)
    assert s.simplify(s.diff(cusp,Gm)-R**4*tau0*(5+n[0]**2)/(64*s.pi**2))==0
    print('PASS direct three-dimensional nonaxis lens integral, true flux cancellation and nonzero packet-gradient term',flush=True)

    # Re-evaluate final bounds with independent integer-root and Machin
    # rational enclosures; consume the separately reviewed actual A bounds.
    precision=10**90
    root=lambda j:F(isqrt(j*precision*precision)+1,precision)
    def atan_interval(n):
        total=sum((F(-1) if j%2 else F(1))*F(1,n**(2*j+1)*(2*j+1)) for j in range(100))
        return total,total+F(1,n**201*201)
    a,b=atan_interval(5),atan_interval(239)
    pi_lo=16*a[0]-4*b[1]
    eps=F(source['source_root_control']['epsilon']);Bup=root(2)*eps
    def norm_entry(e):
        e=s.expand(e);total=F(0)
        for part in [s.re(e),s.im(e)]:
            part=s.expand(part)
            for radical,upper in [(s.sqrt(30),root(30)),(s.sqrt(15),root(15)),(s.sqrt(2),root(2))]:
                coeff=part.coeff(radical);assert coeff.is_Rational
                total+=abs(F(str(coeff)))*upper;part=s.expand(part-coeff*radical)
            assert part.is_Rational;total+=abs(F(str(part)))
        return total
    norm=lambda Q:max(sum(norm_entry(Q[i,j]) for j in range(Q.cols)) for i in range(Q.rows))
    q0=norm(Q0);qnorm2=sum(norm(Q)**2 for Q in Qj)
    q1=F(isqrt((qnorm2.numerator*precision**2)//qnorm2.denominator)+1,precision)
    a=data['actual_A_equals_F_tensor_packet_bounds']
    a1,a20,a2,a3=[F(a[name]) for name in ['A1_origin','A2_origin','A2_global','A3_global']]
    bound=(q0*(a2*a20/2+a1*a3+a2*a3*Bup/2)/4+q1*(3*a1*a2/2+a2*a2*Bup/2)/2)*Bup**5/(10*pi_lo*pi_lo)
    mother=F(data['absolute_q_squared_coefficient_bound']['rational'][1])
    assert bound<mother
    result={'verdict':'PASS','same_actual_contact_all_variables':True,'six_actual_quotient_directions':True,
        'true_B2_B3_from_original_position_moments':paid,'new_unit_direction':list(map(str,n)),
        'exact_source_tangent_lens_q2':str(generated),'direct_lens_equals_body_plus_flux':True,
        'omitted_flux_nonzero_actual_affine_control':str(body.subs(Mm,0)),
        'source_packet_gradient_term_retained':True,'actual_cusp_coefficient_checked':True,
        'source_tangent_Gram_G_plus_M_x_dot_y_paid':True,
        'independent_improved_q_squared_upper':str(bound),'mother_q_squared_upper':str(mother),
        'improved_bound_decimal':str(float(bound)),'new_Lean_declarations':0,
        'seconds':round(time.monotonic()-began,3)}
    for name,digest in manifest['candidate_sha256'].items():
        assert hashlib.sha256((CANDIDATE/name).read_bytes()).hexdigest()==digest,name
    (HERE/'independent.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS independent source/shape/whole-ball coefficient consumer',result['seconds'],flush=True)


if __name__=='__main__':main()
