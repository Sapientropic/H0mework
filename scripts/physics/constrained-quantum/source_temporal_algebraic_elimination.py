#!/usr/bin/env python3
"""Complete temporal stationary branch from thirteen source invariants.

The spatial coframe is absorbed into original native Gram readouts. Three
shift variables are solved by a source-unit 3x3 matrix, leaving two scalar
algebraic equations, or one scalar equation with a regular explicit radical.
Every step concerns the classical reduced symbol; no noncommuting operator
inverse or square root is silently substituted for this source elimination.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from retained_hamiltonian_reduction import DOMAIN
from source_spatial_active_phase_splice import field_element
from source_gauge_legendre import SourceGaugeLegendre
from source_lorentz_contact import PAIRS, ETA, equal, encode
from source_coframe_legendre import rational
from source_quantum_temporal_symbol import (EPS, N, SYM, Jet, inv3, product,
    symmetric, expression_jet, original_compressed_hamiltonian)

C_SOURCE=s.Rational(162,625)
LAMBDA_SOURCE=6*C_SOURCE
J2=s.Matrix([[1,0],[-1,s.Rational(18,5)]])


def cross(v):
    return s.Matrix([[0,-v[2],v[1]],[v[2],0,-v[0]],[-v[1],v[0],0]])


def zero(value): assert s.cancel(value)==0


def original_gram_reduction():
    """All coefficients of the original source Hodge, at generic sixq/foury."""
    model=SourceGaugeLegendre()
    n=s.Symbol('n',positive=True);b=s.Matrix(s.symbols('b1:4',real=True))
    q=[s.Symbol('q'+str(i),positive=True)if i in(0,2,5)else s.Symbol('q'+str(i),real=True)for i in range(6)]
    L=s.Matrix([[q[0],0,0],[q[1],q[2],0],[q[3],q[4],q[5]]])
    Li=rational(L.inv());determinant=L.det();delta=n**2-(b.T*b)[0]
    e=s.diag(n,1,1,1);e[1:,0]=b;e[1:,1:]=L
    raw=rational(model.at(model.kernel_numerator,e)/e.det())
    P0=((delta*s.eye(3)+b*b.T)/(model.sigma*n))
    Q0=cross(b)/(model.sigma*n);R0=-s.eye(3)/(model.sigma*n)
    Pinverse=model.sigma*(n**2*s.eye(3)-b*b.T)/(n*delta)
    equal(rational(P0*Pinverse),s.eye(3));equal(rational(Pinverse*P0),s.eye(3))
    equal(rational(Pinverse*Q0-cross(b)/delta),s.zeros(3))
    equal(rational(Q0.T*Pinverse*Q0-R0-(n**2*s.eye(3)-b*b.T)/(model.sigma*n*delta)),s.zeros(3))
    equal(rational(raw[:3,:3]-L.T*P0*L/determinant),s.zeros(3))
    equal(rational(raw[:3,3:]-L.T*Q0*Li.T),s.zeros(3))
    equal(rational(raw[3:,3:]-determinant*Li*R0*Li.T),s.zeros(3))
    native_inverse=rational(determinant*Li*Pinverse*Li.T)
    equal(rational(raw[:3,:3]*native_inverse),s.eye(3))
    equal(rational(native_inverse*raw[:3,:3]),s.eye(3))
    # The three native Gram families remain full. This identifies their
    # coefficient contractions, not a reduction of the underlying fields.
    E=s.Matrix(symmetric(s.symbols('E0:6',real=True)))
    M=s.Matrix(symmetric(s.symbols('M0:6',real=True)))
    C=s.Matrix(3,3,s.symbols('C0:9',real=True))
    S=rational(determinant*Li.T*(model.sigma*E+M/model.sigma)*Li)
    Ct=rational(determinant*Li.T*C*Li)
    d=s.Matrix([Ct[2,1]-Ct[1,2],Ct[0,2]-Ct[2,0],Ct[1,0]-Ct[0,1]])
    zero(sum(cross(b)[i,j]*Ct[i,j]for i in range(3)for j in range(3))-(b.T*d)[0])
    # One trace cyclicity identity contains every native coefficient; separate
    # blocks keep the rational degree bounded instead of expanding a huge H.
    projected=(n**2*s.eye(3)-b*b.T)/(n*delta)
    electric=rational(model.sigma*determinant*Li*projected*Li.T)
    magnetic=rational(determinant*Li*projected*Li.T/model.sigma)
    mixed=rational(determinant*Li*cross(b)*Li.T/delta)
    equal(rational(native_inverse-electric),s.zeros(3))
    equal(rational(native_inverse*raw[:3,3:]-mixed),s.zeros(3))
    equal(rational(raw[:3,3:].T*native_inverse*raw[:3,3:]-raw[3:,3:]-magnetic),s.zeros(3))
    return {'source_sigma':str(model.sigma),'generic_spatial_coframe':encode(L),
        'native_original_all36_Hodge_coefficients_checked':True,
        'whole_electric_mixed_magnetic_Legendre_coefficients_checked':True,
        'symmetric_invariant':'S=det(L) L^-T (sigma E+sigma^-1 M) L^-1',
        'axial_invariant':'d=(Ct32-Ct23,Ct13-Ct31,Ct21-Ct12), Ct=det(L) L^-T C L^-1',
        'gauge_energy':'Hg=(n^2 tr(S)-b^T S b-2n b^T d)/(2n(n^2-b^T b))',
        'same_original_native_Gram_and_all_fields_retained':True},model.source_hashes


def compress13(data):
    a,q=data[:4],data[4:10]
    L=s.Matrix([[q[0],0,0],[q[1],q[2],0],[q[3],q[4],q[5]]])
    Li=rational(L.inv());determinant=s.factor(L.det())
    E=s.Matrix(symmetric(data[10:16]));C=s.Matrix(3,3,data[16:25]);M=s.Matrix(symmetric(data[25:31]))
    S=rational(determinant*Li.T*(E/2+2*M)*Li)
    Ct=rational(determinant*Li.T*C*Li)
    d=[Ct[2,1]-Ct[1,2],Ct[0,2]-Ct[2,0],Ct[1,0]-Ct[0,1]]
    return [*a,*[S[i,j]for i,j in SYM],*d]


def scalar_data(lam,h,data):
    a0,a=data[0],list(data[1:4])
    S=symmetric(data[4:10]);d=list(data[10:13])
    R=inv3([[S[i][j]-(lam if i==j else 0)for j in range(3)]for i in range(3)])
    Ra=[sum(R[i][j]*a[j]for j in range(3))for i in range(3)]
    Rd=[sum(R[i][j]*d[j]for j in range(3))for i in range(3)]
    dot=lambda u,v:sum(x*y for x,y in zip(u,v))
    U,V,W=dot(a,Ra),dot(d,Rd),dot(a,Rd)
    Up,Vp,Wp=dot(Ra,Ra),dot(Rd,Rd),dot(Ra,Rd)
    B=2*U+lam*Up;C=a0-W-lam*Wp;D=lam*(1-Vp)
    v=[h*Ra[i]-Rd[i]for i in range(3)]
    T=sum(S[i][i]for i in range(3))-lam+V
    return {'E1':h*h*U-T,'E2':h*h*B+2*h*C-D,
            'v':v,'A':a0+h*U-W,'U':U,'V':V,'W':W,'B':B,'C':C,'D':D,'R':R}


def verify_algebraic_reconstruction():
    # Formal scalar contractions of R=(S-lambda I)^-1. Symmetry makes all
    # cross terms cancel without dividing by U=a^T R a, which vanishes at source.
    lam,h,a0,trS,U,V,W,Up,Vp,Wp=s.symbols('lam h a0 trS U V W Up Vp Wp',real=True)
    r2=h*h*Up-2*h*Wp+Vp
    av=h*U-W;dv=h*W-V
    vSv=lam*r2+h*av-dv
    D=1-r2;A=a0+av
    numerator=trS-vSv-2*dv
    E1=h*h*U-trS+lam-V
    E2=h*h*(2*U+lam*Up)+2*h*(a0-W-lam*Wp)-lam*(1-Vp)
    zero(numerator-lam*D+E1)
    zero(lam*D-2*h*A+E2)
    # Once (S-lambda I)v=h a-d is used, these are the actual derivatives
    # of H=n*A+N/(2nD), with n^2=h/D.
    zero(A-numerator/(2*h)-(E1+E2)/(2*h))
    v=s.Symbol('v_component',real=True)
    zero(h*s.Symbol('a_component')-s.Symbol('Sv_plus_d')+v*numerator/D-
         (h*s.Symbol('a_component')-s.Symbol('Sv_plus_d')+lam*v)+v*E1/D)
    b,c,d,r=s.symbols('B C D r',real=True)
    regular_h=d/(c+r)
    numerator=s.together(b*regular_h**2+2*c*regular_h-d).as_numer_denom()[0]
    zero(s.rem(s.Poly(numerator,r),s.Poly(r*r-c*c-b*d,r)).as_expr())
    source={U:0,V:0,W:0,Up:0,Vp:0,Wp:0,trS:6*C_SOURCE,a0:s.Rational(9,5)}
    equations=s.Matrix([E1,E2]).subs(source)
    equal(equations.subs({lam:LAMBDA_SOURCE,h:N*N}),s.zeros(2,1))
    equal(equations.jacobian([lam,h]),J2)
    zero(J2.det()-s.Rational(18,5))
    return {'two_scalar_equations':'E1=h^2 U-tr(S)+lambda-V=0; E2=(2U+lambda Uprime)h^2+2(a0-W-lambda Wprime)h-lambda(1-Vprime)=0',
        'rational_coefficients':'R=(S-lambda I)^-1; U=a^T R a,V=d^T R d,W=a^T R d; Uprime=a^T R^2 a,Vprime=d^T R^2 d,Wprime=a^T R^2 d',
        'whole_original_time_reconstruction':'v=R(h a-d); n=positive sqrt(h/(1-v^T v)); b=n*v; Hred=2n(a0+a^T v)',
        'single_scalar_algebraic_equation':'h(lambda)=D/(C+positive sqrt(C^2+B D)); h(lambda)^2 U-tr(S)+lambda-V=0, B=2U+lambda Uprime,C=a0-W-lambda Wprime,D=lambda(1-Vprime)',
        'source_units':{'S_minus_lambda_identity':str(-4*C_SOURCE),'regular_radical_denominator':str(s.Rational(18,5)),
                        'timelike_square':str(N*N),'source_lambda':str(LAMBDA_SOURCE)},
        'two_scalar_source_Jacobian':encode(J2),'source_Jacobian_determinant':str(J2.det()),
        'single_scalar_source_derivative':'1',
        'all_original_four_time_rows_reconstructed':True,
        'division_by_vanishing_source_a_or_U_used':False}


def sqrt_jet(value,positive_source_value):
    leading=field_element(positive_source_value)
    assert leading*leading==value.c[0] and leading!=DOMAIN.zero
    coefficients=[leading]
    for n in range(1,value.order+1):
        coefficients.append((value.c[n]-sum((coefficients[j]*coefficients[n-j]for j in range(1,n)),DOMAIN.zero))/(2*leading))
    output=Jet(coefficients)
    assert (output*output).c==value.c
    return output


def algebraic_source_branch(data_germ,order):
    """Two source-unit equations generate the full four-time branch at any order."""
    data=[expression_jet(v,order)for v in data_germ]
    expected=[s.Rational(9,5),0,0,0]+[2*C_SOURCE]*3+[0]*6
    assert [v.c[0]for v in data]==list(map(field_element,expected))
    lam=Jet([field_element(LAMBDA_SOURCE)]+[DOMAIN.zero]*order)
    h=Jet([field_element(N*N)]+[DOMAIN.zero]*order)
    inverse=J2.inv()
    for n in range(1,order+1):
        equations=scalar_data(lam,h,data)
        residual=[equations[key].c[n]for key in ('E1','E2')]
        next_values=[-sum((field_element(inverse[i,j])*residual[j]for j in range(2)),DOMAIN.zero)for i in range(2)]
        lam=Jet(list(lam.c[:n])+[next_values[0]]+list(lam.c[n+1:]))
        h=Jet(list(h.c[:n])+[next_values[1]]+list(h.c[n+1:]))
        closed=scalar_data(lam,h,data)
        assert all(closed[key].c[r]==DOMAIN.zero for key in ('E1','E2')for r in range(n+1))
    closed=scalar_data(lam,h,data)
    v=closed['v'];D=1-sum(w*w for w in v)
    n=sqrt_jet(h/D,N)
    y=[n,*[n*w for w in v]];Hred=2*n*closed['A']
    radical=sqrt_jet(closed['C']*closed['C']+closed['B']*closed['D'],s.Rational(9,5))
    explicit_h=closed['D']/(closed['C']+radical)
    assert explicit_h.c==h.c
    return y,Hred,lam,h


def main():
    started=time.monotonic()
    gram,source_hashes=original_gram_reduction()
    print('PASS generic source Hodge/native Gram reduction: complete31 temporal symbol factors through13 source invariants',flush=True)
    algebra=verify_algebraic_reconstruction()
    print('PASS full four temporal equations reduce to two source-unit algebraic equations and one regular radical equation',flush=True)
    original=json.loads((HERE/'source_quantum_temporal_symbol.json').read_text())
    for group in('source_sha256','input_sha256'):
        for name,digest in original[group].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,name
    data31=[s.sympify(v,locals={'source_epsilon':EPS})for v in original['generated_input_germ']]
    data13=compress13(data31)
    y,Hred,lam,h=algebraic_source_branch(data13,7)
    for i,row in enumerate(y):
        assert list(row.c)==[field_element(s.sympify(v))for v in original['actual_order7']['temporal_coefficients'][i]]
    assert list(Hred.c)==[field_element(s.sympify(v))for v in original['actual_order7']['reduced_Hamiltonian_coefficients']]
    # The original four-time symbol is independently evaluated on the new
    # algebraic output, not inferred from agreement with the old coefficients.
    from source_quantum_temporal_symbol import equation_jets
    original_data=[expression_jet(v,7)for v in data31]
    assert all(v==DOMAIN.zero for row in equation_jets(y,original_data)for v in row.c)
    assert original_compressed_hamiltonian(y,original_data).c==Hred.c
    assert lam.c[0]==field_element(LAMBDA_SOURCE) and h.c[0]==field_element(N*N)
    print('PASS independently generated full source branch/Hred through order7, same four Euler rows and regular single-equation radical',flush=True)
    paths=[HERE/name for name in('source_temporal_algebraic_elimination.py','source_quantum_temporal_symbol.py',
        'source_quantum_temporal_symbol.json','source_gauge_legendre.py','source_gauge_legendre.json',
        'independent_source_gauge_legendre.json')]
    result={'root':ROOT_ID,'source_sha256':source_hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},
        'scope':'COMPLETE_SOURCE_TEMPORAL_SYMBOL_THIRTEEN_INVARIANTS_AND_REGULAR_ALGEBRAIC_ELIMINATION',
        'original_Gram_projection':gram,'algebraic_branch':algebra,
        'source_actual_thirteen_argument_germ':list(map(str,data13)),
        'actual_source_coefficients':{'lambda':[str(DOMAIN.to_sympy(v))for v in lam.c],
            'timelike_square_h':[str(DOMAIN.to_sympy(v))for v in h.c],
            'all_four_temporal_and_reduced_energy_match_original_order7':True},
        'all_order_API':'compress13(actual31); algebraic_source_branch(actual13_germ,order) generates lambda,h,all four temporal coefficients and Hred. The analytic source germ also solves the displayed one-scalar radical equation.',
        'field_scope':'The13 invariants are pointwise source readouts retaining dependence on the original coframe/scalar/native gauge/full CAR symbols; no field or Fock carrier is replaced by13 coordinates.',
        'quantum_scope':'Classical analytic elimination is now explicit up to one regular scalar algebraic root. Noncommuting quantization must preserve the source current and coefficient ordering; this does not substitute operators into the commuting inverse or radical.',
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'source_temporal_algebraic_elimination.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS source complete algebraic temporal elimination',result['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
