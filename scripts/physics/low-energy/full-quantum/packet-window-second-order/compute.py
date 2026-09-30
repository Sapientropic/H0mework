#!/usr/bin/env python3
"""Exact controls for the sharp-ball second-order source-current formula.

This constructs analytic-coefficient evidence and examples. It does not replace
the actual source seed or compute an unperformed numerical integral of it.
"""
import hashlib
import json
from pathlib import Path
import sys
import time
import sympy as S

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
FQ=ROOT/'Verification/physics/low-energy-phenomenology/full-quantum'
R,h,s,t=S.symbols('R h s t',positive=True)
z,kappa=S.symbols('z kappa',real=True)


def read(path):return json.loads(path.read_text())


def real(expression):return S.simplify(S.expand_complex(expression).as_real_imag()[0])


def main():
    started=time.monotonic()
    paths={'source_current':FQ/'packet-field/current-data.json',
        'source_seed':FQ/'packet-seed-regularity/receipt.json',
        'source_moments':FQ/'packet-current-moments/receipt.json'}
    data=read(paths['source_current'])
    Q=S.SparseMatrix(*data['selected']['shape'],{(i,j):S.sympify(v) for i,j,v in data['selected']['entries']})
    assert Q==Q.T and all(S.conjugate(v)==v for v in Q.todok().values())
    b=S.zeros(289,1);b[9]=b[259]=1
    source_pairing=(b.T*Q*b)[0]
    assert source_pairing==4
    Q_frobenius_squared=S.simplify(sum(v*v for v in Q.todok().values()))
    density=(2*S.pi)**-3
    volume=4*S.pi*R**3/3
    intersection=S.simplify(2*S.pi*S.integrate(h*(2*h-s),(h,s/2,R)))
    assert S.expand(intersection-(volume-S.pi*R**2*s+S.pi*s**3/12))==0
    short_area=S.simplify(2*S.pi*S.integrate(h,(h,0,s/2)))
    short_volume=S.simplify(2*S.pi*S.integrate(2*h*h,(h,0,s/2)))
    assert short_area==S.pi*s**2/4 and short_volume==S.pi*s**3/6
    print('PASS actual source Q and exact three-dimensional chord geometry',flush=True)

    # Verify the entire moving-endpoint algebra with a generic cubic Hilbert jet.
    gram={(i,j):S.Symbol(f'b{min(i,j)}{max(i,j)}',real=True) for i in range(4) for j in range(4)}
    def B_poly(left,right):
        return S.expand(sum(gram[i,j]*left**i/S.factorial(i)*right**j/S.factorial(j)
            for i in range(4) for j in range(4)))
    chord=S.integrate(B_poly(z,z+s),(z,-h,h-s))
    cplus=B_poly(h,h);cminus=B_poly(-h,-h)
    c0=S.integrate(B_poly(z,z),(z,-h,h))
    bulk2=S.integrate(S.expand(sum(gram[i,j]*z**i/S.factorial(i)*z**(j-2)/S.factorial(j-2)
        for i in range(4) for j in range(2,4))),(z,-h,h))
    expected=c0-s*(cplus+cminus)/2+s*s*bulk2/2
    assert all(S.Poly(S.expand(chord-expected),s).nth(j)==0 for j in range(3))
    print('PASS full generic moving-endpoint second-order cancellation',flush=True)

    examples=[]
    def add_polynomial_example(name,g):
        gp=S.diff(g,z);gpp=S.diff(g,z,2)
        paired=source_pairing*real(S.conjugate(g)*g.subs(z,z+s))
        one_chord=S.integrate(paired,(z,-h,h-s))
        exact=S.simplify(density*S.pi*S.integrate(h*one_chord,(h,s/2,R)))
        L0=S.simplify(exact.subs(s,0))
        diagonal=lambda point:source_pairing*real(S.conjugate(g.subs(z,point))*g.subs(z,point))
        cv=S.simplify(density/4*2*S.pi*S.integrate(h*(diagonal(h)+diagonal(-h)),(h,0,R)))
        bulk=S.simplify(S.pi*S.integrate((R*R-z*z)*source_pairing*real(S.conjugate(g)*gpp),(z,-R,R)))
        flux=S.simplify(2*S.pi*S.integrate(z*source_pairing*real(S.conjugate(g)*gp),(z,-R,R)))
        energy=S.simplify(S.pi*S.integrate((R*R-z*z)*source_pairing*real(S.conjugate(gp)*gp),(z,-R,R)))
        K=S.simplify(density*bulk/4)
        assert S.simplify(flux-energy-bulk)==0
        assert S.simplify(S.diff(exact,s).subs(s,0)+cv)==0
        assert S.simplify(S.diff(exact,s,2).subs(s,0)/2-K)==0
        assert S.simplify(S.limit((L0-exact-cv*s)/s**2,s,0,dir='+')+K)==0
        residual=S.Poly(S.expand(exact-L0+cv*s-K*s*s),s)
        assert all(residual.nth(j)==0 for j in range(3))
        examples.append({'name':name,'test_field':str(g),'carrier':'b=e9+e259 in the actual 289 coordinates; B_Q(b,b)=4',
            'exact_three_dimensional_L':str(exact),'L0':str(L0),'c_v':str(cv),'K_v':str(K),
            'sphere_flux':str(flux),'gradient_energy':str(energy),
            'integration_by_parts_exact':True,'loss_after_cusp_coefficient':str(-K),
            'wrong_drop_boundary_coefficient':str(S.simplify(-density*energy/4)),
            'remainder_polynomial':str(residual.as_expr())})
        print('PASS three-dimensional example',name,'K=',K,flush=True)
    add_polynomial_example('constant',S.Integer(1))
    add_polynomial_example('complex_affine',1+(2+S.I)*z)
    add_polynomial_example('complex_quadratic',1+(1+S.I)*z+(2-S.I)*z*z)
    assert examples[0]['K_v']==examples[1]['K_v']=='0'
    assert S.sympify(examples[1]['wrong_drop_boundary_coefficient'],locals={'R':R})!=0

    phase_exact=S.simplify(density*source_pairing*S.cos(kappa*s)*intersection/2)
    phaseK=S.simplify(-density*source_pairing*kappa*kappa*volume/4)
    phaseCv=S.simplify(density*source_pairing*S.pi*R*R/2)
    assert S.simplify(S.diff(phase_exact,s,2).subs(s,0)/2-phaseK)==0
    assert S.simplify(S.diff(phase_exact,s).subs(s,0)+phaseCv)==0
    examples.append({'name':'phase','test_field':'exp(I*kappa*z)*b',
        'exact_three_dimensional_L':str(phase_exact),'c_v':str(phaseCv),'K_v':str(phaseK),
        'sphere_flux':'0','gradient_energy':str(source_pairing*kappa*kappa*volume),
        'integration_by_parts_exact':True,'nonzero_when_kappa_nonzero':True})
    print('PASS phase example and response-versus-loss sign',flush=True)

    # Full complex coefficient/packet jets, with no assumption that any cross inner is real.
    def complex_vector(name):
        return S.Matrix([S.Symbol(f'{name}{i}r',real=True)+S.I*S.Symbol(f'{name}{i}i',real=True) for i in range(2)])
    W0,W1,W2=[complex_vector(f'w{j}') for j in range(3)]
    J0,J1,J2=[complex_vector(f'j{j}') for j in range(3)]
    qa,qb,qc=S.symbols('qa qb qc',real=True)
    Qtest=S.Matrix([[qa,qb],[qb,qc]])
    a0=W0*J0.T
    a1=W1*J0.T+W0*J1.T
    a2=W2*J0.T+2*W1*J1.T+W0*J2.T
    beta=(S.conjugate(W0).T*Qtest*W0)[0]
    alpha=(S.conjugate(W0).T*Qtest*W1)[0]
    gamma=(S.conjugate(W1).T*Qtest*W1)[0]
    zeta=(S.conjugate(W0).T*Qtest*W2)[0]
    noise=(S.conjugate(J0).T*J0)[0]
    theta=(S.conjugate(J0).T*J1)[0]
    eta=(S.conjugate(J0).T*J2)[0]
    speed=(S.conjugate(J1).T*J1)[0]
    def B_matrix(A,B):return real(S.trace(S.conjugate(A).T*Qtest*B))
    predicted=real(zeta)*noise+2*real(alpha*theta)+beta*real(eta)
    predicted_gradient=gamma*noise+beta*speed+2*real(S.conjugate(alpha)*theta)
    predicted_flux=real(alpha)*noise+beta*real(theta)
    assert S.expand(B_matrix(a0,a2)-predicted)==0
    assert S.expand(B_matrix(a1,a1)-predicted_gradient)==0
    assert S.expand(B_matrix(a0,a1)-predicted_flux)==0
    assert S.expand(real(alpha*theta)-real(alpha)*real(theta)+S.im(alpha)*S.im(theta))==0
    assert S.expand(real(S.conjugate(alpha)*theta)-real(alpha)*real(theta)-S.im(alpha)*S.im(theta))==0
    # Opposite phases cancel in the full field; discarding imaginary cross terms invents a coefficient.
    frequencyW=S.Integer(2);frequencyJ=S.Integer(-2)
    beta0=source_pairing;alpha0=S.I*frequencyW*beta0;theta0=S.I*frequencyJ
    zeta0=-frequencyW**2*beta0;eta0=-frequencyJ**2
    true_contraction=zeta0+2*real(alpha0*theta0)+beta0*eta0
    wrong_real_only=zeta0+2*real(alpha0)*real(theta0)+beta0*eta0
    assert true_contraction==0 and wrong_real_only==-32
    print('PASS full complex WJ beta/cross identities and nonzero imaginary-cross control',flush=True)

    output={'scope':'STRIKE_ANALYTIC_SHARP_BALL_RESPONSE_SECOND_COEFFICIENT',
        'source_inputs_sha256':{str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in paths.values()},
        'source_current_coordinate':data['selected']['source_coordinate'],
        'source_Q_real_symmetric':True,'source_Q_frobenius_squared':str(Q_frobenius_squared),
        'normalization':'L(sv)=(2*pi)^(-3)/2*integral B_Q(f(k),f(k+sv)) dk for real readout',
        'expansion':'ReL(sv)=L(0)-c_v*s+K_v*s^2+o(s^2), s down to0',
        'loss_expansion':'[L(0)-ReL(sv)-c_v*s]/s^2 tends to -K_v',
        'coefficient':'K_v=(2*pi)^(-3)/4*integral_ball B_Q(a,partial_v^2 a)',
        'integration_by_parts':'K_v=(2*pi)^(-3)/4*(integral_sphere (v.n)B_Q(a,partial_v a)-integral_ball B_Q(partial_v a,partial_v a))',
        'geometry':{'exact_overlap_volume':str(intersection),'short_chord_projection_area':str(short_area),
            'short_chord_ball_volume':str(short_volume),'valid_range':'0<s<=2R'},
        'generic_chord_identity':{'cubic_Hilbert_jet_gram_arbitrary_real_symmetric':True,
            'orders_0_1_2_exactly_checked':True,
            'second_endpoint_terms_cancel_by':'c_prime(h)=2*B(a(h),a_prime(h))'},
        'examples':examples,
        'WJ_expansion':{'beta':'W^dagger Q W, real','alpha':'W^dagger Q W_v, complex',
            'gamma':'W_v^dagger Q W_v, real, not assumed positive','zeta':'W^dagger Q W_vv, complex',
            'N':'inner(J,J), real','theta':'inner(J,J_v), complex','eta':'inner(J,J_vv), complex',
            'B_a_avv':'Re(zeta)*N+2*Re(alpha*theta)+beta*Re(eta)',
            'B_av_av':'gamma*N+beta*norm(J_v)^2+2*Re(conj(alpha)*theta)',
            'B_a_av':'Re(alpha)*N+beta*Re(theta)',
            'beta_derivatives':'beta_v=2Re(alpha); beta_vv=2Re(zeta)+2gamma',
            'full_beta_form':'(beta_vv/2-gamma)*N+(beta_v/2)*N_v-2Im(alpha)Im(theta)+beta*(N_vv/2-norm(J_v)^2)',
            'generic_complex_jet_identity_checked':True,
            'opposite_phase_control':{'W_phase_rate':2,'J_phase_rate':-2,'actual_full_contraction':0,
                'incorrect_Real_only_contraction':-32,'difference_nonzero':True}},
        'analytic_remainder':{'regularity_sufficient':'C2 on the closed ball, with continuous directional second derivative; actual source is C-infinity',
            'omega2':'uniform modulus of continuity of partial_v^2 a',
            'unscaled_autocorrelation_error_bound':'||B_Q||*[Vol(ball)*M0*omega2(s)*s^2/2+pi*R^2*(5*M1^2/6+4*M0*M2/3)*s^3+5*pi*M0^2*s^3/12+pi*M0*M2*s^5/12]',
            'C3_improvement':'replace the first omega2 term by Vol(ball)*M0*M3*s^3/6',
            'physical_L_error':'multiply that bound by (2*pi)^(-3)/2'},
        'not_computed':'No numerical value of the actual WJ integral K_v is supplied; examples test the universal identity, not replace the actual prepared source.',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'receipt.json').write_text(json.dumps(output,indent=2)+'\n')
    print('PASS sharp-window second-order construction',output['elapsed_seconds'],flush=True)


if __name__=='__main__':main()
