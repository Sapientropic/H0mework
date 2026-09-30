#!/usr/bin/env python3
"""Source-contracted scalar coefficient tensors and tight whole-ball boxes.

The actual 289 seed is contracted with its actual Q before any estimate. This
is a strike producer, not an independent certificate or a numerical K integral.
"""
from functools import lru_cache
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
FQ=ROOT/'Verification/physics/low-energy-phenomenology/full-quantum'
kx,ky,kz,U,T,ds,curv=s.symbols('kx ky kz U T ds curv',real=True)
u,q=s.symbols('u q',real=True)
variables=(kx,ky,kz,U,T,ds,curv)


def read(path):return json.loads(path.read_text())


def rounded(value,digits=18):
    return s.ceiling(value*10**digits)/10**digits


def sqrt_upper(value,digits=18):
    value=s.Rational(value);scale=10**digits
    bound=isqrt(int(value.p)*scale*scale//int(value.q))
    if bound*bound*value.q<value.p*scale*scale:bound+=1
    result=s.Rational(bound,scale)
    assert result*result>=value
    return result


def main():
    started=time.monotonic()
    seed_path=FQ/'packet-seed-regularity/receipt.json'
    current_path=FQ/'packet-field/current-data.json'
    factor_path=FQ/'light-modes/field-receipt.json'
    seed,current,factor_data=map(read,[seed_path,current_path,factor_path])
    for path,digest in seed['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
    assert seed['source_sha256']==current['source_sha256']==factor_data['source_sha256']
    names={str(v):v for v in variables}
    N={row['index']:s.sympify(row['numerator'],locals=names) for row in seed['fields']}
    Q={(i,j):s.sympify(value) for i,j,value in current['selected']['entries']}
    assert all(Q.get((j,i),0)==c and s.conjugate(c)==c for (i,j),c in Q.items())
    Dexpr=s.sympify(seed['actual_seed_formula']['denominator'],locals=names)
    F=s.Poly(s.sympify(factor_data['axial_source_factor'],locals={'u':u,'q':q}),u,q,domain=s.QQ)
    cf=F.coeff_monomial(u**2)
    Fhat=s.Poly(sum(c*U**(a//2)*T**(b//2) for (a,b),c in F.terms()),U,T,domain=s.QQ)
    f=s.Poly(Fhat.as_expr()/cf,U,T,domain=s.QQ)
    assert s.expand(f.diff(U).as_expr()-Dexpr)==0
    s0=-f.diff(T).eval({U:0,T:0})/f.diff(U).eval({U:0,T:0})
    t0=-(f.diff(T).diff(T).eval({U:0,T:0})+2*f.diff(U).diff(T).eval({U:0,T:0})*s0+
        f.diff(U).diff(U).eval({U:0,T:0})*s0*s0)/f.diff(U).eval({U:0,T:0})
    eps=s.Rational(seed['source_root_control']['epsilon'])
    rmax=s.Rational(seed['source_root_control']['r_window'][1])
    Umax=rmax*eps**2;Tmax=eps**2;kmax=2*eps
    def box2(expression):
        return sum(abs(c)*Umax**a*Tmax**b for (a,b),c in s.Poly(expression,U,T,domain=s.QQ).terms())
    Derror=box2(Dexpr-1)
    Dlower=1-Derror
    assert 0<Dlower<1
    # This cancellation retains s-s0 as O(epsilon^2), not a unit-size input.
    s_diff_numerator=s.expand(-f.diff(T).as_expr()-s0*Dexpr)
    assert s_diff_numerator.subs({U:0,T:0})==0
    ds_bound=box2(s_diff_numerator)/Dlower
    s_bound=abs(s0)+ds_bound
    fTT=f.diff(T).diff(T).as_expr();fUT=f.diff(U).diff(T).as_expr();fUU=f.diff(U).diff(U).as_expr()
    t_bound=(box2(fTT)+2*box2(fUT)*s_bound+box2(fUU)*s_bound*s_bound)/Dlower
    print('PASS full-F slope/curvature boxes', 's0',s0,'t0',t0,
        'ds',float(ds_bound),'|t|',float(t_bound),flush=True)

    from sympy.polys.rings import ring
    K=s.QQ.algebraic_field(s.sqrt(2),s.sqrt(15),s.I)
    P,*gens=ring(variables,K)
    basis_expr=[s.Integer(1),s.sqrt(2),s.sqrt(15),s.sqrt(30),s.I,
        s.I*s.sqrt(2),s.I*s.sqrt(15),s.I*s.sqrt(30)]
    basis=[K.from_sympy(c) for c in basis_expr]
    def coordinates(c):
        values=list(c.to_list())
        return s.Matrix([s.Rational(a.numerator,a.denominator) for a in [K.dom.zero]*(8-len(values))+values])
    inverse_basis=s.Matrix.hstack(*(coordinates(c) for c in basis)).inv()
    @lru_cache(None)
    def number(value):
        value=s.expand(value)
        if value.is_Add:return sum((number(part) for part in value.args),K.zero)
        scalar,radical=value.as_coeff_Mul()
        return K.convert(scalar)*basis[basis_expr.index(radical)]
    def poly(expression):
        return P.from_dict({powers:number(c) for powers,c in s.Poly(s.expand(expression),*variables).terms()})
    zero=P.zero
    source={i:poly(value) for i,value in N.items()}
    bra={i:poly(s.conjugate(value)) for i,value in N.items()}
    qentries={(i,j):number(value) for (i,j),value in Q.items() if i in source and j in source}
    derivative_cache={}
    @lru_cache(None)
    def contracted(orders):
        if orders not in derivative_cache:
            vector=source
            for index in orders:vector={i:v.diff(index) for i,v in vector.items()}
            derivative_cache[orders]=vector
        right=derivative_cache[orders]
        answer=zero
        for (i,j),value in qentries.items():
            answer+=value*bra[i]*right[j]
        return answer
    D=poly(Dexpr);S=P.ground_new(s0)+gens[5];TT=gens[6]
    A=contracted(())
    EU,ET=contracted((3,)),contracted((4,))
    HUU,HUT,HTT=contracted((3,3)),contracted((3,4)),contracted((4,4))
    DU,DT=D.diff(3),D.diff(4)
    DUU,DUT,DTT=D.diff(3).diff(3),D.diff(3).diff(4),D.diff(4).diff(4)
    radialN=S*EU+ET
    radialD=S*DU+DT
    secondN=S*S*HUU+2*S*HUT+HTT+TT*EU
    secondD=S*S*DUU+2*S*DUT+DTT+TT*DU
    rawFirst=[contracted((a,))+gens[a]*radialN for a in range(3)]
    dFirst=[gens[a]*radialD for a in range(3)]
    beta=[D*rawFirst[a]-A*dFirst[a] for a in range(3)]
    delta={}
    for a in range(3):
        for b in range(a,3):
            rawSecond=contracted((a,b))+gens[a]*(S*contracted((b,3))+contracted((b,4)))+\
                gens[b]*(S*contracted((a,3))+contracted((a,4)))+gens[a]*gens[b]*secondN
            dSecond=gens[a]*gens[b]*secondD
            if a==b:
                rawSecond+=radialN;dSecond+=radialD
            delta[a,b]=D*D*rawSecond-D*(rawFirst[a]*dFirst[b]+rawFirst[b]*dFirst[a])-\
                D*A*dSecond+2*A*dFirst[a]*dFirst[b]
            print('GENERATED delta',a,b,'terms',len(delta[a,b]),flush=True)
    print('PASS original Q contraction before estimates',len(qentries),'active entries',flush=True)

    @lru_cache(None)
    def pieces(coefficient):
        return tuple(inverse_basis*coordinates(coefficient))
    @lru_cache(None)
    def coefficient_bound(coefficient):
        return sum(abs(c)*bound for c,bound in zip(pieces(coefficient),[1,2,4,6,1,2,4,6]))
    def expression(coefficient):
        return s.expand(sum(c*b for c,b in zip(pieces(coefficient),basis_expr)))
    box=[kmax,kmax,kmax,Umax,Tmax,ds_bound,t_bound]
    def bound(polynomial):
        return sum(coefficient_bound(c)*s.prod(b**power for b,power in zip(box,powers))
            for powers,c in polynomial.items())
    def constant(polynomial):return polynomial.get((0,)*7,K.zero)
    def serialize(polynomial):
        return [[list(powers),[[i,str(c)] for i,c in enumerate(pieces(coefficient)) if c!=0]]
            for powers,coefficient in sorted(polynomial.items())]
    def real_flags(polynomial):
        return {'entire_polynomial_real':all(all(c==0 for c in pieces(value)[4:]) for value in polynomial.values()),
            'imaginary_monomials':sum(any(c!=0 for c in pieces(value)[4:]) for value in polynomial.values())}
    alpha0=constant(A)
    beta0=[constant(v) for v in beta]
    delta0={key:constant(value) for key,value in delta.items()}
    # Independent central values are comparisons after construction, not definitions.
    assert expression(alpha0)==1944*s.sqrt(15)/390625
    assert all(c==K.zero for c in beta0)
    for (a,b),c in delta0.items():
        assert expression(c)==(144*s.sqrt(15)/78125 if a==b else 0)
    errors={'alpha':rounded(bound(A-D**2*alpha0)/Dlower**2),
        'beta_components':[rounded(bound(v-D**3*c)/Dlower**3) for v,c in zip(beta,beta0)],
        'delta_components':{f'{a}{b}':rounded(bound(value-D**4*delta0[a,b])/Dlower**4)
            for (a,b),value in delta.items()}}
    beta_bound=sqrt_upper(sum(v*v for v in errors['beta_components']))
    delta_frob=sqrt_upper(sum((1 if a==b else 2)*errors['delta_components'][f'{a}{b}']**2 for a,b in delta))
    delta_rows=max(sum(errors['delta_components'][f'{min(a,b)}{max(a,b)}'] for b in range(3)) for a in range(3))
    delta_bound=min(delta_frob,delta_rows)
    print('PASS whole-ball source-contracted scalar bounds',float(errors['alpha']),float(beta_bound),float(delta_bound),flush=True)
    polynomials={'alpha':{'denominator_power':2,'numerator':serialize(A),'center':str(expression(alpha0)),**real_flags(A)},
        'beta':[{ 'axis':a,'denominator_power':3,'numerator':serialize(v),'center':str(expression(beta0[a])),**real_flags(v)} for a,v in enumerate(beta)],
        'delta':[{ 'axes':[a,b],'denominator_power':4,'numerator':serialize(value),'center':str(expression(delta0[a,b])),**real_flags(value)}
            for (a,b),value in delta.items()]}
    # If one replaces the true root slope by a unit-size value, the central delta is changed.
    fake=delta[0,0].evaluate(gens[5],K.convert(1-s0))
    false_center=fake.get((0,)*6,K.zero) if len(fake.ring.gens)==6 else constant(fake)
    slope_control=expression(false_center-delta0[0,0])
    assert slope_control!=0
    result={'scope':'STRIKE_ORIGINAL_FULL_BALL_CURVATURE_COEFFICIENT_TENSORS',
        'source_sha256':seed['source_sha256'],
        'source_inputs_sha256':{str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in [seed_path,current_path,factor_path]},
        'variables':list(map(str,variables)),'coefficient_basis':list(map(str,basis_expr)),
        'seed':'W=N(k,U,T)/D(U,T); T=|k|^2/2 and U=T*originalRoot(T)',
        'slope_variable':'ds=U_prime-125/162; curv=U_second',
        'definitions':{'alpha':'W^dagger Q W','beta_v':'W^dagger Q partial_v W',
            'delta_v':'W^dagger Q partial_v^2 W','integrand':'Re(delta_v)*nu+2Re(beta_v*inner(J,J_v))+alpha*Re(inner(J,J_vv))'},
        'root':{'epsilon':str(eps),'U_box':[0,str(Umax)],'T_box':[0,str(Tmax)],
            'D_minus_one_bound':str(Derror),'D_lower':str(Dlower),'s0':str(s0),'t0':str(t0),
            's_formula':'-Fhat_T/Fhat_U',
            't_formula':'-(Fhat_TT+2Fhat_UT*s+Fhat_UU*s^2)/Fhat_U',
            's_minus_s0_numerator':str(s_diff_numerator),
            's_minus_s0_bound':str(rounded(ds_bound)),'s_absolute_bound':str(rounded(s_bound)),
            't_absolute_bound':str(rounded(t_bound)),
            'bounds_use_unrounded_rationals_in_polynomial_estimates':True},
        'source_contraction_active_Q_entries':len(qentries),'tensor_polynomials':polynomials,
        'centers':{'alpha':str(expression(alpha0)),'beta':[str(expression(v)) for v in beta0],
            'delta_tensor':[[a,b,str(expression(c))] for (a,b),c in delta0.items()],
            'computed_before_comparison_with_independent_center':True},
        'uniform_errors':{'alpha':str(errors['alpha']),'beta_components':list(map(str,errors['beta_components'])),
            'delta_components':{key:str(value) for key,value in errors['delta_components'].items()},
            'all_unit_v_beta':str(beta_bound),'all_unit_v_delta':str(delta_bound),
            'delta_error_frobenius':str(delta_frob),'delta_error_max_row_sum':str(delta_rows),
            'e1_beta':str(errors['beta_components'][0]),'e1_delta':str(errors['delta_components']['00'])},
        'negative_control':{'wrong_root_slope_1_central_delta_difference':str(slope_control),
            'nonzero':True,'scope':'The true U_prime(0) is generated; replacing it by 1 is not an approximation of order epsilon^2.'},
        'estimation':'Contracted scalar polynomials are shifted by the generated source center before coefficient-wise rational boxes; no original289 Frobenius estimate is used.',
        'not_computed':'This bounds source coefficients, not the full quantum current Hessian integral.',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'receipt.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS complete curvature-coefficient source construction',result['elapsed_seconds'],flush=True)


if __name__=='__main__':main()
