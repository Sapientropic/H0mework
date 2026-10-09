#!/usr/bin/env python3
"""Independent source reconstruction and exact-rational ball-overlap enclosure."""
import contextlib
from fractions import Fraction as F
import hashlib
import importlib.util
import io
import json
from math import factorial, isqrt
from pathlib import Path
import sys
import time
from unittest.mock import patch
import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
BASE = ROOT/'Verification/physics/low-energy-phenomenology'


class Interval:
    """Exact Fraction endpoints; square roots enclosed by integer arithmetic."""
    def __init__(self, low, high=None):
        self.lo = F(low)
        self.hi = F(low if high is None else high)
        assert self.lo <= self.hi
    @staticmethod
    def of(value):
        return value if isinstance(value, Interval) else Interval(value)
    def __add__(self, other):
        other = self.of(other)
        return Interval(self.lo+other.lo, self.hi+other.hi)
    __radd__ = __add__
    def __neg__(self): return Interval(-self.hi,-self.lo)
    def __sub__(self, other): return self+-self.of(other)
    def __rsub__(self, other): return self.of(other)+-self
    def __mul__(self, other):
        other = self.of(other)
        ends = [a*b for a in [self.lo,self.hi] for b in [other.lo,other.hi]]
        return Interval(min(ends),max(ends))
    __rmul__ = __mul__
    def __truediv__(self, other):
        other = self.of(other)
        assert other.lo > 0 or other.hi < 0
        return self*Interval(1/other.hi,1/other.lo)
    def __rtruediv__(self, other): return self.of(other)/self
    def square(self):
        low = 0 if self.lo <= 0 <= self.hi else min(self.lo**2,self.hi**2)
        return Interval(low,max(self.lo**2,self.hi**2))
    def sqrt(self, bits=360):
        assert self.lo >= 0
        def floor(value):
            return isqrt((value.numerator << (2*bits))//value.denominator)
        return Interval(F(floor(self.lo),1<<bits),F(floor(self.hi)+1,1<<bits))
    def grow(self, error): return Interval(self.lo-error,self.hi+error)
    def contained_in(self, text):
        lower, upper = map(F,text.strip('[]').split(','))
        assert lower <= self.lo <= self.hi <= upper, (text,self.decimals())
    def decimals(self, digits=70):
        scale=10**digits
        def render(value, ceiling=False):
            numerator=value.numerator*scale
            n=-((-numerator)//value.denominator) if ceiling else numerator//value.denominator
            sign='-' if n<0 else ''
            n=abs(n)
            return sign+str(n//scale)+'.'+str(n%scale).zfill(digits)
        return [render(self.lo),render(self.hi,True)]


def cmul(a,b):
    return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])


def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    start=time.monotonic()
    candidate=load(HERE.parent/'source_kernel.py','frozen_packet_kernel')
    record,data=candidate.exact_source()
    N,omega,H0,Hj,Cinv,K,w=data
    # Independent literal full252 matrices; the candidate's reciprocal table is not the source.
    literal=load(BASE/'full-quantum/induced-quantum/audit/independent_check.py','actual_full252_source')
    n0,C0full,CI0,K0,G5,Hfull,Lfull,Yfull,yukawa,wfull,k=literal.literal_source()
    occupied=json.loads((BASE/'occupied-response/receipt.json').read_text())
    frame=literal.decode(occupied['occupied_frame'])
    equal=literal.equal
    equal(frame*w,wfull)
    equal(CI0*frame,frame*Cinv)
    equal(K0*frame,frame*K)
    Hsmall=H0+sum((k[j]*Hj[j] for j in range(3)),s.zeros(12))
    equal(Hfull*frame,frame*Hsmall)
    equal(frame.H*Hfull,Hsmall*frame.H)
    equal(Yfull*frame,s.zeros(252,12))
    assert Yfull.todok()
    equal(Hsmall.H,Hsmall)
    equal(K*Hsmall,Hsmall*K)
    equal(K*K,2*s.eye(12))
    for j in range(3):
        equal(Hj[j]*Hj[j],N*N*s.eye(12))
    for j in range(3):
        for l in range(j):equal(Hj[j]*Hj[l]+Hj[l]*Hj[j],s.zeros(12))
    assert s.simplify(n0-N)==0
    print('PASS literal source: same full252 preparation, C0, K, both-sided12 reduction, Clifford norms, nonzero Y retained',flush=True)

    # Fourier measure and complete overlap integral, with no radial cutoff.
    r,n,kappa=s.symbols('r n kappa',real=True,positive=True)
    volume=4*s.pi/3
    radial_prefactor=s.simplify(4*s.pi/(2*s.pi)**3*(4*s.pi)**2/volume)
    assert radial_prefactor==6/s.pi
    cap_volume=2*s.integrate(s.pi*(1-s.Symbol('x')**2),(s.Symbol('x'),r/2,1))
    assert s.expand(cap_volume/volume-(1-3*r/4+r**3/16))==0
    overlap=1-3*r/4+r**3/16
    assert s.factor(overlap)==(r-2)**2*(r+4)/16
    assert s.integrate(r*overlap,(r,0,2))==s.Rational(2,5)
    assert s.integrate(3*r**4,(r,0,1))==s.Rational(3,5)
    # Moment formula checked independently of the candidate's exponential antiderivative.
    moment=s.simplify(2**(n+2)/(n+2)-s.Rational(3,4)*2**(n+3)/(n+3)+2**(n+5)/(16*(n+5)))
    assert s.simplify(moment-3*2**(n+2)/((n+2)*(n+3)*(n+5)))==0

    # Separate exact rational interval implementation: integrate the exponential series.
    # |kappa|<3, 0<=r<=2, e^6<3^6=729; the discarded integral is <=(2/5)*729*6^(m+1)/(m+1)!.
    N2=F(str(s.simplify(N*N)))
    omega2=F(str(s.simplify(omega*omega)))
    assert N2==F(54,125) and omega2==F(972,3125)
    nI=Interval(N2).sqrt(); oI=Interval(omega2).sqrt(); spin=Interval(2).sqrt()
    real=Interval((1-3*omega2)/N2); imag=4*oI/N2
    modulus=(real.square()+imag.square()).sqrt()
    kr=((modulus+real)/2).sqrt(); ki=((modulus-real)/2).sqrt()
    assert kr.lo>0 and ki.lo>0 and modulus.hi<9
    power=(Interval(1),Interval(0)); total=(Interval(0),Interval(0))
    degree=130
    for order in range(degree+1):
        coefficient=F(3*2**(order+2),(order+2)*(order+3)*(order+5)*factorial(order))
        total=(total[0]+coefficient*power[0],total[1]+coefficient*power[1])
        power=cmul(power,(-kr,-ki))
    tail=F(2,5)*729*F(6**(degree+1),factorial(degree+1))
    J=(total[0].grow(tail),total[1].grow(tail))
    Z=cmul((-3*oI,Interval(1)),J)
    n2=Z[1]; mean=2*spin/N2*Z[0]/n2
    second=8/(N2*n2)-F(8,1)/(N2*N2)
    variance=second-mean.square()
    assert n2.lo>0 and variance.lo>0 and mean.hi<0
    frozen=json.loads((HERE.parent/'source-kernel-receipt.json').read_text())
    target=frozen['evaluations']
    for key,value in [('raw_filtered_norm_squared',n2),('current_mean_h0',mean),
                      ('current_second_moment_h0',second),('centered_noise_h0',variance)]:
        value.contained_in(target[key])
    print('PASS independent exact-rational overlap bounds lie within every published h=0 interval',flush=True)

    # Derive the nonzero physical shift enclosure with exact endpoints as well.
    xpsi=(Interval(3).sqrt()*N2+nI*Interval(F(3,5)).sqrt())/n2.sqrt()
    xHpsi=xpsi+nI*Interval(F(3,5)).sqrt()/n2.sqrt()
    lipschitz=2*spin/N2*xHpsi+spin/nI
    delta=lipschitz.hi/F(65536)
    published_delta=F(target['nonzero_transfer']['current_vector_error_upper'].strip('[]').split(',')[0])
    assert delta<published_delta
    meanq=mean.grow(delta)
    secondq=second.sqrt().grow(delta).square()
    varianceq=variance.sqrt().grow(2*delta).square()
    assert variance.sqrt().lo>2*delta
    for key,value in [('mean_enclosure',meanq),('second_moment_enclosure',secondq),('centered_noise_enclosure',varianceq)]:
        value.contained_in(target['nonzero_transfer'][key])
    print('PASS published nonzero-q enclosures and displayed scalar upper bound by independent rational arithmetic',flush=True)

    # Infinite radial tail: check the resolvent inequality without a floating spectrum.
    nr2=s.Symbol('a',nonnegative=True); om2=s.Rational(omega2.numerator,omega2.denominator)
    denominator=(1-3*om2+nr2)**2+16*om2
    gap=s.expand(4*denominator-nr2*(1+9*om2+nr2))
    extra=s.Symbol('extra',nonnegative=True)
    shifted=s.Poly(gap.subs(nr2,36*om2+extra),extra)
    assert all(coefficient>0 for coefficient in shifted.all_coeffs())
    # Then radial integrand <=24/pi*(1+1/R)^2/r^4 and its whole tail is the claimed bound.
    Rcut=s.Symbol('Rcut',positive=True)
    assert s.simplify(s.integrate(24/s.pi*(1+1/Rcut)**2/r**4,(r,Rcut,s.oo))-
                     8/s.pi*(1+1/Rcut)**2/Rcut**3)==0
    print('PASS analytic infinite-tail bound; no quadrature error estimate enters the main certification',flush=True)

    # Exact wrong-mouth controls at a literal source point.
    Hzero=H0; z=s.I; originalR=s.I*(z*s.eye(12)-Hzero).inv()*Cinv
    correctD=-s.I*Cinv.inv()*(z*s.eye(12)-Hzero)
    equal((correctD*originalR*w-w).applyfunc(s.simplify),s.zeros(12,1))
    assert literal.clean((correctD*((z*s.eye(12)-Hzero).inv()*w)-w).applyfunc(s.simplify)).todok()
    assert literal.clean((correctD*(s.I*Cinv*(z*s.eye(12)-Hzero).inv()*w)-w).applyfunc(s.simplify)).todok()
    assert mean.hi<0 and mean.square().lo>0
    assert variance.hi<second.lo
    wrong_unfiltered_scale=N2
    assert n2.hi<wrong_unfiltered_scale
    radius=s.Symbol('r',nonnegative=True)
    raw_norm=s.sympify(record['zero_transfer_raw_norm_integrand'],locals={'r':radius})
    assert s.simplify(raw_norm.subs(radius,0)-raw_norm.subs(radius,1)) != 0

    # Frozen script replay; its only writes are redirected into this audit directory.
    program=HERE.parent/'source_kernel.py'
    allowed={HERE.parent/'source-kernel-receipt.json':HERE/'replay-receipt.json',
             HERE.parent/'source-kernel-summary.md':HERE/'replay-summary.md'}
    before={path:hashlib.sha256(path.read_bytes()).hexdigest() for path in allowed}
    write=Path.write_text
    def redirect(path,data,*args,**kwargs):
        assert path in allowed,path
        return write(allowed[path],data,*args,**kwargs)
    stdout=io.StringIO(); argv=sys.argv
    try:
        sys.argv=[str(program),'--dps','50']
        with patch.object(Path,'write_text',redirect),contextlib.redirect_stdout(stdout):
            candidate.main()
    finally:sys.argv=argv
    (HERE/'replay.log').write_text(stdout.getvalue())
    replay=json.loads((HERE/'replay-receipt.json').read_text())
    frozen.pop('elapsed_seconds');replay.pop('elapsed_seconds')
    assert replay==frozen
    assert all(hashlib.sha256(path.read_bytes()).hexdigest()==digest for path,digest in before.items())
    result={'status':'PASS','scope':'FROZEN_CONTINUOUS_DIRAC_FILTERED_PACKET_NUMERICAL_AND_ANALYTIC_PRODUCER',
        'independent_interval_method':'Exact Fraction boxes; 360-bit integer sqrt enclosures; integrated 130-term exponential series',
        'series_absolute_tail_upper':str(tail),
        'h0':{key:value.decimals() for key,value in [('n_squared',n2),('mean',mean),('second_moment',second),('centered_noise',variance)]},
        'nonzero_q':{'physical':['0','0','1/65536'],'mean':meanq.decimals(),'second_moment':secondq.decimals(),
                     'centered_noise':varianceq.decimals(),'lipschitz':lipschitz.decimals()},
        'published_decimal_enclosures_verified':True,'literal_full252_source_reduces_both_sides':True,
        'ball_measure_overlap_and_infinite_tail_verified':True,
        'negative_controls':['ordinary_H_resolvent_without_i_C0','wrong_C0_side','uncentered_second_moment_as_noise',
                              'unfiltered_or_momentumwise_normalization'],
        'replay_equal_except_elapsed':True,'frozen_artifacts_unchanged':True,
        'elapsed_seconds':round(time.monotonic()-start,3)}
    (HERE/'receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS wrong-source/uncentered controls and frozen replay; unchanged frozen artifacts',flush=True)


if __name__=='__main__':main()
