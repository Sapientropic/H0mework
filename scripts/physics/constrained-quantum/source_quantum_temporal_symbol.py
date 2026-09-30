#!/usr/bin/env python3
"""Source analytic temporal reduction before interacting quantization.

The complete homogeneous primary/Gauss-pulled Hamiltonian is linear in the
four time-coframe entries except for the original native gauge Hodge energy.
Its four coefficients and 21 electric/cross/magnetic Gram entries are source
readouts. They generate, rather than assume, every coefficient of the unique
source-connected temporal branch and its reduced Hamiltonian symbol.
"""
from __future__ import annotations

import hashlib
import json
import time
import sympy as s
from dynamic import HERE, ROOT, ROOT_ID
from retained_hamiltonian_reduction import DOMAIN
from source_spatial_active_phase_splice import field_element
from source_coframe_live_ordering import SourceCoframeLiveOrdering, FREE
from source_coframe_legendre import rational, pack
from source_scalar_gauss_reduction import SourceScalarGaussReduction
from source_coframe_initial_constraints import SourceCoframeInitialConstraints
from source_lorentz_contact import ETA, PAIRS, clean, equal, encode

EPS = s.Symbol('source_epsilon', real=True)
SYM = ((0,0),(1,1),(2,2),(0,1),(0,2),(1,2))
N = 3*s.sqrt(30)/25
J0 = s.diag(-s.sqrt(30), *[-2*s.sqrt(30)/3]*3)


class Jet:
    """Exact truncated scalar series over the source algebraic coefficient field."""
    def __init__(self, coefficients):
        self.c = tuple(coefficients)
        self.order = len(self.c)-1
    def lift(self, other):
        if isinstance(other, Jet):
            assert self.order == other.order
            return other
        return Jet([field_element(other)]+[DOMAIN.zero]*self.order)
    def __add__(self, other):
        if isinstance(other,TemporalDual): return NotImplemented
        other=self.lift(other);return Jet([a+b for a,b in zip(self.c,other.c)])
    __radd__=__add__
    def __neg__(self): return Jet([-a for a in self.c])
    def __sub__(self, other): return self+-self.lift(other)
    def __rsub__(self, other): return self.lift(other)+-self
    def __mul__(self, other):
        if isinstance(other,TemporalDual): return NotImplemented
        other=self.lift(other)
        return Jet([sum((self.c[j]*other.c[n-j] for j in range(n+1)),DOMAIN.zero) for n in range(self.order+1)])
    __rmul__=__mul__
    def inverse(self):
        assert self.c[0] != DOMAIN.zero, 'the original source chart denominator vanished'
        out=[DOMAIN.one/self.c[0]]
        for n in range(1,self.order+1):
            out.append(-sum((self.c[j]*out[n-j] for j in range(1,n+1)),DOMAIN.zero)/self.c[0])
        return Jet(out)
    def __truediv__(self, other): return self*self.lift(other).inverse()
    def __rtruediv__(self, other): return self.lift(other)*self.inverse()
    def expression(self): return sum(DOMAIN.to_sympy(v)*EPS**n for n,v in enumerate(self.c))


class TemporalDual:
    """Four actual time partials; coefficients may themselves be arbitrary jets."""
    def __init__(self, value, derivative): self.value,self.derivative=value,tuple(derivative)
    def lift(self, other):
        return other if isinstance(other,TemporalDual) else TemporalDual(other,[other*0]*4)
    def __add__(self, other):
        other=self.lift(other)
        return TemporalDual(self.value+other.value,[a+b for a,b in zip(self.derivative,other.derivative)])
    __radd__=__add__
    def __neg__(self): return TemporalDual(-self.value,[-v for v in self.derivative])
    def __sub__(self, other): return self+-self.lift(other)
    def __rsub__(self, other): return self.lift(other)+-self
    def __mul__(self, other):
        other=self.lift(other)
        return TemporalDual(self.value*other.value,[a*other.value+self.value*b for a,b in zip(self.derivative,other.derivative)])
    __rmul__=__mul__
    def inverse(self):
        inverse=self.value.inverse() if isinstance(self.value,Jet) else s.S.One/self.value
        return TemporalDual(inverse,[-v*inverse*inverse for v in self.derivative])
    def __truediv__(self, other): return self*self.lift(other).inverse()
    def __rtruediv__(self, other): return self.lift(other)*self.inverse()


def compact(value): return s.cancel(value) if isinstance(value,s.Basic) else value


def transpose(A): return [list(v) for v in zip(*A)]
def product(A,B): return [[compact(sum(A[i][r]*B[r][j] for r in range(len(B)))) for j in range(len(B[0]))] for i in range(len(A))]
def inv3(A):
    # Cyclic complementary indices already include the cofactor sign.
    cofactor=[[compact(A[(i+1)%3][(j+1)%3]*A[(i+2)%3][(j+2)%3]-
                 A[(i+1)%3][(j+2)%3]*A[(i+2)%3][(j+1)%3])for j in range(3)]for i in range(3)]
    determinant=compact(sum(A[0][j]*cofactor[0][j] for j in range(3)))
    return [[compact(cofactor[j][i]/determinant)for j in range(3)]for i in range(3)]

def symmetric(values):
    zero=values[0]*0; A=[[zero for _ in range(3)]for _ in range(3)]
    for (i,j),v in zip(SYM,values): A[i][j]=A[j][i]=v
    return A


def original_compressed_hamiltonian(y, data):
    """Literal original wedge-metric kernel and native Legendre energy.

    data=(a4,q6,E6,C9,M6), E=Pi G^-1 Pi^T, C=Pi B^T, M=B G B^T.
    The source sigma=1/2 remains in every electric, mixed and magnetic block.
    """
    a,q=data[:4],data[4:10]
    electric_gram=symmetric(data[10:16])
    cross=[list(data[16+3*i:19+3*i])for i in range(3)]
    magnetic_gram=symmetric(data[25:31])
    zero=y[0]*0
    e=[[y[0],zero,zero,zero], [y[1],q[0],zero,zero],
       [y[2],q[1],q[2],zero], [y[3],q[3],q[4],q[5]]]
    metric=[[sum((-1 if a==0 else 1)*e[a][i]*e[a][j]for a in range(4))for j in range(4)]for i in range(4)]
    determinant=y[0]*q[0]*q[2]*q[5]
    kernel=[[compact(-2*(metric[a][c]*metric[b][d]-metric[a][d]*metric[b][c])/determinant)
             for c,d in PAIRS]for a,b in PAIRS]
    electric=[row[:3]for row in kernel[:3]]
    mixed=[row[3:]for row in kernel[:3]]
    magnetic=[row[3:]for row in kernel[3:]]
    inverse=inv3(electric)
    inverse_mixed=product(inverse,mixed)
    feedback=product(transpose(mixed),inverse_mixed)
    gauge=sum(compact(inverse[i][j]*electric_gram[i][j]/2-
               inverse_mixed[i][j]*cross[i][j]+
               (feedback[i][j]-magnetic[i][j])*magnetic_gram[i][j]/2)
              for i in range(3)for j in range(3))
    return sum(y[i]*a[i]for i in range(4))+gauge


def equation_jets(y, data):
    one=y[0].lift(1);zero=y[0].lift(0)
    temporal=[TemporalDual(v,[one if a==i else zero for a in range(4)])for i,v in enumerate(y)]
    value=original_compressed_hamiltonian(temporal,data)
    return [-v for v in value.derivative]


def expression_jet(expression, order):
    expression=s.cancel(expression)
    numerator,denominator=map(lambda v:s.Poly(v,EPS),s.fraction(expression))
    a=Jet([field_element(numerator.nth(j))for j in range(order+1)])
    b=Jet([field_element(denominator.nth(j))for j in range(order+1)])
    return a/b


def source_branch(data_germ, order):
    """Every order is generated from lower ones; no branch or Hred is input."""
    assert order>=0 and len(data_germ)==31
    data=[expression_jet(v,order)for v in data_germ]
    source_values=[s.Rational(9,5),0,0,0,1,0,1,0,0,1]+[0]*15+[s.Rational(162,625)]*3+[0]*3
    assert [v.c[0]for v in data]==list(map(field_element,source_values))
    y=[Jet([field_element(v)]+[DOMAIN.zero]*order)for v in (N,0,0,0)]
    assert all(v.c[0]==DOMAIN.zero for v in equation_jets(y,data))
    diagonal=[field_element(J0[a,a])for a in range(4)]
    coefficient_checks=[]
    for n in range(1,order+1):
        residual=[v.c[n]for v in equation_jets(y,data)]
        generated=[-residual[a]/diagonal[a]for a in range(4)]
        y=[Jet(list(v.c[:n])+[generated[a]]+list(v.c[n+1:]))for a,v in enumerate(y)]
        equations=equation_jets(y,data)
        assert all(v.c[r]==DOMAIN.zero for v in equations for r in range(n+1))
        # The complete source rational composition has coefficient J0*c_n
        # plus the lower-order residual, with no contribution from c_>n.
        coefficient_checks.append({'order':n,'forcing':list(map(lambda v:str(DOMAIN.to_sympy(v)),residual)),
                                   'generated_time':list(map(lambda v:str(DOMAIN.to_sympy(v)),generated))})
    reduced=original_compressed_hamiltonian(y,data)
    return y,reduced,coefficient_checks


class SourceTemporalSymbol:
    def __init__(self):
        self.coframe=SourceCoframeLiveOrdering()
        self.graph=SourceScalarGaussReduction()
        self.common=self.graph.common
        self.n=s.Symbol('temporal_n',positive=True)
        self.shift=s.Matrix(s.symbols('temporal_b1:4',real=True))
        self.y=(self.n,*self.shift)
        self.e=self.coframe.e.copy();self.e[:,0]=s.Matrix(self.y)

    def verify_all_nongauge_coefficients_affine(self):
        c,m,e=self.coframe,self.coframe.model,self.e
        Hi=rational(m.lorentz.inverse(e));Gt=m.at(m.G[:,:16],e)
        h=e[:,1:].T*ETA*e[:,1:]
        R=rational(m.metric_lift_numerator(e)/e.det())
        Bi=rational(4*e.det()*m.metric_inverse_numerator.xreplace(dict(zip(m.h_variables,pack(h))))/h.det())
        Q=rational(R*Bi*R.T)
        ports=m.lorentz.raw_matter_ports(e)
        current=[rational(s.diag(s.I*ports['E'].inv()*V,s.I*(ports['E'].inv()*V).conjugate()))for V in ports['V']]
        L=rational(c.S*s.eye(24)[:6,:]+Gt.T*Hi)
        T=[rational(sum((L[i,a]*current[a]for a in range(24)),s.zeros(8)))for i in range(16)]
        K=rational(c.A.T*Q*c.A/2)
        mixed=[rational(sum(((c.A.T*Q)[r,j]*T[j]for j in range(16)),s.zeros(8)))for r in range(6)]
        W=rational((L.T*Q*L+Hi)/2)
        # Keep both ordered current slots; do not commute the CAR matrices.
        flat=s.Matrix.hstack(*(J.reshape(64,1)for J in current))
        quartic=rational(flat*W*flat.T)
        drift=rational(-s.I*sum(((c.A.T*Q)[r,j]*c.A.diff(q)[j,:]for r,q in enumerate(c.q)for j in range(16)),s.zeros(1,6))/2)
        correction=rational(-s.I*sum(((c.A.T*Q)[r,j]*T[j].diff(q)for r,q in enumerate(c.q)for j in range(16)),s.zeros(8))/2)
        inverse=rational(e.adjugate()/e.det());metric=rational(e.det()*inverse*ETA*inverse.T)
        h00=metric[0,0]
        scalar=rational(s.diag(s.Matrix([[1/h00]]),s.zeros(3)))
        scalar[0,1:]=rational(-metric[0,1:]/h00)
        scalar[1:,1:]=rational(metric[1:,0]*metric[0,1:]/h00-metric[1:,1:])
        families={'coframe_kinetic':K,'coframe_two_ordered_current_slots':quartic,'live_drift':drift,
                  'live_current_derivative':correction,'scalar_momentum_and_potential':scalar,
                  'source_volume':s.Matrix([[e.det()]])}
        families.update({f'coframe_mixed_{i}':v for i,v in enumerate(mixed)})
        families.update({f'matter_principal_{i}':rational(ports['E'].inv()*ports['oriented_principals'][i])for i in range(1,4)})
        families['Yukawa_coefficient']=rational(e.det()*ports['E'].inv())
        counts={}
        for name,matrix in families.items():
            values=list(matrix.todok().values())
            assert all(s.Poly(s.cancel(v),self.y).total_degree()<=1 for v in values),name
            assert all(s.cancel(v.subs(dict.fromkeys(self.y,0)))==0 for v in values),name
            counts[name]=len(values)
        for variable in self.y:
            equal(rational(ports['E'].diff(variable)),s.zeros(4))
            equal(c.A.diff(variable),s.zeros(16,6));equal(c.S.diff(variable),s.zeros(16,6))
        self.affinity_counts=counts
        return counts

    def compress_canonical(self,q,x,pi,kappa,A,Pi_A,psi,p):
        """Generate all31 arguments from the same original canonical fields."""
        c=self.coframe
        equal(A[0,:],s.zeros(1,12))
        e=self.e.subs(dict(zip(c.q,q)))
        data=self.common.matter_data(e,self.graph.constraints.vacuum,A)
        chi=self.common.canonical_dual(data,p)
        current=self.common.coframe.lorentz.matter_current(e,psi,chi)
        # A/S and the temporal six currents are independent of e[:,0].
        Pi_e=clean(c.at(c.A,q)*kappa+c.at(c.S,q)*current[:6,:])
        scalar=self.graph.embed(x,pi,A,Pi_A,[s.zeros(3,12)]*3,psi,p)
        result=self.common.hamiltonian(e,Pi_e,s.zeros(48,1),scalar['phi'],scalar['Pi_phi'],
            [s.zeros(70,1)]*3,A,Pi_A,s.zeros(3,48),psi,p,[s.zeros(252,1)]*3,s.zeros(10,1))
        equal(rational(result['coframe_primary']),s.zeros(10,1))
        equal(rational(self.graph.select.T*scalar['Gauss']),s.zeros(9,1))
        nongauge=s.factor(sum(value for name,value in result['components'].items()if name!='gauge'))
        a=[s.cancel(s.diff(nongauge,y))for y in self.y]
        assert all(not(set(self.y)&value.free_symbols)for value in a)
        assert s.cancel(nongauge-sum(y*v for y,v in zip(self.y,a)))==0
        B,_=self.common.gauge.spatial_data(A,s.zeros(3,48))
        E=clean(Pi_A*self.common.gauge.gram_inverse*Pi_A.T)
        C=clean(Pi_A*B.T);M=clean(B*self.common.gauge.gram*B.T)
        compressed=[*a,*q,*[E[i,j]for i,j in SYM],*list(C),*[M[i,j]for i,j in SYM]]
        direct=s.cancel(original_compressed_hamiltonian(self.y,compressed)-result['value'])
        assert direct==0
        return compressed,{'non_gauge_coefficients':list(map(str,a)),
            'whole_original_Hamiltonian':str(s.factor(result['value'])),
            'all10_primary_and9_broken_Gauss_rows_zero':True,
            'residual_stabilizer_Gauss':encode(self.graph.stabilizer.T*scalar['Gauss'])}


def main():
    started=time.monotonic();model=SourceTemporalSymbol()
    affinity=model.verify_all_nongauge_coefficients_affine()
    print('PASS generic sixq/fourtime affinity of complete primary-pulled two-current, live derivative, scalar and full matter coefficients',flush=True)
    original=SourceCoframeInitialConstraints()
    q=[s.S.One,0,s.S.One,0,0,s.S.One]
    x=s.zeros(61,1);x[19]=EPS/29
    pi=s.zeros(61,1);pi[7]=EPS/31
    kappa=s.Matrix([EPS*s.Rational(j+1,43)for j in range(6)])
    A=original.A.copy();A[0,:]=s.zeros(1,12)
    Pi_A=s.zeros(3,12);Pi_A[0,0]=EPS/37;Pi_A[1,6]=2*EPS/41;Pi_A[2,1]=-EPS/47
    source_p=clean(-s.I*original.chi0*model.common.matter_data(original.e0,original.vacuum,A)['E'])
    data,actual=model.compress_canonical(q,x,pi,kappa,A,Pi_A,original.psi0,source_p)
    print('PASS actual original canonical fields generate all31 temporal-symbol arguments and whole Hamiltonian identity',flush=True)
    constant_data=[expression_jet(v.subs(EPS,0) if isinstance(v,s.Basic) else v,1)for v in data]
    actual_J=s.zeros(4)
    for j in range(4):
        trial=[Jet([field_element(v),DOMAIN.one if a==j else DOMAIN.zero])for a,v in enumerate((N,0,0,0))]
        for a,row in enumerate(equation_jets(trial,constant_data)):
            assert row.c[0]==DOMAIN.zero
            actual_J[a,j]=DOMAIN.to_sympy(row.c[1])
    equal(actual_J,J0)
    y,Hred,checks=source_branch(data,6)
    assert all(any(v!=DOMAIN.zero for v in row.c[1:])for row in y)
    print('PASS source-connected four-time branch through order6, all original temporal coefficients vanish and Hred generated',flush=True)
    # Independently recompute with a longer truncation. Coefficients already
    # generated must be unchanged because each update only consumes lower ones.
    y7,H7,_=source_branch(data,7)
    for a in range(4):assert y[a].c==y7[a].c[:7]
    assert Hred.c==H7.c[:7]
    # An arbitrary next coefficient changes the original constraint by J0*d,
    # not by an assumed target branch or a selected Hamiltonian root.
    n=7;germs=[expression_jet(v,n)for v in data]
    delta=[field_element(s.Rational(a+1,11))for a in range(4)]
    changed=[Jet(list(v.c[:n])+[v.c[n]+delta[a]])for a,v in enumerate(y7)]
    defect=equation_jets(changed,germs)
    for a in range(4):
        assert all(v==DOMAIN.zero for v in defect[a].c[:n])
        assert defect[a].c[n]==field_element(J0[a,a])*delta[a]
    print('PASS arbitrary next-coefficient source Jacobian law and all-order truncation compatibility',flush=True)
    paths=[HERE/name for name in ('source_quantum_temporal_symbol.py','source_common_hamiltonian.py',
        'source_coframe_live_ordering.py','source_scalar_gauss_reduction.py','source_gauge_legendre.py',
        'source_temporal_dirac_reduction.json','independent_source_temporal_dirac_reduction.json',
        'source_coframe_initial_constraints.json','independent_source_coframe_initial_constraints.json')]
    saved=json.loads((HERE/'source_temporal_dirac_reduction.json').read_text())
    for group in ('source_sha256','input_sha256'):
        for name,expected in saved[group].items():assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==expected,name
    result={'root':ROOT_ID,'source_sha256':saved['source_sha256'],
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},
        'scope':'COMPLETE_HOMOGENEOUS_SOURCE_TEMPORAL_REDUCED_ANALYTIC_SYMBOL_AND_ALL_ORDER_COEFFICIENT_PRODUCER',
        'generic_time_affinity_coefficient_counts':affinity,
        'compressed_original_Hamiltonian':'H(y,z)=sum y_a*a_a(z)+1/2 Einv:E-(Einv Q):C+1/2(Q^T Einv Q-Kmag):M; all gauge blocks from original -wedge^2(e^T eta e)/(sigma det e)',
        'source_argument_inventory':'a4 from all nongauge primary/Gauss-pulled energy; q6; E6=Pi G^-1 Pi^T; C9=Pi B^T; M6=B G B^T',
        'all_order_recursion':'y0=(N,0,0,0); y_n=-J0^-1 [epsilon^n]F(sum_{r<n}epsilon^r*y_r,z(epsilon)); Hred_n=[epsilon^n]H(y(epsilon),z(epsilon))',
        'source_Jacobian':encode(actual_J),'source_Jacobian_determinant':'800/3',
        'actual_source_canonical_germ':actual,'generated_input_germ':list(map(str,data)),
        'actual_order7':{'temporal_coefficients':[[str(DOMAIN.to_sympy(v))for v in row.c]for row in y7],
                         'reduced_Hamiltonian_coefficients':[str(DOMAIN.to_sympy(v))for v in H7.c],
                         'source_equation_coefficients_zero':True,'lower_coefficient_compatibility':True},
        'recursion_steps':checks,
        'analytic_semantics':'The rational source F has nonzero original denominators and det J0=800/3. The previously generated unique analytic implicit branch has exactly these recursively generated coefficients. Every analytic input germ in that same neighborhood is admitted; the all-order API takes its source arguments, never Hred or a completed branch.',
        'matter_symbols':'Original complete number-preserving p M psi currents; no affine translation of CAR creators or annihilators by classical source spinors.',
        'quantum_ordering_scope':'This generates the actual time-reduced classical analytic symbol. Quantizing its nonlinear products must retain the already signed current and coefficient order; substituting noncommuting operators into a commuting square root or this classical IFT is not performed.',
        'full_quantum_evolution_spectrum_or_lifetime_generated':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'source_quantum_temporal_symbol.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS complete original temporal reduced symbol',result['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
