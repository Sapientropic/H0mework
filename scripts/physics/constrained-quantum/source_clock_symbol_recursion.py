#!/usr/bin/env python3
"""All-order original canonical clock symbols on the source principal cone.

This generates a closed differential DAG at every requested filtration depth.
Its leaves are the actual four-energy Weyl family, and every Moyal operation
has its finite original canonical derivative evaluator. No residual or clock
coefficient is input. Formal symbol completion does not assert operator summation.
"""
from __future__ import annotations
import hashlib
import gzip
import io
import json
import time
from functools import lru_cache
from math import factorial
from pathlib import Path
from dynamic import HERE, ROOT, ROOT_ID, decode
from source_canonical_star_temporal_reduction import bound
from source_lorentz_contact import encode
from source_gauss_quantum_current import encode_state

"""Original source Weyl leaves and arbitrary finite canonical derivatives."""
from types import SimpleNamespace
import sympy as s
from source_scalar_weyl_symbol import SourceScalarWeylSymbol
from source_common_weyl_symbol import gauge_coefficients
from source_temporal_coframe_pairing import generic_pairing
from source_reducing_coframe_metric import complete_coefficients
from source_quantum_ordered_temporal import OrderedTemporalCoefficients
from source_coframe_live_ordering import full
from source_gauss_quantum_current import apply_superposition, normal_pair, weighted_sum
from source_coframe_legendre import rational
from source_lorentz_contact import equal
from source_quantum_temporal_symbol import N

class SourceWeylLeafFactory:
    def __init__(self):
        self.weyl=SourceScalarWeylSymbol();m=self.weyl
        self.source_point=m.section.b0.copy();self.free=tuple(m.section.free)
        self.y=m.temporal.family.y
        metric=complete_coefficients(SimpleNamespace(section=m.section))
        self.pairing=generic_pairing(SimpleNamespace(coframe=m.native.joint.coframe,metric=metric),m.temporal.family)
        self.charges=[s.SparseMatrix(Q) for Q in m.charges]
        raw=OrderedTemporalCoefficients()
        self.weights=[f.subs(dict(zip(raw.y,self.y)),simultaneous=True) for f in raw.coefficients]
        n,*b=self.y;self.den=n*(n*n-sum(v*v for v in b))
        polys=[s.Poly(s.cancel(self.den*f),self.y) for f in self.weights]
        self.monomials=sorted(set().union(*(set(P.monoms()) for P in polys)))
        B=s.Matrix([[P.coeff_monomial(a) for P in polys] for a in self.monomials])
        self.rows=B.T.rref()[1];assert len(self.rows)==13
        self.inverse=B[list(self.rows),:].inv()
    def extract(self,state):
        out=[{} for _ in range(13)]
        for word,c in state.items():
            P=s.Poly(s.cancel(self.den*c),self.y)
            v=self.inverse*s.Matrix([P.coeff_monomial(self.monomials[i]) for i in self.rows])
            assert s.cancel(sum(a*f for a,f in zip(v,self.weights))-c)==0
            assert not set(self.y).intersection(v.free_symbols)
            for j,a in enumerate(v):
                if a:out[j][word]=s.factor(a)
        return out
    @lru_cache(None)
    def background(self,configuration):
        m=self.weyl;point=self.source_point.copy()
        for i,k in enumerate(self.free):point[k]=configuration[i]
        q=tuple(point[:6,0]);x=point[6:67,:];A=point[67:,:].reshape(3,12)
        scalar=m.coefficients(self.y,q,x,A);gauge=gauge_coefficients(m,scalar)
        cf=m.native.joint.coframe.coefficients(q)
        original=m.temporal.family.coefficients(self.y,q,x,A)
        return q,x,A,scalar,gauge,cf,original
    def at(self,phase200,state):
        assert len(phase200)==200
        m=self.weyl
        q,x,A,scalar,gauge,cf,original=self.background(tuple(phase200[:100]))
        p=s.Matrix(phase200[100:]);v=s.prod(q[j] for j in (0,2,5))
        def clean_state(rows):return {w:s.factor(c) for w,c in weighted_sum(rows).items() if s.factor(c)}
        def apply(M,st=state):return apply_superposition(s.SparseMatrix(M),st)
        currents=[apply(Q) for Q in self.charges]
        def quadratic(d):
            deg2=clean_state([((p[6:,:].T*d['principal']*p[6:,:])[0],state)])
            row=rational(p[6:,:].T*d['momentum_current'])
            deg1=clean_state([((p[6:,:].T*d['momentum_identity'])[0],state)]+
                            [(c,currents[a]) for a,c in enumerate(row) if c])
            deg0=clean_state([(d['classical_zero']+d['half_density_potential']+d['weyl_correction'],state)]+
                [(c,currents[a]) for a,c in enumerate(d['linear_current']) if c]+
                [(c,apply(self.charges[a],currents[b])) for (a,b),c in d['square_current'].todok().items()])
            return (deg0,deg1,deg2)
        scalar_rows=quadratic(scalar);gauge_rows=quadratic(gauge)
        qsub=dict(zip(m.native.joint.coframe.q,q));n=self.y[0]
        M=full(rational(sum((M*p[j] for j,M in enumerate(self.pairing['Mh'])),s.zeros(8)).subs(qsub)))
        cf1=apply(M);cf2=clean_state([(n/N*(p[:6,:].T*cf['K']*p[:6,:])[0],state)])
        J=[s.SparseMatrix(full(J)) for J in cf['J']]
        cf0=[(n/N,apply(full(cf['one_body']+cf['correction'])))]
        for word,c in state.items():
            count=len(word)
            cf0.append((n*c*((3*count**2+18*count+20)/(16*v)+3*v),{word:1}))
            cf0 += [(n*c*weight/N,normal_pair(J[a],J[b],word)) for (a,b),weight in cf['W'].todok().items()]
        cf_rows=(clean_state(cf0),cf1,cf2)
        linear_identity=s.factor((p[6:,:].T*(scalar['momentum_identity']+gauge['momentum_identity']))[0])
        linear_weights=rational(p[6:,:].T*(scalar['momentum_current']+gauge['momentum_current']))
        linear_current=rational(M+sum((value*self.charges[a] for a,value in enumerate(linear_weights)),s.zeros(504)))
        id_atoms=self.extract({():linear_identity})
        matrix_atoms=self.extract(linear_current.todok())
        order1_pairs=[{'identity':id_atoms[a].get((),s.S.Zero),
                       'current':s.SparseMatrix(504,504,matrix_atoms[a])} for a in range(13)]
        matter=apply(original['matter_CAR'])
        Yprimal=rational(-s.I*original['e'].det()*original['matter']['inverse_E']*original['matter']['Y'])
        Y=apply(s.diag(Yprimal,-Yprimal.conjugate()))
        Y_over_n={w:s.factor(c/n) for w,c in Y.items()}
        assert not set(self.y).intersection(set().union(*(c.free_symbols for c in Y_over_n.values())))
        H=[clean_state([(1,cf_rows[k]),(1,scalar_rows[k]),(1,gauge_rows[k])]+([(1,matter)] if k==0 else [])) for k in range(3)]
        atoms=[self.extract(clean_state([(1,row),(-1,Y)]) if k==0 else row)+[Y_over_n if k==0 else {}]
               for k,row in enumerate(H)]
        return {'homogeneous':H,'atoms':atoms,
            'components':{'coframe':cf_rows,'scalar':scalar_rows,'gauge':gauge_rows,
                          'matter_noY':clean_state([(1,matter),(-1,Y)]),'original_Y':Y},
            'phase200':tuple(phase200),'order1_pairs':order1_pairs}
    def leaf_derivative(self,atom,degree,alpha200,phase200,state):
        assert 0<=atom<14 and 0<=degree<=2 and len(alpha200)==200
        assert all(isinstance(k,int) and k>=0 for k in alpha200)
        if sum(alpha200[100:])>degree or (atom==13 and degree!=0):return {}
        variables={j:s.Dummy('source_canonical_'+str(j),positive=True) if j in (0,2,5)
                     else s.Dummy('source_canonical_'+str(j),real=True)
                   for j,k in enumerate(alpha200) if k}
        argument=[variables.get(j,v) for j,v in enumerate(phase200)]
        leaf=self.at(argument,state)['atoms'][degree][atom]
        point={v:phase200[j] for j,v in variables.items()}
        result={}
        for word,c in leaf.items():
            for j,v in variables.items():c=s.diff(c,v,alpha200[j])
            value=s.factor(c.subs(point,simultaneous=True))
            if value:result[word]=value
        return result

from functools import lru_cache
from itertools import combinations_with_replacement
from collections import defaultdict
import sympy as s

c,T,s00,s11,s01,s02,s12=s.symbols('c T S00 S11 S01 S02 S12',real=True)
S=s.Matrix([[s00,s01,s02],[s01,s11,s12],[s02,s12,T-s00-s11]])
J=s.diag(-T/c**3,0,0,0);J[1:,1:]=(S-T*s.eye(3))/c**3
JI=J.inv().applyfunc(s.factor)

@lru_cache(None)
def norm(expression):
 return s.cancel(expression)

class Arena:
 def __init__(self):
  self.nodes=[];self.lookup={};self.polys=[];self.plookup={};self.clock_def={}
  self.zero=self.poly({});self.one=self.scalar(1)
 def poly(self,terms):
  term=tuple(sorted((w,norm(v))for w,v in terms.items()if norm(v)!=0))
  if term not in self.plookup:self.plookup[term]=len(self.polys);self.polys.append(term)
  return self.plookup[term]
 def scalar(self,x):return self.poly({():s.sympify(x)})
 def add(self,*ids):
  out=defaultdict(lambda:s.S.Zero)
  for i in ids:
   for w,v in self.polys[i]:out[w]+=v
  return self.poly(out)
 def scale(self,x,e):return self.poly({w:x*v for w,v in self.polys[e]})
 def central(self,e):return all(all(self.nodes[a][1] for a in w)for w,v in self.polys[e])
 def atom(self,kind,key,central=False):
  token=(kind,central,key)
  if token not in self.lookup:self.lookup[token]=len(self.nodes);self.nodes.append(token)
  return self.poly({(self.lookup[token],):s.S.One})
 def multiply(self,a,b):
  out=defaultdict(lambda:s.S.Zero)
  for w,u in self.polys[a]:
   for z,v in self.polys[b]:
    word=w+z
    word=tuple(sorted(i for i in word if self.nodes[i][1]))+tuple(i for i in word if not self.nodes[i][1])
    out[word]+=u*v
  return self.poly(out)
 @lru_cache(None)
 def moyal(self,r,a,b):
  if r==0:return self.multiply(a,b)
  if a==self.zero or b==self.zero:return self.zero
  # Split additivity, retaining every nonconstant scalar inside differentiation.
  if len(self.polys[a])>1 or len(self.polys[b])>1:
   return self.add(*(self.moyal(r,self.poly({w:u}),self.poly({z:v}))for w,u in self.polys[a]for z,v in self.polys[b]))
  w,u=self.polys[a][0];z,v=self.polys[b][0]
  factor=1
  if not u.free_symbols:factor*=u;a=self.poly({w:s.S.One})
  if not v.free_symbols:factor*=v;b=self.poly({z:s.S.One})
  # A constant identity has zero positive canonical derivatives.
  if a==self.one or b==self.one:return self.zero
  ca,cb=self.central(a),self.central(b)
  if (not ca and cb)or(ca and cb and a>b):a,b=b,a;factor*=(-1)**r
  if a==b and ca and r%2:return self.zero
  return self.scale(factor,self.atom('moyal',(r,a,b),ca and cb))
 def jordan(self,r,a,b):return self.scale(s.Rational(1,2),self.add(self.moyal(r,a,b),self.moyal(r,b,a)))

ZERO=(0,0,0)
def polyadd(arena,*polys):
 out={}
 for p in polys:
  for ell,e in p.items():out[ell]=arena.add(out.get(ell,arena.zero),e)
 return {ell:e for ell,e in out.items()if e!=arena.zero}
def polyscale(arena,coefficient,p):return {ell:arena.scale(coefficient,e)for ell,e in p.items()if arena.scale(coefficient,e)!=arena.zero}
def shiftpoly(p,ell):return {tuple(a+b for a,b in zip(k,ell)):v for k,v in p.items()}
def weighted(arena,r,a,b):
 out={}
 for ell,x in a.items():
  for other,y in b.items():
   key=tuple(u+v for u,v in zip(ell,other));value=arena.jordan(r,x,y)
   out[key]=arena.add(out.get(key,arena.zero),value)
 return {key:value for key,value in out.items()if value!=arena.zero}

class Engine:
 def __init__(self,order):
  assert isinstance(order,int) and order>=1
  self.a=Arena();self.order=order;self.clock=[[self.a.scalar(c)]+[self.a.zero]*order]+[[self.a.zero]*(order+1)for _ in range(3)]
  self.records=[]
 def source(self,slot):
  source2=[T/(2*c*c),0,0,0,s00,s11,T-s00-s11,s01,s02,s12,0,0,0]
  ans=[{ZERO:self.a.scalar(source2[slot])}if source2[slot]else{}]
  for degree in (1,0):
   value=self.a.atom('source',(degree,slot))
   if degree==0 and slot==0:value=self.a.add(value,self.a.atom('source',(0,13)))
   ans.append({ZERO:value})
  return tuple(ans[:self.depth+1]+[{}]*max(0,self.depth-2))
 def source_trace(self):return tuple(polyadd(self.a,*rows)for rows in zip(self.source(4),self.source(5),self.source(6)))
 def setup(self,depth):
  self.depth=depth
  self.Jclocks=[tuple({ZERO:row[k]}if row[k]!=self.a.zero else{} for k in range(depth+1))for row in self.clock]
  self.ellclock=[]
  for k in range(depth+1):
   rows=[self.Jclocks[0][k]]
   for j in range(3):rows.append(shiftpoly(self.Jclocks[j+1][k],tuple(int(i==j)for i in range(3))))
   self.ellclock.append(polyadd(self.a,*rows))
  self.memoR={};self.memoJ={};self.memoWord={}
 def js(self,index,X):
  key=(index,tuple(tuple(sorted(p.items()))for p in X))
  if key in self.memoJ:return self.memoJ[key]
  ans=[]
  for k in range(self.depth+1):
   ans.append(polyadd(self.a,*(weighted(self.a,r,self.Jclocks[index][i],X[j])for i in range(k+1)for j in range(k-i+1)for r in [k-i-j])))
  self.memoJ[key]=tuple(ans);return tuple(ans)
 def resolvent(self,X):
  key=tuple(tuple(sorted(p.items()))for p in X)
  if key in self.memoR:return self.memoR[key]
  ans=[]
  for k in range(self.depth+1):
   lower=[]
   for i in range(k+1):
    for j in range(k+1-i):
     r=k-i-j
     if i==0 and r==0:continue
     lower.append(weighted(self.a,r,self.ellclock[i],ans[j]))
   residual=polyadd(self.a,X[k],polyscale(self.a,-1,polyadd(self.a,*lower)))
   ans.append(polyscale(self.a,1/c,residual))
  self.memoR[key]=tuple(ans);return tuple(ans)
 def word(self,tokens,X):
  key=(tokens,tuple(tuple(sorted(p.items()))for p in X))
  if key in self.memoWord:return self.memoWord[key]
  out=X
  for t in reversed(tokens):out=self.resolvent(out)if t=='R'else self.js(int(t[1]),out)
  self.memoWord[key]=out;return out
 def average(self,poly):
  out=[]
  for e,v in poly.items():
   if any(i%2 for i in e):continue
   mu=s.prod(s.factorial2(i-1)for i in e)/s.factorial2(sum(e)+1)/(sum(e)+2)
   out.append(self.a.scale(mu,v))
  return self.a.add(*out)
 def table(self,a,b,equation=None):
  rows=defaultdict(lambda:s.S.Zero)
  for u,v in ((a,b),(b,a)):rows[('R','J'+str(u),'R','J'+str(v),'R')]+=1
  if equation is None:return [((0,0,0),word,coef)for word,coef in rows.items()]
  out=[]
  for word,coef in rows.items():
   for j,tok in enumerate(word):
    if tok=='R':out.append((ZERO if equation==0 else tuple(int(i==equation-1)for i in range(3)),word[:j]+('R','R')+word[j+1:],coef))
    elif tok=='J'+str(equation):out.append((ZERO,word[:j]+word[j+1:],-coef))
  return out
 def applyT(self,a,b,X,equation=None):
  out=[{}for _ in range(self.depth+1)]
  for ell,word,coef in self.table(a,b,equation):
   result=self.word(word,X)
   for k in range(self.depth+1):out[k]=polyadd(self.a,out[k],polyscale(self.a,coef,shiftpoly(result[k],ell)))
  return [self.average(row)for row in out]
 def force_or_energy(self,equation):
  if equation is None:
   affine=[self.js(a,self.source(a))for a in range(4)]
   out=[self.a.add(*(row[k].get(ZERO,self.a.zero)for row in affine))for k in range(self.depth+1)]
  else:out=[self.a.scale(-1,row.get(ZERO,self.a.zero))for row in self.source(equation)]
  terms=[(s.Rational(1,2),self.applyT(0,0,self.source_trace(),equation))]
  for i in range(3):terms.append((-s.Rational(1,2),self.applyT(i+1,i+1,self.source(4+i),equation)))
  for i,j,slot in ((0,1,7),(0,2,8),(1,2,9)):terms.append((-1,self.applyT(i+1,j+1,self.source(slot),equation)))
  for i in range(3):terms.append((-1,self.applyT(0,i+1,self.source(10+i),equation)))
  return [self.a.add(out[k],*(self.a.scale(coef,series[k])for coef,series in terms))for k in range(self.depth+1)]
 def generate(self):
  self.setup(0)
  assert all(self.force_or_energy(a)[0]==self.a.zero for a in range(4))
  self.leading_energy=self.force_or_energy(None)[0]
  for k in range(1,self.order+1):
   self.setup(k);residual=[self.force_or_energy(a)[k]for a in range(4)]
   old=[row[:]for row in self.clock]
   for a in range(4):
    expr=self.a.atom('clock',(k,a));self.clock[a][k]=expr
    definition=self.a.add(*(self.a.scale(-JI[a,b],residual[b])for b in range(4)))
    self.a.clock_def[(k,a)]=definition
   self.setup(k)
   corrected=[]
   for a in range(4):
    new=self.force_or_energy(a)[k]
    corrected.append(new)
    expected=self.a.add(residual[a],*(self.a.scale(J[a,b],self.clock[b][k])for b in range(4)))
    assert new==expected,(k,a,len(self.a.polys[new]),len(self.a.polys[expected]))
   energy=self.force_or_energy(None)[k]
   newest={self.a.polys[self.clock[a][k]][0][0][0]for a in range(4)}
   assert not any(set(word)&newest for word,coef in self.a.polys[energy])
   self.records.append({'order':k,'residual_exprs':residual,'corrected_force_exprs':corrected,
     'clock_exprs':[self.clock[a][k]for a in range(4)],
     'clock_definition_exprs':[self.a.clock_def[(k,a)]for a in range(4)],'energy_expr':energy})
   print('PASS',k,'nodes',len(self.a.nodes),'polys',len(self.a.polys),'force terms',[len(self.a.polys[x])for x in residual],flush=True)
  return self



def state_normalize(state):
 return {w:norm(v)for w,v in state.items()if norm(v)!=0}


def state_sum(*states):
 answer=defaultdict(lambda:s.S.Zero)
 for st in states:
  for w,v in st.items():answer[w]+=v
 return state_normalize(answer)


def state_scale(v,state):return state_normalize({w:v*x for w,x in state.items()})


def moyal_differential(order,left_derivative,right_derivative,state):
 """Full finite Moyal coefficient for the original100 canonical pairs.

 Alpha=(q-left,p-left); the right derivative interchanges its two halves.
 Repeated canonical contractions are collected as one multiindex, including
 (i/2)^r (-1)^|beta|/(alpha! beta!), not an unspecified differential oracle.
 """
 result={}
 for slots in combinations_with_replacement(range(200),order):
  alpha=[0]*200
  for j in slots:alpha[j]+=1
  alpha=tuple(alpha);beta=alpha[100:]+alpha[:100]
  right=right_derivative(beta,state)
  if not right:continue
  coefficient=(s.I/2)**order*(-1)**sum(alpha[100:])/s.prod(factorial(v)for v in alpha)
  image=state_sum(*(state_scale(value,left_derivative(alpha,{word:s.S.One}))for word,value in right.items()))
  result=state_sum(result,state_scale(coefficient,image))
 return result


class SourceEvaluator:
 """Evaluate the closed DAG on original finite-CAR symbols, at actual phase."""
 def __init__(self,engine,factory,phase,clockjets,sourceS):
  self.engine=engine;self.a=engine.a;self.factory=factory;self.phase=tuple(phase)
  self.sourceS=sourceS
  self.jetdata={c:clockjets['principal_clock'],T:clockjets['traceS2']}
  self.pointscalars={c:s.sympify(self.jetdata[c]['value']),T:s.sympify(self.jetdata[T]['value']),
   s00:sourceS[0,0],s11:sourceS[1,1],s01:sourceS[0,1],s02:sourceS[0,2],s12:sourceS[1,2]}
  self.actual=self.basis_leaves((144,396))
  self.pairs=self.actual['order1_pairs']
 @lru_cache(None)
 def basis_leaves(self,word):return self.factory.at(self.phase,{word:s.S.One})
 @lru_cache(None)
 def scalar_environment(self,phase):
  if phase==self.phase:return self.pointscalars
  q,x,A,sc,ga,cf,original=self.factory.background(phase[:100])
  p=s.Matrix(phase[100:]);n=self.factory.y[0];v=s.prod(q[j]for j in(0,2,5))
  aa=norm((p[:6,:].T*cf['K']*p[:6,:])[0]/N+s.diff((p[6:,:].T*sc['principal']*p[6:,:])[0],n))
  Pi=rational(ga['a']*p[6:,:]).reshape(3,12)
  L=original['e'][1:,1:];Li=L.inv()
  gram=rational(v*Li.T*Pi*self.factory.weyl.native.gauge.gram_inverse*Pi.T*Li/2)
  tr=s.trace(gram)
  return {c:s.sqrt(tr/(2*aa)),T:tr,s00:gram[0,0],s11:gram[1,1],s01:gram[0,1],s02:gram[0,2],s12:gram[1,2]}
 def coefficient(self,x,phase):return norm(x.subs(self.scalar_environment(tuple(phase)),simultaneous=True))
 def evaluate(self,expr,phase,state):
  return state_sum(*(state_scale(v,self.evaluate_basis(expr,tuple(phase),w))for w,v in state.items()))
 @lru_cache(None)
 def evaluate_basis(self,expr,phase,word):
  result={}
  for atoms,coef in self.a.polys[expr]:
   image={word:s.S.One}
   for atom in reversed(atoms):image=self.atom_action(atom,phase,image)
   result=state_sum(result,state_scale(self.coefficient(coef,phase),image))
  return result
 def atom_action(self,atom,phase,state):
  kind,central,key=self.a.nodes[atom]
  if kind=='clock':return self.evaluate(self.a.clock_def[key],phase,state)
  if kind=='source':
   degree,slot=key
   if phase==self.phase and degree==1:
    op=self.pairs[slot]
    return state_sum(state_scale(op['identity'],state),apply_superposition(op['current'],state))
   return state_sum(*(state_scale(v,(self.basis_leaves(w)if phase==self.phase else self.factory.at(phase,{w:s.S.One}))['atoms'][degree][slot])for w,v in state.items()))
  assert kind=='moyal'
  r,left,right=key
  if phase==self.phase and central and r==2 and self.small_scalar_jet(left) and self.small_scalar_jet(right):
   ja=self.scalar_twojet(left);jb=self.scalar_twojet(right)
   value=0
   for (i,j),v in ja[2].todok().items():
    ii=i+100 if i<100 else i-100;jj=j+100 if j<100 else j-100
    value+=v*(1 if i<100 else -1)*(1 if j<100 else -1)*jb[2][ii,jj]
   return state_scale(norm(-value/8),state)
  return moyal_differential(r,lambda alpha,st:self.derivative(left,alpha,phase,st),
   lambda alpha,st:self.derivative(right,alpha,phase,st),state)
 def small_scalar_jet(self,expr):
  return all(not word and coef.free_symbols<={c,T} for word,coef in self.a.polys[expr])
 @lru_cache(None)
 def scalar_twojet(self,expr):
  assert all(not word for word,coef in self.a.polys[expr]),'higher geometric nodes use the general differential evaluator'
  f=sum(coef for word,coef in self.a.polys[expr]);assert f.free_symbols<={c,T},f
  env=self.pointscalars
  g=s.zeros(200,1);H=s.zeros(200)
  gs={x:decode(self.jetdata[x]['gradient200'])for x in(c,T)}
  hs={x:decode(self.jetdata[x]['Hessian200'])for x in(c,T)}
  for x in(c,T):
   d=self.coefficient(s.diff(f,x),self.phase);g+=d*gs[x];H+=d*hs[x]
   for y in(c,T):H+=self.coefficient(s.diff(f,x,y),self.phase)*gs[x]*gs[y].T
  return self.coefficient(f,self.phase),rational(g),rational(H)
 def derivative(self,expr,alpha,phase,state):
  return state_sum(*(state_scale(v,self.derivative_basis(expr,tuple(alpha),tuple(phase),w))for w,v in state.items()))
 @lru_cache(None)
 def derivative_basis(self,expr,alpha,phase,word):
  if not any(alpha):return self.evaluate_basis(expr,phase,word)
  variables={j:s.Dummy('actual_phase_'+str(j),positive=True)if j in(0,2,5)else s.Dummy('actual_phase_'+str(j),real=True)
    for j,count in enumerate(alpha)if count}
  argument=tuple(variables.get(j,v)for j,v in enumerate(phase))
  image=self.evaluate_basis(expr,argument,word)
  at={v:phase[j]for j,v in variables.items()}
  out={}
  for w,value in image.items():
   for j,v in variables.items():value=s.diff(value,v,alpha[j])
   value=norm(value.subs(at,simultaneous=True))
   if value:out[w]=value
  return out


def inspect_and_export(engine):
 a=engine.a;seenp=set();seenn=set()
 def visit_expr(e):
  if e in seenp:return
  seenp.add(e)
  for word,coef in a.polys[e]:
   for atom in word:
    if atom in seenn:continue
    seenn.add(atom);kind,central,key=a.nodes[atom]
    if kind=='moyal':visit_expr(key[1]);visit_expr(key[2])
    if kind=='clock':visit_expr(a.clock_def[key])
 @lru_cache(None)
 def clock_levels(e):
  out=set()
  for word,coef in a.polys[e]:
   for atom in word:
    kind,central,key=a.nodes[atom]
    if kind=='clock':out.add(key[0])
    if kind=='moyal':out.update(clock_levels(key[1]));out.update(clock_levels(key[2]))
  return frozenset(out)
 @lru_cache(None)
 def degree(e):
  answer=set()
  for word,coef in a.polys[e]:
   weight=norm(2*(T*s.diff(coef,T)+sum(x*s.diff(coef,x)for x in(s00,s11,s01,s02,s12)))/coef)
   assert weight.is_Integer,weight
   for atom in word:
    kind,central,key=a.nodes[atom]
    if kind=='source':weight+=key[0]
    elif kind=='clock':weight-=key[0]
    else:weight+=degree(key[1])+degree(key[2])-key[0]
   answer.add(int(weight))
  assert len(answer)<=1,answer
  return next(iter(answer))if answer else 0
 @lru_cache(None)
 def grade(e):
  possible=set()
  for word,coef in a.polys[e]:
   degrees={0}
   for atom in word:
    kind,central,key=a.nodes[atom]
    if kind=='source':g={int(key==(0,13))}
    elif kind=='clock':g=grade(a.clock_def[key])
    else:g={x+y for x in grade(key[1])for y in grade(key[2])}
    degrees={x+y for x in degrees for y in g}
   possible.update(degrees)
  return frozenset(possible)
 visit_expr(engine.leading_energy)
 traces=[]
 for row in engine.records:
  k=row['order']
  for e in row['residual_exprs']+row['clock_definition_exprs']+[row['energy_expr']]:
   assert all(j<k for j in clock_levels(e))
  for e in row['residual_exprs']:
   assert degree(e)==2-k
  for e in row['clock_definition_exprs']:
   assert degree(e)==-k and all(2*g<=k for g in grade(e))
  assert degree(row['energy_expr'])==2-k
  for name in('residual_exprs','corrected_force_exprs','clock_exprs','clock_definition_exprs'):
   for e in row[name]:visit_expr(e)
  visit_expr(row['energy_expr'])
  traces.append({**row,'all_sub_DAGs_only_earlier_clocks':True,
   'clock_source_grade_support':[sorted(grade(e))for e in row['clock_definition_exprs']],
   'clock_homogeneous_degrees':[degree(e)for e in row['clock_definition_exprs']],
   'residual_term_counts':[len(a.polys[e])for e in row['residual_exprs']]})
 pmap={old:j for j,old in enumerate(sorted(seenp))};nmap={old:j for j,old in enumerate(sorted(seenn))}
 nodes=[]
 for old in sorted(seenn):
  kind,central,key=a.nodes[old]
  if kind=='moyal':key=(key[0],pmap[key[1]],pmap[key[2]])
  nodes.append([kind,central,list(key)])
 polys=[[[[nmap[i]for i in word],str(coef)]for word,coef in a.polys[old]]for old in sorted(seenp)]
 for row in traces:
  for key in('residual_exprs','corrected_force_exprs','clock_exprs','clock_definition_exprs'):row[key]=[pmap[e]for e in row[key]]
  row['energy_expr']=pmap[row['energy_expr']]
 return {'nodes':nodes,'polys':polys,'clock_def':[{'order':k,'axis':axis,'expression':pmap[e]}for(k,axis),e in sorted(a.clock_def.items())],
  'leading_energy_expr':pmap[engine.leading_energy],'stages':traces,
  'reachable_node_count':len(nodes),'reachable_expression_count':len(polys)}


def source_uniform_law():
 raw=OrderedTemporalCoefficients();n,*b=raw.y
 inputs=[T/(2*c*c),0,0,0,s00,s11,T-s00-s11,s01,s02,s12,0,0,0]
 H=sum(f*x for f,x in zip(raw.coefficients,inputs))
 F=-s.Matrix([s.diff(H,y)for y in raw.y]);at={n:c,**dict.fromkeys(b,0)}
 equal(F.subs(at).applyfunc(norm),s.zeros(4,1))
 actual=F.jacobian(raw.y).subs(at).applyfunc(norm)
 equal(actual,J);equal((J*JI).applyfunc(norm),s.eye(4));equal((JI*J).applyfunc(norm),s.eye(4))
 from source_temporal_cone_resolvent import cone_expression
 e=Engine(1);ell=s.symbols('l0:4')
 for a in range(4):
  for b in range(4):
   for equation in(None,0,1,2,3):
    got=defaultdict(lambda:s.S.Zero)
    for exponent,word,v in e.table(a,b,equation):got[word]+=v*s.prod(ell[j+1]**exponent[j]for j in range(3))
    wanted={w:v.subs(ell[0],1)if isinstance(v,s.Basic)else v for w,v in cone_expression(a,b,equation).items()}
    assert {w:norm(v)for w,v in got.items()if norm(v)}=={w:norm(v)for w,v in wanted.items()if norm(v)}
 return {'original_thirteen_weights':list(map(str,raw.coefficients)),
  'original_principal_force_Jacobian':encode(J),'source_generated_two_sided_inverse':encode(JI),
  'cone_R_J_table_matches_original_source_maps':True,
  'uniform_filtration_proof':[
   'A Moyal coefficient r differentiates its two factors r times in total canonical momentum. Its exact finite100-pair multiindex sum therefore lowers momentum degree by r; configuration derivatives do not change that degree.',
   'C0=(c,0,0,0) is the generated scalar root on the original cone and c>0. The angular Jordan operator has leading multiplication c, independent of ell. Its coefficient-k inverse equation divides by c and reads only j<k because every other summand has i+j+r=k with (i,r)!=(0,0).',
   'Each fixed k therefore uses finitely many source homogeneous leaves, earlier clock coefficients, canonical derivative orders r<=k and polynomial angular moments. Neither a force remainder nor a completed inverse is an input.',
   'For k>=1, a term containing m>=1 copies of a new C_-k and additional lower-clock/derivative cost d+r has total loss m*k+d+r. It can reach force order2-k only when (m-1)*k+d+r=0, hence m=1 and d=r=0.',
   'At that surviving degree all principal factors are scalar. Literal original13 time differentiation gives exactly the displayed J2*C_-k. The constructor evaluates the old-clock force remainder R_k itself, then defines C_-k=-J2^-1 R_k. The checked two-sided inverse cancels that complete coefficient and does not change any higher order.',
   'Induction gives every coefficient and all four zero formal force series. Any two series with this generated principal root first differ at some k; the same invertible J2 kills that difference, giving uniqueness in this formal-symbol class.',
   'The principal energy derivative vanishes by the original four forces. Thus energy coefficient2-k is generated from earlier clocks alone, by the same original retraction, not ordinary commuting substitution.',
   'The original raising leaf Y/n has source grade1 and starts at momentum0, costing two degrees. Every derivative preserves source grade and every product adds it. Induction gives grade at most floor(k/2) in C_-k. On particle number m, words with more than m raises vanish by the original FockFilteredWords theorem, with all boson factors retained.'
  ],
  'uniform_scope':'The proof is the constructor filtration/induction argument for every integer k>=1. The exported k1..k4 DAGs are concrete executions and independent consumers, not a finite test standing in for that uniform argument.',
  'nonformal_responsibility':'The generated formal symbols do not establish Borel or operator summation, correction of a smoothing remainder, a common closed quantum-clock domain, a spectral measure, or a lifetime.'}


def actual_consumers(engine,paid):
 principal=paid['source_principal_clock_cone'];source=principal['original_source_factors']
 factory=SourceWeylLeafFactory();point=factory.source_point
 p=decode(principal['actual_source_cotangent_witness']['canonical_p100'])
 phase=tuple(point[j]for j in factory.free)+tuple(p)
 word=(144,396);unit={word:s.S.One}
 ev=SourceEvaluator(engine,factory,phase,paid['source_clock_principal_jets']['actual_consumer'],
  decode(principal['actual_source_cotangent_witness']['source_S2']))
 data=ev.actual;timepoint=dict(zip(factory.y,(N,0,0,0)))
 def at_time(state):return state_normalize({w:v.subs(timepoint)for w,v in state.items()})
 second=paid['source_clock_second_order']['actual_consumer'];sub=paid['source_clock_subprincipal']
 component_map={'coframe':data['components']['coframe'][0],
  'scalar_form':data['components']['scalar'][0],'gauge':data['components']['gauge'][0],
  'matter_noY':data['components']['matter_noY'],'original_Y':data['components']['original_Y']}
 decode_state=lambda rows:{tuple(w):s.sympify(v)for w,v in rows}
 for key,value in component_map.items():assert not state_sum(at_time(value),state_scale(-1,decode_state(second['original_zero_order_Weyl_components'][key])))
 assert not state_sum(at_time(data['homogeneous'][1]),state_scale(-1,decode_state(sub['actual_consumer']['first_reduced_energy_image'])))
 assert not state_sum(state_scale(N,data['atoms'][0][13]),state_scale(-1,at_time(data['components']['original_Y'])))
 for degree in range(3):
  rebuilt=state_sum(*(state_scale(f,data['atoms'][degree][a])for a,f in enumerate(factory.weights)),
    state_scale(factory.y[0],data['atoms'][degree][13]))
  assert not state_sum(rebuilt,state_scale(-1,data['homogeneous'][degree]))
 for i,pair in enumerate(ev.pairs):
  saved=sub['all13_original_atom_order1_symbols'][i]
  zero=norm(pair['identity']-s.sympify(saved['identity']));assert zero==0
  equal(pair['current'],decode(saved['current504']))
 full_pairs=[]
 for axis in range(4):
  identity=0;matrix=s.zeros(504)
  for atoms,coef in engine.a.polys[engine.a.clock_def[(1,axis)]]:
   assert len(atoms)==1
   kind,central,key=engine.a.nodes[atoms[0]];assert kind=='source'and key[0]==1
   value=ev.coefficient(coef,phase);op=ev.pairs[key[1]]
   identity+=value*op['identity'];matrix+=value*op['current']
  expected=sub['four_clock_order_minus1_symbols'][axis]
  assert norm(identity-s.sympify(expected['identity']))==0
  equal(rational(matrix),decode(expected['current504']))
  full_pairs.append({'identity':str(norm(identity)),'current504':encode(rational(matrix))})
 print('PASS source fourteen leaf split, original five order0 components and complete504 C_minus1 symbols',flush=True)
 clocks={};energies={};force_images={}
 for k in(1,2):
  clocks[k]=[ev.evaluate(engine.a.clock_def[(k,a)],phase,unit)for a in range(4)]
  expected=(sub['actual_consumer']['clock_order_minus1_images']if k==1 else second['four_clock_order_minus2'])
  for image,want in zip(clocks[k],expected):assert not state_sum(image,state_scale(-1,decode_state(want)))
  row=engine.records[k-1]
  force_images[k]=[ev.evaluate(x,phase,unit)for x in row['corrected_force_exprs']]
  assert all(not image for image in force_images[k])
  energies[k]=ev.evaluate(row['energy_expr'],phase,unit)
  want=sub['actual_consumer']['first_reduced_energy_image']if k==1 else second['first_reduced_energy_order0']
  assert not state_sum(energies[k],state_scale(-1,decode_state(want)))
 print('PASS new recursive full source N2 C_minus1/C_minus2, both reduced energies and every corrected force',flush=True)
 # Evaluate a genuine full finite canonical Moyal coefficient, independently
 # of the source C/T two-jet acceleration: second derivative of original A2.
 used={}
 def left(alpha,state):
  key=tuple(alpha)
  if key not in used:used[key]=factory.leaf_derivative(0,2,key,phase,unit)
  return state_sum(*(state_scale(value,used[key])for w,value in state.items()))
 def right(alpha,state):
  if alpha[100]==2 and sum(alpha)==2:return state_scale(2,state)
  return {}
 moyal=moyal_differential(2,left,right,unit)
 alpha=[0]*200;alpha[0]=2
 derivative=used[tuple(alpha)]
 Ajet=paid['source_clock_principal_jets']['actual_consumer']['a0_2']
 assert not state_sum(derivative,state_scale(-decode(Ajet['Hessian200'])[0,0],unit))
 assert not state_sum(moyal,state_scale(s.Rational(1,4),derivative))
 assert moyal
 over=[0]*200;over[100]=3
 assert not factory.leaf_derivative(0,2,tuple(over),phase,unit)
 return {'source_configuration':encode(s.Matrix(phase[:100])),'source_canonical_momentum':encode(p),
  'all14_original_leaves_rebuild_each_homogeneous_degree':True,'original_Y_split_exactly_once':True,
  'four_full504_clock_order_minus1_symbols':full_pairs,
  'actual_N2_clock_coefficients':{str(k):[encode_state(v)for v in values]for k,values in clocks.items()},
  'actual_N2_reduced_energy_coefficients':{str(k):encode_state(v)for k,v in energies.items()},
  'all4_force_coefficients_at_both_orders_zero':True,
  'source_q0_second_derivative_A2':encode_state(derivative),
  'actual_Moyal2_A2_pq0_squared':encode_state(moyal),
  'excess_momentum_derivative_vanishes_by_original_degree':True,
  'actual_differential_evaluator':'SourceWeylLeafFactory.leaf_derivative symbolically differentiates the actual source coefficients in exactly the requested original phase coordinates, then evaluates at the source point. It accepts no caller-supplied jet.',
  'high_order_scope':'The actual full504/N2 numerical consumers here are k1 and k2. The exported k3 and k4 objects are generated complete formal differential DAGs, including their unevaluated but finitely evaluable higher source derivatives.'}


def write_dag_asset(dag):
 payload=json.dumps(dag,separators=(',',':'),sort_keys=True).encode('utf-8')
 stream=io.BytesIO()
 with gzip.GzipFile(filename='',mode='wb',fileobj=stream,mtime=0,compresslevel=9) as compressed:
  compressed.write(payload)
 data=stream.getvalue();path=HERE/'source_clock_symbol_recursion.dag.json.gz'
 path.write_bytes(data)
 assert json.loads(gzip.decompress(data))==dag
 return {'path':str(path.relative_to(ROOT)),'codec':'deterministic gzip (mtime=0), UTF-8 JSON',
  'sha256':hashlib.sha256(data).hexdigest(),'decompressed_sha256':hashlib.sha256(payload).hexdigest(),
  'compressed_bytes':len(data),'decompressed_bytes':len(payload),
  'reachable_node_count':dag['reachable_node_count'],'reachable_expression_count':dag['reachable_expression_count'],
  'stage_summaries':[{key:row[key]for key in('order','residual_term_counts','clock_source_grade_support','clock_homogeneous_degrees','all_sub_DAGs_only_earlier_clocks')}for row in dag['stages']]}


def load_dag_asset(descriptor):
 data=(ROOT/descriptor['path']).read_bytes()
 assert hashlib.sha256(data).hexdigest()==descriptor['sha256']
 payload=gzip.decompress(data)
 assert hashlib.sha256(payload).hexdigest()==descriptor['decompressed_sha256']
 return json.loads(payload)


def main():
 started=time.monotonic()
 names=('source_principal_clock_cone','independent_source_principal_clock_cone',
  'source_clock_subprincipal','independent_source_clock_subprincipal',
  'source_clock_second_order','independent_source_clock_second_order',
  'source_clock_principal_jets','independent_source_clock_principal_jets',
  'source_temporal_cone_resolvent','independent_source_temporal_cone_resolvent',
  'source_common_weyl_symbol','independent_source_common_weyl_symbol')
 paid={name:bound(name)for name in names}
 uniform=source_uniform_law()
 engine=Engine(4).generate()
 dag=inspect_and_export(engine)
 print('PASS complete exported four-order source differential DAG closure, homogeneity and Fock grades',flush=True)
 actual=actual_consumers(engine,paid)
 dag_asset=write_dag_asset(dag)
 paths=[HERE/(name+'.json')for name in names]+[HERE/name for name in(
  'source_clock_symbol_recursion.py','source_scalar_weyl_symbol.py','source_common_weyl_symbol.py',
  'source_temporal_coframe_pairing.py','source_reducing_coframe_metric.py','source_quantum_ordered_temporal.py',
  'source_coframe_live_ordering.py','source_gauss_quantum_current.py','source_temporal_cone_resolvent.py',
  'FockFilteredWords.lean','FockRaisingTensor.lean','FockRaising.lean','source_clock_symbol_recursion.dag.json.gz')]
 result={'root':ROOT_ID,'scope':'ALL_ORDER_SOURCE_CANONICAL_FORMAL_CLOCK_AND_REDUCED_ENERGY_RECURSION',
  'source_sha256':paid['source_common_weyl_symbol']['source_sha256'],
  'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},
  'source_owned_construction':uniform,
  'DAG_schema':{'polys':'polys[id] is a sum of [ordered atom word, central coefficient in c,T,S00,S11,S01,S02,S12]. S22=T-S00-S11, A=T/(2c^2), with c and all S actual source functions.',
   'nodes':'[kind, central, key]; source key=[momentum degree,slot]; clock key=[k,axis] has its generated clock_def; moyal key=[r,left expr,right expr] includes the full (i/2)^r multiindex coefficient.',
   'source':'Slots0..12 are extracted from the original thirteen rational time weights after full four-energy Weyl assembly. Slot13 is original Y/n at degree0 only; it is removed from grade0 slot0.',
   'scalar_derivatives':'c,T,S are source functions on the actual canonical200 phase chart, not frozen values. The two-jet acceleration applies only to pure c/T scalar expressions at the exact paid source point; all other expressions use the finite general derivative evaluator.',
   'Moyal_definition':'Sum over |alpha|+|beta|=r of (i/2)^r(-1)^|beta|/(alpha! beta!) (partial_z^alpha partial_p^beta A)(partial_p^alpha partial_z^beta B), with100 original canonical pairs and ordered CAR products.'},
  'differential_DAG':dag_asset,'actual_consumers':actual,
  'formal_operator_summation_or_spectrum_generated':False,
  'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
 (HERE/'source_clock_symbol_recursion.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
 print('PASS source all-order clock symbol recursion',result['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
