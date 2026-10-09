from pathlib import Path
import json,random
from fractions import Fraction as F
P=Path(__file__).resolve().parent;d=json.loads((P/'decoded-source.json').read_text());rng=random.Random(0)
def evaluate(terms,x):
 out=F(0)
 for powers,(a,b) in terms:
  term=F(a,b)
  for v,e in zip(x,powers):term*=v**e
  out+=term
 return out
def point(pole):
 if pole<2:
  p=[F(rng.randint(-3,3)) for _ in range(7)];p[pole]=F(0);return p
 A=[[F(rng.randint(-3,3)) for _ in range(2)] for _ in range(3)]
 Q=[[sum(A[i][a]*A[j][a] for a in range(2)) for j in range(3)] for i in range(3)]
 T=sum(Q[i][i] for i in range(3))/2
 return [F(rng.randint(1,3)),T,T-Q[0][0],T-Q[1][1],-Q[0][1],-Q[0][2],-Q[1][2]]
candidates={pole:[point(pole) for _ in range(100)] for pole in range(3)}
rows=[]
for i,coef in enumerate(d['coefficients']):
 for pole,e in enumerate(coef['poles']):
  if not e:continue
  for attempt in range(10000):
   x=candidates[pole][attempt];value=evaluate(coef['terms'],x)
   if value:
    rows.append({'coefficient':i,'pole':pole,'point':[[v.numerator,v.denominator] for v in x],'value':[value.numerator,value.denominator]});break
  else:raise ValueError((i,pole,'no witness'))
(P/'pole-witnesses.json').write_text(json.dumps(rows,separators=(',',':'))+'\n')
print('EXACT NONDIVISIBILITY WITNESSES',len(rows))
