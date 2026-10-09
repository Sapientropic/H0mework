"""Read the two exact original axial pole legs in all primitive raw matter currents."""
import json,itertools,time,hashlib
from pathlib import Path
import sympy as s
HERE=Path(__file__).resolve().parent; BASE=HERE.parents[1]
u,q=s.symbols('u q',real=True);p=s.symbols('p0:4',real=True)
ROOT=HERE.parents[4]
a=json.loads((BASE/'active-gauge/receipt.json').read_text())
f=json.loads((HERE.parent/'light-modes/field-receipt.json').read_text())
v=json.loads((BASE/'matter-vertices/receipt.json').read_text())
for path,digest in a['source_sha256'].items():
 assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==digest,path
N=s.sympify(a['source_lapse']); scale=N*s.sqrt(2)
fields=a['fields']; native={(x['group'],tuple(x['coordinate'])):i for i,x in enumerate(fields)}
leg=s.SparseMatrix(289,1,{(i,j):s.sympify(c,locals={'u':u,'q':q}) for i,j,c in f['axial_original289_pole_leg']['entries']})
minus=leg.subs({u:-u,q:-q},simultaneous=True)
inside=[(d,w) for d in [6,2,4] for w in itertools.combinations(range(7),d)]
occ=[63*spin+inside.index((2,(color,5))) for spin in range(4) for color in range(3)]
where={c:j for j,c in enumerate(occ)}
primal=[native['primal_H',(im,spin,col)] for im in range(2) for spin in range(4) for col in range(3)]
dual=[native['dual_H',(im,spin,col)] for im in range(2) for spin in range(4) for col in range(3)]
ph=[scale*u,0,0,s.I*s.sqrt(2)*q]
# Internal realification precedes substitution of the complex Fourier symbol.
out=[]
start=time.monotonic()
for n,b in enumerate(v['primitive_vertices']):
 terms=[]
 for i,j,c in b['operator']['entries']:
  if i not in where or j not in where: continue
  z=s.sympify(c,locals=dict(zip(map(str,p),p)))
  x,y=s.expand(s.re(z)),s.expand(s.im(z));i,j=where[i],where[j]
  for im1,im2,c in [(0,0,x),(0,1,-y),(1,0,-y),(1,1,-x)]:
   if c==0:continue
   cp=c.subs(dict(zip(p,ph)),simultaneous=True)
   cm=cp.subs({u:-u,q:-q},simultaneous=True)
   terms.append(minus[dual[12*im1+i]]*cp*leg[primal[12*im2+j]]+
      leg[dual[12*im1+i]]*cm*minus[primal[12*im2+j]])
 result=s.expand(sum(terms))
 out.append({'index':n,'group':b['group'],'coordinate':b['coordinate'],'polynomial':str(result)})
 if result!=0:
  degree=min(sum(m) for m,c in s.Poly(result,u,q).terms())
  low=s.Add(*[c*u**i*q**j for (i,j),c in s.Poly(result,u,q).terms() if i+j==degree])
  print(n,b['group'],b['coordinate'],'terms',len(s.Poly(result,u,q).terms()),'degree',degree,'low',s.factor(low),flush=True)
print('nonzero',sum(x['polynomial']!='0' for x in out),'seconds',time.monotonic()-start,flush=True)
(HERE/'vertices-receipt.json').write_text(json.dumps({'scope':'ALL158_PRIMITIVE_VERTICES_ON_ORIGINAL_LIGHT_POLE_LEGS','vertices':out,'source_sha256':a['source_sha256'],'internal_realification_precedes_Fourier':True,'independent_dual_from_full289':True,'nonzero_count':sum(x['polynomial']!='0' for x in out)},indent=2)+'\n')
