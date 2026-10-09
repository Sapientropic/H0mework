"""Full raw gauge-current second variation on the same original289 axial legs."""
import importlib.util,json,sys,time
from pathlib import Path
import sympy as s
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1]
sys.path.insert(0,str(BASE/'nonlinear-contact'))
from slice_checks import GAMMA
u,q=s.symbols('u q',real=True); r,w=s.symbols('r w',real=True)
a=json.loads((BASE/'active-gauge/receipt.json').read_text());f=json.loads((HERE.parent/'light-modes/field-receipt.json').read_text())
vs=json.loads((BASE/'matter-vertices/receipt.json').read_text());raw=json.loads((HERE/'vertices-receipt.json').read_text())['vertices']
fields=a['fields'];idx={(x['group'],tuple(x['coordinate'])):i for i,x in enumerate(fields)}
N=s.sympify(a['source_lapse']);e0=s.diag(N,1,1,1);ei=e0.inv()
leg=s.Matrix(289,1,lambda i,j:0)
for i,j,c in f['axial_original289_pole_leg']['entries']:leg[i]=s.sympify(c,locals={'u':u,'q':q})
minus=leg.subs({u:-u,q:-q},simultaneous=True)
e=s.Matrix(4,4,lambda i,j:leg[idx['coframe',(i,j)]])
assert e==s.Matrix(4,4,lambda i,j:minus[idx['coframe',(i,j)]])
X=ei*e; tr=s.trace(X)
adj0=e0.adjugate();adj1=(N*(tr*ei-ei*e*ei)).applyfunc(s.expand)
adj2=(N*((tr*tr-s.trace(X*X))*ei-2*tr*ei*e*ei+2*ei*e*ei*e*ei)).applyfunc(s.expand)
# Native triplet occupies the exact Lambda2 color_i wedge hyper+ slots.
import itertools
inside=[(d,t) for d in [6,2,4] for t in itertools.combinations(range(7),d)]
occ=[63*spin+inside.index((2,(color,5))) for spin in range(4) for color in range(3)];where={c:j for j,c in enumerate(occ)}
primal=[idx['primal_H',(im,spin,col)] for im in range(2) for spin in range(4) for col in range(3)]
dual=[idx['dual_H',(im,spin,col)] for im in range(2) for spin in range(4) for col in range(3)]
psi=s.Matrix([int(c==1)-int(c==3)+int(c==7)-int(c==9) for c in range(12)])
S=s.kronecker_product(s.Matrix(GAMMA[0])*s.diag(-1,-1,1,1),s.eye(3))
chi=s.sqrt(2)*psi.T*S
zero=s.zeros(289,1)
for i in range(12):zero[primal[i]]=s.re(psi[i]);zero[primal[12+i]]=s.im(psi[i]);zero[dual[i]]=s.re(chi[i]);zero[dual[12+i]]=s.im(chi[i])
def pairing(matrix,left,right):
 ans=0
 for (i,j),z in s.SparseMatrix(matrix).todok().items():
  for im1,im2,c in [(0,0,s.re(z)),(0,1,-s.im(z)),(1,0,-s.im(z)),(1,1,-s.re(z))]:
   if c:ans+=left[dual[12*im1+i]]*c*right[primal[12*im2+j]]
 return s.expand(ans)
primitive={(x['group'],tuple(x['coordinate'])):x for x in vs['primitive_vertices']}
rawBy={(x['group'],tuple(x['coordinate'])):s.sympify(x['polynomial'],locals={'u':u,'q':q}) for x in raw}
start=time.monotonic();out=[]
for aidx in range(12):
 blocks=[]
 for mu in range(4):
  v=primitive['gauge_A',(mu,aidx)]
  full=s.SparseMatrix(252,252,{(i,j):s.sympify(z) for i,j,z in v['operator']['entries']})
  full=full.extract(occ,occ)/(N*ei[mu,mu]);blocks.append(full)
 for mu in range(4):
  value=0;bare=0
  for b in range(4):
   B=blocks[b]
   two=pairing(B,minus,leg)+pairing(B,leg,minus)
   first=pairing(B,zero,leg)+pairing(B,leg,zero)
   second=pairing(B,zero,minus)+pairing(B,minus,zero)
   constant=pairing(B,zero,zero)
   bare+=adj0[mu,b]*two
   value+=adj0[mu,b]*two+adj1[mu,b]*(first+second)+adj2[mu,b]*constant
  bare=s.expand(bare);value=s.expand(value);contact=s.expand(value-bare)
  assert s.expand(bare-rawBy.get(('gauge_A',(mu,aidx)),0))==0
  if value:
   degree=min(sum(m) for m,c in s.Poly(value,u,q).terms())
   low=sum(c*u**i*q**j for (i,j),c in s.Poly(value,u,q).terms() if i+j==degree)
   print(mu,aidx,'terms',len(s.Poly(value,u,q).terms()),'contact',contact!=0,'low',s.factor(low),flush=True)
  out.append({'coordinate':[mu,aidx],'full_polynomial':str(value),'contact_polynomial':str(contact)})
selected=next(x for x in out if x['coordinate']==[1,1]);num=s.expand(s.sympify(selected['full_polynomial'],locals={'u':u,'q':q})/s.sqrt(15))
poly=s.Poly(num,u,q); assert all(i%2==j%2==0 for (i,j),c in poly.terms())
# Positive normalization fixes the actual pole legs supplied by the original g00 source.
C=s.Integer(58042407852806400000000000)
reduced=s.expand(-sum(c*w**((i+j)//2)*r**(i//2) for (i,j),c in poly.terms())/C/w)
assert s.expand(reduced.subs(w,0)-r)==0
remainder=s.cancel((reduced-r)/w)
assert s.fraction(remainder)[1].free_symbols==set()
terms=[{'r':i,'w':j,'coefficient':str(c)} for (i,j),c in s.Poly(remainder,r,w).terms()]
bound=sum(abs(c)*2**i for (i,j),c in s.Poly(remainder,r,w).terms())
eps=s.Rational(5234375,294988800512)
print('selected normalization',C,'remainder terms',len(terms),'bound',bound,'epsilon squared bound',s.factor(eps**2*bound),flush=True)
print('source branch r lower',s.Rational(125,162)-s.Rational(1,20),flush=True)
report={'scope':'ORIGINAL_RAW_GAUGE_CURRENT_MIXED_LIGHT_POLE_LEGS_WITH_COFAME_CONTACT',
 'source_sha256':a['source_sha256'],'normalization':'u pole residues of the original g00 forcing; physical lambda residues multiply lapse sqrt(2) on each leg',
 'native_gauge_labels':a['native_P286_labels'],'all48_bare_match_original158':True,
 'all48_current_coefficients':out,'selected_coordinate':[1,1],'selected_numerator_factor':str(C),
 'selected_normalized_remainder':terms,'selected_remainder_bound':str(bound),
 'selected_leading_u_residue':'9*sqrt(15)/6250','selected_leading_lambda_residue':'486*sqrt(15)/390625',
 'common_momentum_radius':str(eps),'nonzero_bound':str(eps**2*bound),
 'elapsed_seconds':round(time.monotonic()-start,3)}
(HERE/'contact-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
