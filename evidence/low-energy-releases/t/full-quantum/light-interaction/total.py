"""Actual total source-action cubic with two generated light legs and an external P286 source."""
import importlib.util,sys,json,itertools,time
from pathlib import Path
import sympy as s
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1];ROOT=HERE.parents[4]
sys.path.insert(0,str(BASE));sys.path.insert(0,str(BASE/'nonlinear-contact'))
import exact_readout as src
from slice_checks import PAIRS,W,COLOR,source_matrices
u,q,r,w=s.symbols('u q r w',real=True)
a=json.loads((BASE/'active-gauge/receipt.json').read_text());f=json.loads((HERE.parent/'light-modes/field-receipt.json').read_text());mat=json.loads((HERE/'contact-receipt.json').read_text())
idx={(x['group'],tuple(x['coordinate'])):i for i,x in enumerate(a['fields'])}
leg=s.SparseMatrix(289,1,{(i,j):s.sympify(c,locals={'u':u,'q':q}) for i,j,c in f['axial_original289_pole_leg']['entries']});minus=leg.subs({u:-u,q:-q},simultaneous=True)
Ap=s.Matrix(4,12,lambda i,j:leg[idx['gauge_A',(i,j)]]);Am=s.Matrix(4,12,lambda i,j:minus[idx['gauge_A',(i,j)]])
Bp=s.Matrix(6,12,lambda i,j:leg[idx['gauge_B',(i,j)]]);Bm=s.Matrix(6,12,lambda i,j:minus[idx['gauge_B',(i,j)]])
source_matrices(ROOT);_,vacuum,degrees,hashes=src.parse_source(ROOT)
raw=src.generators([(0,1,2),(3,4)]);fund=[s.Matrix(m)*(s.I if im else 1) for _,im,m in raw]
assert fund[1]==s.diag(2*COLOR[0],s.zeros(5))
gram=s.Matrix(12,12,lambda i,j:s.re(-s.trace(fund[i]*fund[j])));native=gram.copy();native[-1,-1]=1
assert gram[-1,-1]==2
br={};gi=gram.inv()
for i,j in itertools.product(range(12),repeat=2):
 comm=fund[i]*fund[j]-fund[j]*fund[i];cs=gi*s.Matrix([s.re(-s.trace(t*comm)) for t in fund])
 assert sum((cs[c]*fund[c] for c in range(12)),s.zeros(7))==comm
 for c in range(12):
  if cs[c]:br[i,j,c]=cs[c]
basis4=list(itertools.combinations(range(7),4));vc=s.Matrix([vacuum.get(t,0) for t in basis4])
orbits=[s.Matrix(src.exterior_action(m,4))*(s.I if im else 1)*vc for _,im,m in raw]
for mu in range(4):
 assert sum((Ap[mu,j]*orbits[j] for j in range(12)),s.zeros(35,1)).applyfunc(s.expand)==s.zeros(35,1)
 assert sum((Am[mu,j]*orbits[j] for j in range(12)),s.zeros(35,1)).applyfunc(s.expand)==s.zeros(35,1)
print('PASS full light connection directions preserve actual scalar; scalar source exactly zero',flush=True)
def curvature_read(A,mu,gen):
 return s.Matrix(6,12,lambda pair,c:
  (sum(br.get((gen,b,c),0)*A[PAIRS[pair][1],b] for b in range(12)) if mu==PAIRS[pair][0] else 0)+
  (sum(br.get((b,gen,c),0)*A[PAIRS[pair][0],b] for b in range(12)) if mu==PAIRS[pair][1] else 0))
outputs=[];start=time.monotonic()
for rec in mat['all48_current_coefficients']:
 mu,gen=rec['coordinate'];fp=curvature_read(Ap,mu,gen);fm=curvature_read(Am,mu,gen)
 bf=s.expand(s.trace(native*(Bp.T*W*fm+Bm.T*W*fp)))
 matter=s.sympify(rec['full_polynomial'],locals={'u':u,'q':q});total=s.expand(bf+matter)
 if total:print(mu,gen,'terms',len(s.Poly(total,u,q).terms()),'BF',bf!=0,flush=True)
 outputs.append({'coordinate':[mu,gen],'matter':str(matter),'gauge_BF':str(bf),'total':str(total)})
selected=next(x for x in outputs if x['coordinate']==[1,1]);num=s.expand(s.sympify(selected['total'],locals={'u':u,'q':q})/s.sqrt(15));C=s.Integer(58042407852806400000000000)
poly=s.Poly(num,u,q);assert all(i%2==j%2==0 for (i,j),c in poly.terms())
reduced=s.expand(-sum(c*w**((i+j)//2)*r**(i//2) for (i,j),c in poly.terms())/C/w)
assert s.expand(reduced.subs(w,0)-r)==0
remainder=s.cancel((reduced-r)/w);assert s.fraction(remainder)[1].free_symbols==set()
terms=[{'r':i,'w':j,'coefficient':str(c)} for (i,j),c in s.Poly(remainder,r,w).terms()]
bound=sum(abs(c)*2**i for (i,j),c in s.Poly(remainder,r,w).terms());eps=s.Rational(5234375,294988800512)
assert eps**2*bound<s.Rational(1,20)
result={'scope':'TOTAL_ORIGINAL_ACTION_GAUGE_SOURCE_CUBIC_ON_ACTUAL_LIGHT_POLE_LEGS',
 'all48_total_source_cubics':outputs,'original_scalar_current_zero_on_whole_affine_light_connection_path':True,
 'selected_coordinate':[1,1],'selected_label':a['native_P286_labels'][1],
 'normalization_factor':str(C),'source_normalized_remainder':terms,'remainder_bound':str(bound),
 'domain':str(eps),'domain_error_bound':str(eps**2*bound),
 'leading_u_residue':'9*sqrt(15)/6250','leading_original_lambda_residue':'486*sqrt(15)/390625',
 'selected_bare_matter_differs':s.expand(s.sympify(selected['total'],locals={'u':u,'q':q})-next(s.sympify(x['polynomial'],locals={'u':u,'q':q}) for x in json.loads((HERE/'vertices-receipt.json').read_text())['vertices'] if x['index']==13))!=0,
 'clock':'lambda=lapse*sqrt(2)*u; k=sqrt(2)*q, no time replacement',
 'elapsed_seconds':round(time.monotonic()-start,3)}
(HERE/'total-receipt.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS full source cubic; generated uniform numerator bound',bound,flush=True)
