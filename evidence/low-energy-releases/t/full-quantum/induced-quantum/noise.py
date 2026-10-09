"""Source Re-density noise, before any boson covariance is chosen."""
from pathlib import Path
import json,itertools,sys,hashlib
import sympy as s
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1];ROOT=HERE.parents[4]
sys.path.insert(0,str(BASE/'nonlinear-contact'))
from slice_checks import GAMMA,source_matrices
source_matrices(ROOT)
a=json.loads((BASE/'active-gauge/receipt.json').read_text()); v=json.loads((BASE/'matter-vertices/receipt.json').read_text())
for p,h in a['source_sha256'].items(): assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==h
inside=[(d,t) for d in [6,2,4] for t in itertools.combinations(range(7),d)]
w=s.zeros(252,1)
for spin,col,c in [(0,1,1),(1,0,-1),(2,1,1),(3,0,-1)]:w[63*spin+inside.index((2,(col,5)))]=s.Rational(c,2)
assert (w.conjugate().T*w)[0]==1
N=s.sympify(a['source_lapse']);S=s.kronecker_product(s.Matrix(GAMMA[0])*s.diag(-1,-1,1,1),s.eye(63));K=s.sqrt(2)*s.kronecker_product(s.diag(-1,-1,1,1),s.eye(63));Cinv=s.I*N*s.kronecker_product(s.Matrix(GAMMA[0]),s.eye(63))
p=s.symbols('p0:4',real=True);k=s.symbols('k1:4',real=True)
def matrix(rec):return s.SparseMatrix(*rec['shape'],{(i,j):s.sympify(z,locals=dict(zip(map(str,p),p))) for i,j,z in rec['entries']})
V=matrix(next(x['operator'] for x in v['primitive_vertices'] if x['group']=='coframe' and x['coordinate']==[0,0]))
assert V.diff(p[0])==s.zeros(252)
V0=V.subs(dict.fromkeys(p,0));Vp=V.subs(dict(zip(p,[0,*[s.I*x for x in k]])),simultaneous=True);Vm=V.subs(dict(zip(p,[0,*[-s.I*x for x in k]])),simultaneous=True)
# Actual Re-density at incoming0 and reciprocal ±k; cos(k.x) contributes 1/2 to each shift.
R0=-s.I/N*Cinv*V0;Rp=-s.I/N*Cinv*Vp;Rm=-s.I/N*Cinv*Vm
assert (K*R0+s.sqrt(2)*S*V0).applyfunc(s.expand)==s.zeros(252)
Bplus=((K*R0+(K*Rp).conjugate().T)/(2*N)).applyfunc(s.expand)
Bminus=((K*R0+(K*Rm).conjugate().T)/(2*N)).applyfunc(s.expand)
tauplus=(Bplus*w).applyfunc(s.expand);tauminus=(Bminus*w).applyfunc(s.expand)
noise=s.expand((tauplus.conjugate().T*tauplus+tauminus.conjugate().T*tauminus)[0])
expected=s.Rational(20,3)+s.Rational(125,54)*sum(x*x for x in k)
assert s.expand(noise-expected)==0
# The full initial raw scalar operator is an arrow; its Re-density has a real returned norm.
sigma=list(itertools.combinations(range(7),4)).index((0,2,3,4))
Y=matrix(next(x['operator'] for x in v['primitive_vertices'] if x['group']=='scalar' and x['coordinate']==[0,sigma]))
RY=-s.I/N*Cinv*Y;WY=K*RY
assert s.expand((w.conjugate().T*WY*w)[0])==0
assert s.expand((w.conjugate().T*WY*WY*w)[0])==0
H=-2*(WY+WY.conjugate().T)
assert H==H.conjugate().T
scalarNoise=s.expand((w.conjugate().T*H*H*w)[0])
assert scalarNoise==s.Rational(108,125)
report={'scope':'ORIGINAL_FULL_FOCK_REAL_DENSITY_CURRENT_NOISE',
 'source_sha256':a['source_sha256'],
 'actual_prepared_vector_normalized':True,
 'coframe00_densitized_time_principal_zero':True,
 'coframe00_cosine_probe':'delta(g00)=cos(k.x); delta(e00)=-cos(k.x)/(2N)',
 'coframe00_shared_carrier':'incoming0 plus intermediate +k and -k; original source oneParticle only in incoming0',
 'initial_g00_cosine_noise':str(noise),
 'all_momenta_rotation_invariant':True,
 'coframe_noise_strictly_positive':True,
 'physical_word_normalization':'g00: (2/N) HermitianPart[dGamma(K) dGamma(Rcos)]; scalar: -4 HermitianPart[dGamma(K)dGamma(RY)]',
 'scalar_direction':[0,2,3,4],'scalar_raw_mean':0,'scalar_raw_ordered_square':0,'scalar_real_density_noise':str(scalarNoise),
 'no_new_quantum_state_or_target_covariance':True,
 'retarded_commutator_not_identified_with_noise':True}
(HERE/'noise-receipt.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2),flush=True)
