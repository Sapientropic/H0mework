from fractions import Fraction as F
import json,hashlib,re as regex
from pathlib import Path
BASE=Path(__file__).resolve().parent
class Q:
 def __init__(self,r=0,i=0): self.r=F(r);self.i=F(i)
 def __add__(self,b):
  b=c(b);return Q(self.r+b.r,self.i+b.i)
 __radd__=__add__
 def __neg__(self):return Q(-self.r,-self.i)
 def __sub__(self,b):return self+-c(b)
 def __rsub__(self,b):return c(b)+-self
 def __mul__(self,b):
  b=c(b);return Q(self.r*b.r-self.i*b.i,self.r*b.i+self.i*b.r)
 __rmul__=__mul__
 def __truediv__(self,b):
  b=c(b);d=b.r*b.r+b.i*b.i;return self*Q(b.r/d,-b.i/d)
 def conj(self):return Q(self.r,-self.i)
 def __eq__(self,b):b=c(b);return self.r==b.r and self.i==b.i
 def __repr__(self):return f'({self.r},{self.i})'
def c(x):return x if isinstance(x,Q) else Q(x)
def mat(x):return [[c(y) for y in r] for r in x]
def zero(n,m):return mat([[0]*m for _ in range(n)])
def eye(n):return mat([[int(i==j) for j in range(n)] for i in range(n)])
def diag(d):return mat([[d[i] if i==j else 0 for j in range(len(d))] for i in range(len(d))])
def add(A,B):return [[x+y for x,y in zip(a,b)] for a,b in zip(A,B)]
def sc(a,A):return [[a*x for x in r] for r in A]
def sub(A,B):return add(A,sc(-1,B))
def mul(A,B):return [[sum(A[i][k]*B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]
def act(A,v):return [sum(x*y for x,y in zip(r,v)) for r in A]
def adj(A,wl,wr):return [[A[j][i].conj()*wl[j]/wr[i] for j in range(len(A))] for i in range(len(A[0]))]
def pair(x,y,w):return sum(a.conj()*b*t for a,b,t in zip(x,y,w))
def comm(A,B):return sub(mul(A,B),mul(B,A))
def inverse(A):
 n=len(A);B=[r[:] + s[:] for r,s in zip(A,eye(n))]
 for i in range(n):
  k=next(k for k in range(i,n) if B[k][i]!=0);B[i],B[k]=B[k],B[i]
  z=B[i][i];B[i]=[a/z for a in B[i]]
  for k in range(n):
   if k!=i:
    z=B[k][i];B[k]=[a-z*b for a,b in zip(B[k],B[i])]
 return [r[n:] for r in B]
def block(A):
 n=len(A);Z=zero(n,n);return [a+z for a,z in zip(A,Z)]+[z+a for z,a in zip(Z,A)]
def eq(A,B):return A==B


checks={};negative={k:0 for k in ['drop_carre_cross_defect','wrong_carre_factor','discard_complete_U_anticommutator','wrong_second_green_half_factor','false_direct_UD_floor','wrong_relative_R3_factor','independent_cross_volume_noise']}
def ck(name,b):assert b,name;checks[name]=True
for wi in [[1,1,1,1],[1,2,3,4]]:
 n=4;I=eye(n);wi=list(map(F,wi));Wi=diag([1/x for x in wi]);P=diag([1,1,1,0])
 H=mul(Wi,mat([[2,1,2,0],[1,-1,1,0],[2,1,3,2],[0,0,2,-2]]));C=mul(mul(P,H),P);DF=sub(H,C)
 A=mul(Wi,mat([[0,1,0,2],[-1,0,2,0],[0,-2,0,1],[-2,0,-1,0]]))
 B=mul(Wi,mat([[0,2,0,1],[-2,0,1,0],[0,-1,0,2],[-1,0,-2,0]]));U=diag([F(1,2),F(2,3),F(3,4),F(4,5)])
 L=sub(mul(A,A),sc(3,B));Lt=add(mul(A,A),sc(3,B))
 def gen(X):return sub(add(mul(Lt,X),mul(X,L)),sc(2,mul(mul(A,X),A)))
 def complete(X):return add(gen(X),sc(3,add(mul(U,X),mul(X,U))))
 tag=str(wi)
 ck(tag+'_source_drift_transpose',adj(L,wi,wi)==Lt)
 ck(tag+'_identity_conservation',gen(I)==zero(n,n))
 ck(tag+'_complete_current_keeps_U_mass',complete(I)==sc(6,U))
 for X in [I,H,C,DF,U,mul(H,H)]:
  ck(tag+repr(X)+'_whole_commutator_source',gen(X)==add(comm(A,comm(A,X)),sc(3,comm(B,X))))
  ck(tag+repr(X)+'_full_Q_U_anticommutator',complete(X)==add(add(comm(A,comm(A,X)),sc(3,comm(B,X))),sc(3,add(mul(U,X),mul(X,U)))))
  negative['discard_complete_U_anticommutator']+=complete(X)!=gen(X)
 carre=sub(sub(gen(mul(H,H)),mul(gen(H),H)),mul(H,gen(H)))
 AH=comm(A,H);AC=comm(A,C);AD=comm(A,DF)
 ck(tag+'_full_H0_carre_operator',carre==sc(2,mul(AH,AH)))
 ck(tag+'_whole_CF_plus_full_dF_noise',AH==add(AC,AD))
 ck(tag+'_actual_anti_A_self_H0_commutator_selfpaired',adj(AH,wi,wi)==AH)
 for j,vec in enumerate([[Q(1),Q(0),Q(0),Q(0)],[Q(1,1),Q(2),Q(0,-1),Q(3,2)],[Q(0),Q(0),Q(1),Q(-2,1)]]):
  lhs=pair(vec,act(carre,vec),wi);rhs=2*pair(act(AH,vec),act(AH,vec),wi)
  ck(tag+str(j)+'_actual_carre_form_squared',lhs==rhs and rhs.i==0 and rhs.r>=0)
  no_cross=2*(pair(act(AC,vec),act(AC,vec),wi)+pair(act(AD,vec),act(AD,vec),wi))
  negative['drop_carre_cross_defect']+=lhs!=no_cross
  negative['wrong_carre_factor']+=lhs!=rhs*F(1,2)
# Exact integrand Gram from one common source row. These are finite controls;
# universal interval-integral positivity and source zero jets are Lean mouths.
for v0,v1 in [(F(1),F(4)),(F(4),F(9)),(F(1,4),F(9,4))]:
 rows=[F(1),F(1,2)]
 if (v0,v1)==(F(4),F(9)):rows=[F(1,2),F(1,3)]
 if (v0,v1)==(F(1,4),F(9,4)):rows=[F(2),F(2,3)]
 for i,v in enumerate([v0,v1]):ck(str(v0)+str(v1)+str(i)+'_true_source_inverse_root_volume',rows[i]*rows[i]*v==1)
 ker=[[2*rows[i]*rows[j] for j in range(2)] for i in range(2)]
 for j,co in enumerate([[Q(1),Q(1)],[Q(1,2),Q(-3,1)],[Q(1),Q(-1)]]):
  s=sum(co[i].conj()*ker[i][j]*co[j] for i in range(2) for j in range(2));a=sum(co[i]*rows[i] for i in range(2));q=2*a.conj()*a
  ck(str(v0)+str(v1)+str(j)+'_same_noise_zerojet_Gram',s==q and s.r>=0 and s.i==0)
  diagonal=sum(co[i].conj()*ker[i][i]*co[i] for i in range(2));negative['independent_cross_volume_noise']+=s!=diagonal
# Source regularization at points with exact rational sqrt V and sqrt(V+18s).
for r0,r1 in [(F(1),F(1)),(F(1),F(2)),(F(2),F(3)),(F(3,2),F(7,3))]:
 v=r0*r0;s=(r1*r1-v)/18;a=1/r0;ar=1/r1;b=r0-v/r1
 ck(str(r0)+str(r1)+'_source_regularization_coefficient',(a-ar)==b/v and b>=0 and b*b<=18*s)
 for lapse in [F(1,3),F(2),F(7,5)]:
  k=3*lapse/8
  ck(str(r0)+str(r1)+str(lapse)+'_actual_joint_four_price',18*s*4/k==192*s/lapse)
  for j,p,phase in [(F(1),F(1,2),F(1,2)),(F(3),F(1,4),F(2))]:
   price_scale=192*s/lapse;J=j;R=J-phase;err=price_scale*J
   ck(str(r0)+str(r1)+str(lapse)+str(j)+str(p)+str(phase)+'_source_once_clip_relative_R3',max(F(0),err-2*price_scale*R)==price_scale*max(F(0),J-2*R))
   negative['wrong_relative_R3_factor']+=max(F(0),err-price_scale*R)!=price_scale*max(F(0),J-2*R)
   for ep in [F(1,100),F(2)]:ck(str(s)+str(lapse)+str(ep)+str(j)+'_common_tail_allocation',price_scale*ep/(price_scale+1)<=ep)
# P3<=4J3 is essential: the completed C3 joint column is not a direct UD floor.
for lapse in [F(1,3),F(2)]:
 ud=Q(1);dc=Q(0,F(1,4));k=3*lapse/8
 j=k*(pair([ud],[ud],[1]).r+12*pair([dc],[dc],[1]).r-6*pair([ud],[dc],[1]).i)
 ck(str(lapse)+'_true_four_factor_native_slot',k/4<=j)
 negative['false_direct_UD_floor']+=j<k
for sig in [F(-2),F(-1,3),F(1,5),F(3)]:
 for energy,end,rest in [(F(1),F(2),F(-3)),(F(-2),F(1,3),F(7))]:
  dren=2*end-4*sig*sig*energy;r3=2*energy+rest
  ck(str(sig)+str(energy)+str(end)+'_actual_secondCF_half_endpoint_incidence',r3==end/(sig*sig)-dren/(2*sig*sig)+rest)
  negative['wrong_second_green_half_factor']+=r3!=end/(sig*sig)-dren/(sig*sig)+rest
assert all(v>0 for v in negative.values()),negative

INPUT_SHA={'SourceClockPhiMatchedElectricSource.lean': '409eb9d1c2e2f60b2e4a59278212b90d1ec4957fd3d48c222cbb8965e44bc4f6', 'SourceClockPhiRenormalizedSecondGreen.lean': '70d028b8ff713d8717100d27fb03cba7832f878fd775350decd99dc13f3cfc19'}
source=BASE/'SourceClockPhiMatchedDiffusionSource.lean'
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
assert sha(source)=='dd2fffb3597149612cfdffe450876638708956113b2d1e30a0a2d78a1e362c1f','frozen source moved'
for name,digest in INPUT_SHA.items():assert sha(BASE/name)==digest,(name,'input moved')
flat=regex.sub(r'\s+',' ',source.read_text())
role_count=len(checks)
def token(name,parts):ck(name,all(p in flat for p in parts))
token('actual_source_A_and_D_not_selected',['private abbrev A:End:=combinedConjugate'])
token('actual_same_source_B3',['def driftClock:End:=matchedColumn+(3:ℂ) • U'])
token('actual_sourceld_and_transpose',['def diffusionDrift:End:=A*A-(3:ℂ) • driftClock', 'def diffusionDriftTranspose:End:=A*A+(3:ℂ) • driftClock'])
token('whole_noise_current_preserves_two_A_legs',['diffusionDriftTranspose*X+X*diffusionDrift-(2:ℂ) • (A*X*A)'])
token('complete_Q_preserves_U_anticommutator',['def completeCurrent(X:End):End:=diffusionCurrent X+(3:ℂ) • (U*X+X*U)'])
token('actual_volume_noise_row',['def noiseRow(s:ℝ)(x:physicalChart):ℝ:=(Real.sqrt (GaussNativeEnergy.volume x.val+18*max s 0))⁻¹'])
token('actual_common_noise_two_volume_kernel',['def noiseKernel(t:ℝ)(x y:physicalChart):ℝ:=2*∫s in (0:ℝ)..t,noiseRow s x*noiseRow s y'])
token('conservative_diffusion_and_original_volume_drift',['diffusionCurrent (1:End)=0', 'diffusionCurrent SourceCoframeVolume.volumeAction=(18:ℂ) • (1:End)'])
token('all_finite_complex_cross_volume_Gram',['{ι:Type*}[Fintype ι]', '(x:ι → physicalChart)(c:ι → ℂ)', 'star (c i)*((noiseKernel t (x i) (x j):ℝ):ℂ)*c j'])
token('zerojet_actual_two_half_weight_QuantumTest_legs',['HasDerivAt (fun s:ℝ=>(noiseKernel s p q:ℂ)*inner ℂ (D f p.val) (D g q.val))', '(2*inner ℂ (A f p.val) (A g q.val)) 0'])
token('full_H0_carre_is_complete_CF_plus_dF',['diffusionCurrent (H0*H0)-diffusionCurrent H0*H0-H0*diffusionCurrent H0', '2*‖embed (bracket A (compressionCore F) f+bracket A (defectAction F) f)‖^2'])
token('actual_regularization_conjugate_and_192_price',['def regularizedConjugate(s:ℝ)(hs:0≤ s):End:', '(192*t/n)*matchedPrice m ell F z hz g'])
token('whole_frequency_source_onceclip_384_R3_payment',['(384*t/n)*matchedForcingWord m ell F (actualFrequency advanced μ r)', 'actual_regularization_common_payment t ht'])
token('cofinal_common_N_and_both_causal_not_point_only',['∀μ:ℝ,∀hμ:0<μ,∀g:diagonal.domain,∀ε:ℝ,0<ε → ∃N:ℕ', '∀ᶠ F in (sourceFilter:Filter Index),∀advanced:Bool'])
token('actual_complete_Q_H0_price_returns_J3',['diffusionSourcePrice m ell F z hz g=matchedPrice m ell F z hz g', 'diffusionSourcePrice m ell F z hz g=electricForcingWord'])
token('same_source_phase_keeps_full_column',['6*z.im*(sourcePair (matchedColumn (normalizedState m ell F z hz g)) (normalizedState m ell F z hz g)).im'])
token('actual_secondCF_half_factor_and_full_drift',['matchedForcingWord m ell F z hz g=fixedEndpointWord m ell F z hz g/z.im^2-', '/(2*z.im^2)+ diffusionRemainder m ell F z hz g'])
token('mandatory_source_inverse_z_counterterm',['2*‖embed (SourceClockPhiRenormalizedSecondGreen.fixedColumn m ell g)‖^2*(z⁻¹).re'])
token('Root_three_mouth_cost_consumed_in_actual_final_word',['SourceClockPhiRenormalizedSecondGreen.actual_renormalized_fixed_source g', 'SourceClockPhiRenormalizedSecondGreen.renormalizedEndpoint m ell F z hz g'])
token('actual_fixed_H0_squared_source_pair_sums_kept',['sourcePair (SourceClockPhiRenormalizedSecondGreen.fixedSecondTester', 'SourceClockPhiRenormalizedSecondGreen.fixedSecondResponse', 'sourcePair (SourceClockPhiRenormalizedSecondGreen.fixedFirstTester'])
token('all_fields_inside_single_source_price',['def matchedField(w:QuantumTest):ℝ:', 'def diffusionRemainder(m ell:ℕ)'])
token('only_two_original_public_theorem_mouths',['theorem original_matched_diffusion_covariance', 'theorem actual_matched_diffusion_source(g:diagonal.domain):'])
result={'module':'SourceClockPhiMatchedDiffusionSource','all_pass':True,'count':len(checks),'role_mechanism_count':role_count,'checks':checks,'effective_negative_controls':{k:v>0 for k,v in negative.items()},'negative_witness_counts':negative,'source_sha256':sha(source),'script_sha256':sha(__file__),'input_sha256':{k:sha(BASE/k) for k in INPUT_SHA},'helper_sha256':{},'arithmetic':'Self-contained exact Fraction paired-role diffusion/carre algebra, common noise Gram integrands at actual inverse-root-volume coefficients, 192/384 relative source pricing, original full secondCF half-factor and source/public-word guards.','scope':'Certifies controls for the original cross-volume noise/full-H0 CF+dF source, actual relative regularization price and exact Root3-to-R3 incidence. No finite-matrix volume CCR, H0/CF time replacement, auxiliary semigroup, H0 sandwich bound or full R3 small-tail claim.'}
(BASE/'clock-phi-matched-diffusion-source-check.json').write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'module':result['module'],'controls':result['count'],'role_controls':role_count,'negative':len(negative),'inputs':len(INPUT_SHA),'helpers':0,'all_pass':True}))
