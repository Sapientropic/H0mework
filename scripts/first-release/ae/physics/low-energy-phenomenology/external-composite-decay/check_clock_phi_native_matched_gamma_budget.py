from fractions import Fraction as Q
from pathlib import Path
import json,hashlib
BASE=Path(__file__).resolve().parent
checks={};negative={k:False for k in ['wrong_shift40_rho_constant','wrong_native_radius_denominator_16','omit_normalized_norm_tail','omit_matched_phase_debit','wrong_original_coefficient_48','drop_R3_factor_two']}
def ck(k,b):
 assert b,k
 checks[k]=True
def clip(x):return max(Q(0),x)
for phi,vac in [(Q(0),Q(0)),(Q(1,3),Q(7,5)),(Q(-2),Q(3,7))]:
 rho2=1+phi*phi/4;shift=(phi-Q(2,5)*vac)**2;other=(phi-Q(4,5)*vac)**2
 ck(f'{phi}_{vac}_actual_rho_shift40_identity',rho2==1+2*vac*vac/25+shift/2-other/4)
 negative['wrong_shift40_rho_constant']|=rho2!=1+Q(9,128)*vac*vac+shift/2-other/4
for mu,n,vac2 in [(Q(1,7),Q(1,3),Q(0)),(Q(1),Q(3,2),Q(5,3)),(Q(13,3),Q(1,3),Q(11,7))]:
 nf=mu*(1+2*vac2/25);pf=mu/(20*n)
 ck(f'{mu}_{n}_true_J3_shift40_radius_coefficient',pf*10*n==mu/2)
 negative['wrong_native_radius_denominator_16']|=(mu/(16*n))*10*n!=mu/2
 for epsilon in [Q(1,100),Q(1),Q(7,3)]:
  delta=epsilon/(nf+pf+1);tag=f'{mu}_{n}_{vac2}_{epsilon}'
  ck(tag+'_both_internal_tail_debits_paid', (nf+pf)*delta<=epsilon)
  for R3,error,norm2 in [(Q(0),Q(0),Q(0)),(Q(3,7),delta/2,delta),(Q(-1,9),delta,delta)]:
   J3=2*R3+error
   lhs=clip(nf*norm2+pf*J3)
   rhs=nf*norm2+pf*(2*clip(R3)+clip(error))
   ck(tag+f'_{R3}_{error}_{norm2}_literal_once_clip_matched_payment',lhs<=rhs)
   negative['omit_normalized_norm_tail']|=lhs>pf*(2*clip(R3)+clip(error))
   negative['omit_matched_phase_debit']|=lhs>nf*norm2+2*pf*clip(R3)
 for muFactor,radiusPrice in [(Q(0),Q(3)),(Q(1,5),Q(7,3)),(Q(5,2),Q(11,7))]:
  C=6*muFactor*radiusPrice;coef=48*muFactor*radiusPrice*pf;tag=f'{mu}_{n}_{muFactor}_{radiusPrice}'
  ck(tag+'_original_Q8_radius_and_matched_word_coefficient48',C*4*2*pf==coef)
  negative['wrong_original_coefficient_48']|=coef!=24*muFactor*radiusPrice*pf
  negative['drop_R3_factor_two']|=coef!=C*4*pf
  for epsilon in [Q(1,100),Q(1),Q(7,3)]:
   delta=epsilon/(10*(C+1));tag2=tag+f'_{epsilon}'
   ck(tag2+'_original_full_sharp_common_epsilon_allocation',epsilon/2+C*5*delta<=epsilon)
   for R3 in [Q(0),Q(3,7)]:
    ck(tag2+f'_{R3}_original_terminal_full_matched_cost',epsilon/2+C*(delta+4*(delta+2*pf*R3))<=epsilon+coef*R3)
ck('six_effective_negatives',all(negative.values()))
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
source=BASE/'SourceClockPhiNativeMatchedGammaBudget.lean'
assert sha(source)=='2ddc3f461565dc64d271f08a9c53325035a5085f5ea1f7527538bb36bcda7ccb'
inputs=['SourceClockPhiNativeMatchedSource.lean','SourceClockPhiRadiusNormalizedFluxBudget.lean','SourceClockRadiusAffineCutoff.lean','SourceClockYukawaQ8RadiusBudget.lean']
result={'module':'SourceClockPhiNativeMatchedGammaBudget','all_pass':True,'count':len(checks),'checks':checks,'effective_negative_controls':negative,'source_sha256':sha(source),'script_sha256':sha(__file__),'input_sha256':{f:sha(BASE/f) for f in inputs},'helper_sha256':{},'arithmetic':'Exact Fraction actual rho shift40 constant, native J3/(20n) radius comparison, once-clipped R3 with both internal norm and matched-phase debits, common epsilon and original Q8/radius factor48.','scope':'Finite source-price arithmetic. Lean supplies actual seventy-column rho point identity and J3 source floor, actual original two-seed R3 measurability, original commonN/cofinalF/allsharp Gamma with both tails internally paid. No R3 integral small tail, moving H0Aw graph, physical dressed width or lifetime is inferred.'}
Path(__file__).with_name('clock-phi-native-matched-gamma-budget-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({'count':len(checks),'negative':len(negative),'all_pass':True}))
