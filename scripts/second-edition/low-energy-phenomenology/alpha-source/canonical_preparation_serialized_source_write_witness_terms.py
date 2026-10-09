from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent;d=json.loads((P/'decoded-source.json').read_text());w=json.loads((P/'pole-witnesses.json').read_text())
keys=list(dict.fromkeys((r['pole'],str(r['point'])) for r in w));points={k:i for i,k in enumerate(keys)}
def rat(v):
 a,b=v;return str(a) if b==1 else f'({a}/{b})'
lines=[]
for k,i in points.items():
 pole,txt=k;q=json.loads(txt)
 lines += [f'private def witnessPoint{i} : Fin 7 → ℚ := ![{",".join(map(rat,q))}]',f'private theorem witnessPole{i} : rationalEvaluation witnessPoint{i} (polePolynomial {pole})=0 := by',f'  norm_num [witnessPoint{i},rationalEvaluation,polePolynomial,determinantPolynomial,centralQ,Matrix.det_fin_three,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.vecHead,Matrix.vecTail]','']
for r in (w if '--all' in sys.argv else [w[0],w[-1],max(w,key=lambda r:len(d["coefficients"][r["coefficient"]]["terms"]))]):
 i,pole=r['coefficient'],r['pole'];j=points[(pole,str(r['point']))]
 args=[f'coefficient{i}','rationalEvaluation_monomial']
 if len(d['coefficients'][i]['terms'])>1:args+=['map_add']
 args+=['Fin.prod_univ_succ']
 if any(any(power) for power,_ in d['coefficients'][i]['terms']):args+=['Finsupp.single_apply']
 if any(sum(bool(e) for e in power)>1 for power,_ in d['coefficients'][i]['terms']):args+=['Finsupp.add_apply']
 args+=[f'witnessPoint{j}']
 lines += [f'private theorem nondivides_{i}_{pole} : ¬ polePolynomial {pole}∣coefficient{i}.numerator := by',f'  apply nondivides_of_evaluation witnessPoint{j} _ _ witnessPole{j}',f'  simp only [{",".join(args)}]','  decide +kernel','']
if '--all' in sys.argv:
 for i,c in enumerate(d['coefficients']):
  positive=[j for j,e in enumerate(c['poles']) if e]
  lines += [f'private theorem coefficientReduced{i} : coefficient{i}.numerator≠0 ∧ ∀ p,CancelledAt p coefficient{i} := by','  constructor']
  if positive:
   pole=positive[0]
   lines += [f'  · intro zero;apply nondivides_{i}_{pole};rw [zero];exact dvd_zero _']
  else:
   lines += ['  · intro zero',f'    have read:=congrArg (rationalEvaluation (fun _=>1)) zero',f'    norm_num [coefficient{i},rationalEvaluation,rationalEvaluation_monomial,Fin.prod_univ_succ,Finsupp.single_apply,Finsupp.add_apply] at read']
  lines += ['  · intro p;fin_cases p']
  for pole,e in enumerate(c['poles']):
   lines += [f'    · exact Or.inr nondivides_{i}_{pole}' if e else '    · exact Or.inl rfl']
  lines+=['']
 lines += ['theorem fixed_coefficient_reduced (i : Fin 878) :','    (fixedCoefficient i).numerator≠0 ∧ ∀ p,CancelledAt p (fixedCoefficient i) := by','  unfold fixedCoefficient']
 def proof(a,b,indent):
  if b-a==1:return [indent+f'exact coefficientReduced{a}']
  m=(a+b)//2;h=f'h{a}_{b}'
  return [indent+f'by_cases {h} : i.val < {m}',indent+f'· simp only [if_pos {h}]']+proof(a,m,indent+'  ')+[indent+f'· simp only [if_neg {h}]']+proof(m,b,indent+'  ')
 lines+=proof(0,878,'  ')
 lines += ['','theorem fixed_coefficient_canceled (i : Fin 878) : cancelCoefficient (fixedCoefficient i)=fixedCoefficient i :=', '  cancelCoefficient_fixed _ (fixed_coefficient_reduced i).1 (fixed_coefficient_reduced i).2','']
s=(P/'consumer-template.lean.in').read_text();start=s.index('-- SOURCE_WITNESSES');end=s.index('-- END_SOURCE_WITNESSES',start) if '-- END_SOURCE_WITNESSES' in s else start+len('-- SOURCE_WITNESSES')
s=s[:start]+'-- SOURCE_WITNESSES\n'+'\n'.join(lines)+'\n-- END_SOURCE_WITNESSES'+s[end+len('-- END_SOURCE_WITNESSES') if '-- END_SOURCE_WITNESSES' in s else end:]
(P/'LiteralConsumer.lean').write_text(s)
print('WITNESS_TERMS',len(lines),'all', '--all' in sys.argv)
