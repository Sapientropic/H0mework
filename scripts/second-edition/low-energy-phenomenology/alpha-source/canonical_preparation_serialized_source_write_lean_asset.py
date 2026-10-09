from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent;d=json.loads((P/'decoded-source.json').read_text())
lines=['import Codec','','set_option autoImplicit false','set_option maxHeartbeats 100000000','set_option maxRecDepth 8192','set_option backward.isDefEq.respectTransparency false','noncomputable section','namespace LowEnergy.PreparationVacuumSerializedSource','open PreparationVacuumDAGCoefficient','open scoped BigOperators','']
def balanced(items,arg='i.val'):
 def go(a,b):
  if b-a==1:return items[a]
  mid=(a+b)//2
  return f'(if {arg} < {mid} then {go(a,mid)} else {go(mid,b)})'
 return go(0,len(items))
def rat(v):
 a,b=v;return f'({a} : ℚ)' if b==1 else f'({a}/{b} : ℚ)'
def monomial(t):
 powers,v=t;exps=[f'Finsupp.single {i} {n}' for i,n in enumerate(powers) if n];power=' + '.join(exps) or '0'
 return f'MvPolynomial.monomial ({power}) {rat(v)}'
coeff=[]
for i,e in enumerate(d['coefficients']):
 numerator=' + '.join(map(monomial,e['terms'])) or '0'
 lines.append(f'def coefficient{i} : NormalizedCoefficient := ⟨{numerator}, ![{",".join(map(str,e["poles"]))}]⟩')
 coeff.append(f'coefficient{i}')
lines+=['',f'def fixedCoefficient (i : Fin {len(coeff)}) : NormalizedCoefficient := {balanced(coeff)}','']
clock={(row['order'],row['axis']):row['expression'] for row in d['clock_def']};node=[]
for kind,central,key in d['nodes']:
 if kind=='source':expr=f'.source {key[0]} {key[1]}'
 elif kind=='clock':expr=f'.clock {key[0]-1} {key[1]} {clock[tuple(key)]}'
 else:expr=f'.moyal {key[0]} {key[1]} {key[2]}'
 node.append(f'⟨{str(central).lower()},{expr}⟩')
lines+=[f'def fixedNode (i : Fin 3934) : Node 747 := {balanced(node)}','']
for i,rows in enumerate(d['polys']):
 body=','.join('⟨['+','.join(map(str,w))+f'],{c}⟩' for w,c in rows)
 lines.append(f'def rows{i} : List (RawRow 3934 878) := [{body}]')
lines+=['',f'def fixedRows (i : Fin 747) : List (RawRow 3934 878) := {balanced([f"rows{i}" for i in range(747)])}',f'def fixedHeight (i : Fin 747) : ℕ := {balanced([str(i) for i in d["height"]])}','', 'def fixedSource : SourceTable 747 3934 878 := ⟨fixedNode,fixedRows,fixedCoefficient,fixedHeight⟩','', 'theorem fixed_rows_valid : ∀ i,rowsValid fixedSource i=true := by decide +kernel','theorem fixed_closed : SourceClosed fixedSource := sourceClosed_of_rowsValid fixedSource fixed_rows_valid','theorem fixed_height_bound : ∀ i,fixedSource.height i≤5 := by decide +kernel','']
lines+=['def fixedEnergyIds : Fin 4 → Fin 747 := !['+','.join(str(row['energy_expr']) for row in d['stages'])+']','def fixedClockIds : Fin 4 → Fin 4 → Fin 747 := !['+','.join('!['+','.join(map(str,row['clock_definition_exprs']))+']' for row in d['stages'])+']',f'def fixedLeadingEnergyId : Fin 747 := {d["leading_energy_expr"]}','', 'end LowEnergy.PreparationVacuumSerializedSource','#print axioms LowEnergy.PreparationVacuumSerializedSource.fixed_closed','#print axioms LowEnergy.PreparationVacuumSerializedSource.fixed_height_bound']
(P/'SourceAsset.lean').write_text('\n'.join(lines)+'\n')
print('SOURCE_BYTES',len((P/'SourceAsset.lean').read_bytes()))
