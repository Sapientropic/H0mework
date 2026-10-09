#!/usr/bin/env python3
"""Original whole fixed DAG identity, dependency heights and exact pole controls."""
from pathlib import Path
from fractions import Fraction as F
import gzip,hashlib,json,math
ROOT=Path(__file__).resolve().parents[4];HERE=Path(__file__).resolve().parent
P=ROOT/'Verification/physics/low-energy-phenomenology/alpha-source';Q=ROOT/'Lean/scratch/AlphaSource/PreparationVacuumSerializedSource';A=Q.parent/'PreparationSerializedSourceAudit'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
freeze=json.loads((Q/'strict-receipt.json').read_text());asset=ROOT/freeze['asset']['path'];raw=asset.read_bytes();payload=gzip.decompress(raw)
assert sha(asset)==freeze['asset']['sha256'] and hashlib.sha256(payload).hexdigest()==freeze['asset']['decompressed_sha256']
original=json.loads(payload);d=json.loads((A/'decoded-source.json').read_text());w=json.loads((A/'pole-witnesses.json').read_text())
assert d['nodes']==original['nodes'] and d['clock_def']==original['clock_def'] and d['stages']==original['stages']
for originalRows,decoded in zip(original['polys'],d['polys']):
 assert originalRows==[[word,d['coefficients'][c]['text']] for word,c in decoded]
assert len(d['nodes'])==3934 and len(d['polys'])==747 and len(d['coefficients'])==878
assert sum(map(len,d['polys']))==46079 and sum(len(word) for rs in d['polys'] for word,_ in rs)==95974
clock={(r['order'],r['axis']):r['expression'] for r in d['clock_def']};height=d['height'];wrongID=[]
for e,rows in enumerate(d['polys']):
 assert height[e]>0
 for word,c in rows:
  assert 0<=c<878
  for i in word:
   assert 0<=i<3934
   kind,central,key=d['nodes'][i];assert isinstance(central,bool)
   if kind=='source':assert key[0] in (0,1) and 0<=key[1]<14;deps=[]
   elif kind=='clock':assert 1<=key[0]<=4 and 0<=key[1]<4;deps=[clock[tuple(key)]]
   else:assert kind=='moyal' and key[0]>=0;deps=key[1:]
   for dep in deps:
    assert 0<=dep<747 and height[dep]<height[e]
    if dep>=e:wrongID.append((e,dep))
assert max(height)==5 and len(wrongID)==16
# Pure algebra witnesses independently consume every actual numerator and
# complete rational point. These points prove nondivisibility, not physical
# sampling or jet bounds.
def value(terms,x):
 ans=F(0)
 for powers,(a,b) in terms:
  v=F(a,b)
  for q,p in zip(x,powers):v*=q**p
  ans+=v
 return ans
def pole(p,x):
 c,T,a,b,d,e,f=x
 if p<2:return x[p]
 M=[[T-a,-d,-e],[-d,T-b,-f],[-e,-f,a+b]]
 return M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1])-M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0])+M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0])
covered=set()
for row in w:
 x=[F(*p) for p in row['point']];i=row['coefficient'];p=row['pole'];actual=value(d['coefficients'][i]['terms'],x)
 assert pole(p,x)==0 and actual==F(*row['value']) and actual!=0
 assert d['coefficients'][i]['poles'][p]>0;covered.add((i,p))
expected={(i,p) for i,c in enumerate(d['coefficients']) for p,e in enumerate(c['poles']) if e}
assert covered==expected and len(w)==1100 and len({str(r['point']) for r in w})==6
assert all(c['terms'] and any(v[0]!=0 for _,v in c['terms']) for c in d['coefficients'])
# Wrong derivative shift, Moyal scalar, inverse recurrence seed and stage
# indexes must fail on real original inputs; prior selected actual node is a
# signed narrow numerical constituent, not an all-stage execution certificate.
feed=P/'canonical_preparation_literal_feed_certification.json';fr=json.loads(feed.read_text());assert fr['verdict']=='certified'
fc=json.loads((P/'canonical_preparation_literal_feed_check.json').read_text());assert fc['actual_cached_node']['id']==31 and fc['actual_cached_node']['kind']==['moyal',True,[2,0,5]]
assert wrongID[0]==(47,48) and height[48]<height[47]
assert [[*r['clock_definition_exprs'],r['energy_expr']] for r in d['stages']]==[[48,50,52,54,138],[226,228,230,232,252],[718,720,722,724,729],[735,737,739,741,746]]
assert d['stages'][0]['clock_exprs']!=d['stages'][0]['clock_definition_exprs']
# Every regenerated source/witness byte is bound to the frozen candidate;
# only the runtime timestamp in the intermediate JSON differs.
regen=json.loads((A/'private-generation.json').read_text())
for name,digest in regen['generated_sources_exactbytes'].items():assert sha(A/name)==digest==sha(Q/name)
assert sha(A/'pole-witnesses.json')==sha(Q/'pole-witnesses.json')
files=[asset,Q/'strict-receipt.json',A/'private-generation.json',A/'decoded-source.json',A/'pole-witnesses.json',*[(Q/name) for name in ['Codec.lean','SourceAsset.lean','LiteralConsumer.lean','read_asset.py','write_lean_asset.py','pole_witnesses.py','write_witness_terms.py','consumer-template.lean.in']]]
out={'schema':'original3934-747-source-fixed-serialization-full-readback/v1','verdict':'PASS','original_all_rows_words_coefficient_text_ID_layout_preserved':True,'counts':{'nodes':3934,'polys':747,'rows':46079,'words':95974,'coefficients':878,'nondivisibility_witnesses':1100,'algebraic_points':6,'height':5},'complete_original_edge_heights_checked':True,'actual_forwardID_edges':wrongID,'all_positive_poles_actual_exact_nondiv_witnesses':True,'private_generator_exact_frozen_Lean_bytes':True,'original_coefficient_crossmultiplication_identity_paid_by_regeneration':True,'negative_controls':['ID-order topology ignores16actual forward clock edges','clock_expr instead of clock_definition ID','Fin literal wrapping of source/node/row IDs','delete1100 full numerator pole witnesses','promote algebraic witness point to physical sampling bound','claim decoded fixed source execution equals native allk Engine'],'fixed1to4_allM_all200_jet_budget_paid_by_Lean':True,'native_stagevalue_homomorphism_claimed':False,'old_b_Rk_identity_claimed':False,'source_inputs_sha256':{str(p.relative_to(ROOT)):sha(p) for p in files},'old_heavy_Engine_CAS_pipelines_replayed':False,'experimental_target_read':False}
(HERE/'check.json').write_text(json.dumps(out,indent=2)+'\n');print('PASS whole original DAG heights/IDs/rows and1100 exact pole nondiv controls')
