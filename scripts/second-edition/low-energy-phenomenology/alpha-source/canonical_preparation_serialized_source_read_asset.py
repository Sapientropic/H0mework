from pathlib import Path
import gzip,json,hashlib,time,collections,re
import sympy as s
ROOT=Path(__file__).resolve().parents[4];HERE=Path(__file__).resolve().parent
DATA=ROOT/'Verification/physics/low-energy-phenomenology/external-composite-decay'
t0=time.monotonic();asset=DATA/'source_clock_symbol_recursion.dag.json.gz'
raw=asset.read_bytes();payload=gzip.decompress(raw);dag=json.loads(payload)
descriptor=json.loads((DATA/'source_clock_symbol_recursion.json').read_text())['differential_DAG']
assert hashlib.sha256(raw).hexdigest()==descriptor['sha256']
assert hashlib.sha256(payload).hexdigest()==descriptor['decompressed_sha256']
nodes,polys=dag['nodes'],dag['polys'];clock={(v['order'],v['axis']):v['expression'] for v in dag['clock_def']}
assert len(nodes)==3934 and len(polys)==747
names=('c','T','S00','S11','S01','S02','S12');variables=s.symbols(' '.join(names));c,T,s00,s11,s01,s02,s12=variables
S=s.Matrix([[s00,s01,s02],[s01,s11,s12],[s02,s12,T-s00-s11]])
det=s.Poly((T*s.eye(3)-S).det(),*variables)
texts=list(dict.fromkeys(coef for rows in polys for _,coef in rows));pool=[]
for text in texts:
 assert set(re.findall(r'[A-Za-z][A-Za-z0-9_]*',text))<=set(names)
 assert re.fullmatch(r'[A-Za-z0-9_+*/() .\-]+',text)
 expression=s.sympify(text,locals=dict(zip(names,variables)))
 numerator,denominator=s.fraction(s.cancel(expression));den=s.Poly(denominator,*variables);poles=[]
 for axis in (0,1):
  exponent=min(p[axis] for p,value in den.terms());den=den.exquo(s.Poly(variables[axis]**exponent,*variables));poles.append(exponent)
 exponent=0
 while den.total_degree()>0:
  quotient,remainder=s.div(den,det);assert remainder.is_zero
  den=quotient;exponent+=1
 poles.append(exponent);assert den.total_degree()==0
 num=s.Poly(numerator/den.as_expr(),*variables)
 # Full exact identity, not sampled coefficients or encoded upper powers.
 assert s.Poly(s.expand(num.as_expr()*denominator-numerator*c**poles[0]*T**poles[1]*det.as_expr()**poles[2]),*variables).is_zero
 pool.append({'text':text,'poles':poles,'terms':[[list(p),[int(v.p),int(v.q)]] for p,v in num.terms()]})
print('COEFFICIENTS',len(pool),round(time.monotonic()-t0,3),flush=True)
index={text:i for i,text in enumerate(texts)}
rows=[[[word,index[text]] for word,text in poly] for poly in polys]
def dependencies(node):
 kind,central,key=node
 if kind=='source':assert key[0] in (0,1) and 0<=key[1]<14;return []
 if kind=='clock':assert tuple(key) in clock;return [clock[tuple(key)]]
 assert kind=='moyal' and len(key)==3 and key[0]>=0
 assert 0<=key[1]<len(polys) and 0<=key[2]<len(polys)
 return key[1:]
nodeDeps=[dependencies(node) for node in nodes]
deps=[]
for poly in rows:
 ids={j for word,_ in poly for atom in word for j in nodeDeps[atom]};deps.append(sorted(ids))
heights={};active=set()
def height(i):
 if i in heights:return heights[i]
 assert i not in active,('cycle',i)
 active.add(i);heights[i]=1+max([height(j) for j in deps[i]]+[0]);active.remove(i);return heights[i]
for i in range(len(polys)):height(i)
assert all(heights[j]<heights[i] for i in range(len(polys)) for j in deps[i])
out={'asset_sha256':hashlib.sha256(raw).hexdigest(),'payload_sha256':hashlib.sha256(payload).hexdigest(),'descriptor':descriptor,
 'algorithm_sha256':{n:hashlib.sha256((DATA/n).read_bytes()).hexdigest() for n in ['source_clock_symbol_recursion.py','source_clock_dag_majorants.py']},
 'nodes':nodes,'polys':rows,'coefficients':pool,'clock_def':dag['clock_def'],'stages':dag['stages'],'leading_energy_expr':dag['leading_energy_expr'],
 'height':[heights[i] for i in range(len(polys))],'maximum_height':max(heights.values()),'topological_ids':sorted(heights,key=lambda i:(heights[i],i)),
 'elapsed_seconds':round(time.monotonic()-t0,3)}
(HERE/'decoded-source.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
print('DONE',len(nodes),len(polys),sum(map(len,rows)),out['maximum_height'],out['elapsed_seconds'],flush=True)
