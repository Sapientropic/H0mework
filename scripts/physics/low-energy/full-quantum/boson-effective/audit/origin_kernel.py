#!/usr/bin/env python3
"""Identify the six retained coordinates with the actual origin matter kernel graph."""
import importlib.util
import json
from pathlib import Path
import sys
import sympy as s

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[2]
spec=importlib.util.spec_from_file_location('boson_origin_audit',HERE/'independent_check.py')
audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit)
source=json.loads((BASE/'active-gauge/quotient.json').read_text())
active=json.loads((BASE/'active-gauge/receipt.json').read_text())
saved=json.loads((HERE.parent/'receipt.json').read_text())
ret=saved['original_retained103'];sc=list(map(s.sympify,saved['normalized_field_scaling']))
lam,k=s.symbols('lam k',real=True);N=s.sympify(active['source_lapse'])
K=s.SparseMatrix(103,103,{(i,j):s.sympify(v.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs({lam:0,k:0})*sc[i]*sc[j]/N for i,j,v in source['quotient_operator_103_by_103']})
m=[ret.index(i) for i in saved['matter48_source_indices']];h=[ret.index(i) for i in saved['heavy42_source_indices']];l=[ret.index(i) for i in saved['light6_source_indices']]
G=audit.clean(K.extract(h,h).inv(method='DM'))
graph=s.zeros(48,6,cls=s.SparseMatrix)
for j,i in enumerate(l):graph[m.index(i),j]=1
heavy=-G*K.extract(h,l)
for (i,j),value in s.SparseMatrix(heavy).todok().items():graph[m.index(h[i]),j]=value
M=K.extract(m,m);audit.equal(M*graph,s.zeros(48,6));assert graph.rank()==6 and M.rank()==42
nonzero_axes=sum(bool(M[:,m.index(i)].todok()) for i in l)
receipt={'status':'PASS','kernel_graph_dimension':6,'full_origin_matter_rank':42,
    'source_light_coordinate_axes_that_need_heavy_completion':nonzero_axes,
    'actual_kernel_graph':audit.encoded(graph),
    'scope':'The retained six coordinates parametrize the true M0 kernel after the generated heavy writeback; no assertion that each raw coordinate axis is itself a kernel vector.'}
(HERE/'origin-kernel-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='actual_kernel_graph'},indent=2))
