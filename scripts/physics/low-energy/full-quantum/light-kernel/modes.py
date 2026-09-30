#!/usr/bin/env python3
"""Identify the five light graph coordinates with the original emitted zero modes."""
import importlib.util
import json
from pathlib import Path
import sympy as s
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('light_modes_source',HERE/'compute.py')
b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
u,q=b.u,b.q
r=json.loads((HERE/'receipt.json').read_text());d=json.loads((HERE/'direct-receipt.json').read_text())
p=json.loads((HERE/'propagation-receipt.json').read_text());old=json.loads((HERE.parent/'boson-effective/receipt.json').read_text())
o=json.loads((HERE.parents[1]/'active-gauge/origin.json').read_text())
quot=json.loads((HERE.parents[1]/'active-gauge/quotient.json').read_text())
Z=s.SparseMatrix(289,5,{(i,j):s.sympify(v) for i,j,v in o['source_289_mode_columns']})
lam,k=s.symbols('lam k',real=True)
Q=s.SparseMatrix(103,112,{(i,j):s.sympify(v.replace('lambda','lam'),locals={'lam':lam,'k':k}).subs({lam:0,k:0})
    for i,j,v in quot['quotient_readback_103_by_112']})
sc=list(map(s.sympify,old['normalized_field_scaling']))
coordinates=b.clean(s.diag(*[1/v for v in sc])*Q*Z[9:121,:])
light=[old['original_retained103'].index(i) for i in r['light5_source_indices']]
chart=coordinates[light,:]
E0=b.decode(d['direct103_field_jet']).subs({u:0,q:0})
b.zero(E0*chart-coordinates)
full0=b.decode(r['whole289_field_writeback_degree2']).subs({u:0,q:0})
b.zero(full0*chart-Z)
assert chart.det()!=0
J=b.decode(p['first_order_matrix']);S=b.decode(r['light5_degree2'])
first=b.clean(chart.T*J*chart)
second=b.clean(chart.T*b.homogeneous(S,2)*chart)
phases=second.extract([1,3],[1,3])
expected=s.diag(s.Rational(32,11)*u*u+s.Rational(160,67)*q*q,-40*u*u+s.Rational(2500,81)*q*q)
b.zero(phases-expected)
print('original mode chart',chart,'first order',first,'phase2',phases,flush=True)
report={'scope':'LIGHT5_TRUE_GRAPH_OF_ALL_ORIGINAL_FIVE_ZERO_MODES',
 'source_mode_names':o['source_mode_names'],'source_zero_modes_289':b.encode(Z),
 'normalized103_source_modes':b.encode(coordinates),'original_modes_in_light5':b.encode(chart),
 'original_mode_chart_determinant':str(chart.det()),'first_order_in_original_modes':b.encode(first),
 'second_order_in_original_modes':b.encode(second),'original_two_phase_operator':b.encode(phases),
 'metric_reader_original_modes_degree2':b.encode(b.clean(b.decode(p['g00_reader5_through_degree2'])*chart)),
 'all_original289_zero_mode_fields_recovered_exactly':True,
 'agrees_with_original_canonical_phase_degree2':True,'all_five_source_modes_equal_true_graph_in_faithful103':True}
(HERE/'modes-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
