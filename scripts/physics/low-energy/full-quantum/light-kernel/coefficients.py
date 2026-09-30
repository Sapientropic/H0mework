#!/usr/bin/env python3
"""Read-only comparison of Lean coefficients against the actual source-mode jet."""
import importlib.util
import json
from pathlib import Path
import re
import sympy as s
HERE=Path(__file__).resolve().parent;ROOT=HERE.parents[4]
spec=importlib.util.spec_from_file_location('light_coeff_source',HERE/'compute.py')
b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
u,q=b.u,b.q
path=ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/LightKernel/Source.lean'
text=path.read_text()
r=json.loads((HERE/'modes-receipt.json').read_text())
scalars={}
for name,rhs in re.findall(r'^def (\w+) \(u q : ℂ\) : ℂ := ([^\n]+)',text,re.M):
    scalars[name]=s.sympify(rhs.replace('Complex.I','I').replace('^','**'),locals={'u':u,'q':q})
def matrix(name):
    match=re.search(r'^def '+name+r' .*?:=\s*!!\[([^]]+)\]',text,re.M)
    assert match,name
    def value(raw):
        raw=raw.strip()
        for key,entry in scalars.items():
            if raw==key+' u q':return entry
        return s.sympify(raw.replace('^','**'),locals={'u':u,'q':q})
    return s.Matrix([[value(v) for v in row.split(',')] for row in match.group(1).split(';')])
first=matrix('first');second=matrix('second')
b.zero(first-u*b.decode(r['first_order_in_original_modes']))
b.zero(second-b.decode(r['second_order_in_original_modes']))
order=[2,4,0,1,3];ordered=second.extract(order,order)
b.zero(matrix('pairSecond')-ordered[:2,:2]);b.zero(matrix('core')-ordered[2:,2:]);b.zero(matrix('mixing')-ordered[:2,2:])
b.zero(matrix('pair')-first.extract([2,4],[2,4]))
metric=(ROOT/'Lean/SaturationMonoid/PhysicsCore/LowEnergy/LightKernel/Metric.lean').read_text()
match=re.search(r'def metricReader .*?:= !\[([^]]+)\]',metric)
assert match
reader=s.Matrix([[s.sympify(v,locals={'u':u}) for v in match.group(1).split(',')]])
actual=b.homogeneous(b.decode(r['metric_reader_original_modes_degree2']),1).extract([0],[0,1,3])
b.zero(reader-actual)
report={'scope':'LEAN_SOURCE_POLYNOMIALS_EQUAL_ACTUAL_ORIGINAL_FIVE_MODE_JET',
 'first_and_second_source_matrices_equal':True,'all_reordered_source_blocks_equal':True,
 'metric_reader_equals_original_source_pullback':True,'production_file':str(path.relative_to(ROOT))}
(HERE/'coefficient-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
