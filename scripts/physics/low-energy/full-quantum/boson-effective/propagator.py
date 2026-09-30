#!/usr/bin/env python3
"""A complete source boson inverse and its whole289 field propagator on a nonempty exact domain."""
import importlib.util
import json
from pathlib import Path
import time
import sympy as s
HERE=Path(__file__).resolve().parent;BASE=HERE.parents[1]
spec=importlib.util.spec_from_file_location('boson_green_builder',HERE/'compute.py');built=importlib.util.module_from_spec(spec);spec.loader.exec_module(built)
source=built.source;normalized,assertzero,encode=built.normalized,built.assertzero,built.encode
u,q=s.symbols('u q',real=True);r=json.loads((HERE/'receipt.json').read_text());wb=json.loads((HERE/'readback-receipt.json').read_text());a=json.loads((BASE/'active-gauge/receipt.json').read_text());start=time.monotonic()
values={u:s.Rational(3,5)*(1-3*s.I),q:s.Rational(3,10)}
def at(record):return s.SparseMatrix(*record['shape'],{(i,j):s.cancel(s.sympify(v,locals={'u':u,'q':q}).subs(values)) for i,j,v in record['entries']})
S=at(r['effective_boson55']);R=source.block_inverse(S)
assertzero(S*R-s.eye(55));assertzero(R*S-s.eye(55))
F=at(wb['field_response_lift']);J=at(wb['source_injection']);full=normalized(F*R)
N=s.sympify(a['source_lapse']);p=[N*s.sqrt(2)*values[u],0,0,s.I*s.sqrt(2)*values[q]]
H=built.source_matrix(a['Fourier_Jacobi_entries'],289,p);assertzero(H*full-J)
report={'scope':'SOURCE55_BOSON_ACTUAL_INVERSE_WHOLE289_PROPAGATOR','source_sha256':a['source_sha256'],
 'u':str(values[u]),'q':str(values[q]),'original_derivative_symbols':list(map(str,p)),
 'true55_boson_inverse':encode(R),'whole289_field_green':encode(full),'original_source_injection':encode(J),
 'both55_inverse_identities':True,'all289_by55_original_sourced_equations':True,'elapsed_seconds':round(time.monotonic()-start,3)}
(HERE/'propagator-receipt.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({key:report[key] for key in ['scope','u','q','both55_inverse_identities','all289_by55_original_sourced_equations','elapsed_seconds']},indent=2))
