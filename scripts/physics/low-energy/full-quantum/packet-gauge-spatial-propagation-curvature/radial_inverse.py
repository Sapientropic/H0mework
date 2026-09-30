#!/usr/bin/env python3
"""Exact univariate inverse circuit of the original axial112, at the true frequency."""
import json
import gzip
import hashlib
from pathlib import Path
import sys
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
q, x = s.symbols('q x', real=True)


def main():
    start = time.monotonic()
    src = json.loads((FQ/'packet-gauge-momentum-domain/source.json').read_bytes())
    A = s.SparseMatrix(112, 112, {(i, j): s.expand(s.sympify(v, locals={'q': q, 'x': x}).subs(x, 6*(1-s.I)))
                                  for i, j, v in src['normalized112']['entries']})
    ring = s.QQ_I.poly_ring(q)
    matrix = DomainMatrix.from_Matrix(A).convert_to(ring)
    graph = [set() for _ in range(112)]
    for i, j in matrix.to_dok():
        graph[i].add(j); graph[j].add(i)
    seen, blocks = set(), []
    for seed in range(112):
        if seed in seen: continue
        stack, part = [seed], []
        seen.add(seed)
        while stack:
            vertex = stack.pop(); part.append(vertex)
            for other in graph[vertex]-seen:
                seen.add(other); stack.append(other)
        blocks.append(sorted(part))
    records = []
    for part in blocks:
        block = matrix.extract(part, part)
        numerator, denominator = block.inv_den(method='rref')
        target = DomainMatrix.eye(len(part), ring).scalarmul(denominator)
        assert block.matmul(numerator) == numerator.matmul(block) == target
        assert denominator and denominator.evaluate(0, 0)
        records.append({'indices': part, 'denominator': str(ring.to_sympy(denominator)),
                        'numerator': [[i, j, str(ring.to_sympy(v))] for (i, j), v in numerator.to_dok().items()]})
        print('PASS axial original block', len(part), 'degree', denominator.degree(),
              'numerator entries', len(numerator.to_dok()), flush=True)
    result = {'scope': 'ORIGINAL112_SOURCE_RADIAL_RATIONAL_INVERSE_CIRCUIT',
              'original_x': '6*(1-i)', 'physical_momentum': '[0,0,sqrt2*q]',
              'normalization': 'D H121_section D/N', 'keep112': src['keep112'],
              'scales112': src['scales112'], 'blocks': records,
              'both_polynomial_inverse_identities': True,
              'seconds': round(time.monotonic()-start, 3)}
    data = (json.dumps(result, separators=(',', ':'))+'\n').encode()
    compressed = gzip.compress(data, mtime=0)
    (HERE/'radial-inverse.json.gz').write_bytes(compressed)
    (HERE/'radial-compression.json').write_text(json.dumps({'file': 'radial-inverse.json.gz',
        'decoded_sha256': hashlib.sha256(data).hexdigest(), 'decoded_bytes': len(data),
        'compressed_bytes': len(compressed)}, indent=2)+'\n')
    print('PASS complete actual radial inverse', result['seconds'], flush=True)


if __name__ == '__main__': main()
