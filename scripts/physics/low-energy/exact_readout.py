#!/usr/bin/env python3
"""Exact, dependency-free subordinate readouts of the existing SU(7) source.

Uses Python integers/Fraction for every certificate. Floating point occurs only
in dimensionless running samples, root labels, and SVG coordinates. Does not
install a new source, infer physical units, fit couplings, or identify protons.
"""
from __future__ import annotations
import argparse
import hashlib
import itertools as it
import json
import math
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import re

Matrix = list[list[Q]]


def eye(n: int) -> Matrix:
    return [[Q(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return [list(row) for row in zip(*a)]


def mul(a, b):
    out = [[Q(0) for _ in b[0]] for _ in a]
    rows = [[(j, x) for j, x in enumerate(row) if x] for row in b]
    for i, row in enumerate(a):
        for k, x in enumerate(row):
            if x:
                for j, y in rows[k]:
                    out[i][j] += x * y
    return out


def add(a, b, scale=Q(1)):
    return [[x + scale*y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def rref(a):
    a = [[Q(x) for x in row] for row in a]
    pivots, row = [], 0
    for col in range(len(a[0])):
        p = next((i for i in range(row, len(a)) if a[i][col]), None)
        if p is None:
            continue
        a[row], a[p] = a[p], a[row]
        d = a[row][col]
        a[row] = [x/d for x in a[row]]
        for i in range(len(a)):
            if i != row and a[i][col]:
                d = a[i][col]
                a[i] = [x-d*y for x, y in zip(a[i], a[row])]
        pivots.append(col)
        row += 1
        if row == len(a):
            break
    return a, pivots


def inverse(a):
    n = len(a)
    r, p = rref([row + e for row, e in zip(a, eye(n))])
    if p != list(range(n)):
        raise ValueError('Matrix is singular; do not integrate a massless direction.')
    return [row[n:] for row in r]


def nullspace(a):
    r, piv = rref(a)
    free = [j for j in range(len(a[0])) if j not in piv]
    cols = []
    for j in free:
        v = [Q(0)]*len(a[0]); v[j] = Q(1)
        for i, p in enumerate(piv):
            v[p] = -r[i][j]
        cols.append(v)
    return transpose(cols) if cols else [[] for _ in a[0]]


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def charpoly(a):
    """Monic coefficients, descending order, by Faddeev-LeVerrier."""
    n = len(a); b = eye(n); out = [Q(1)]
    for k in range(1, n+1):
        ab = mul(a, b); c = -trace(ab)/k
        out.append(c); b = add(ab, eye(n), c)
    assert all(x == 0 for row in b for x in row), 'Cayley-Hamilton certificate failed'
    return out


def divide_linear(p, root):
    q = [p[0]]
    for coefficient in p[1:]:
        q.append(coefficient + root*q[-1])
    return q[:-1], q[-1]


def factors(p):
    """Finite rational-root search; an unfactored polynomial is retained exactly."""
    out = []
    candidates = sorted({Q(a, b) for a in range(-28, 57) for b in range(1, 15)})
    for root in candidates:
        count = 0
        while len(p) > 1:
            q, rem = divide_linear(p, root)
            if rem: break
            p = q; count += 1
        if count: out.append({'root': str(root), 'multiplicity': count})
    return out, p


def polynomial_value(p, x):
    y = 0
    for c in p: y = y*x+c
    return y


def positive_root_intervals(p):
    if len(p) <= 1: return []
    out = []
    for i in range(512):
        a, b = Q(i, 64), Q(i+1, 64)
        fa, fb = polynomial_value(p, a), polynomial_value(p, b)
        if fa*fb < 0:
            aa, bb = a, b
            for _ in range(45):
                m = (aa+bb)/2
                if polynomial_value(p, aa)*polynomial_value(p, m) < 0: bb = m
                else: aa = m
            out.append({'lower': str(a), 'upper': str(b), 'approximation': float((aa+bb)/2)})
    return out


def parse_source(root):
    core = root/'Lean/SaturationMonoid/PhysicsCore'
    names = ['colorZeroIndex','colorOneIndex','colorTwoIndex','weakZeroIndex',
             'weakOneIndex','hyperPlusIndex','hyperMinusIndex']
    texts = {}
    for name in ['SU7ExteriorYukawaMassSpectrum.lean', 'SU7ExteriorBreakingYukawa.lean',
                 'SU7MotherLieAlgebra.lean', 'SU7ExteriorMatterRepresentation.lean',
                 'SU7ExteriorMatterRestriction.lean','StageNineDynamicBreakingVacuum.lean',
                 'StageNineGlobalIntegratedAction.lean','StageNineExteriorMotherLieRepresentation.lean',
                 'StageNineFormNativeMotherAction.lean','Stage9C/Material/SpinPair/Parameters.lean']:
        texts[name] = (core/name).read_text()
    source = texts['SU7ExteriorYukawaMassSpectrum.lean']
    block = source.split('def finiteGenerationScalarSubset :',1)[1].split('\ndef ',1)[0]
    terms = re.findall(r'\|\s*([01]),\s*([01])\s*=>\s*\{([^}]+)\}', block)
    if len(terms) != 4: raise ValueError('Joint scalar source syntax changed; review extractor.')
    scalar = Counter()
    for o, i, raw in terms:
        values = [names.index(x.strip()) for x in raw.split(',')]
        if len(set(values)) != 4: raise ValueError('Invalid exterior basis subset')
        scalar[tuple(sorted(values))] += 1
    joint = source.split('def finiteGenerationJointBreakingScalar :',1)[1].split('\ntheorem ',1)[0]
    if '∑ output : Fin 2' not in joint or '∑ input : Fin 2' not in joint:
        raise ValueError('Joint scalar sum changed; review extractor.')
    degrees_block = texts['SU7ExteriorMatterRepresentation.lean'].split('def exteriorSpinorDegree',1)[1].split('\n\n',1)[0]
    degrees = [int(x) for x in re.findall(r'\|\s*[012]\s*=>\s*(\d+)', degrees_block)]
    if sorted(degrees) != [2,4,6]: raise ValueError('Matter degrees changed; review inventory.')
    manifest = {str((core/k).relative_to(root)): hashlib.sha256(v.encode()).hexdigest() for k,v in texts.items()}
    return names, scalar, degrees, manifest


def branch_counts(degrees):
    counts = Counter()
    for k in degrees:
        for subset in it.combinations(range(7),k):
            c = sum(i < 3 for i in subset); w = sum(i in (3,4) for i in subset)
            q = int(5 in subset)-int(6 in subset)
            counts[('3' if c == 1 else '3bar' if c == 2 else '1', '2' if w == 1 else '1', q)] += 1
    rows, traces = [], [Q(0)]*3
    for (c,w,q), components in sorted(counts.items()):
        dc, dw = (1 if c == '1' else 3), (1 if w == '1' else 2)
        m = Q(components, dc*dw)
        assert m.denominator == 1
        rows.append({'color':c, 'weak':w, 'charge':q, 'multiplicity':int(m), 'components':components})
        traces[0] += m*dw*(Q(1,2) if c != '1' else 0)
        traces[1] += m*dc*(Q(1,2) if w != '1' else 0)
        traces[2] += components*q*q
    return rows, traces


def sign(values):
    return (-1)**sum(values[i] > values[j] for i in range(len(values)) for j in range(i+1,len(values)))


def yukawa(scalar):
    inputs, outputs = list(it.combinations(range(7),2)), list(it.combinations(range(7),6))
    index = {v:i for i,v in enumerate(outputs)}
    y = [[Q(0) for _ in inputs] for _ in outputs]
    for j, inp in enumerate(inputs):
        for sc, amplitude in scalar.items():
            if set(inp).isdisjoint(sc):
                joined = inp+sc
                y[index[tuple(sorted(joined))]][j] += amplitude*sign(joined)
    g = mul(y, transpose(y))
    assert all(i==j or not g[i][j] for i in range(7) for j in range(7))
    return inputs, outputs, y, g


def generators(blocks=None):
    out = []
    blocks = [tuple(range(7))] if blocks is None else blocks
    def push(label, imaginary, entries):
        m = [[Q(0)]*7 for _ in range(7)]
        for i,j,v in entries: m[i][j] = Q(v)
        out.append((label, imaginary, m))
    for block in blocks:
        for i,j in it.combinations(block,2):
            push(f'A{i}{j}',False,[(i,j,1),(j,i,-1)])
            push(f'S{i}{j}',True,[(i,j,1),(j,i,1)])
        for i in block[:-1]:
            push(f'D{i}-{block[-1]}',True,[(i,i,1),(block[-1],block[-1],-1)])
    if len(blocks) > 1:
        push('Y',True,[(5,5,1),(6,6,-1)])
    return out


def exterior_action(generator, degree):
    basis = list(it.combinations(range(7),degree)); ids = {s:i for i,s in enumerate(basis)}
    matrix = [[Q(0)]*len(basis) for _ in basis]
    for col, subset in enumerate(basis):
        for slot, original in enumerate(subset):
            for new in range(7):
                value = generator[new][original]
                if not value: continue
                changed = list(subset); changed[slot] = new
                if len(set(changed)) != degree: continue
                matrix[ids[tuple(sorted(changed))]][col] += value*sign(changed)
    return matrix


def grams(gs, scalar, native):
    basis = list(it.combinations(range(7),4)); v = [[Q(scalar.get(s,0))] for s in basis]
    vectors = [mul(exterior_action(g,4),v) for _,_,g in gs]
    k, b = [], []
    for i,(_,im,g) in enumerate(gs):
        k.append([]); b.append([])
        for j,(_,jm,h) in enumerate(gs):
            k[-1].append(sum(x[0]*y[0] for x,y in zip(vectors[i],vectors[j])) if im == jm else Q(0))
            b[-1].append(sum(x*y for gr,hr in zip(g,h) for x,y in zip(gr,hr)) if im == jm else Q(0))
    if native:
        assert gs[-1][0] == 'Y' and b[-1][-1] == 2
        b[-1][-1] = Q(1)  # exactly hyperchargeLiePairing, NOT mother trace restriction
    r = mul(inverse(b),k)
    polynomial = charpoly(r); linear, rem = factors(polynomial)
    v0 = nullspace(k)
    p0 = mul(mul(mul(v0,inverse(mul(mul(transpose(v0),b),v0))),transpose(v0)),b)
    h = add(inverse(add(r,p0)),p0,Q(-1))
    exchange = mul(h,inverse(b))
    unit = eye(len(gs))
    assert mul(p0,p0) == p0 and mul(k,p0) == [[Q(0)]*len(gs) for _ in gs]
    assert exchange == transpose(exchange)
    assert mul(exchange,k) == add(unit,p0,Q(-1))
    assert mul(k,exchange) == add(unit,transpose(p0),Q(-1))
    assert mul(mul(k,exchange),k) == k and mul(mul(exchange,k),exchange) == exchange
    return {'generators':[x[0] for x in gs], 'K':k, 'B':b, 'B_inverse_K':r,
            'rank':len(rref(k)[1]), 'nullspace_columns':v0, 'light_projector':p0,
            'inverse_on_massive_current_slots':exchange, 'characteristic_polynomial':polynomial,
            'linear_factors':linear, 'remaining_factor':rem, 'positive_root_intervals':positive_root_intervals(rem),
            'checks':['Cayley-Hamilton','P0^2=P0','K P0=0','C^T=C', 'C K=I-P0',
                      'K C=I-P0^T','K C K=K','C K C=C']}


def sparse_currents(gs, degrees):
    out = []
    for label, imaginary, g in gs:
        entries, offset = [], 0
        for degree in degrees:
            a = exterior_action(g,degree)
            for i,row in enumerate(a):
                for j,x in enumerate(row):
                    if x: entries.append([offset+i,offset+j,int(x)])
            offset += len(a)
        assert offset == 63
        out.append({'generator':label,'multiply_by_i':imaginary,'entries':entries})
    return out


def encode(obj):
    if isinstance(obj,Q): return str(obj)
    if isinstance(obj,dict): return {str(k):encode(v) for k,v in obj.items()}
    if isinstance(obj,(list,tuple)): return [encode(x) for x in obj]
    return obj


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    parser.add_argument('--out',type=Path,required=True)
    args = parser.parse_args(); args.out.mkdir(parents=True,exist_ok=True)
    names, scalar, degrees, manifest = parse_source(args.root)
    scalars, st = branch_counts([4]); matter, ft = branch_counts(degrees)
    mother_f = sum(Q(math.comb(5,k-1),2) for k in degrees)
    mother_s = Q(math.comb(5,3),2)
    f = [mother_f]+ft; ss = [mother_s]+st
    b0 = [Q(11,3)*c-Q(2,3)*wf-Q(1,3)*sc for c,wf,sc in zip([7,3,2,0],f,ss)]
    dirac_diagnostic = [Q(11,3)*c-Q(4,3)*wf-Q(1,3)*sc for c,wf,sc in zip([7,3,2,0],f,ss)]
    ins, outs, y, yg = yukawa(scalar)
    mother = grams(generators(),scalar,False)
    residual_generators = generators([(0,1,2),(3,4)])
    residual = grams(residual_generators,scalar,True)
    residual_mother_metric = grams(residual_generators,scalar,False)
    sig = Q(1,2)  # sourceCoupling_eq; audited separately in Lean, never fitted
    samples=[]
    for k in range(129):
        ell = -12+k/8; t = ell/(8*math.pi**2)
        i3 = float(Q(1,2)/sig)+float(b0[1])*t
        i2 = float(Q(1,2)/sig)+float(b0[2])*t
        iy = float(1/sig)+float(b0[3])*t
        samples.append({'log_mu_ratio':ell,'reduced_time':t,'inverse_g3_squared':i3,
                        'inverse_g2_squared':i2,'inverse_gY_squared':iy,'inverse_g1_squared':iy/4})
    result={'status':'EXACT_SUBORDINATE_READOUT_NOT_EMPIRICAL_PARTICLE_IDENTIFICATION',
      'source_sha256':manifest,'basis_names':names,'weyl_degrees':degrees,
      'joint_scalar_terms':[[list(k),v] for k,v in sorted(scalar.items())],
      'scalar_branching':scalars,'weyl_branching':matter,'scalar_traces':ss,'weyl_traces':f,
      'b0_one_left_Weyl_copy_plus_complex35':b0,'b0_two_Weyl_copies_diagnostic_only':dirac_diagnostic,
      'yukawa':{'input_basis':ins,'output_basis':outs,'matrix':y,'output_gram':yg,
                'rank':len(rref(y)[1]),'input_nullity':21-len(rref(y)[1]),
                'squared_singular_values':dict(Counter(yg[i][i] for i in range(7)))},
      'mother_orbit_gram_not_48_dynamical_vectors':mother,
      'native_P286_scalar_gauge_block':residual,
      'P286_with_mother_metric_comparison_not_native':residual_mother_metric,
      'factorized_current_operators':sparse_currents(residual_generators,degrees),
      'running':{'scope':'fixed-inventory one-loop diagnostic; no thresholds or GeV matching',
                 'sigma':sig,'canonical_boundary_inverse_g_squared':[1,1,Q(1,2)],
                 'canonical_b0':[b0[1],b0[2],b0[3]/4], 'samples':samples},
      'proton_lifetime':None,
      'open_interfaces':['physical chiral loop counting','canonical kinetic matching proof to full action',
        'coupled fluctuation/pole spectrum on actual curved nonzero-field background',
        'physical low-energy states and thresholds','source-unit to GeV calibration',
        'baryon/lepton identification and hadronic/RG matrix elements']}
    target=args.out/'exact-readout.json'; target.write_text(json.dumps(encode(result),ensure_ascii=False,indent=2)+'\n')
    print('PASS: exact arithmetic, basis-derived branching, full joint-Yukawa map, orbit Grams, and projected exchange checks')
    print('scalar traces:',ss,'b0:',b0,'Yukawa rank:',result['yukawa']['rank'])
    print('mother rank:',mother['rank'],'spectrum:',mother['linear_factors'])
    print('native P286 rank:',residual['rank'],'rational spectrum:',residual['linear_factors'],'remaining:',residual['remaining_factor'])
    print('native nonrational eigenvalues:',residual['positive_root_intervals'])
    print('wrote',target)

if __name__=='__main__':
    main()
