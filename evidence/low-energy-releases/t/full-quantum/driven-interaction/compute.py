#!/usr/bin/env python3
"""Original total current on all four causal theta growth-leg pairings."""
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import sys
import time
import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
BASE = ROOT / 'Verification/physics/low-energy-phenomenology'
u, q = s.symbols('u q', real=True)
START = time.monotonic()


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    original = load(HERE.parent / 'light-interaction/audit/source_check.py', 'original_cubic_mechanism')
    source = json.loads((BASE / 'active-gauge/receipt.json').read_text())
    field = json.loads((HERE.parent / 'light-modes/field-receipt.json').read_text())
    old = json.loads((HERE.parent / 'light-interaction/total-receipt.json').read_text())
    for path, digest in source['source_sha256'].items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, path
    core = ROOT / 'Lean/SaturationMonoid/PhysicsCore'
    gamma = []
    text = (core / 'DiracCliffordRepresentation.lean').read_text()
    for name in ['Zero', 'One', 'Two', 'Three']:
        raw = text.split('def diracGamma' + name + ' : DiracMatrix :=', 1)[1].split(']', 1)[0].split('!![', 1)[1]
        gamma.append(s.Matrix([[s.sympify(v.replace('Complex.I', 'I')) for v in row.split(',')] for row in raw.split(';')]))
    bits = load(BASE / 'mixed-symbol/audit/independent_check.py', 'original_exterior_coordinates')
    inventory = load(BASE / 'exact_readout.py', 'original_native_inventory')
    _, vacuum, _, _ = inventory.parse_source(ROOT)
    raw = inventory.generators([(0, 1, 2), (3, 4)])
    fundamental = [s.Matrix(m) * (s.I if imaginary else 1) for _, imaginary, m in raw]
    assert fundamental[1] == s.diag(s.Matrix([[0, s.I], [s.I, 0]]), s.zeros(5))
    triplet = [bits.basis(2).index((i, 5)) for i in range(3)]
    action = bits.exterior(fundamental[1], 2).extract(triplet, triplet)
    B = original.pairblock(s.I * s.kronecker_product(gamma[1], action))
    pairing = lambda left, right: s.expand((left.T * B * right)[0])
    N = s.sympify(source['source_lapse'])
    c = N * s.sqrt(2)
    indices = {(x['group'], tuple(x['coordinate'])): i for i, x in enumerate(source['fields'])}
    leg = s.SparseMatrix(289, 1, {(i, j): s.sympify(v, locals={'u': u, 'q': q}) for i, j, v in field['axial_original289_pole_leg']['entries']})
    pi = [indices['primal_H', (im, sp, col)] for im in range(2) for sp in range(4) for col in range(3)]
    ci = [indices['dual_H', (im, sp, col)] for im in range(2) for sp in range(4) for col in range(3)]
    psi = s.Matrix(list(map(s.sympify, source['actual_background']['primal_H'])))
    exchange = s.kronecker_product(gamma[0] * s.diag(-1, -1, 1, 1), s.eye(3))
    chi = s.sqrt(2) * psi.T * exchange
    x0 = psi.applyfunc(s.re).col_join(psi.applyfunc(s.im))
    c0 = chi.T.applyfunc(s.re).col_join(chi.T.applyfunc(s.im))
    pairs = [(0, 1), (0, 2), (0, 3), (2, 3), (3, 1), (1, 2)]
    wedge = s.Matrix(6, 6, lambda i, j: 0 if len(set(pairs[i] + pairs[j])) < 4 else original.parity(pairs[i] + pairs[j]))
    def primitive(V, group, n):
        return [sum((V[indices[group, (i, j)]] * fundamental[j] for j in range(12)), s.zeros(7)) for i in range(n)]
    def curvature(A):
        return [(fundamental[1] * A[b] - A[b] * fundamental[1] if a == 1 else s.zeros(7)) +
                (A[a] * fundamental[1] - fundamental[1] * A[a] if b == 1 else s.zeros(7)) for a, b in pairs]
    # The original lightCoframe includes e30; its selected cofactor is still c0*c2*c3.
    e = [leg[indices['coframe', (i, i)]] for i in [0, 2, 3]]
    diagonal = s.Matrix(4, 4, lambda i, j: leg[indices['coframe', (i, j)]])
    assert all(diagonal[i,j] == 0 for i,j in itertools.product(range(4), repeat=2)
               if i != j and (i,j) != (3,0))
    d = s.expand(e[0] + N * (e[1] + e[2]))
    dd = s.expand(2 * (e[0]*e[1] + e[0]*e[2] + N*e[1]*e[2]))
    outputs = []
    for first, second in itertools.product([1, -1], repeat=2):
        plus = leg.subs({u: first*u}, simultaneous=True)
        minus = leg.subs({u: second*u, q: -q}, simultaneous=True)
        for V in [plus, minus]:
            assert all(s.expand(V[indices['coframe', (i, i)]] - e[j]) == 0 for j, i in enumerate([0, 2, 3]))
        xp, xm, cp, cm = plus[pi, :], minus[pi, :], plus[ci, :], minus[ci, :]
        bare = s.expand(N * (pairing(cp, xm) + pairing(cm, xp)))
        contact = s.expand(d*(pairing(cp, x0) + pairing(c0, xp) + pairing(cm, x0) + pairing(c0, xm)) + dd*pairing(c0, x0))
        Ap, Am = primitive(plus, 'gauge_A', 4), primitive(minus, 'gauge_A', 4)
        Bp, Bm = primitive(plus, 'gauge_B', 6), primitive(minus, 'gauge_B', 6)
        fp, fm = curvature(Ap), curvature(Am)
        bf = s.expand(sum(-wedge[i,j]*s.trace(Bp[i]*fm[j] + Bm[i]*fp[j])
                         for i,j in itertools.product(range(6), repeat=2) if wedge[i,j]))
        total = s.expand(bare + contact + bf)
        if (first, second) == (1, -1):
            signed = next(x for x in old['all48_total_source_cubics'] if x['coordinate'] == [1, 1])
            assert s.expand(total - s.sympify(signed['total'], locals={'u': u, 'q': q})) == 0
        terms = s.Poly(total / s.sqrt(15), u, q)
        lowest = min(sum(m) for m, _ in terms.terms())
        leading = sum(coef*u**i*q**j for (i,j),coef in terms.terms() if i+j == lowest)
        outputs.append({'growth_signs': [first, second], 'bare': str(bare), 'coframe_contact': str(contact),
                        'gauge_BF': str(bf), 'total': str(total), 'terms': len(terms.terms()),
                        'leading_without_sqrt15': str(s.factor(leading)),
                        'own_u_derivative_product_sign': first*second})
        print(first, second, 'terms', len(terms.terms()), 'leading', s.factor(leading), flush=True)
    bysign = {tuple(x['growth_signs']): s.sympify(x['total'], locals={'u':u,'q':q}) for x in outputs}
    assert s.expand(bysign[1,1]-bysign[-1,-1]) == 0
    assert s.expand(bysign[1,-1]-bysign[-1,1]) == 0
    M = s.expand(-2*N*leg[57])
    assert M == s.sympify(field['axial_metric_pole_numerator'], locals={'u':u,'q':q}).expand()
    report = {'scope': 'ORIGINAL_SELECTED_CURRENT_ON_ALL_FOUR_PHYSICAL_THETA_GROWTH_LEGS',
              'source_sha256': source['source_sha256'], 'selected_source': 'A1(S01)',
              'spatial_momenta': ['+sqrt(2)*q', '-sqrt(2)*q'],
              'physical_clock': str(c), 'g00_numerator': str(M), 'pairings': outputs,
              'growth_reversal_even': True, 'reciprocal_signed_cubic_recovered': True,
              'residue_leg': 'c*L(sigma*u,spatial_q)/(sigma*partial_u_F(u,q))',
              'metric_residue_leg': 'sigma*R; R=c*M(u,q)/partial_u_F(u,q)',
              'seconds': round(time.monotonic()-START, 3)}
    (HERE/'receipt.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS four actual source pairings and original reciprocal control', flush=True)


if __name__ == '__main__':
    main()
