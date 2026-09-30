#!/usr/bin/env python3
"""Generate transverse/longitudinal vertices from the original source action.

The only inputs are the original source inventory and its generated 289-field
light legs. Existing four-pair receipts are checked after the action is evaluated.
Default replay compares the owned Lean table; --emit creates it during strike.
"""
import argparse
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
FQ = BASE / 'full-quantum'
LEAN = ROOT / 'Lean/SaturationMonoid/PhysicsCore/LowEnergy/VertexTensor/Coefficients.lean'
u, q, r, w = s.symbols('u q r w', real=True)


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def source_tables(generate_tables=True):
    helper = load(FQ / 'light-interaction/audit/source_check.py', 'tensor_native_cubic')
    native = load(BASE / 'exact_readout.py', 'tensor_native_inventory')
    exterior = load(BASE / 'mixed-symbol/audit/independent_check.py', 'tensor_native_exterior')
    actual = json.loads((BASE / 'active-gauge/receipt.json').read_text())
    field = json.loads((FQ / 'light-modes/field-receipt.json').read_text())
    for path, digest in actual['source_sha256'].items():
        assert hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == digest, path
    idx = {(row['group'], tuple(row['coordinate'])): i for i, row in enumerate(actual['fields'])}
    N = s.sympify(actual['source_lapse'])
    e0 = s.diag(N, 1, 1, 1)
    leg = s.SparseMatrix(289, 1, {(i, j): s.sympify(value, locals={'u': u, 'q': q})
        for i, j, value in field['axial_original289_pole_leg']['entries']})
    assert all(leg[i] == 0 for i, row in enumerate(actual['fields']) if row['group'] == 'scalar_J')
    fundamental = [s.Matrix(matrix) * (s.I if imaginary else 1)
        for _, imaginary, matrix in native.generators([(0, 1, 2), (3, 4)])]
    text = (ROOT / 'Lean/SaturationMonoid/PhysicsCore/DiracCliffordRepresentation.lean').read_text()
    gamma = []
    for name in ['Zero', 'One', 'Two', 'Three']:
        body = text.split('def diracGamma' + name + ' : DiracMatrix :=', 1)[1].split(']', 1)[0].split('!![', 1)[1]
        gamma.append(s.Matrix([[s.sympify(x.replace('Complex.I', 'I')) for x in row.split(',')] for row in body.split(';')]))
    triplet = [exterior.basis(2).index((j, 5)) for j in range(3)]
    actions = [exterior.exterior(t, 2).extract(triplet, triplet) for t in fundamental]
    blocks = {(gen, a): helper.pairblock(s.I * s.kronecker_product(gamma[a], actions[gen]))
        for gen in range(12) for a in range(4)}
    pi = [idx['primal_H', (im, spin, col)] for im in range(2) for spin in range(4) for col in range(3)]
    ci = [idx['dual_H', (im, spin, col)] for im in range(2) for spin in range(4) for col in range(3)]
    psi = s.Matrix(list(map(s.sympify, actual['actual_background']['primal_H'])))
    exchange = s.kronecker_product(gamma[0] * s.diag(-1, -1, 1, 1), s.eye(3))
    assert exchange.T == exchange
    chi = s.sqrt(2) * exchange * psi
    x0 = psi.applyfunc(s.re).col_join(psi.applyfunc(s.im))
    y0 = chi.applyfunc(s.re).col_join(chi.applyfunc(s.im))
    pairs = [(0, 1), (0, 2), (0, 3), (2, 3), (3, 1), (1, 2)]

    def primitive(v, group, count):
        return [sum((v[idx[group, (i, j)]] * fundamental[j] for j in range(12)), s.zeros(7)) for i in range(count)]

    def evaluate(first, second):
        P = leg.subs(u, first*u)
        Q = leg.subs({u: second*u, q: -q}, simultaneous=True)
        xp, xm, yp, ym = P[pi, :], Q[pi, :], P[ci, :], Q[ci, :]
        cofactors = {}
        for mu, a in itertools.product(range(4), repeat=2):
            rows = [i for i in range(4) if i != a]
            cols = [i for i in range(4) if i != mu]
            out = {}
            for permutation in itertools.permutations(range(3)):
                term = {(0, 0): s.Integer((-1)**(mu+a) * helper.parity(permutation))}
                for row, j in zip(rows, permutation):
                    col = cols[j]
                    entries = [((0, 0), e0[row, col]), ((1, 0), P[idx['coframe', (row, col)]]),
                        ((0, 1), Q[idx['coframe', (row, col)]])]
                    term = helper.poly_mul(term, {key: value for key, value in entries if value != 0})
                for key, value in term.items():
                    out[key] = out.get(key, 0) + value
            cofactors[mu, a] = {key: s.expand(value) for key, value in out.items() if s.expand(value) != 0}
        Ap, Am = primitive(P, 'gauge_A', 4), primitive(Q, 'gauge_A', 4)
        Bp, Bm = primitive(P, 'gauge_B', 6), primitive(Q, 'gauge_B', 6)
        results = {}
        for mu, gen in itertools.product(range(4), range(12)):
            matter = 0
            for a in range(4):
                if not cofactors[mu, a]:
                    continue
                B = blocks[gen, a]
                current = {(0, 0): (y0.T*B*x0)[0], (1, 0): (yp.T*B*x0+y0.T*B*xp)[0],
                    (0, 1): (ym.T*B*x0+y0.T*B*xm)[0], (1, 1): (yp.T*B*xm+ym.T*B*xp)[0]}
                matter += helper.poly_mul(cofactors[mu, a], current).get((1, 1), 0)
            def curvature(A):
                return [(fundamental[gen]*A[b]-A[b]*fundamental[gen] if mu == a else s.zeros(7)) +
                    (A[a]*fundamental[gen]-fundamental[gen]*A[a] if mu == b else s.zeros(7)) for a, b in pairs]
            fp, fm = curvature(Ap), curvature(Am)
            bf = sum(-helper.parity(pairs[i]+pairs[j])*s.trace(Bp[i]*fm[j]+Bm[i]*fp[j])
                for i, j in itertools.product(range(6), repeat=2) if len(set(pairs[i]+pairs[j])) == 4)
            results[mu, gen] = s.expand(matter+bf)
        return results

    tables = {signs: evaluate(*signs) for signs in itertools.product([1, -1], repeat=2)} if generate_tables else {}
    context = {'indices': idx, 'coframe': e0, 'blocks': blocks, 'primal_indices': pi,
        'dual_indices': ci, 'primal': x0, 'dual': y0, 'pairs': pairs,
        'fundamental': fundamental, 'helper': helper, 'leg': leg}
    return actual, field, N, tables, context


def lean_source(records):
    header = '''import SaturationMonoid.PhysicsCore.LowEnergy.DrivenInteraction.Polynomial

/-! Exact longitudinal-minus-transverse source tables, generated from all
four original 289-field cubic evaluations with coframe and BF contacts. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.VertexTensor
open LightModes
noncomputable section

'''
    for name, record in records.items():
        terms = ', '.join('⟨%s,%s,%s⟩' % (row['r'], row['w'], row['coefficient']) for row in record['difference_terms'])
        header += f'def {name}Difference : List Term :=\n  [{terms}]\n\n'
        header += f'''theorem {name}_difference_bound : coefficientBound {name}Difference={record['bound']} := by
  norm_num [{name}Difference,coefficientBound]

theorem {name}_difference_small : momentumRadius^2*coefficientBound {name}Difference<1/20 := by
  rw [{name}_difference_bound]
  norm_num [momentumRadius]

theorem {name}_difference_admissible : ∀ t∈{name}Difference, t.rPower≤ t.wPower+2 := by
  simp [{name}Difference]

'''
    return header + 'end\nend SaturationMonoid.PhysicsCore.LowEnergy.VertexTensor\n'


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--emit', action='store_true')
    args = parser.parse_args()
    start = time.monotonic()
    actual, field, N, tables, _ = source_tables()
    old = json.loads((FQ / 'driven-interaction/receipt.json').read_text())
    old_opposite = json.loads((FQ / 'light-interaction/total-receipt.json').read_text())
    for row in old['pairings']:
        assert s.expand(tables[tuple(row['growth_signs'])][1, 1] - s.sympify(row['total'], locals={'u': u, 'q': q})) == 0
    for row in old_opposite['all48_total_source_cubics']:
        assert s.expand(tables[1, -1][tuple(row['coordinate'])] - s.sympify(row['total'], locals={'u': u, 'q': q})) == 0
    scale = s.Poly(s.expand(tables[1, 1][1, 1]/s.sqrt(15)), u, q).coeff_monomial(u**2)
    factor = s.Poly(s.sympify(field['axial_source_factor'], locals={'u': u, 'q': q}), u, q)
    source_coefficient = factor.coeff_monomial(u**2)
    assert scale/(4*source_coefficient**2) == s.Rational(9, 6250)
    records = {}
    for name, second in [('same', 1), ('opposite', -1)]:
        table = tables[1, second]
        assert all(s.expand(table[key].subs(u, -u)-tables[-1, -second][key]) == 0 for key in table)
        T = table[1, 1]
        L = s.expand(table[3, 6]-table[3, 7])
        assert s.expand(T-T.subs(u, -u)) == s.expand(L-L.subs(u, -u)) == 0
        assert table[2, 0] == T
        allowed = {(1, 1), (2, 0), (3, 6), (3, 7), (0, 6), (0, 7)}
        assert all(value == 0 for key, value in table.items() if key not in allowed)
        assert s.expand(table[3, 6]+table[3, 7]) == 0
        difference = s.Poly(s.expand(second*(L-T)/(s.sqrt(15)*scale)), u, q)
        assert all(i % 2 == j % 2 == 0 and j >= 2 and i+j >= 4 for (i, j), _ in difference.terms())
        terms = {(i//2, (i+j)//2-2): coefficient for (i, j), coefficient in difference.terms()}
        normalized = s.expand(sum(coefficient*r**i*w**j for (i, j), coefficient in terms.items()))
        rebuilt = sum(coefficient*u**(2*i)*q**(2*(j+2-i)) for (i, j), coefficient in terms.items())
        assert s.expand(rebuilt-difference.as_expr()) == 0
        delta_scaled = sum(coefficient*r**(i//2)*w**((i+j)//2) for (i, j), coefficient in difference.terms())
        assert s.expand(delta_scaled-w**2*normalized) == 0
        bound = sum(abs(coefficient)*2**i for (i, _), coefficient in terms.items())
        eps = s.Rational(5234375, 294988800512)
        assert eps**2*bound < s.Rational(1, 20)
        assert normalized.subs(w, 0) == -s.Rational(4475, 972)*r
        sample = s.Rational(1, 131072)
        discrepancy = s.Poly(s.expand((L-T)/s.sqrt(15)).subs(q, sample), u, domain=s.QQ)
        pole = s.Poly(factor.as_expr().subs(q, sample), u, domain=s.QQ)
        assert s.gcd(discrepancy, pole).degree() == 0
        records[name] = {'raw_transverse': str(T), 'raw_longitudinal': str(L),
            'source_difference': str(s.expand(L-T)), 'own_derivative_sign': second,
            'difference_terms': [{'r': i, 'w': j, 'coefficient': str(coefficient)} for (i, j), coefficient in terms.items()],
            'bound': str(bound), 'common_radius_error': str(eps**2*bound),
            'infrared_difference_polynomial': str(normalized.subs(w, 0)),
            'nonzero_on_every_actual_pole_at_q': str(sample),
            'all48': [{'coordinate': list(key), 'total': str(value)} for key, value in table.items()]}
        print('PASS', name, 'all48 source / existing transverse /', len(terms), 'difference terms / common radius', flush=True)
    generated = lean_source(records)
    if args.emit:
        LEAN.parent.mkdir(parents=True, exist_ok=True)
        LEAN.write_text(generated)
    else:
        assert LEAN.read_text() == generated, 'Lean source table differs from actual action-generated table'
    result = {'scope': 'ORIGINAL_SPATIAL_GAUGE_TENSOR_T_T_L_AND_OWN_DERIVATIVE_NORMALIZATION',
        'source_sha256': actual['source_sha256'], 'source_coefficient': str(source_coefficient),
        'source_numerator_scale_without_sqrt15': str(scale), 'physical_clock': str(N*s.sqrt(2)),
        'spatial_basis': ['S01', 'A01', 'D0-2 minus D1-2'], 'pairings': records,
        'all_four_growth_pairs_reconstructed': True, 'existing_transverse_and_reciprocal48_recovered': True,
        'original_light_scalar_increment_exactly_zero': True,
        'full48_growth_reversal_is_u_reflection': True, 'spatial_growth_reversal_even': True,
        'elapsed_seconds': round(time.monotonic()-start, 3)}
    (HERE / 'receipt.json').write_text(json.dumps(result, indent=2)+'\n')
    print('PASS source-normalized longitudinal tables and Lean source comparison', flush=True)


if __name__ == '__main__':
    main()
