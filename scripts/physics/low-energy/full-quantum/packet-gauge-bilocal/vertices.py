#!/usr/bin/env python3
"""Two independent first jets of the original full current density.

No integration-by-parts identification between the two frequencies is made
while producing the vertex. Opposite Fourier legs and conjugate Laplace legs
are subsequently checked as distinct specializations of the same source.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

import sympy as s

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
BASE = FQ.parent
ROOT = HERE.parents[4]


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def clean(matrix):
    return s.SparseMatrix(matrix.rows, matrix.cols, {key: v for key, raw in
        s.SparseMatrix(matrix).todok().items() if (v := s.expand(raw)) != 0})


def decode(record):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(value) for i, j, value in record['entries']})


def density_hessian(jet, coordinates, density):
    out = {}
    for key, value in density.terms.items():
        if len(key) != 2:
            continue
        for left, right in [key, key[::-1]]:
            i, a = coordinates.jets[left]
            j, b = coordinates.jets[right]
            index = (i, j, a, b)
            out[index] = out.get(index, jet.ZERO)+value
    out = {key: value for key, value in out.items() if value}
    assert all(out.get((j, i, b, a), jet.ZERO) == value for (i, j, a, b), value in out.items())
    return out


def opposite_operator(jet, data):
    out = {}
    for (i, j, a, b), value in data.items():
        powers = [0]*4
        if a >= 0:
            powers[a] += 1
        if b >= 0:
            powers[b] += 1
        key = (i, j, tuple(powers))
        out[key] = out.get(key, jet.ZERO)+(-value if a >= 0 else value)
    return {key: value for key, value in out.items() if value}


def evaluate(entries, left, right):
    out = s.MutableSparseMatrix(289, 289, {})
    for i, j, a, b, value in entries:
        out[i, j] += s.sympify(value)*(left[a] if a >= 0 else 1)*(right[b] if b >= 0 else 1)
    return clean(out)


def main():
    started = time.monotonic()
    original = json.loads((BASE/'active-gauge/receipt.json').read_text())
    source = json.loads((FQ/'packet-gauge-kernel/source.json').read_text())
    readers = json.loads((FQ/'packet-gauge-kernel/readers.json').read_text())
    for path, digest in original['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest
    jet = load(BASE/'active-gauge/compute.py', 'bilocal_original_jet')
    tensor = load(FQ/'vertex-tensor/compute.py', 'bilocal_native_vertices')
    sys.modules['compute'] = tensor
    covariance = load(FQ/'vertex-tensor/covariance.py', 'bilocal_original_nonderivative_current')
    _, _, _, _, context = tensor.source_tables(False)
    bare = covariance.source_hessians(context)
    coordinates = jet.Coordinates()
    for name, shape in [('scalar_J', (9,)), ('gauge_A', (4, 12)), ('coframe', (4, 4)),
        ('primal_H', (2, 4, 3)), ('dual_H', (2, 4, 3)), ('Lorentz', (4, 6)),
        ('gravity_B', (6, 6)), ('multiplier', (6, 6)), ('gauge_B', (6, 12))]:
        coordinates.group(name, shape)
    assert coordinates.fields == original['fields']
    q, J = coordinates.value, jet.Jet
    inclusion, v = decode(source['scalar_J_inclusion']), decode(source['scalar_v'])
    rho = list(map(decode, source['scalar_rho']))
    abar = decode(source['gauge_background'])
    e0 = context['coframe']
    e = jet.matrix(4, 4, lambda a, mu: e0[a, mu]+q('coframe', a, mu))
    ei = jet.inverse_second_jet(e, e0.inv())
    volume = jet.determinant(e)
    metric_density = jet.matrix(4, 4, lambda mu, nu: volume*sum(
        (jet.ETA[a, a]*ei[mu][a]*ei[nu][a] for a in range(4)), J()))
    eta = jet.multiply(jet.fixed(inclusion), jet.matrix(9, 1, lambda i, j: q('scalar_J', i)))
    phi = jet.add(jet.fixed(v), eta)
    covariant = []
    for nu in range(4):
        derivative = jet.multiply(jet.fixed(inclusion), jet.matrix(9, 1,
            lambda i, j: q('scalar_J', i, derivative=nu)))
        for g in range(12):
            derivative = jet.add(derivative, jet.multiply(jet.fixed(rho[g]), jet.add(
                jet.scale(abar[nu, g], eta), jet.scale(q('gauge_A', nu, g), phi))))
        covariant.append(derivative)
    changed = jet.multiply(jet.fixed(rho[1]), phi)
    prior = {tuple(row['reader']): row for row in readers['readers']}
    records = []
    z = s.Rational(3, 5)-s.I*s.Rational(2, 7)
    physical = [z, s.I/s.Integer(5), -s.I/s.Integer(7), s.I/s.Integer(9)]
    conjugate = list(map(s.conjugate, physical))
    differing = []
    for mu in range(4):
        for g in range(12):
            reader = jet.multiply(jet.fixed(rho[g]), phi)
            scalar = sum((metric_density[nu][mu]*sum(
                (a[0]*b[0] for a, b in zip(covariant[nu], reader)), J()) for nu in range(4)), J())
            contact = metric_density[1][mu]*sum((a[0]*b[0] for a, b in zip(changed, reader)), J())
            scalar_bijet = density_hessian(jet, coordinates, scalar)
            full = {(i, j, -1, -1): jet.number(value) for (i, j), value in bare[mu, g].todok().items()}
            for key, value in scalar_bijet.items():
                full[key] = full.get(key, jet.ZERO)+value
            full = {key: value for key, value in full.items() if value}
            contact_bijet = density_hessian(jet, coordinates, contact)
            assert all(a == b == -1 for i, j, a, b in contact_bijet)
            assert jet.encoded_operator(opposite_operator(jet, full)) == prior[mu, g]['Q0']
            assert jet.encoded_operator(opposite_operator(jet, contact_bijet)) == prior[mu, g]['Q1_contact']
            entries = [[int(i), int(j), int(a), int(b), jet.stringify(value)]
                for (i, j, a, b), value in sorted(full.items())]
            contact_entries = [[int(i), int(j), int(a), int(b), jet.stringify(value)]
                for (i, j, a, b), value in sorted(contact_bijet.items())]
            actual_pair = evaluate(entries, conjugate, physical)
            assert actual_pair == actual_pair.conjugate().T
            wrong_pair = evaluate(entries, [-value for value in physical], physical)
            difference = clean(actual_pair-wrong_pair)
            if difference.todok():
                (i, j), value = next(iter(difference.todok().items()))
                differing.append({'reader': [mu, g], 'entry': [int(i), int(j)], 'difference': str(value)})
            records.append({'reader': [mu, g], 'Q0_bijet': entries, 'Q1_bijet': contact_entries,
                'scalar_bijet_entries': len(scalar_bijet), 'opposite_full_symbol_recovered': True,
                'Hermitian_conjugate_pair_verified': True})
    assert differing
    result = {
        'scope': 'STRIKE_ORIGINAL_CURRENT_DENSITY_WITH_TWO_INDEPENDENT_FIRST_JETS',
        'source_sha256': original['source_sha256'],
        'input_sha256': {name: hashlib.sha256((FQ/'packet-gauge-kernel'/name).read_bytes()).hexdigest()
            for name in ['source.json', 'readers.json']},
        'entry_convention': '[i,j,a,b,coefficient]; derivative index -1 is value, 0..3 are original physical partials',
        'density_identity': 'j_b^(2)(X)=1/2 sum c_ijab (partial_a X_i)(partial_b X_j); the current density is generated before integration by parts',
        'bilocal_identity': 'Q_b(l,r)_ij=sum c_ijab l_a r_b, where l_-1=r_-1=1; Q_b(l,r)^T=Q_b(r,l)',
        'external_family': source['external_family'],
        'reader_derivative_identity': 'Q_b(epsilon;l,r)=Q_b(0;l,r)+epsilon Q_b_prime(l,r)',
        'opposite_Fourier_specialization': 'l=-p,r=p exactly recovers all48 previously certified full Q_b(p), including scalar terms',
        'conjugate_specialization': 'l=conj(p),r=p is Hermitian, and generally differs from the opposite-leg symbol when Re(p0)>0',
        'control_positive_damping_point': list(map(str, physical)),
        'opposite_vs_conjugate_actual_differences': differing,
        'readers': records,
        'scalar_bijet_entry_count': sum(row['scalar_bijet_entries'] for row in records),
        'all_bijet_entry_count': sum(len(row['Q0_bijet']) for row in records),
        'source_contact_entry_count': sum(len(row['Q1_bijet']) for row in records),
        'scope_of_time': 'First-jet polarization of the same local density; matching to actual Laplace fields must also account for their initial data and convergence',
        'elapsed_seconds': round(time.monotonic()-started, 3),
    }
    (HERE/'vertices.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS all48 source density bi-jets and opposite-symbol readback', result['all_bijet_entry_count'], flush=True)
    print('PASS actual positive-damping conjugate pairs Hermitian; distinct from opposite for', len(differing), 'readers', flush=True)
    print('seconds', result['elapsed_seconds'], flush=True)


if __name__ == '__main__':
    main()
