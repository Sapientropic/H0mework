#!/usr/bin/env python3
"""Actual moving packet jets for all physical current probes, before Gram reads."""
import gzip
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
ROOT = HERE.parents[4]
from algebra import SphereAlgebra
from wave import QuadraticSphere, WaveVector


def main():
    began = time.monotonic()
    source_path = FQ/'packet-noise/source_kernel.py'
    spec = importlib.util.spec_from_file_location('probe_moments_packet_source', source_path)
    original = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(original)
    provenance, (N, omega, H0, Hj, CI, K, prepared) = original.exact_source()
    content = gzip.decompress((HERE/'operators.json.gz').read_bytes())
    operators = json.loads(content)
    receipt = json.loads((HERE/'operators.json').read_text())
    assert hashlib.sha256(content).hexdigest() == receipt['uncompressed_sha256']
    assert operators['source_sha256'] == provenance['source_sha256']
    A = SphereAlgebra(s.QQ_I)
    Q = QuadraticSphere(A)
    c = N*s.sqrt(2)
    cw, ow = s.simplify(c/s.sqrt(15)), s.simplify(omega/s.sqrt(15))
    assert cw.is_Rational and ow.is_Rational
    realF = A.scalar(-1+3*omega**2)-A.scalar(c*c)*A.x
    packet_den = realF*realF+A.scalar(16*omega**2)
    G0 = original.clean(CI/(s.I*N))
    seed_full = original.clean(G0*prepared)
    blocks = []
    for source_block in operators['blocks']:
        sign = source_block['chirality']
        indices = source_block['original12_indices']
        D = A.decode_polynomial(source_block['D'])
        seed = seed_full.extract(indices, [0])
        assert all(s.re(value).is_Rational and s.im(value).is_Rational for value in seed)
        hj = [A.from_matrix(original.decode(record)) for record in source_block['physical_Hj_over_N']]
        h0 = A.from_matrix(original.decode(source_block['h0']))
        h = A.add(h0, *(A.scale(A.v[i], hj[i]) for i in range(3)))
        qseed = [Q.scalar(value) for value in seed]
        partner = [Q.zero for _ in range(4)]
        for j in range(3):
            partial = Q.matvec(hj[j], qseed)
            partner = [Q.add(old, Q.scale(A.v[j], value)) for old, value in zip(partner, partial)]
        # Raw original Dirac packet is -N*g*b/n. g=(i-H)^-1 G0*w.
        # Multiplying by the conjugate chiral linear factor gives one common
        # real quadratic packet denominator for both source chirality blocks.
        num = [Q.add(Q.mul(Q.scalar(s.I, -3*sign*ow), value),
                     Q.mul(Q.scalar(0, cw), term)) for value, term in zip(qseed, partner)]
        conjugate_linear = realF, A.scalar(4*sign*s.I*ow)
        num = [Q.mul(value, conjugate_linear) for value in num]
        g = WaveVector(Q, D, packet_den, num)
        hnum = Q.matvec(h, num)
        residual = [Q.add(Q.scale(s.I, left), Q.mul(Q.scalar(0, -cw), middle),
                         Q.scale(-packet_den, right)) for left, middle, right in zip(num, hnum, qseed)]
        assert all(value == Q.zero for value in residual)
        dg = [g.packet_partial(j) for j in range(3)]
        d2g = {(i, j): dg[i].packet_partial(j) for i in range(3) for j in range(i, 3)}

        def apply(op, vector):
            return vector.operator(A.decode(op['numerator']), op['D_power'])

        def add(*vectors):
            result = vectors[0]
            for vector in vectors[1:]:
                result = result.plus(vector)
            return result

        def zero_like(vector):
            return WaveVector(Q, D, packet_den, [Q.zero for _ in range(4)], 0, 1)

        kinds = {}
        for kind in ['B', 'C']:
            G0op = source_block[kind+'0']
            G1 = source_block[kind+'1']
            G2 = {tuple(record['axes']): record for record in source_block[kind+'2']}
            z = apply(G0op, g)
            jets = [{'order': 0, 'axes': [], 'b': z.encode()}]
            for i in range(3):
                bb = apply(G1[i], g).plus(apply(G0op, dg[i]).scaled(-1))
                bt = z.scaled(-2*A.v[i])
                jets.append({'order': 1, 'axes': [i], 'b': bb.encode(), 't': bt.encode()})
            for i in range(3):
                for j in range(i, 3):
                    bb = add(apply(G2[i, j], g), apply(G1[i], dg[j]).scaled(-1),
                        apply(G1[j], dg[i]).scaled(-1), apply(G0op, d2g[i, j]))
                    bt = add(apply(G1[i], g).scaled(-2*A.v[j]), apply(G1[j], g).scaled(-2*A.v[i]),
                        apply(G0op, dg[j]).scaled(2*A.v[i]), apply(G0op, dg[i]).scaled(2*A.v[j]),
                        z.scaled(2) if i == j else zero_like(z))
                    bu = z.scaled(4*A.v[i]*A.v[j])
                    jets.append({'order': 2, 'axes': [i, j], 'b': bb.encode(), 't': bt.encode(), 'u': bu.encode()})
            kinds[kind] = jets
            print('PASS actual normalized moving-packet', sign, kind, 'all0/1/2 jets', flush=True)
        blocks.append({'chirality': sign, 'original12_indices': indices, 'D': A.encode_polynomial(D),
            'g': g.encode(), 'jets': kinds,
            'physical_prefactor': 'raw packet -N; normalized B pref sign*sqrt2/N², C pref sign/N²; order m physical probe uses 2^(-m/2); all divide same source n'})
    result = {'scope': 'STRIKE_ORIGINAL_PACKET_MOVEMENT_AND_FULL_PHYSICAL_B_C_PROBE_JETS',
        'source_sha256': provenance['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [source_path, HERE/'operators.json.gz', HERE/'operators.json']},
        'variables': ['v1', 'v2', 'v3', 'x'], 'radical_basis': [1, 'sqrt15'],
        'packet_denominator': A.encode_polynomial(packet_den),
        'lapse_squared': str(s.expand(N*N)), 'physical_frequency': str(c*6*(1-s.I)),
        'source_relations': 'physical p=sqrt2*v; x=v.v; r=|physical p|; t=bprime/r; u=(bsecond-bprime/r)/r²',
        'wavepacket_identity_all_momenta': '(i-c h(v))*g(v)=G0 w, before any angular or Gram read; original raw f=-N g',
        'first_jet': 'G_i psi-G0 partial_i psi',
        'second_jet': 'G_ij psi-G_i partial_j psi-G_j partial_i psi+G0 partial_ij psi; original fixed output/current-probe convention',
        'fixed_normalization_and_P': True, 'blocks': blocks,
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    raw = (json.dumps(result, separators=(',', ':'))+'\n').encode()
    blob = gzip.compress(raw, mtime=0)
    (HERE/'vectors.json.gz').write_bytes(blob)
    receipt = {key: value for key, value in result.items() if key != 'blocks'}
    receipt.update({'compressed_sha256': hashlib.sha256(blob).hexdigest(),
        'uncompressed_sha256': hashlib.sha256(raw).hexdigest(), 'uncompressed_bytes': len(raw),
        'compressed_bytes': len(blob), 'block_chiralities': [row['chirality'] for row in blocks]})
    (HERE/'vectors.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print('PASS complete packet probe jets', result['elapsed_seconds'], 'compressed bytes', len(blob), flush=True)


if __name__ == '__main__':
    main()
