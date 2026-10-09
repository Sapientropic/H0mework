#!/usr/bin/env python3
"""Original all-momentum B/C probe circuits in one polynomial normal form."""
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
from algebra import SphereAlgebra, SharedMatrix


def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    began = time.monotonic()
    source_path = FQ/'packet-noise/source_kernel.py'
    original = load(source_path, 'probe_moments_original_source')
    provenance, (N, omega, H0, Hj, CI, K, seed) = original.exact_source()
    circuit_path = FQ/'packet-gauge-probe-laplace/resolvent.json'
    circuit = json.loads(circuit_path.read_text())
    cosine_path = FQ/'packet-gauge-cosine/source.json'
    cosine = json.loads(cosine_path.read_text())
    V = original.decode(cosine['V'])
    assert circuit['source_sha256'] == provenance['source_sha256']
    c, zeta = N*s.sqrt(2), 6*(1-s.I)
    A = SphereAlgebra(s.QQ_I)
    radial = s.Symbol('x', real=True)
    atom_x = s.Symbol('x')
    imaginary = A.scalar(s.I)
    records = []
    for block in circuit['blocks']:
        sign = block['chirality']
        rows = block['original12_indices']
        h0 = original.clean(H0.extract(rows, rows)/c)
        hjs = [original.clean(H.extract(rows, rows)/N) for H in Hj]
        v = original.clean(V.extract(rows, rows)/N)
        h = A.add(A.from_matrix(h0), *(A.scale(A.v[j], A.from_matrix(hjs[j])) for j in range(3)))
        dj = list(map(A.from_matrix, hjs))
        vv = A.from_matrix(v)
        D = s.Poly(1, radial, domain=s.QQ_I)
        coefficients = {}
        for i, j, text in block['actual_inverse_polynomial_coefficients']:
            value = s.cancel(s.sympify(text, locals={'x': radial}))
            coefficients[i, j] = value
            D = s.lcm(D, s.Poly(s.fraction(value)[1], radial, domain=s.QQ_I)).monic()
        den = A.expression(D.as_expr().subs(radial, atom_x))
        hp = [A.identity()]
        for _ in range(3):
            hp.append(A.matmul(hp[-1], h))
        # The shared Sylvester numerator as an actual16x16 matrix. All entries
        # remain polynomials; no per-entry rational cancellation is performed.
        action = A.zero_matrix(16, 16)
        for (a, b), coefficient in coefficients.items():
            value = s.cancel(coefficient*D.as_expr())
            s.Poly(value, radial, domain=s.QQ_I)
            weight = A.expression(value.subs(radial, atom_x))
            for i in range(4):
                for j in range(4):
                    for k in range(4):
                        for l in range(4):
                            action[4*i+j][4*k+l] += A.mul(weight, A.mul(hp[a][i][k], hp[b][l][j]))
        action = [[A.normal(entry) for entry in row] for row in action]
        generator = A.zero_matrix(16, 16)
        for i in range(4):
            for j in range(4):
                generator[4*i+j][4*i+j] += A.scalar(zeta)
                for k in range(4):
                    generator[4*i+j][4*k+j] -= A.mul(imaginary, h[i][k])
                    generator[4*i+j][4*i+k] += A.mul(imaginary, h[k][j])
        expected = A.scale(den, A.identity(16))
        assert A.matmul(generator, action) == expected
        assert A.matmul(action, generator) == expected

        def R(M):
            vector = [[M.numerator[i][j]] for i in range(4) for j in range(4)]
            result = A.matmul(action, vector)
            return SharedMatrix(A, den, [[result[4*i+j][0] for j in range(4)] for i in range(4)], M.power+1)

        def wrap(M):
            return SharedMatrix(A, den, M)

        def commutator(M):
            return M.left(vv).plus(M.right(vv).scaled(-1))

        def sylvester(M):
            return M.scaled(zeta).plus(M.left(h).scaled(-s.I)).plus(M.right(h).scaled(s.I))

        def same(left, right):
            difference = left.plus(right.scaled(-1))
            assert A.is_zero(difference.numerator)

        B0, C0 = wrap(A.scale(2/zeta, h)), wrap(A.scale(2/zeta, vv))
        B1, C1 = [], []
        for i in range(3):
            rhs = wrap(A.scale(-1, dj[i])).plus(B0.right(dj[i]).scaled(s.I))
            Bi = R(rhs)
            same(sylvester(Bi), rhs)
            B1.append(Bi)
            crhs = C0.right(dj[i]).scaled(s.I).plus(commutator(Bi).scaled(s.I))
            Ci = R(crhs)
            same(sylvester(Ci), crhs)
            C1.append(Ci)
        B2, C2 = [], []
        for i in range(3):
            for j in range(i, 3):
                rhs = B1[i].right(dj[j]).plus(B1[j].right(dj[i])).scaled(s.I)
                Bij = R(rhs)
                same(sylvester(Bij), rhs)
                crhs = C1[i].right(dj[j]).plus(C1[j].right(dj[i])).plus(commutator(Bij)).scaled(s.I)
                Cij = R(crhs)
                same(sylvester(Cij), crhs)
                B2.append({'axes': [i, j], **Bij.encode()})
                C2.append({'axes': [i, j], **Cij.encode()})
        print('PASS exact source block', sign, 'all-p double Sylvester inverse and B/C probe jet equations', flush=True)
        records.append({'chirality': sign, 'original12_indices': rows,
            'D': A.encode_polynomial(den), 'D_factorization': str(s.factor(D.as_expr(), extension=s.I)),
            'h0': original.encode(h0), 'physical_Hj_over_N': list(map(original.encode, hjs)),
            'V_over_N': original.encode(v),
            'B0': B0.encode(), 'C0': C0.encode(), 'B1': list(map(lambda M: M.encode(), B1)),
            'C1': list(map(lambda M: M.encode(), C1)), 'B2': B2, 'C2': C2,
            'all_p_source_equations_exact_mod_sphere': True})
    result = {'scope': 'STRIKE_NATIVE_WHOLE_MOMENTUM_PROBE_JETS_WITH_SHARED_DENOMINATOR',
        'source_sha256': provenance['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [source_path, circuit_path, cosine_path]},
        'variables': ['v1', 'v2', 'v3', 'x'], 'source_relation': 'physical p=sqrt2*v; x=v.v; v3²=x-v1²-v2²',
        'actual_laplace_frequency': str(c*zeta), 'packet_Green_frequency_kept': 'i (E0 eta1)',
        'operator_normalization': 'Bphysical=(sign*sqrt2/N²)*Bnormalized; Cphysical=(sign/N²)*Cnormalized; order m physical probe derivative adds (sqrt2)^(-m)',
        'kernel_input_shift': 'normalized d=k/sqrt2; incoming v-d, fixed output v; no wavepacket change or separate momentum state',
        'blocks': records, 'elapsed_seconds': round(time.monotonic()-began, 3)}
    raw = (json.dumps(result, separators=(',', ':'))+'\n').encode()
    blob = gzip.compress(raw, mtime=0)
    (HERE/'operators.json.gz').write_bytes(blob)
    receipt = {key: value for key, value in result.items() if key != 'blocks'}
    receipt['blocks'] = [{key: value for key, value in row.items() if key not in ['B0', 'C0', 'B1', 'C1', 'B2', 'C2']}
                         for row in records]
    receipt.update({'compressed_sha256': hashlib.sha256(blob).hexdigest(),
        'uncompressed_sha256': hashlib.sha256(raw).hexdigest(), 'uncompressed_bytes': len(raw),
        'compressed_bytes': len(blob)})
    (HERE/'operators.json').write_text(json.dumps(receipt, indent=2)+'\n')
    print('PASS common-denominator source operators', result['elapsed_seconds'], 'bytes', len(blob), flush=True)


if __name__ == '__main__':
    main()
