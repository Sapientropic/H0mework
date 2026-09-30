#!/usr/bin/env python3
"""Direct seven-matrix orbit minor and native volume audit."""
from pathlib import Path
import sympy as s
import hashlib
import json
import time
from independent_source_gauss_section_measure import RawSectionMeasure
from independent_source_gauge_slice_coordinates import pair, algebraic_determinant
from source_joint_form_hamiltonian import read_bound
from dynamic import HERE, ROOT, ROOT_ID


def run(expected, model=None):
    m = RawSectionMeasure() if model is None else model
    native = m.native
    G = s.Matrix(12, 12, lambda i, j: pair(native.fund[i], native.fund[j]))
    G36 = s.diag(G, G, G)
    fixed = tuple(j-67 for j in m.section.fixed)
    free = tuple(j for j in range(36) if j not in fixed)
    E = s.eye(36)[:, list(free)]
    G33 = E.T*G36*E
    G3 = s.Matrix(3, 3, lambda i, j: pair(m.K[i], m.K[j]))
    unit = s.sqrt(algebraic_determinant(G36)/(algebraic_determinant(G3)*algebraic_determinant(G33)))
    a = [s.Symbol('gauge_'+str(j), positive=True) if j in (1, 12)
         else s.Symbol('gauge_'+str(j), real=True) for j in range(36)]
    A = E*E.T*s.Matrix(a)
    matrices = [sum((A[12*i+j]*native.fund[j] for j in range(12)), s.zeros(7)) for i in range(3)]
    def coordinate(B, j):
        assert j in (0, 6)
        return s.re(B[0, 1]) if j == 0 else s.im(B[0, 0])
    minor = s.Matrix(3, 3, lambda i, j:
        coordinate(m.K[j]*matrices[fixed[i]//12]-matrices[fixed[i]//12]*m.K[j], fixed[i] % 12))
    det = s.factor(minor.det())
    source = m.section.source[67:, :]
    det0 = s.simplify(det.subs(dict(zip(a, source))))
    J0 = s.simplify(unit*abs(det0))
    density = s.simplify(unit*abs(det))
    relative = s.simplify(det/det0)
    flat_factor = s.sqrt(algebraic_determinant(native.R.T*native.R)*algebraic_determinant(G33))
    assert s.simplify(density*flat_factor-6144*s.sqrt(3)*a[1]**2*a[12]) == 0
    locals_ = {str(x): x for x in a}
    for key, value in [('source_jacobian', J0), ('source_jacobian_squared', J0**2),
                       ('relative_determinant', relative), ('native100_over_dz100', flat_factor),
                       ('coordinate_density', density*flat_factor)]:
        assert s.simplify(value-s.sympify(expected[key], locals=locals_)) == 0, key
    assert relative > 0 and density > 0
    print('PASS independent7x7 orbit minor, full33-variable native density and original coordinate pairing', flush=True)
    return {'original_minor': minor, 'native_density': density,
            'source_jacobian': J0, 'native100_over_dz100': flat_factor}


def audit():
    began = time.monotonic(); candidate = read_bound('source_gauss_history_domain')
    result = run(candidate['native_measure'])
    paths = [Path(__file__)]+[HERE/name for name in ('source_gauss_history_domain.json',
        'independent_source_gauss_section_measure.py', 'independent_source_gauge_slice_coordinates.py')]
    payload = {'root': ROOT_ID, 'scope': candidate['scope'],
        'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'algorithm': 'Direct original7x7 Lie commutators, original native pair Gram determinants and the original free-coordinate slice; no candidate Jacobian/relative inverse constructor imported.',
        'full33_variable_native_density_return': True,
        'positive_original_patch_admits_the_generated_Jacobian': True,
        'source_jacobian': str(result['source_jacobian']),
        'native100_over_dz100': str(result['native100_over_dz100']),
        'seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_gauss_history_domain.json').write_text(json.dumps(payload, separators=(',', ':'))+'\n')
    print('PASS independent source Gauss100 domain normalization', payload['seconds'], 'seconds', flush=True)


if __name__ == '__main__': audit()
