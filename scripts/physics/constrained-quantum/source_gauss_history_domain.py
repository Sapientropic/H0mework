#!/usr/bin/env python3
"""Native orbit/slice Gram Jacobian returned to the original Gauss measure."""
from pathlib import Path
import sympy as s
import hashlib
import json
import time
from source_joint_form_hamiltonian import read_bound
from source_live_differential_hamiltonian import clean
from source_gauge_slice_coordinates import algebraic_det
from dynamic import decode, HERE, ROOT, ROOT_ID


def run(graph=None):
    if graph is None:
        from source_scalar_gauss_reduction import SourceScalarGaussReduction
        graph = SourceScalarGaussReduction()
    saved = read_bound('source_gauge_slice_coordinates')
    read_bound('independent_source_gauge_slice_coordinates')
    gauge = graph.common.gauge
    G = decode(saved['source_orbit']['native_gram'])
    E = decode(saved['actual_section_equivalence']['coordinate_embedding'])
    F0 = decode(saved['actual_section_equivalence']['source_forward'])
    inverse = decode(saved['actual_section_equivalence']['source_inverse'])
    Gstab = clean(graph.stabilizer.T*gauge.gram*graph.stabilizer)
    Gslice = clean(E.T*G*E)
    domain_gram = s.diag(Gstab, Gslice)
    square = s.cancel(algebraic_det(clean(F0.T*G*F0))/algebraic_det(domain_gram))
    J0 = s.sqrt(square)
    assert J0 > 0
    a = [s.Symbol('gauge_'+str(j), positive=True) if j in (1, 12)
         else s.Symbol('gauge_'+str(j), real=True) for j in range(36)]
    A = E*E.T*s.Matrix(a)
    adjoint = [s.diag(*([gauge.ad(graph.stabilizer[:, k])]*3)) for k in range(3)]
    V = clean(s.Matrix.hstack(*(L*A for L in adjoint)))
    relative = clean(inverse*V.row_join(E))
    assert not relative[:3, 3:].todok()
    assert not clean(relative[3:, 3:]-s.eye(33)).todok()
    relative_det = s.factor(relative[:3, :3].det())
    assert relative_det > 0
    native100_factor = s.sqrt(algebraic_det(clean(graph.R.T*graph.R))*algebraic_det(Gslice))
    rho = 8*a[1]**2*a[12]
    assert s.simplify(J0*relative_det*native100_factor-768*s.sqrt(3)*rho) == 0
    # The Lean source basis and Python source basis parameterize the same
    # tangent map; both the domain Gram and orbit columns change together.
    S = s.diag(decode(saved['source_orbit']['python_from_spinpair']), s.eye(33))
    lean_forward = clean(F0*S)
    lean_domain = clean(S.T*domain_gram*S)
    lean_square = s.cancel(algebraic_det(clean(lean_forward.T*G*lean_forward))/algebraic_det(lean_domain))
    assert s.cancel(lean_square-square) == 0
    changed_relative = clean(S.inv()*relative*S)
    assert s.cancel(changed_relative[:3, :3].det()-relative_det) == 0
    scalar_det = algebraic_det(clean(graph.R.T*graph.R))
    print('PASS full33-variable native Jacobian, original rho3, scalar61 volume and actual spin-basis return', flush=True)
    result = {'source_jacobian': str(J0), 'source_jacobian_squared': str(square),
        'relative_determinant': str(relative_det), 'native100_over_dz100': str(native100_factor),
        'coordinate_density': str(s.expand(J0*relative_det*native100_factor)),
        'scalar61_Gram_determinant': str(scalar_det), 'coordinate33_Gram_determinant': str(algebraic_det(Gslice)),
        'positive_guard_from_original_patch': True,
        'scope': 'Entire original coordinate gauge section with a1,a12>0; full native Gram normalizations, not a frozen source-point Jacobian.'}
    print(result, flush=True)
    return result


def report(result, graph):
    dependencies = ('source_gauge_slice_coordinates', 'independent_source_gauge_slice_coordinates',
        'source_common_temporal_form', 'independent_source_common_temporal_form',
        'source_quantum_grade_structure', 'independent_source_quantum_grade_structure')
    for name in dependencies:
        if name == 'source_quantum_grade_structure':
            # This earlier receipt stores input bindings; its independent
            # receipt below also binds the original source declarations.
            data = json.loads((HERE/(name+'.json')).read_text())
            assert data['root'] == ROOT_ID
            for path, digest in data['input_sha256'].items():
                assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == digest, path
        else:
            read_bound(name)
    paths = [Path(__file__)]+[HERE/(name+'.json') for name in dependencies]
    paths += [HERE/name for name in ('FiniteCoreEvolution.lean', 'WeakCoreEvolution.lean',
        'GaussHistoryHilbert.lean', 'GaussHalfDensity.lean', 'NativeHistoryGrade.lean',
        'source_live_differential_hamiltonian.py', 'SourceQuantumGaugeSliceCoordinates.lean')]
    return {'root': ROOT_ID, 'scope': 'SOURCE_GAUSS100_DOMAIN_AND_RETARDED_WEAK_CORE_CONSTRUCTOR',
        'source_sha256': graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'native_measure': result,
        'actual_domain': 'The source coordinate slice Coframe x scalarSlice x coordinateSlice has generated dimension100. The admitted positive source patch carries its native orbit/slice Jacobian times v^(N+2), all504 CAR modes, and a dense compact smooth Fock core.',
        'half_density': 'The actual sqrt(nativeJacobian*v^(N+2)) is a surjective complex linear isometry to the unweighted native100 measure. At the same source its value is sqrt(81sqrt2/250), not1. The separate native100/dz100 factor1024sqrt3 is retained.',
        'analytic_constructor': {
            'input': 'A symmetric LinearPMap T on a dense invariant core; no propagator, resolvent, selfadjoint extension or spectral measure is supplied.',
            'construction': 'All finite subsets of that SAME core generate finite Hermitian compressions. One shared cofinal ultrafilter and Riesz give a contraction E(t) with E(0)=I and strong continuity. Finite sets containing x and Tx supply a uniform quadratic remainder and all-time strong derivative Eprime(t)x=-i E(t)Tx.',
            'weak_source_equation': 'For core x,Tx,y,Ty, <E(t)x,Ty>=<E(t)Tx,y>. The forward integral test has exactly the boundary -eta(0)<x,y>.',
            'native_blocks': 'Actual Number0..504 and Lambda6 grade0..56 projections form a complete orthogonal resolution on Gauss100. Finite pinching preserves contraction, initial identity and source core equations when T preserves/commutes with those original blocks.',
            'flat_reader': 'The same Gauss half-density transports the constructed history back to the flat native representation, preserving its original pairing.',
            'scope': 'Kernel-checked analytic/domain constructor. Its T remains explicit; a concrete Lean assembly of literal original H0 and the required operator/Heisenberg-domain continuation are downstream. No group law, limit norm preservation, completed nonlinear forcing or lifetime is asserted.'},
        'normalization_controls': {'source_jacobian_is_not_one': s.sympify(result['source_jacobian']) != 1,
            'native100_coordinate_factor_is_not_one': s.sympify(result['native100_over_dz100']) != 1},
        'controller': 'Fixed source/root/current and whole ledger unchanged; subordinate producer.'}


def main():
    from source_scalar_gauss_reduction import SourceScalarGaussReduction
    began = time.monotonic(); graph = SourceScalarGaussReduction()
    result = run(graph); payload = report(result, graph)
    payload['seconds'] = round(time.monotonic()-began, 3)
    (HERE/'source_gauss_history_domain.json').write_text(json.dumps(payload, separators=(',', ':'))+'\n')
    print('PASS source Gauss100 domain/weak-history binding', payload['seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
