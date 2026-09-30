"""Focused source momentum audit: full tangent inverse, implicit constraints, bit CAR."""
from pathlib import Path
import hashlib
import json
import time
import sympy as s
from source_full_gauss_section import SourceFullGaussSection
from source_live_differential_hamiltonian import clean
from source_gauss_quantum_current import apply_superposition, weighted_sum
from source_joint_form_hamiltonian import read_bound
from dynamic import decode, HERE, ROOT, ROOT_ID
from independent_source_native_chi_euler_forcing import D, field, mask, current, columns


def run(source=None):
    m = SourceFullGaussSection() if source is None else source
    saved = read_bound('source_full_gauss_section')
    read_bound('independent_source_full_gauss_section')
    read_bound('source_gauss_history_domain')
    E, C, R = m.embedding[6:, 6:], m.constraint[:, 6:], m.retraction[6:, 6:]
    L = [A[6:, 6:] for A in m.L]
    points = (m.z0, decode(saved['generic_configuration_density']['actual_nonzero_point']))
    physical = read_bound('source_native_chi_euler_forcing')['source']
    word = tuple(physical['values'][0][0]); unit = {word:s.S.One}; bitunit = {mask(word):D.one}
    gradient = decode(physical['gradient100'][0][1])[6:, :]
    matter = [apply_superposition(A, unit) for A in m.R]
    results = []
    for case, point in enumerate(points):
        base = clean(m.offset+m.embedding*point)[6:, :]
        V = clean(s.Matrix.hstack(*(A*base for A in L)))
        F = V.row_join(E)
        I = clean(F.inv(method='DM'))
        assert not clean(F*I-s.eye(106)).todok()
        assert not clean(I*F-s.eye(106)).todok()
        alpha, free = (C*V).gauss_jordan_solve(C)
        assert free.rows == 0
        alpha = clean(alpha); beta = clean(R*(s.eye(106)-V*alpha))
        implicit = alpha.col_join(beta)
        assert not clean(I-implicit).todok()
        if case == 0:
            old = decode(saved['source_inverse_first_jet'])
            assert not clean(I[:12, :]-old[:12, 6:]).todok()
            assert not clean(I[12:, :]-old[18:, 6:]).todok()
        nonzero_jets = 0
        CVinv = clean((C*V).inv(method='DM'))
        for k in range(94):
            dV = clean(s.Matrix.hstack(*(A*E[:, k] for A in L)))
            dF = dV.row_join(s.zeros(106, 94))
            dI = clean(-I*dF*I)
            da = clean(-CVinv*(C*dV)*alpha)
            db = clean(-R*(dV*alpha+V*da))
            assert not clean(dI-da.col_join(db)).todok(), (case,k)
            nonzero_jets += bool(dI.todok())
        images=[]; connection_active=0
        for j in range(106):
            direct = weighted_sum([(-s.I*(I[12:, j].T*gradient)[0],unit)]+
                [(-s.I*I[a,j], image) for a,image in enumerate(matter) if I[a,j]])
            rho = clean(sum((alpha[a,j]*m.R[a] for a in range(12) if alpha[a,j]), s.zeros(504)))
            bits = current(columns(rho), bitunit)
            bitout = {w:field(-s.I)*c for w,c in bits.items()}
            c = field(-s.I*(beta[:,j].T*gradient)[0])
            if c: bitout[mask(word)] = bitout.get(mask(word),D.zero)+c
            bitout={w:c for w,c in bitout.items() if c}
            assert {mask(w):field(c) for w,c in direct.items()} == bitout, (case,j)
            connection_active += bool(bits)
            images.append(direct)
        assert connection_active and nonzero_jets
        for a in range(12):
            back=weighted_sum((V[j,a],images[j]) for j in range(106) if V[j,a])
            expected=weighted_sum([(-s.I,matter[a])])
            assert weighted_sum([(1,back),(-1,expected)]) == {}, (case,a)
        for k in range(94):
            back=weighted_sum((E[j,k],images[j]) for j in range(106) if E[j,k])
            assert weighted_sum([(1,back),(s.I*gradient[k],unit)]) == {}, (case,k)
        result={'point':case,'all106_momenta_return':True,'all94_inverse_derivatives':True,
            'all12_orbit_and94_slice_readers':True,'nonzero_inverse_jets':nonzero_jets,
            'nonzero_native_connections':connection_active}
        results.append(result); print('PASS native core momentum',result,flush=True)
    return results


def main():
    began=time.monotonic(); m=SourceFullGaussSection(); result=run(m)
    deps=('source_full_gauss_section','independent_source_full_gauss_section',
        'source_gauss_history_domain','independent_source_gauss_history_domain',
        'source_native_chi_euler_forcing','independent_source_native_chi_euler_forcing')
    for name in deps: read_bound(name)
    paths=[Path(__file__)]+[HERE/(name+'.json') for name in deps]
    paths += [HERE/name for name in ('GaussLiveMomentum.lean','GaussNativeMatter.lean',
        'GaussCoreDifferential.lean','GaussCoreHilbert.lean','source_full_gauss_section.py',
        'source_gauss_quantum_current.py','independent_source_native_chi_euler_forcing.py')]
    report={'root':ROOT_ID,'scope':'ORIGINAL_NATIVE106_MOMENTUM_ON_ACTUAL_DENSE_GAUSS100_CORE',
        'source_sha256':m.native.graph.common.source_hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'kernel_contract': 'Every point of the original Gauss100 physical chart generates the invertible native12 plus scalar61/gauge33 tangent split, its smooth inverse, and dI=-I(dD)I. The original full504 matter representation and this inverse generate the covariant momentum on all smooth compact tests. The test carrier is linearly equivalent to the actual weighted dense Fock core, giving a concrete core-preserving LinearPMap.',
        'exact_pairing': 'The same Gauss100 numberMeasure and its generated Jacobian are used; no alternate source occurrence or root-normalized measure is installed.',
        'algorithms': 'Direct106 inverse versus original12 implicit constraint solve; all94 derivatives; tuple CAR versus independent integer-bit CAR; all12 orbit and94 slice readbacks.',
        'point_audits':result,
        'operator_scope': 'Original native first-order momenta. Their products do not silently replace the previously proved form correction or the coframe/contact components of H0. The complete H0 assembly and two-leg retarded operator-domain continuation remain downstream.',
        'controller':'Original root/current and whole ledger unchanged; subordinate producer.',
        'seconds':round(time.monotonic()-began,3)}
    (HERE/'source_native_core_momentum.json').write_text(json.dumps(report,separators=(',',':'))+'\n')
    print('PASS source native Hilbert-core momentum',report['seconds'],'seconds',flush=True)


if __name__ == '__main__': main()
