#!/usr/bin/env python3
"""Independent polynomial audit of the source affine Hamiltonian forcing.

Rebuild the original289 operator and Legendre descriptor, then check the
reported whole-column identities directly. The candidate constructor and
its pivot/cokernel reduction are not imported. Source currents are unchanged.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import json
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from independent_retained_hamiltonian_reduction import (
    HERE, BASE, ROOT, ROOT_ID, P, K, LAM, DOMAIN, decode, check_bindings)
from independent_source_spatial_active_phase_splice import field_number

FIELD = DOMAIN.poly_ring(LAM)
Z = FIELD.gens[0]


@lru_cache(maxsize=None)
def scalar(value):
    value = s.sympify(value)
    if value == LAM: return Z
    if not value.free_symbols: return FIELD.convert(field_number(value), DOMAIN)
    if value.is_Add: return sum((scalar(v) for v in value.args), FIELD.zero)
    if value.is_Mul:
        answer = FIELD.one
        for v in value.args: answer *= scalar(v)
        return answer
    if value.is_Pow and value.exp.is_Integer: return scalar(value.base)**int(value.exp)
    raise ValueError(value)


def matrix(value):
    values = {}
    for (i, j), entry in s.SparseMatrix(value).todok().items():
        v = scalar(entry)
        if v: values.setdefault(i, {})[j] = v
    return DM(values, value.shape, FIELD).to_sparse()


def saved(row): return matrix(decode(row))
def eye(n): return DM.eye((n, n), FIELD).to_sparse()
def zero(value): assert value.is_zero_matrix


def dagger(value):
    return matrix(value.to_Matrix().conjugate().T.xreplace({s.conjugate(LAM): LAM}))


def coefficient(value, n):
    result = {}
    for i, row in value.rep.items():
        for j, entry in row.items():
            v = entry.get((n,), DOMAIN.zero)
            if v: result.setdefault(i, {})[j] = FIELD.convert(v, DOMAIN)
    return DM(result, value.shape, FIELD).to_sparse()


def degree(value):
    answer = -1
    for row in value.rep.values():
        for entry in row.values():
            answer = max(answer, max(power[0] for power in entry))
    return answer


def original_operator(active, momentum):
    entries = {}
    for i, j, powers, entry in active['Fourier_Jacobi_entries']:
        value = s.sympify(entry)*s.prod((s.I*k)**n for k, n in zip(momentum, powers[1:]))
        term = scalar(value)*Z**powers[0]
        entries.setdefault(i, {})[j] = entries.get(i, {}).get(j, FIELD.zero)+term
    return DM(entries, (289, 289), FIELD).to_sparse()


def original_fiber(sign, row, retained, catalog, active):
    old = next(r for r in catalog['source_momenta'] if any(s.sympify(v) != 0 for v in r['momentum']))
    k = tuple(sign*s.sympify(v) for v in old['momentum'])
    assert list(map(str, k)) == row['momentum']
    def cached(name):
        value = decode(old[name])
        return matrix(value if sign == 1 else value.conjugate())
    point = dict(zip(P, [LAM, *[s.I*v for v in k]]))
    opposite = dict(zip(P, [-LAM, *[-s.I*v for v in k]]))
    lift = matrix(decode(retained['retained_field_lift']).subs(point))
    read = matrix(decode(retained['retained_field_lift']).subs(opposite).T)
    contact = matrix(decode(retained['auxiliary_only_contact']).subs(point))
    original = original_operator(active, k)
    injection = matrix(s.SparseMatrix(289, 121, {(i, i): 1 for i in range(121)}))
    H = matrix(decode(retained['retained_operator']).subs(point))
    zero(original*lift-injection*H)
    zero(original*contact+injection*read-eye(289))
    zero(contact*original+lift*injection.transpose()-eye(289))
    zero(injection.transpose()*contact)
    C0, C1, C2 = (coefficient(H, n) for n in range(3))
    zero(H-C0-C1.scalarmul(Z)-C2.scalarmul(Z**2))
    z121 = DM.zeros((121, 121), FIELD)
    omega242 = DM.vstack(DM.hstack(C1, C2), DM.hstack(-C2, z121))
    energy242 = DM.vstack(DM.hstack(-C0, z121), DM.hstack(z121, -C2))
    at = dict(zip(K, k))
    zero(omega242-matrix(decode(retained['presymplectic_form']).subs(at)))
    zero(energy242-matrix(decode(retained['Legendre_energy_hessian']).subs(at)))
    S, R = cached('velocity_quotient_section'), cached('velocity_quotient_retraction')
    zero(R*S-eye(172))
    omega, energy = dagger(S)*omega242*S, dagger(S)*energy242*S
    D = omega.scalarmul(Z)-energy
    B = dagger(S)*DM.vstack(read, DM.zeros((121, 289), FIELD))
    Uward = decode(retained['normal_coordinate_change'])[:, 112:121]
    raw_ward = decode(retained['retained_field_lift'])*Uward
    W = matrix(raw_ward.subs(opposite).T)
    zero(W*original)
    assert len(W.rref()[1]) == 9
    zero(W-saved(row['original_Ward_map']))
    zero(B-saved(row['original_descriptor_source']))
    C, Q = cached('consistent_initial_data_embedding'), cached('quotient_map')
    Qs, A = cached('quotient_section'), cached('Hamiltonian_generator')
    U = C*cached('free_derivative_directions')
    zero(omega*U)
    Elift = saved(row['descriptor_dynamic_lift'])
    Pbase, Ptotal = saved(row['affine_particular']), saved(row['descriptor_total_particular'])
    forcing, consistent = saved(row['physical_forcing']), saved(row['consistent_forcing'])
    zero(forcing-Q*consistent)
    # Recover the repair coordinates using a Gram left inverse, independently
    # of the candidate's pivot solve. Every repair lies in the original free
    # derivative image, not in an added source-dependent gauge carrier.
    leftU = (dagger(U)*U).convert_to(DOMAIN).inv().convert_to(FIELD)*dagger(U)
    correction = Elift-C*Qs
    affine_correction = Ptotal-Pbase
    zero(U*leftU*correction-correction)
    zero(U*leftU*affine_correction-affine_correction)
    assert not correction.is_zero_matrix and not affine_correction.is_zero_matrix
    assert not (omega*C*Qs*A-energy*C*Qs).is_zero_matrix
    zero(omega*Elift*A-energy*Elift)
    zero(Q*Qs-eye(126)); zero(Q*cached('free_derivative_directions'))
    zero(omega*Elift*forcing+D*Ptotal-B-saved(row['descriptor_Ward_factor'])*W)
    first = matrix(s.SparseMatrix(121, 242, {(i, i): 1 for i in range(121)}))
    Y, Yp = first*S*Elift, first*S*Ptotal
    zero(Y-saved(row['retained_field_lift']))
    zero(Yp-saved(row['retained_field_particular']))
    euler_reader = DM.hstack(eye(121), -eye(121).scalarmul(Z))*dagger(R)
    L = euler_reader*omega*Elift
    zero(L-saved(row['retained_Euler_physical_factor']))
    zero(H*Y-L*(eye(126).scalarmul(Z)-A))
    euler_residual = H*Yp+L*forcing-read
    zero(euler_residual-saved(row['retained_Euler_Ward_factor'])*W)
    zero(euler_residual-euler_reader*saved(row['descriptor_Ward_factor'])*W)
    X, Pc = saved(row['full289_field_lift']), saved(row['full289_field_particular'])
    zero(X-lift*Y); zero(Pc-contact-lift*Yp)
    Lfull = injection*L
    zero(original*X-Lfull*(eye(126).scalarmul(Z)-A))
    full_residual = original*Pc+Lfull*forcing-eye(289)
    zero(full_residual-injection*saved(row['retained_Euler_Ward_factor'])*W)
    # A source produced by the original action is Ward compatible at every z.
    # The bad formulas are tested on that actual compatibility kernel, not on
    # an arbitrary inadmissible current or on a static CAR state.
    zero(full_residual*original)
    duplicated_contact_defect = original*contact*original
    assert not duplicated_contact_defect.is_zero_matrix
    omitted_source_derivatives = Lfull*(forcing-coefficient(forcing, 0))*original
    assert not omitted_source_derivatives.is_zero_matrix
    omitted_affine = original*(Pc-contact)*original
    assert not omitted_affine.is_zero_matrix
    assert degree(forcing) == row['forcing_polynomial_degree'] == 3
    assert degree(Ptotal) == row['total_particular_polynomial_degree'] == 2
    assert [r['carrier_dimension'] for r in row['consistency_chain']] == [172, 156, 147, 138]
    assert [r['new_constraints'] for r in row['consistency_chain']] == [16, 9, 9, 0]
    return dict(momentum=list(map(str, k)), physical_dimension=A.shape[0],
        all_original289_polynomial_equations_modulo_Ward=True,
        original9_Ward_rows_and_actual_source_unchanged=True,
        original_Legendre_descriptor_rederived_from_action=True,
        dynamic_section_and_affine_repair_use_original_free_derivatives=True,
        original_quotient_section_without_repair_fails=True,
        physical_forcing_degree=degree(forcing), affine_particular_degree=degree(Ptotal),
        missing_source_derivatives_changes_compatible_forcing=True,
        missing_affine_particular_changes_compatible_forcing=True,
        duplicated_auxiliary_contact_changes_compatible_forcing=True), {
            'W': W, 'B': B, 'Elift': Elift, 'P': Ptotal, 'F': forcing, 'X': X, 'Pc': Pc}


def main():
    began = time.monotonic()
    names = ['source_forced_hamiltonian_reduction.json', 'retained_matter_action.json',
             'retained_hamiltonian_reduction.json', 'independent_retained_matter_action.json',
             'independent_retained_hamiltonian_reduction.json']
    records = [json.loads((HERE/name).read_text()) for name in names]
    checks = sum(check_bindings(record) for record in records)
    candidate, retained, catalog, *_ = records
    assert all(r['root'] == ROOT_ID and r['source_sha256'] == candidate['source_sha256'] for r in records)
    active_path = BASE/'active-gauge/receipt.json'
    active = json.loads(active_path.read_text()); checks += check_bindings(active)
    reports, fibers = [], []
    for sign, row in zip((1, -1), candidate['source_momenta'], strict=True):
        report, fiber = original_fiber(sign, row, retained, catalog, active)
        reports.append(report); fibers.append(fiber)
        print('PASS original289 polynomial forced action, native descriptor and unaltered Ward source', sign, flush=True)
    for name in fibers[0]:
        conjugate = fibers[0][name].to_Matrix().conjugate().xreplace({s.conjugate(LAM): LAM})
        zero(fibers[1][name]-matrix(conjugate))
    print('PASS both Fourier partners and nonzero compatible-source derivative/contact omission controls', flush=True)
    paths = [HERE/name for name in [*names, 'source_forced_hamiltonian_reduction.py',
        'independent_source_forced_hamiltonian_reduction.py',
        'independent_retained_hamiltonian_reduction.py',
        'independent_source_spatial_active_phase_splice.py']]+[active_path]
    result = {'root': ROOT_ID, 'source_sha256': candidate['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'verdict': 'CERTIFIED_ORIGINAL_AFFINE_HAMILTONIAN_FORCING_AND_FULL289_POLYNOMIAL_RECONSTRUCTION',
        'scope': candidate['scope'], 'checked_input_bindings': checks,
        'candidate_constructor_imported': False, 'source_fibers': reports,
        'independent_algorithm': 'Rebuild original289 Fourier action; differentiate its retained polynomial to recover the172 descriptor; verify whole-column rational identities and recover repairs using an independent Gram left inverse.',
        'affine_chain_review': 'At each carrier C, original left-null consistency is L E C x=-L(B-(z Omega-E)P)j. The generated particular adds C times its solution, and the carrier restricts to ker(L E C). The candidate retains each unsolved row as a factor of the original Ward source. Final all-column identities, rather than source samples, are independently checked here.',
        'time_domain_contract': 'For smooth currents with W(partial_t)j=0, (partial_t-A)xi=F(partial_t)j and field=X xi+Pfull(partial_t)j solve all original289 rows. Ptotal has degree2 and F degree3. Distributional currents retain their derivatives and initial deltas; no ordinary zero-initial interpretation is substituted.',
        'scope_boundary': 'The two signed nonzero source momenta. This producer supplies compatible classical forcing, not an interacting quantum spectrum or a proton label.',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'independent_source_forced_hamiltonian_reduction.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS independent source affine Hamiltonian forcing', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
