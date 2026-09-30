#!/usr/bin/env python3
"""The four original quantum energies in one canonical Weyl representation.

The actual residual3 section is used before taking symbol derivatives. The
result quantizes back to the same source form, including its original Y;
the time-coframe variables remain the four parameters of that form.
"""
from __future__ import annotations

import hashlib
import json
import time
from types import SimpleNamespace
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_scalar_weyl_symbol import SourceScalarWeylSymbol, quadratic_weyl_action
from source_common_temporal_form import SourceCommonTemporalForm
from source_reducing_coframe_metric import complete_coefficients
from source_temporal_coframe_pairing import generic_pairing
from source_joint_form_hamiltonian import read_bound
from source_full_quantum_adjoint import split_matter
from source_coframe_live_ordering import full, verify_jet_action
from source_coframe_legendre import rational
from source_lorentz_contact import equal, encode
from source_gauss_quantum_current import weighted_sum, apply_superposition, encode_state
from source_quantum_temporal_symbol import N


def zero(x): assert s.cancel(s.expand(x)) == 0
def state_equal(a, b): assert weighted_sum([(1, a), (-1, b)]) == {}


def gauge_coefficients(model, scalar):
    graph = scalar['section_primitives']; free, piv = graph['free'], graph['pivots']
    U, T, dM, dT = (graph[name] for name in ('U', 'T', 'dM', 'dT'))
    source = model.native.joint.gauge
    raw = source.coefficients(scalar['e'])
    at = dict(zip(source.coordinates, scalar['point103'][67:, :]))
    def evaluate(value):
        return rational(value.subs(at)) if isinstance(value, s.MatrixBase) else s.cancel(value.subs(at))
    original = {name: evaluate(value) for name, value in raw.items()}
    W, C = original['weight'], original['momentum_shift']
    zero(original['derivative_ordering_constant'])
    E, Bp = s.eye(97)[61:, list(free)], s.eye(97)[61:, list(piv)]
    a = rational(E-Bp*T.T)
    equal(a, graph['Z'][:, 61:].T)
    c = s.zeros(36, 9).row_join(rational(-Bp*U.T))
    dU = [rational(-U*dm*U) for dm in dM]
    da = [rational(-Bp*dt.T) for dt in dT]
    dc = [s.zeros(36, 9).row_join(rational(-Bp*du.T)) for du in dU]
    dC = [evaluate(raw['momentum_shift'].diff(source.coordinates[u-61])) if u >= 61 else s.zeros(36, 1)
          for u in free]
    trace = rational(sum((dt[j, :] for j, dt in enumerate(dT)), s.zeros(1, 3)))
    div_a = rational(-Bp*trace.T)
    principal = rational(a.T*W*a/2)
    divergence = rational((a.T*W*div_a+sum((da[j].T*W*a[:, j] for j in range(94)), s.zeros(94, 1)))/2)
    active_M = [j for j, dm in enumerate(dM) if dm.todok()]
    ddiv = []
    for i in range(94):
        dt = rational(-sum((dT[i][j, :]*dM[j]*U for j in active_M), s.zeros(1, 3))-trace*dM[i]*U)
        ddiv.append(rational(-Bp*dt.T))
    J = [s.SparseMatrix(94, 94, lambda j, i: dT[i][j, alpha]) for alpha in range(3)]
    small_weight = rational(Bp.T*W*Bp)
    crossed = sum(weight*s.trace(J[alpha]*J[beta]) for (alpha, beta), weight in small_weight.todok().items())
    divdiv = s.cancel(((div_a.T*W*div_a)[0]+crossed+
        2*sum((a[:, i].T*W*ddiv[i])[0] for i in range(94)))/2)
    momentum_current = rational(a.T*W*c)
    momentum_identity = rational(-a.T*W*C)
    div_current = rational(c.T*W*div_a+sum((dc[i].T*W*a[:, i] for i in range(94)), s.zeros(12, 1)))
    div_identity = s.cancel(-(div_a.T*W*C)[0]-sum((a[:, i].T*W*dC[i])[0] for i in range(94)))
    ell, logH = scalar['ell'], scalar['log_Hessian']
    density = s.cancel((ell.T*principal*ell)[0]+(divergence.T*ell)[0]+
        sum(v*logH[i, j] for (i, j), v in principal.todok().items()))
    return {'principal': principal, 'div_principal': divergence, 'divdiv_principal': divdiv,
        'momentum_current': momentum_current, 'momentum_identity': momentum_identity,
        'div_momentum_current': div_current, 'div_momentum_identity': div_identity,
        'square_current': rational(c.T*W*c/2), 'linear_current': rational(-c.T*W*C),
        'classical_zero': s.cancel((C.T*W*C)[0]/2+original['magnetic_potential']),
        'half_density_potential': density, 'weyl_correction': divdiv/4,
        'a': a, 'current': c, 'd_a': da, 'div_a': div_a, 'original': original}


def coframe_action(model, data, pairing, values, gradients, Hessians):
    cf = model.native.joint.coframe; q = tuple(model.section.b0[:6, 0])
    family = model.temporal.family
    sub = {**dict(zip(cf.q, q)), **dict(zip(family.y, data['e'][:, 0]))}
    def at(M): return rational(M.subs(sub)) if isinstance(M, s.MatrixBase) else s.cancel(M.subs(sub))
    divdiv = s.cancel(sum(s.diff(pairing['K'][i, j], cf.q[i], cf.q[j]) for i in range(6) for j in range(6)))
    zero(divdiv+family.y[0]/pairing['volume'])
    terms = []
    for word in set(values)|set(gradients)|set(Hessians):
        value = values.get(word, 0); g = gradients.get(word, s.zeros(100, 1))[:6, :]
        H = Hessians.get(word, s.zeros(100))[:6, :6]
        constant = verify_jet_action(data['coframe'], word, value, s.zeros(6, 1), s.zeros(6))
        terms.append((1, {tuple(w): s.sympify(v) for w, v in constant['raw_nested_square']}))
        correction = at(pairing['potential'].subs(pairing['m'], len(word))+divdiv/4)
        quadratic = -sum(v*H[i, j] for (i, j), v in data['coframe']['K'].todok().items())
        quadratic -= (at(pairing['divergence']).T*g)[0]+at(divdiv)*value/4
        terms.append((quadratic+correction*value, {word: 1}))
        for j, M in enumerate(pairing['Mh']):
            terms.append((-s.I*g[j], apply_superposition(full(at(M)), {word: 1})))
    return weighted_sum(terms)


def encode_quadratic(d):
    return {name: encode(d[name]) if isinstance(d[name], s.MatrixBase) else str(d[name]) for name in (
        'principal', 'div_principal', 'divdiv_principal', 'momentum_current', 'momentum_identity',
        'div_momentum_current', 'div_momentum_identity', 'square_current', 'linear_current',
        'classical_zero', 'half_density_potential', 'weyl_correction')}


def main():
    started = time.monotonic()
    deps = ('source_scalar_weyl_symbol', 'source_coframe_weyl_symbol',
            'independent_source_coframe_weyl_symbol', 'source_common_temporal_form')
    saved = {name: read_bound(name) for name in deps}
    model = SourceScalarWeylSymbol(); common = SourceCommonTemporalForm()
    row = saved['source_scalar_weyl_symbol']['actual_consumer']
    from dynamic import decode
    q = tuple(map(s.sympify, row['q'])); x, A = decode(row['x61']), decode(row['A36'])
    timepoint = tuple(map(s.sympify, row['time_column']))
    scalar = model.coefficients(timepoint, q, x, A)
    gauge = gauge_coefficients(model, scalar)
    assert gauge['weyl_correction'] and gauge['half_density_potential']
    for d in (scalar, gauge):
        equal(d['principal'].T, d['principal']); equal(d['principal'].conjugate(), d['principal'])
        equal(d['square_current'].T, d['square_current']); equal(d['square_current'].conjugate(), d['square_current'])
        equal(d['momentum_current'].conjugate(), d['momentum_current'])
        equal(d['momentum_identity'].conjugate(), d['momentum_identity'])
    print('PASS original gauge canonical Weyl coefficients with complete section derivatives and density', flush=True)
    data = common.coefficients(timepoint, q, x, A)
    equal(data['scalar']['momentum_vectors'], scalar['raw']['momentum_vectors'])
    metric = complete_coefficients(SimpleNamespace(section=model.section))
    pairing = generic_pairing(SimpleNamespace(coframe=model.native.joint.coframe, metric=metric), model.temporal.family)
    word = (144, 396); values = {word: s.S.One}
    g = decode(row['gradient100']); H = decode(row['Hessian100'])
    gradients, Hessians = {word: g}, {word: H}
    ell = s.zeros(100, 1); ell[6:, :] = scalar['ell']
    logH = s.zeros(100); logH[6:, 6:] = scalar['log_Hessian']
    for j in (0, 2, 5): ell[j] = s.Rational(len(word)+2, 2)/q[j]; logH[j, j] = -ell[j]/q[j]
    jet = model.section.extend_jet(values, {word: rational(g-ell)},
        {word: rational(H-ell*g.T-g*ell.T+ell*ell.T-logH)})
    gauss = model.section.verify_Gauss_jet(jet)
    original = common.action(data, jet)
    scalar_image = model.weyl_action(scalar, values, gradients, Hessians)
    gauge_image = quadratic_weyl_action(gauge, values, gradients, Hessians, model.current_word, model.current)
    M0, Y = split_matter(data)
    pieces = {'scalar_form': scalar_image, 'gauge': gauge_image,
        'coframe': coframe_action(model, data, pairing, values, gradients, Hessians),
        'matter_noY': apply_superposition(M0, values)}
    for name, image in pieces.items(): state_equal(image, original['pieces'][name])
    H0 = weighted_sum((1, image) for image in pieces.values())
    Yimage = apply_superposition(Y, values)
    Himage = weighted_sum([(1, H0), (1, Yimage)])
    sharp = weighted_sum([(1, H0), (1, apply_superposition(Y.H, values))])
    state_equal(Himage, original['H']); state_equal(sharp, original['Hsharp'])
    assert all(pieces.values()) and Yimage
    frozen = quadratic_weyl_action(gauge, values, gradients, Hessians, model.current_word, model.current,
                                  omit_weyl_correction=True)
    defect = weighted_sum([(1, gauge_image), (-1, frozen)])
    state_equal(defect, {word: gauge['weyl_correction']}); assert defect
    print('PASS complete four-energy full504 Weyl readback, original Y and all actual Gauss rows', flush=True)
    files = [HERE/(name+'.json') for name in deps]+[HERE/name for name in (
        'source_common_weyl_symbol.py', 'source_scalar_weyl_symbol.py', 'source_coframe_weyl_symbol.py',
        'source_common_temporal_form.py', 'source_gauge_quantum_energy.py', 'source_quantum_gauss_section.py',
        'source_full_quantum_adjoint.py', 'source_gauss_section_measure.py')]
    result = {'root': ROOT_ID, 'scope': 'COMPLETE_FOUR_ENERGY_SOURCE_CANONICAL_WEYL_SYMBOL_ON_ACTUAL_GAUSS_SLICE',
        'source_sha256': model.graph.common.source_hashes,
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'canonical_chart': 'Original z=(q6,x61,Afree33) with canonical momenta p100 and all504 CAR modes.',
        'symbol_equation': 'OpW(sigma0+Y)=U H(n,b) U^-1, U=sqrt(rho3)*v^(1+Number/2). Sigma0 is Hermitian; the original multiplication Y is unchanged and sigma_sharp=sigma0+Ydagger.',
        'gauge_construction': 'Ahat=Z_g^T, Chat=-alpha_g^T Qs-C; P=Ahat^T W Ahat/2, momentum current=Ahat^T W Chat. Both differentiated original orbit inverse and all rho3 half-density terms are retained.',
        'gauge_symbol_coefficients': encode_quadratic(gauge),
        'original_four_time_parameters_remain_parameters': True,
        'actual_consumer': {'q': list(map(str, q)), 'time': list(map(str, timepoint)),
            'x61': encode(x), 'A36': encode(A), 'input_CAR': list(word), 'gradient100': encode(g), 'Hessian100': encode(H),
            'Gauss': gauss, 'four_Weyl_component_images': {k: encode_state(v) for k, v in pieces.items()},
            'four_original_component_images': {k: encode_state(v) for k, v in original['pieces'].items()},
            'Weyl_H0': encode_state(H0), 'Weyl_H': encode_state(Himage), 'original_H': encode_state(original['H']),
            'original_Y': encode_state(Yimage), 'Weyl_Hsharp': encode_state(sharp),
            'omitted_gauge_divdiv_symbol_defect': encode_state(defect)},
        'quantum_ordering_or_source_occurrence_replaced': False,
        'time_secondary_quantum_solution_or_full_spectrum_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_common_weyl_symbol.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS source common canonical Weyl symbol', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
