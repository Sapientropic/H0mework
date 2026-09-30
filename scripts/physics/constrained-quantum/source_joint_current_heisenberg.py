#!/usr/bin/env python3
"""Exact Heisenberg derivative of all 100 original current ports of the common
local Hamiltonian: Jdot_j := i[H,J_j] for J_j = OpW(Q(M_j(z))).

Because sigma is quadratic in p with central d2_p sigma = 2K and the current
symbol Q(M_j(z)) is p-independent, the matrix-valued Moyal bracket terminates:

  Jdot_j(p) = sum_l p_l Q(U_jl) + Q(W_j)
            + sum_k N(M_k, D_kj)
            + i sum_(c,A,B) c (N([A,M_j],B) + N(A,[B,M_j]))
  U_jl = 2 sum_k K_lk D_kj + i [M_l, M_j]
  W_j  = sum_k l_k D_kj + (1/2) sum_k (M_k D_kj + D_kj M_k) + i [M_0, M_j]
  D_kj = d/dz_k M_j at z0

and OpW(sum_l p_l Q(U_jl)) acting on the plane wave picks up the ordering term
-(i/2) Q(sum_l d_l U_jl) with

  sum_l d_l U_jl = 2 sum_k divergence_k D_kj
                 + i sum_l ([D_ll, M_j] + [M_l, D_lj]).

The producer checks the symbol against the ORIGINAL differential H on the
first-order Taylor current J1_j(z) = M_j(z0) + sum_k D_kj (z-z0)_k, applied to
plane-wave CAR words (V1), runs reverse controls (V2), verifies the
source-real CAR charge generators commute with every nonzero Jacobian entry
(V3), and reports Jacobian sparsity/divergence facts (V4).  The full nonzero
Jacobian is stored in source_joint_current_heisenberg.jacobian.json.gz, bound
into this receipt by sha256."""
import gzip
import hashlib
import json
import multiprocessing as mp
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

import sympy as s

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ROOT = BASE.parents[2]
sys.path.insert(0, str(BASE / 'nonlinear-contact'))
os.chdir(HERE)

from dynamic import decode
from source_joint_ccr_car_ports import SourceJointCCRCarPorts, same, simplified
import source_lorentz_contact
from source_joint_form_hamiltonian import ROOT_ID, read_bound
from source_scalar_weyl_symbol import quadratic_weyl_action
from source_common_weyl_symbol import coframe_action
from source_lorentz_contact import encode
from source_coframe_live_ordering import full
from source_gauss_quantum_current import (apply_superposition, encode_state,
    normal_pair, weighted_sum)


def strong_equal(left, right):
    """The imported `equal` only expands; symbolic Jacobian configurations need
    cancel/factor to recognize the same zero residual.  Same assertion."""
    residual = s.SparseMatrix(left - right).applyfunc(s.expand)
    if residual.todok():
        residual = s.SparseMatrix(left - right).applyfunc(
            lambda v: s.factor(s.cancel(v)))
    assert not residual.todok(), list(residual.todok().items())[:3]


def patch_symbolic_equal():
    original = source_lorentz_contact.equal
    for module in list(sys.modules.values()):
        if getattr(module, 'equal', None) is original:
            module.equal = strong_equal


def decode_entries(entries):
    return s.SparseMatrix(504, 504, {(int(i), int(j)): s.sympify(v)
                                     for i, j, v in entries})


def commutator(A, B):
    return A*B - B*A


def slim_columns(matrix_pair, modes):
    """Sparse commutator [A,M] restricted to the listed columns."""
    A, M = matrix_pair
    data = {}
    for m in modes:
        column = s.SparseMatrix(A*M[:, m] - M*A[:, m])
        data.update({(i, m): v for (i, _), v in column.todok().items()})
    return s.SparseMatrix(504, 504, data)


_MODEL = None
_PHASE = None


def jacobian_column(k):
    _, gradients = _MODEL.force_and_velocity_gradient(k, _PHASE)
    column = {}
    for j, gradient in enumerate(gradients):
        entries = encode(gradient.one_body)['entries']
        if entries:
            column[j] = entries
    return k, column


def main():
    began = time.monotonic()
    patch_symbolic_equal()
    deps = ('source_joint_ccr_car_ports', 'source_joint_charge_conservation')
    saved = {name: read_bound(name) for name in deps}
    ports = saved['source_joint_ccr_car_ports']
    charge = saved['source_joint_charge_conservation']
    model = SourceJointCCRCarPorts()
    z0 = tuple(map(s.sympify, ports['configuration100']))
    p0 = tuple(map(s.sympify, ports['configuration_momenta100']))
    phase = z0 + p0
    d = model.coefficients(z0)
    K, ell, currents, zero = (d['principal'], d['linear_identity'],
                              d['linear_current'], d['zero'])
    currents = [s.SparseMatrix(M) for M in currents]
    M0 = s.SparseMatrix(zero.one_body)
    pairs = list(zero.pairs)
    coframe_W_count = len(d['coframe']['W'].todok())
    prefix_pair_count = (1 + len(d['scalar']['square_current'].todok())
                         + len(d['gauge']['square_current'].todok()))
    assert len(pairs) == prefix_pair_count + coframe_W_count == 119
    print('PASS model coefficients and W-tail pair tagging', flush=True)

    global _MODEL, _PHASE
    _MODEL, _PHASE = model, phase
    jacobian_seconds = time.monotonic()
    jac_columns = {}
    jac_cache = os.environ.get('JH_JACOBIAN_GZ')
    if jac_cache:
        jac_columns = {int(k): {int(j): e for j, e in column.items()}
                       for k, column in json.load(
                           gzip.open(jac_cache))['columns'].items()}
        jac_mode = {'mode': 'cache',
                    'cache_sha256': hashlib.sha256(
                        Path(jac_cache).read_bytes()).hexdigest()}
    else:
        with ProcessPoolExecutor(max_workers=14,
                                 mp_context=mp.get_context('fork')) as pool:
            for k, column in pool.map(
                    jacobian_column, range(100), chunksize=1):
                jac_columns[k] = column
                print('jacobian column', k, 'nonzero currents', len(column),
                      flush=True)
        jac_mode = {'mode': 'fresh'}
    jacobian_seconds = time.monotonic()-jacobian_seconds
    D = {}
    for k, column in jac_columns.items():
        for j, entries in column.items():
            D[(k, j)] = decode_entries(entries)
    print('PASS full current Jacobian:', len(D), 'nonzero (k,j) blocks in',
          round(jacobian_seconds, 1), 'seconds', flush=True)

    m = model.leaf.weyl
    q, x0, A0, _, _, _, _ = model.leaf.background(z0)
    qsub = dict(zip(m.native.joint.coframe.q, q))
    p = s.Matrix(p0)
    divergence = s.zeros(100, 1)
    divergence[:6, :] = model.at_time(
        model.leaf.pairing['divergence'].subs(qsub))
    divergence[6:, :] = model.at_time(
        d['scalar']['div_principal']+d['gauge']['div_principal'])
    divdiv = model.at_time(sum(s.diff(model.leaf.pairing['K'][i, j],
        m.native.joint.coframe.q[i], m.native.joint.coframe.q[j])
        for i in range(6) for j in range(6)).subs(qsub))
    divdiv += model.at_time(
        d['scalar']['divdiv_principal']+d['gauge']['divdiv_principal'])
    divlinear = model.at_time(
        d['scalar']['div_momentum_identity']+d['gauge']['div_momentum_identity'])
    divweights = model.at_time(
        d['scalar']['div_momentum_current']+d['gauge']['div_momentum_current'])
    divmatrix = sum((c*Q for c, Q in zip(divweights, model.leaf.charges)),
                    s.SparseMatrix(504, 504, {}))
    ordering = s.factor(-s.I*(divergence.T*p)[0]-divdiv/4-s.I*divlinear/2)

    def native_action(values, gs, hs):
        terms = []
        has_value = any(values.values())
        if (has_value or any(g[6:, :].todok() for g in gs.values())
                or any(h[6:, 6:].todok() for h in hs.values())):
            for component in ('scalar', 'gauge'):
                terms.append((1, quadratic_weyl_action(
                    d[component], values, gs, hs, m.current_word, m.current)))
        if (has_value or any(g[:6, :].todok() for g in gs.values())
                or any(h[:6, :6].todok() for h in hs.values())):
            terms.append((1, coframe_action(m,
                {'coframe': d['coframe'], 'e': d['matter']['e']},
                model.leaf.pairing, values, gs, hs)))
        if has_value:
            terms.append((1, apply_superposition(
                d['matter']['matter_CAR'], values)))
        return simplified({w: model.at_time(c)
                           for w, c in weighted_sum(terms).items()})

    def native_plane_action(state):
        return native_action(state,
            {w: c*s.I*p for w, c in state.items()},
            {w: -c*p*p.T for w, c in state.items()})

    # sanity: the replicated closures reproduce the original Weyl quantization
    # identity OpW(sigma)(plane wave) = symbol.apply + ordering - i/2 Q(divmatrix)
    for word in ((144, 396), (5, 144, 396)):
        state = {word: s.S.One}
        image = model.symbol(phase).apply(state)
        quantized = simplified(weighted_sum(((1, image), (ordering, state),
            (-s.I/2, apply_superposition(divmatrix, state)))))
        expected = native_plane_action(state)
        same(quantized, expected)
        assert expected
    print('PASS replicated native H action matches OpW(sigma) on test words',
          flush=True)

    Kp = K*p
    Mp = sum((p0[l]*currents[l] for l in range(100)), s.SparseMatrix(504, 504, {}))
    divJac = sum((D[(l, l)] for l in range(100) if (l, l) in D),
                 s.SparseMatrix(504, 504, {}))
    nonzero_of = {j: [k for k in range(100) if (k, j) in D] for j in range(100)}

    heisenberg_cache = {}

    def heisenberg_symbol(j, drop_D=False, drop_stress=False,
                          one_sided=False, pair_mask=None):
        """(one_body U+W, quartic N(A,B) summands, divergence one_body)."""
        key = (j, drop_D, drop_stress, one_sided,
               None if pair_mask is None else tuple(pair_mask))
        if key in heisenberg_cache:
            return heisenberg_cache[key]
        M_j = currents[j]
        nz = [] if drop_D else nonzero_of[j]
        Ubar = sum((2*Kp[k]*D[(k, j)] for k in nz), s.SparseMatrix(504, 504, {}))
        Ubar += s.I*commutator(Mp, M_j)
        W = sum((ell[k]*D[(k, j)] for k in nz), s.SparseMatrix(504, 504, {}))
        if one_sided:
            W += sum((currents[k]*D[(k, j)] for k in nz),
                     s.SparseMatrix(504, 504, {}))
        else:
            W += sum(((currents[k]*D[(k, j)]+D[(k, j)]*currents[k])/2
                      for k in nz), s.SparseMatrix(504, 504, {}))
        W += s.I*commutator(M0, M_j)
        local_divJac = s.SparseMatrix(504, 504, {}) if drop_D else divJac
        divU = sum((2*divergence[k]*D[(k, j)] for k in nz),
                   s.SparseMatrix(504, 504, {}))
        divU += s.I*(commutator(local_divJac, M_j)
                     + sum((commutator(currents[l], D[(l, j)]) for l in nz),
                           s.SparseMatrix(504, 504, {})))
        stress = [] if drop_stress or drop_D else [(s.S.One, currents[k],
                         D[(k, j)]) for k in nz]
        pair_terms = []
        for index, (c, A, B) in enumerate(pairs):
            if pair_mask is not None and not pair_mask[index]:
                continue
            pair_terms.append((s.I*c, ('Acomm', A, M_j), B))
            pair_terms.append((s.I*c, A, ('Bcomm', B, M_j)))
        heisenberg_cache[key] = (Ubar, W, divU, stress, pair_terms)
        return heisenberg_cache[key]

    def symbol_image(j, word, **variant):
        Ubar, W, divU, stress, pair_terms = heisenberg_symbol(j, **variant)
        state = {word: s.S.One}
        terms = [(1, apply_superposition(Ubar + W - s.I*divU/2, state))]
        for c, A, B in stress:
            terms.append((c, normal_pair(A, B, word)))
        for c, first, second in pair_terms:
            if isinstance(first, tuple):
                slim = slim_columns((first[1], first[2]), word)
                terms.append((c, normal_pair(slim, second, word)))
            else:
                slim = slim_columns((second[1], second[2]), word)
                terms.append((c, normal_pair(first, slim, word)))
        return simplified(weighted_sum(terms))

    plane_images = {(144, 396): None, (5, 144, 396): None}
    for word in plane_images:
        plane_images[word] = native_plane_action({word: s.S.One})

    def native_image(j, word):
        M_j = currents[j]
        state = {word: s.S.One}
        c_image = apply_superposition(M_j, state)
        d_images = {k: apply_superposition(D[(k, j)], state)
                    for k in nonzero_of[j]}
        words = set(c_image)
        for image in d_images.values():
            words |= set(image)
        values, gs, hs = {}, {}, {}
        for v in words:
            dv = s.zeros(100, 1)
            for k in nonzero_of[j]:
                dv[k] = d_images[k].get(v, 0)
            cv = c_image.get(v, 0)
            values[v] = cv
            gs[v] = s.I*p*cv + dv
            hs[v] = -cv*p*p.T + s.I*(p*dv.T + dv*p.T)
        plane = plane_images[word]
        return simplified({w: s.I*c for w, c in weighted_sum(
            ((1, native_action(values, gs, hs)),
             (-1, apply_superposition(M_j, plane)))).items()})

    tests = [(j, (144, 396)) for j in range(100)] + [
        (j, (5, 144, 396)) for j in (0, 1, 2, 3, 4, 5, 6, 30, 66, 67, 80, 99)]
    native_images, v1_checks = {}, []
    for j, word in tests:
        native = native_image(j, word)
        symbol = symbol_image(j, word)
        same(native, symbol)
        native_images[(j, word)] = native
        v1_checks.append({'j': j, 'word': list(word),
                          'image_entries': len(native)})
        print('PASS V1 heisenberg current j', j, 'word', word,
              'entries', len(native), flush=True)
    print('PASS V1 exact symbol-vs-differential Heisenberg derivative on all',
          len(tests), '(j,w) checks', flush=True)

    def control_defect(j, word, kind):
        """variant - base symbol image; equals variant - native by V1."""
        M_j = currents[j]
        state = {word: s.S.One}
        nz = nonzero_of[j]
        if kind == 'drop_all_D_terms':
            dU = sum((2*Kp[k]*D[(k, j)] for k in nz), s.SparseMatrix(504, 504, {}))
            dW = sum((ell[k]*D[(k, j)] for k in nz), s.SparseMatrix(504, 504, {}))
            dW += sum(((currents[k]*D[(k, j)]+D[(k, j)]*currents[k])/2
                       for k in nz), s.SparseMatrix(504, 504, {}))
            ddivU = sum((2*divergence[k]*D[(k, j)] for k in nz),
                        s.SparseMatrix(504, 504, {}))
            ddivU += s.I*(commutator(divJac, M_j)
                          + sum((commutator(currents[l], D[(l, j)])
                                 for l in nz), s.SparseMatrix(504, 504, {})))
            terms = [(1, apply_superposition(dU + dW - s.I*ddivU/2, state))]
            terms += [(1, normal_pair(currents[k], D[(k, j)], word))
                      for k in nz]
            return simplified(weighted_sum(terms))
        if kind == 'drop_lorentz_elimination_pair_derivations':
            terms = []
            for c, A, B in pairs[prefix_pair_count:]:
                terms.append((s.I*c, normal_pair(
                    slim_columns((A, M_j), word), B, word)))
                terms.append((s.I*c, normal_pair(
                    A, slim_columns((B, M_j), word), word)))
            return simplified(weighted_sum(terms))
        if kind == 'one_sided_quadratic_term':
            delta = sum(((currents[k]*D[(k, j)]-D[(k, j)]*currents[k])/2
                         for k in nz), s.SparseMatrix(504, 504, {}))
            return simplified(weighted_sum(
                ((1, apply_superposition(delta, state)),)))
        if kind == 'drop_normal_current_stress':
            return simplified(weighted_sum(
                [(1, normal_pair(currents[k], D[(k, j)], word))
                 for k in nz]))
        raise AssertionError(kind)

    # Exact operator-level invariance proof for the Lorentz-elimination tail:
    # the pairs sector sum_(a,b) W_ab (N([J_a,M_j],J_b)+N(J_a,[J_b,M_j]))
    # vanishes identically iff the coframe tensor
    #   Theta_j[i,j0,k,l] = sum_ab W_ab([J_a,M_j][i,j0] J_b[k,l]
    #                                  + J_a[i,j0] [J_b,M_j][k,l])
    # vanishes under BOTH normal-ordered restrictions:
    #   same-sector (m == m'):  Theta^AA = Theta[i,j,k,l] - Theta[k,j,i,l]
    #                                   - Theta[i,l,k,j] + Theta[k,l,i,j]
    #   cross-sector (m != m'): Theta_sym = Theta[i,j,k,l] + Theta[k,l,i,j]
    # since full(X) = X8 (x) I_63 preserves the internal sector of every mode.
    # For j >= 6 we assert [J_a, M_j] = 0 in full 504 directly.
    Js8 = [s.SparseMatrix(J) for J in d['coframe']['J']]
    W_cf = s.SparseMatrix(d['coframe']['W'])
    M8 = [model.at_time(M.subs(qsub)) for M in model.leaf.pairing['Mh']]

    def sector_clean(M):
        return s.SparseMatrix(
            s.SparseMatrix(M).applyfunc(lambda v: s.cancel(s.expand(v))))

    for j in range(6):
        assert not sector_clean(
            s.SparseMatrix(full(M8[j])) - currents[j]).todok()
    J_support = sorted({rc for J in Js8 for rc in J.todok()})
    J_basis = s.Matrix(len(J_support), len(Js8),
                       lambda i, b: Js8[b][J_support[i]])
    lorentz_invariance = {
        'J_family_size': len(Js8),
        'J_span_rank': J_basis.rank(),
        'W_entries': len(W_cf.todok()),
        'criterion': ('Theta^AA[i,j,k,l] = Theta[i,j,k,l] - Theta[k,j,i,l] '
                      '- Theta[i,l,k,j] + Theta[k,l,i,j] == 0 (same-sector) '
                      'AND Theta_sym[i,j,k,l] = Theta[i,j,k,l] + '
                      'Theta[k,l,i,j] == 0 (cross-sector) on the 8-mode '
                      'coframe sector <=> the W-tail derivation operator '
                      'vanishes on every Fock word'),
        'per_current': {}}
    for j in range(6, 100):
        for a, Ja in enumerate(Js8):
            residual = sector_clean(
                s.SparseMatrix(full(Ja))*currents[j]
                - currents[j]*s.SparseMatrix(full(Ja)))
            assert not residual.todok(), (j, a)
        lorentz_invariance['per_current'][str(j)] = 'zero_commutator_504'
    for j in range(6):
        Mm = s.SparseMatrix(M8[j])
        comms = [s.SparseMatrix(Ja*Mm - Mm*Ja).applyfunc(s.cancel)
                 for Ja in Js8]
        nz = [a for a, cm in enumerate(comms) if cm.todok()]
        if not nz:
            lorentz_invariance['per_current'][str(j)] = 'zero_commutator_8'
            continue
        Theta = {}
        for (a, b), c in W_cf.todok().items():
            for (i, jj), x in comms[a].todok().items():
                for (k, l), y in Js8[b].todok().items():
                    Theta[(i, jj, k, l)] = (Theta.get((i, jj, k, l), 0)
                                            + c*x*y)
            for (i, jj), x in Js8[a].todok().items():
                for (k, l), y in comms[b].todok().items():
                    Theta[(i, jj, k, l)] = (Theta.get((i, jj, k, l), 0)
                                            + c*x*y)
        bad_aa, bad_sym = [], []
        for i in range(8):
            for k in range(8):
                for jj in range(8):
                    for l in range(8):
                        val_aa = (Theta.get((i, jj, k, l), 0)
                                  - Theta.get((k, jj, i, l), 0)
                                  - Theta.get((i, l, k, jj), 0)
                                  + Theta.get((k, l, i, jj), 0))
                        if s.cancel(val_aa) != 0:
                            bad_aa.append((i, jj, k, l))
                        val_sym = (Theta.get((i, jj, k, l), 0)
                                   + Theta.get((k, l, i, jj), 0))
                        if s.cancel(val_sym) != 0:
                            bad_sym.append((i, jj, k, l))
        assert not bad_aa and not bad_sym, (j, bad_aa[:5], bad_sym[:5])
        lorentz_invariance['per_current'][str(j)] = {
            'verdict': 'invariant_form',
            'nonzero_commutator_Js': nz,
            'theta_entries': len(Theta),
            'theta_AA_failures': len(bad_aa),
            'theta_sym_failures': len(bad_sym)}
    print('PASS exact tensor-level Lorentz W-form invariance: '
          'rank', lorentz_invariance['J_span_rank'], 'of', len(Js8),
          'coframe currents; verdicts',
          {j: v if isinstance(v, str) else v['verdict']
           for j, v in lorentz_invariance['per_current'].items()},
          flush=True)

    controls = {}
    for name in ('drop_all_D_terms', 'drop_lorentz_elimination_pair_derivations',
                 'one_sided_quadratic_term', 'drop_normal_current_stress'):
        witnesses = []
        for j, word in tests:
            defect = control_defect(j, word, name)
            if defect:
                witnesses.append({'j': j, 'word': list(word),
                                  'defect_entries': len(defect),
                                  'sample': encode_state(
                                      {w: defect[w] for w in
                                       list(defect)[:2]})})
        if name == 'drop_lorentz_elimination_pair_derivations' and not witnesses:
            # The coframe W-form is ad-invariant under every current:
            # sum_{(a,b)} W_ab*(N([J_a,M_j],J_b)+N(J_a,[J_b,M_j]))|w> == 0
            # identically, so dropping the tail derivations is a no-op.
            # Witness a nonzero single-pair derivation to prove the
            # pair-derivation machinery itself is live.
            live_witness = None
            for c, A, B in pairs[prefix_pair_count:]:
                for j, word in tests[:100]:
                    single = simplified(weighted_sum((
                        (s.I*c, normal_pair(
                            slim_columns((A, currents[j]), word), B, word)),
                        (s.I*c, normal_pair(
                            A, slim_columns((B, currents[j]), word), word)))))
                    if single:
                        live_witness = {'j': j, 'word': list(word),
                                        'image_entries': len(single),
                                        'sample': encode_state(
                                            {w: single[w] for w in
                                             list(single)[:2]})}
                        break
                if live_witness:
                    break
            assert live_witness, name
            controls[name] = {
                'nonzero_defects': 0,
                'invariant_form_cancellation': True,
                'tensor_proof': 'lorentz_elimination_invariance',
                'single_pair_derivation_witness': live_witness}
            print('PASS V2 control', name,
                  'vacuous: coframe W-form is ad-invariant under all currents;'
                  ' live single-pair witness at j',
                  live_witness['j'], live_witness['word'], flush=True)
            continue
        assert witnesses, name
        controls[name] = {'nonzero_defects': len(witnesses),
                          'first_witness': witnesses[0]}
        print('PASS V2 control', name, 'defects', len(witnesses), flush=True)

    generators = [s.SparseMatrix(decode(entry))
                  for entry in charge['source_real_CAR504_generators']]
    charge_commutator_checks = 0
    for alpha, Q in enumerate(generators):
        if Q.is_diagonal():
            diag = [Q[i, i] for i in range(504)]
            equal_pairs = {}
            for (k, j), Dmat in D.items():
                for i, l in Dmat.todok():
                    key = (diag[i], diag[l])
                    if key not in equal_pairs:
                        equal_pairs[key] = s.cancel(diag[i]-diag[l]) == 0
                    assert equal_pairs[key], (alpha, k, j, i, l)
                charge_commutator_checks += 1
        else:
            for (k, j), Dmat in D.items():
                residual = s.SparseMatrix(Q*Dmat - Dmat*Q).applyfunc(s.cancel)
                assert not residual.todok(), (alpha, k, j)
                charge_commutator_checks += 1
    print('PASS V3 all 14 source real CAR generators commute with every nonzero'
          ' Jacobian entry:', charge_commutator_checks, 'checks', flush=True)

    free = model.leaf.free
    def block(k):
        return 'coframe' if free[k] < 6 else 'scalar' if free[k] < 67 else 'gauge'
    block_counts = {'coframe': 0, 'scalar': 0, 'gauge': 0}
    for (k, j) in D:
        block_counts[block(k)] += 1
    coframe_div = sum((D[(k, k)] for k in range(6) if (k, k) in D),
                      s.SparseMatrix(504, 504, {}))
    coframe_div_zero = not s.SparseMatrix(
        coframe_div.applyfunc(s.cancel)).todok()
    scalar_gauge_div = sum((D[(k, k)] for k in range(6, 100) if (k, k) in D),
                           s.SparseMatrix(504, 504, {}))
    residual = s.SparseMatrix(scalar_gauge_div - divmatrix).applyfunc(s.cancel)
    assert not residual.todok(), list(residual.todok().items())[:5]
    quartic_counts = {}
    stress_witness = None
    for j, word in tests[:100]:
        _, _, _, stress, pair_terms = heisenberg_symbol(j)
        contributing = len(stress)
        pair_nonzero = 0
        for c, first, second in pair_terms:
            slim = slim_columns(
                (first[1], first[2]) if isinstance(first, tuple)
                else (second[1], second[2]), word)
            if slim.todok():
                pair_nonzero += 1
        quartic_counts[j] = {'normal_stress_terms': contributing,
                             'pair_derivation_terms': pair_nonzero}
        quartic = weighted_sum(
            [(c, normal_pair(A, B, word)) for c, A, B in stress]
            + [(c, normal_pair(slim_columns((first[1], first[2]), word),
                                second, word))
               if isinstance(first, tuple) else
               (c, normal_pair(first, slim_columns((second[1], second[2]), word),
                               word))
               for c, first, second in pair_terms])
        if stress_witness is None and quartic:
            w0, c0 = next(iter(quartic.items()))
            stress_witness = {'j': j, 'word': list(word),
                              'image_word': list(w0), 'coefficient': str(c0)}
    assert stress_witness
    print('PASS V4 Jacobian report and quartic-stress witness', flush=True)

    jacobian_payload = {
        'root': ROOT_ID,
        'scope': 'JACOBIAN_OF_THE_100_ONE_BODY_CURRENTS_AT_CONFIGURATION100',
        'dimensions': [100, 100, 504, 504],
        'formula': 'D_kj = d/dz_k linear_current[j].one_body at z0',
        'columns': {str(k): {str(j): entries for j, entries in column.items()}
                    for k, column in jac_columns.items()},
    }
    gz_path = HERE/'source_joint_current_heisenberg.jacobian.json.gz'
    gz_bytes = gzip.compress(json.dumps(
        jacobian_payload, separators=(',', ':')).encode(), mtime=0)
    gz_path.write_bytes(gz_bytes)
    jacobian_sha = hashlib.sha256(gz_bytes).hexdigest()
    print('jacobian gz bytes', len(gz_bytes), flush=True)

    files = {}
    for name in (
        'Verification/physics/low-energy-phenomenology/external-composite-decay/source_joint_current_heisenberg.py',
        'Verification/physics/low-energy-phenomenology/external-composite-decay/source_joint_current_heisenberg.jacobian.json.gz',
        'Verification/physics/low-energy-phenomenology/external-composite-decay/source_joint_ccr_car_ports.py',
        'Verification/physics/low-energy-phenomenology/external-composite-decay/source_joint_form_hamiltonian.py',
        'Verification/physics/low-energy-phenomenology/external-composite-decay/source_scalar_weyl_symbol.py',
        'Verification/physics/low-energy-phenomenology/external-composite-decay/source_common_weyl_symbol.py',
        'Verification/physics/low-energy-phenomenology/external-composite-decay/source_clock_symbol_recursion.py',
        'Verification/physics/low-energy-phenomenology/external-composite-decay/source_gauss_quantum_current.py',
        'Verification/physics/low-energy-phenomenology/external-composite-decay/JointCCRCarPorts.lean',
        'Verification/physics/low-energy-phenomenology/external-composite-decay/JointCurrentHeisenberg.lean',
        'Verification/physics/low-energy-phenomenology/external-composite-decay/source_joint_ccr_car_ports.json',
        'Verification/physics/low-energy-phenomenology/external-composite-decay/source_joint_charge_conservation.json',
    ):
        files[name] = hashlib.sha256((ROOT/name).read_bytes()).hexdigest()

    result = {
        'root': ROOT_ID,
        'scope': 'ACTUAL_GAUSS100_FULL504_CURRENT_HEISENBERG_DERIVATIVE',
        'source_sha256': model.leaf.weyl.graph.common.source_hashes,
        'input_sha256': files,
        'jacobian_file': 'source_joint_current_heisenberg.jacobian.json.gz',
        'jacobian_sha256': jacobian_sha,
        'jacobian_bytes': len(gz_bytes),
        'jacobian_computation': jac_mode,
        'fixture': {'configuration': 'configuration100',
                    'momenta': 'configuration_momenta100'},
        'symbol': {
            'current': 'J_j = OpW(Q(M_j(z))), M_j = coefficients(z)["linear_current"][j]',
            'heisenberg_derivative': 'Jdot_j = i[H,J_j] = OpW(Jdot_j(p))',
            'Jdot_j': 'sum_l p_l Q(U_jl) + Q(W_j) + sum_k N(M_k,D_kj) + i sum_(c,A,B) c (N([A,M_j],B) + N(A,[B,M_j]))',
            'U_jl': '2 sum_k K_lk D_kj + i [M_l,M_j]',
            'W_j': 'sum_k l_k D_kj + (1/2) sum_k (M_k D_kj + D_kj M_k) + i [M_0,M_j]',
            'D_kj': 'd/dz_k M_j at z0 (Jacobian receipt in the gz file)',
            'ordering_term': 'OpW(sum_l p_l Q(U_jl)) = action + -(i/2) Q(sum_l d_l U_jl)',
            'divergence_U': 'sum_l d_l U_jl = 2 sum_k divergence_k D_kj + i sum_l ([D_ll,M_j] + [M_l,D_lj])',
            'normal_product': 'Q(A)Q(B) = Q(AB) + N(A,B), N symmetric',
        },
        'V1_native_composition': {
            'statement': 'i (H(J1 psi) - J1(H psi)) = Jdot_j(p0)|w> - (i/2) Q(div U_j)|w>',
            'checks': v1_checks,
        },
        'V2_reverse_controls': controls,
        'V3_charge_conservation': {
            'source_real_CAR504_generators': len(generators),
            'nonzero_D_commutator_checks': charge_commutator_checks,
            'conclusion': '[Q_alpha, D_kj] = 0 for all nonzero Jacobian blocks and all 14 generators; with closure under products/commutators and Lean SourceJointCurrentHeisenberg.normalProduct_charge_commute, quantize(Q_alpha) commutes with Jdot_j',
        },
        'V4_jacobian_report': {
            'nonzero_blocks': len(D),
            'block_counts': block_counts,
            'coframe_diagonal_divergence_zero': coframe_div_zero,
            'scalar_gauge_diagonal_equals_divmatrix': True,
            'per_current_quartic_stress': quartic_counts,
            'quartic_stress_witness': stress_witness,
        },
        'lorentz_elimination_pairs_tail_count': coframe_W_count,
        'lorentz_elimination_invariance': lorentz_invariance,
        'proton_lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'seconds': round(time.monotonic()-began, 3),
    }
    (HERE/'source_joint_current_heisenberg.json').write_text(
        json.dumps(result, indent=2))
    print('PASS exact Heisenberg derivative of all 100 original current ports '
          f'{round(time.monotonic()-began,3)} seconds', flush=True)


if __name__ == '__main__':
    main()
