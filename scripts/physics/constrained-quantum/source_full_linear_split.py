#!/usr/bin/env python3
"""Complete source Jacobi inventory, including the scalar/matter cross block.

The occupied12 projector reduces the background Dirac operator and all
non-scalar vertices. It does not reduce every scalar vertex. The actual
background generates a triangular dual-complement -> scalar61 -> primal-
complement linear response, which is retained here.
"""
from __future__ import annotations

from collections import Counter
from functools import lru_cache
import hashlib
import json
import time

import sympy as s

from dynamic import HERE, BASE, ROOT, ROOT_ID
from source_common_hamiltonian import SourceCommonHamiltonian
from source_lorentz_contact import clean, equal, encode, ETA


P = s.symbols('p0:4', real=True)
K = s.symbols('k1:4', real=True)
LAMBDA = s.Symbol('source_laplace')
LOCALS = {str(v): v for v in (*P, *K)}


def decode(record):
    return s.SparseMatrix(*record['shape'], {(i, j): s.sympify(value, locals=LOCALS)
                                            for i, j, value in record['entries']})


def realify(A):
    return clean(A.applyfunc(s.re).row_join(-A.applyfunc(s.im)).col_join(
                 A.applyfunc(s.im).row_join(A.applyfunc(s.re))))


def real_pair(A):
    """The coefficient of Re(chi A psi), with both fields independent."""
    return clean(A.applyfunc(s.re).row_join(-A.applyfunc(s.im)).col_join(
                 (-A.applyfunc(s.im)).row_join(-A.applyfunc(s.re))))


def coefficients(A):
    values = [clean(A.subs(dict.fromkeys(P, 0))), *[clean(A.diff(p)) for p in P]]
    equal(A, values[0]+sum((p*value for p, value in zip(P, values[1:])), s.zeros(*A.shape)))
    assert all(not value.free_symbols for value in values)
    return values


def real_Fourier_generator(constant, spatial):
    # Realify the original coefficient matrices before substituting d_i=i*k_i.
    # Taking Re/Im after that substitution confuses Fourier i with matter i.
    return clean(realify(constant)+sum((s.I*k*realify(A) for k, A in zip(K, spatial)),
                                      s.zeros(2*constant.rows)))


def assemble(rows, cols, blocks):
    entries = {}
    for row, col, block in blocks:
        for (i, j), value in s.SparseMatrix(block).todok().items():
            key = row+i, col+j
            entries[key] = entries.get(key, 0)+value
    return clean(s.SparseMatrix(rows, cols, entries))


class SourceFullLinearSplit:
    def __init__(self):
        self.common = SourceCommonHamiltonian()
        self.active = json.loads((BASE/'active-gauge/receipt.json').read_bytes())
        self.occupied = json.loads((BASE/'occupied-response/receipt.json').read_bytes())
        self.vertices = json.loads((BASE/'matter-vertices/receipt.json').read_bytes())
        self.phase = json.loads((BASE/'full-phase/receipt.json').read_bytes())
        self.scalar_record = json.loads((HERE/'scalar_canonical_phase.json').read_bytes())
        self.O = decode(self.occupied['occupied_frame'])
        equal(self.O.H*self.O, s.eye(self.O.cols))
        self.projector = clean(self.O*self.O.H)
        self.complement = clean(s.eye(self.O.rows)-self.projector)
        assert self.projector.is_diagonal()
        indices = [i for i in range(self.O.rows) if self.complement[i, i] == 1]
        self.C = s.SparseMatrix.eye(self.O.rows)[:, indices]
        equal(self.C*self.C.H, self.complement)
        equal(self.C.H*self.C, s.eye(self.C.cols))
        equal(self.O.H*self.C, s.zeros(self.O.cols, self.C.cols))
        equal(self.O.applyfunc(s.im), s.zeros(*self.O.shape))
        self.N = s.sympify(self.vertices['source_lapse'])
        self.D = decode(self.vertices['full_stationary_Dirac_operator'])
        self.E = clean(self.N*self.D.diff(P[0]))
        self.Ei = [clean(self.N*self.D.diff(p)) for p in P[1:]]
        self.K0 = clean(self.N*self.D.subs(dict.fromkeys(P, 0)))
        background = self.active['actual_background']
        self.e = s.Matrix(background['coframe']).applyfunc(s.sympify)
        self.A = s.Matrix(background['gauge_connection']).applyfunc(s.sympify)
        self.psi0 = clean(self.O*s.Matrix(background['primal_H']).applyfunc(s.sympify))
        self.chi0 = clean(s.sympify(background['dual_multiple'])*self.psi0.T)
        equal(self.projector*self.psi0, self.psi0); equal(self.chi0*self.projector, self.chi0)
        self.V = [decode(item['operator']) for item in self.vertices['primitive_vertices']]
        self.scalar_vertices = [V for item, V in zip(self.vertices['primitive_vertices'], self.V)
                                if item['group'] == 'scalar']
        self.R = decode(self.scalar_record['scalar_coordinate_embedding'])
        self.P61 = decode(self.scalar_record['projector61'])
        self.As = decode(self.scalar_record['canonical_generator'])
        self.scalar_gram_inverse = clean((self.R.T*self.R).inv())
        self.orbit = clean(s.Matrix.hstack(*[R*self.common.scalar.vacuum for R in self.common.scalar.rho]))
        self.J = self.orbit[:, self.active['J_independent_columns']]
        self.B70 = clean(s.Matrix.hstack(*[self.C.H*V*self.psi0 for V in self.scalar_vertices]))
        self.B61 = clean(self.B70*self.R)

    def inventory(self):
        rows, counts = [], Counter()
        for item, V in zip(self.vertices['primitive_vertices'], self.V):
            cross = []
            for coefficient in coefficients(V):
                right, left = clean(self.C.H*coefficient*self.O), clean(self.O.H*coefficient*self.C)
                cross.append((len(right.todok()), len(left.todok())))
            counts[item['group']] += 1
            if item['group'] != 'scalar':
                assert all(right == left == 0 for right, left in cross)
            rows.append({'group': item['group'], 'coordinate': item['coordinate'],
                         'cross_nonzero_entries_constant_p0_p1_p2_p3': cross})
        assert sum(counts.values()) == len(self.V) == 158
        background = [*map(decode, self.phase['principal_coefficients']),
                      decode(self.phase['original_constant_B']), decode(self.phase['original_Y']),
                      decode(self.phase['phase_generator']), decode(self.phase['stationary_primal_constant'])]
        for matrix in [self.E, self.K0, *self.Ei, *background]:
            equal(self.C.H*matrix*self.O, s.zeros(self.C.cols, self.O.cols))
            equal(self.O.H*matrix*self.C, s.zeros(self.O.cols, self.C.cols))
        for a, V in enumerate(self.scalar_vertices):
            expected = self.N*(s.I if a >= 35 else 1)*self.common.yukawa_basis[a % 35]
            equal(V, expected)
            equal(self.chi0*V, s.zeros(1, 252))
            equal(self.O.H*V*self.psi0, s.zeros(self.O.cols, 1))
        assert any(self.C.H*V*self.O != s.zeros(self.C.cols, self.O.cols) for V in self.scalar_vertices)
        assert self.B70.todok()
        equal(self.B70*self.J, s.zeros(self.C.cols, self.J.cols))
        equal(self.B70*self.P61, self.B70)
        real_source = self.B70.applyfunc(s.re).col_join(self.B70.applyfunc(s.im))
        return {'occupied_complex_dimension': self.O.cols, 'complement_complex_dimension': self.C.cols,
                'occupied_frame': encode(self.O), 'occupied_Hermitian_projector': encode(self.projector),
                'complement_frame': encode(self.C), 'primitive_counts': dict(counts), 'all158_coefficient_checks': rows,
                'all_original_Dirac_principals_K_and_phase_preserve_both_blocks': True,
                'scalar_primitive_right_cross_nonzero_count': sum(bool((self.C.H*V*self.O).todok()) for V in self.scalar_vertices),
                'scalar_primitive_left_cross_nonzero_count': sum(bool((self.O.H*V*self.C).todok()) for V in self.scalar_vertices),
                'actual_scalar_source_complex_rank': self.B70.rank(), 'actual_scalar_source_real_rank': real_source.rank(),
                'actual_scalar_source_nonzero_columns': sum(bool(self.B70[:, a].todok()) for a in range(70)),
                'actual_scalar_source': encode(self.B70), 'all_active_scalar9_sources_zero': True,
                'actual_dual_background_scalar_forcing_zero': True,
                'Hermitian_projector_does_not_impose_chi_equals_psi_adjoint': True}

    def scalar_symbol(self):
        h = self.N*self.e.inv()*ETA*self.e.inv().T
        RA = [clean(sum((self.A[mu, a]*self.common.scalar.rho[a] for a in range(12)), s.zeros(70)))
              for mu in range(4)]
        for matrix in RA:
            equal(matrix*self.common.scalar.vacuum, s.zeros(70, 1))
            equal(matrix*self.P61, self.P61*matrix)
        operator = clean(-sum((h[mu, nu]*(P[mu]*s.eye(70)+RA[mu])*(P[nu]*s.eye(70)+RA[nu])
                              for mu in range(4) for nu in range(4)), s.zeros(70))-2*self.N*s.eye(70))
        equal(self.J.T*operator*self.R, s.zeros(9, self.R.cols))
        equal(self.R.T*operator*self.J, s.zeros(self.R.cols, 9))
        equal(self.R*self.scalar_gram_inverse*self.R.T, self.P61)
        equal(self.J*(self.J.T*self.J).inv()*self.J.T+self.P61, s.eye(70))
        scalar = json.loads((BASE/'scalar-exchange/receipt.json').read_bytes())
        normalized = decode(scalar['normalized_full_scalar_operator'])
        substitute = {v: (P[0]/(self.N*s.sqrt(2)) if str(v) == 'u' else
                          P[int(str(v)[1:])]/s.sqrt(2)) for v in normalized.free_symbols}
        equal(operator, self.N*normalized.subs(substitute))
        return operator

    def active_matter_and_scalar_readback(self, scalar_operator):
        hessian = s.MutableSparseMatrix(289, 289, {})
        for i, j, powers, value in self.active['Fourier_Jacobi_entries']:
            hessian[i, j] += s.sympify(value)*s.prod(p**n for p, n in zip(P, powers))
        hessian = clean(hessian)
        indices = {group: [i for i, field in enumerate(self.active['fields']) if field['group'] == group]
                   for group in ('scalar_J', 'primal_H', 'dual_H')}
        equal(hessian.extract(indices['scalar_J'], indices['scalar_J']), self.J.T*scalar_operator*self.J)
        D12 = clean(self.N*self.O.H*self.D*self.O)
        equal(hessian.extract(indices['dual_H'], indices['primal_H']), real_pair(D12))
        minus = dict(zip(P, [-p for p in P]))
        equal(hessian.extract(indices['primal_H'], indices['dual_H']), real_pair(D12.subs(minus, simultaneous=True)).T)
        # The original97 bosonic source operators have an already certified
        # full289 consumer. Recheck every mixed leg on this same occupied frame.
        by_key = {(item['group'], tuple(item['coordinate'])): V
                  for item, V in zip(self.vertices['primitive_vertices'], self.V)}
        for index, field in enumerate(self.active['fields']):
            key = (field['group'], tuple(field['coordinate']))
            if key in by_key:
                V = by_key[key]
            elif field['group'] == 'scalar_J':
                V = clean(sum((self.J[a, field['coordinate'][0]]*self.scalar_vertices[a]
                               for a in range(70)), s.zeros(252)))
            else:
                continue
            for group in ('primal_H', 'dual_H'):
                for col in indices[group]:
                    imaginary, spin, color = self.active['fields'][col]['coordinate']
                    point = 3*spin+color
                    value = ((self.chi0*V*self.O)[point] if group == 'primal_H' else
                             (self.O.H*V.subs(dict.fromkeys(P, 0))*self.psi0)[point])
                    assert s.expand(s.re(s.I**imaginary*value)-hessian[index, col]) == 0
        return hessian

    @lru_cache(maxsize=1)
    def tail_blocks(self):
        EC = clean(self.C.H*self.E*self.C)
        inverse = clean(EC.inv())
        KC = clean(self.C.H*self.K0*self.C)
        spatial = [clean(self.C.H*V*self.C) for V in self.Ei]
        primal = [-inverse*KC, *[-inverse*V for V in spatial]]
        dual = [(KC*inverse).T, *[-(V*inverse).T for V in spatial]]
        equal(EC*primal[0]+KC, s.zeros(self.C.cols))
        equal(dual[0].T*EC-KC, s.zeros(self.C.cols))
        for V, ap, ad in zip(spatial, primal[1:], dual[1:]):
            equal(EC*ap+V, s.zeros(self.C.cols)); equal(ad.T*EC+V, s.zeros(self.C.cols))
        Ap = real_Fourier_generator(*[primal[0], primal[1:]])
        Ad = real_Fourier_generator(*[dual[0], dual[1:]])
        minus = dict(zip(K, [-k for k in K]))
        for value in (Ap, Ad, self.As):
            equal(value.conjugate(), value.subs(minus, simultaneous=True))
        # Explicit control for the distinct internal-complex/Fourier factors.
        wrong = realify(primal[0]+s.I*primal[1])
        assert clean(Ap.subs(dict(zip(K, [1, 0, 0])))-wrong).todok()
        q_force = clean(-inverse*self.B61)
        C = clean(q_force.applyfunc(s.re).col_join(q_force.applyfunc(s.im)).row_join(s.zeros(2*self.C.cols, self.R.cols)))
        Jchi = clean(self.B61.T.applyfunc(s.re).row_join(-self.B61.T.applyfunc(s.im)))
        B = clean(s.zeros(self.R.cols, 2*self.C.cols).col_join(Jchi))
        equal(EC*q_force+self.B61, s.zeros(self.C.cols, self.R.cols))
        equal(C*B, s.zeros(Ap.rows, Ad.cols))
        cascade = clean(C*self.As*B)
        assert cascade.todok()
        # Canonical scalar momenta are the original Pi=-dot(phi)/N.
        phi_second_from_chi = clean(self.R*self.As[:self.R.cols, :]*B/self.N+
                                    self.R*self.scalar_gram_inverse*Jchi)
        equal(phi_second_from_chi, s.zeros(70, Ad.cols))
        return {'dual': Ad, 'scalar': self.As, 'primal': Ap,
                'dual_to_scalar': B, 'scalar_to_primal': C, 'third_time_cascade': cascade,
                'complex_primal_coefficients': primal, 'complex_dual_coefficients': dual,
                'complex_scalar_to_primal': q_force}

    def complete_action_split(self, active, scalar):
        """Explicit original1310 carrier and its full raw quadratic action."""
        fields = self.active['fields']
        bosons = [i for i, field in enumerate(fields)
                  if field['group'] not in ('scalar_J', 'primal_H', 'dual_H')]
        bindex = {index: row for row, index in enumerate(bosons)}
        nb, ns, nr = len(bosons), 70, 2*self.O.rows
        nfull = nb+ns+2*nr
        phi, psi, chi = nb, nb+ns, nb+ns+nr
        active_n, scalar_n, matter_n = active.rows, self.R.cols, 2*self.C.cols
        q, cp, cd = active_n, active_n+scalar_n, active_n+scalar_n+matter_n
        assert cd+matter_n == nfull
        injection, retraction = {}, {}
        Jreader = clean((self.J.T*self.J).inv()*self.J.T)
        Rreader = clean(self.scalar_gram_inverse*self.R.T)
        for old, field in enumerate(fields):
            group, coordinate = field['group'], field['coordinate']
            if old in bindex:
                injection[bindex[old], old] = 1
                retraction[old, bindex[old]] = 1
            elif group == 'scalar_J':
                col = coordinate[0]
                for a in range(70):
                    if self.J[a, col]: injection[phi+a, old] = self.J[a, col]
                    if Jreader[col, a]: retraction[old, phi+a] = Jreader[col, a]
            else:
                imaginary, spin, color = coordinate
                offset = psi if group == 'primal_H' else chi
                for a in range(self.O.rows):
                    value = self.O[a, 3*spin+color]
                    if value:
                        injection[offset+imaginary*self.O.rows+a, old] = value
                        retraction[old, offset+imaginary*self.O.rows+a] = value
        for (a, b), value in self.R.todok().items(): injection[phi+a, q+b] = value
        for (a, b), value in Rreader.todok().items(): retraction[q+a, phi+b] = value
        for physical, split in ((psi, cp), (chi, cd)):
            for imaginary in range(2):
                for (a, b), value in self.C.todok().items():
                    injection[physical+imaginary*self.O.rows+a, split+imaginary*self.C.cols+b] = value
                    retraction[split+imaginary*self.C.cols+b, physical+imaginary*self.O.rows+a] = value
        T = s.SparseMatrix(nfull, nfull, injection)
        Ti = s.SparseMatrix(nfull, nfull, retraction)
        equal(T*Ti, s.SparseMatrix.eye(nfull)); equal(Ti*T, s.SparseMatrix.eye(nfull))
        minus = dict(zip(P, [-p for p in P]))
        adjoint = lambda A: clean(A.subs(minus, simultaneous=True).T)
        # Rebuild the raw full action from its original density coefficients.
        original_blocks = [(0, 0, active.extract(bosons, bosons)), (phi, phi, scalar)]
        pair = real_pair(self.N*self.D)
        original_blocks += [(chi, psi, pair), (psi, chi, adjoint(pair))]
        by_key = {(item['group'], tuple(item['coordinate'])): V
                  for item, V in zip(self.vertices['primitive_vertices'], self.V)}
        h = self.N*self.e.inv()*ETA*self.e.inv().T
        RA = [clean(sum((self.A[mu, a]*self.common.scalar.rho[a] for a in range(12)), s.zeros(70)))
              for mu in range(4)]
        for old in bosons:
            field = fields[old]
            key = (field['group'], tuple(field['coordinate']))
            row = bindex[old]
            if key in by_key:
                V = by_key[key]
                left = clean(self.chi0*V)
                right = clean(V.subs(dict.fromkeys(P, 0))*self.psi0).T
                bl = clean(left.applyfunc(s.re).row_join(-left.applyfunc(s.im)))
                br = clean(right.applyfunc(s.re).row_join(-right.applyfunc(s.im)))
                original_blocks += [(row, psi, bl), (psi, row, adjoint(bl)),
                                    (row, chi, br), (chi, row, adjoint(br))]
            if field['group'] == 'gauge_A':
                nu, a = field['coordinate']
                column = clean(-sum((h[mu, nu]*(P[mu]*s.eye(70)+RA[mu])*
                                      self.common.scalar.rho[a]*self.common.scalar.vacuum
                                      for mu in range(4)), s.zeros(70, 1)))
                original_blocks += [(phi, row, column), (row, phi, adjoint(column))]
        full_scalar_source = clean(s.Matrix.hstack(*[V*self.psi0 for V in self.scalar_vertices]))
        phi_chi = clean(full_scalar_source.T.applyfunc(s.re).row_join(-full_scalar_source.T.applyfunc(s.im)))
        original_blocks += [(phi, chi, phi_chi), (chi, phi, phi_chi.T)]
        original = assemble(nfull, nfull, original_blocks)
        DC = clean(self.N*self.C.H*self.D*self.C)
        B = real_pair(DC)
        Jchi = clean(self.B61.T.applyfunc(s.re).row_join(-self.B61.T.applyfunc(s.im)))
        ntail = scalar_n+2*matter_n
        tail = assemble(ntail, ntail, [(0, 0, self.R.T*scalar*self.R),
            (0, scalar_n+matter_n, Jchi), (scalar_n+matter_n, 0, Jchi.T),
            (scalar_n+matter_n, scalar_n, B), (scalar_n, scalar_n+matter_n, adjoint(B))])
        expected = assemble(nfull, nfull, [(0, 0, active), (active_n, active_n, tail)])
        equal(T.T*original*T, expected)
        equal(Ti.T*expected*Ti, original)
        equal(adjoint(original), original)
        return {'original_real_field_dimension': nfull,
                'original_field_order': 'old232 bosonic primitives, full_scalar70, primal(real252,imag252), independent_dual(real252,imag252)',
                'old_bosonic_field_indices': bosons,
                'split_field_order': 'active289, peripheral_scalar61, primal_complement(real240,imag240), independent_dual_complement(real240,imag240)',
                'source_field_embedding': encode(T), 'source_field_retraction': encode(Ti),
                'raw_full_Jacobi_nonzero_entries': len(original.todok()),
                'full_raw_density_congruence_both_directions_checked': True,
                'full_raw_formal_adjoint_identity_checked': True,
                'tail_scalar_dual_cross': encode(Jchi),
                'original_scalar_gauge_mixed_source': '-sum_mu h(mu,nu)*(p_mu+rho(A_mu))*rho_a*v',
                'source_decoupling_mechanism': 'All background D_mu v vanish; P61 commutes with every background scalar covariant derivative, its image is orthogonal to rho_a v, and every scalar background current chi0*Va*psi0 is zero. The retained scalar-dual cross is not discarded.'}

    def tail_generator(self, momentum):
        blocks = self.tail_blocks()
        at = lambda A: clean(A.subs(dict(zip(K, momentum))))
        d, b, p = [at(blocks[key]) for key in ('dual', 'scalar', 'primal')]
        B, C = blocks['dual_to_scalar'], blocks['scalar_to_primal']
        size = d.rows+b.rows+p.rows
        return assemble(size, size, [(0, 0, d), (d.rows, 0, B), (d.rows, d.rows, b),
                                     (d.rows+b.rows, d.rows, C), (d.rows+b.rows, d.rows+b.rows, p)])


def phase_inventory(model, blocks):
    record = json.loads((HERE/'retained_hamiltonian_reduction.json').read_bytes())
    assert record['root'] == ROOT_ID
    rows = []
    for old in record['source_momenta']:
        active = decode(old['Hamiltonian_generator'])
        form = decode(old['nondegenerate_phase_form'])
        equal(active.H*form+form*active, s.zeros(*form.shape))
        assert active.rows == active.cols == old['dynamic_quotient_dimension']
        momentum = list(map(s.sympify, old['momentum']))
        tail = model.tail_generator(momentum)
        dimension = active.rows+tail.rows
        rows.append({'momentum': old['momentum'], 'active_phase_dimension': active.rows,
                     'scalar_phase_dimension': blocks['scalar'].rows,
                     'complete_matter_complement_real_phase_dimension': blocks['dual'].rows+blocks['primal'].rows,
                     'full_phase_dimension': dimension,
                     'actual_tail_generator_shape': list(tail.shape),
                     'actual_tail_generator_nonzero_entries': len(tail.todok()),
                     'full_generator': 'diag(original_retained_Hamiltonian_generator,actual_tail_generator)',
                     'characteristic_factorization': 'det(lambda-A_full)=det(lambda-A_active)*det(lambda-A_dual_C)*det(lambda-A_scalar61)*det(lambda-A_primal_C)',
                     'scope': 'The two already generated source momenta; no new uniform active-phase rank claim. At nonzero k this is a complex Fourier fiber of real fields, paired with its conjugate at -k; it is not the real dimension of an independent +/-k pair.'})
    return rows


def verify_source_inputs(model):
    records = [model.active, model.occupied, model.vertices, model.phase, model.scalar_record,
               json.loads((HERE/'retained_hamiltonian_reduction.json').read_bytes())]
    checked = set()
    for record in records:
        for group in ('source_sha256', 'input_sha256'):
            for name, digest in record.get(group, {}).items():
                if (name, digest) in checked:
                    continue
                assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
                checked.add((name, digest))
    return len(checked)


def main():
    started = time.monotonic()
    model = SourceFullLinearSplit()
    bindings = verify_source_inputs(model)
    inventory = model.inventory()
    print('PASS actual158 vertices and all incoming coefficients; nonzero scalar/complement cross retained', flush=True)
    scalar = model.scalar_symbol()
    active = model.active_matter_and_scalar_readback(scalar)
    print('PASS raw full70 scalar split and original289 matter/scalar/mixed legs', flush=True)
    blocks = model.tail_blocks()
    print('PASS original dual240 -> scalar61 -> primal240 equations and nonzero third-time response', flush=True)
    common = model.complete_action_split(active, scalar)
    print('PASS explicit original1310 common carrier and full raw Jacobi congruence', flush=True)
    phases = phase_inventory(model, blocks)
    print('PASS actual catalog phase inventories', [row['full_phase_dimension'] for row in phases], flush=True)
    inputs = [HERE/'source_full_linear_split.py', HERE/'source_common_hamiltonian.py', HERE/'scalar_canonical_phase.json',
              HERE/'retained_hamiltonian_reduction.json', HERE/'independent_retained_hamiltonian_reduction.json',
              BASE/'active-gauge/receipt.json', BASE/'occupied-response/receipt.json', BASE/'full-phase/receipt.json',
              BASE/'matter-vertices/receipt.json', BASE/'scalar-exchange/receipt.json']
    output = {'root': ROOT_ID, 'source_sha256': model.vertices['source_sha256'],
              'original_input_binding_checks': bindings,
              'verdict': 'COMPLETE_SOURCE_LINEAR_SPLIT_WITH_SCALAR_COMPLEMENT_TRIANGULAR_RESPONSE',
              'source_inventory': inventory,
              'scalar_active9_frame': encode(model.J), 'scalar_peripheral61_frame': encode(model.R),
              'full_scalar_operator': encode(scalar),
              'active289_full252_and_scalar70_restriction_exact': True,
              'complete_common_action_carrier': common,
              'Jacobi_field_partition': {'active': active.rows, 'peripheral_scalar': model.R.cols,
                                        'matter_complement_real': 4*model.C.cols,
                                        'whole_original_real_fields': active.rows+model.R.cols+4*model.C.cols},
              'triangular_tail': {name: encode(blocks[name]) for name in
                    ('dual', 'scalar', 'primal', 'dual_to_scalar', 'scalar_to_primal', 'third_time_cascade')},
              'tail_state_order': 'independent_dual_complement_real480, canonical_scalar122, primal_complement_real480',
              'Fourier_reality': 'Each generator obeys conjugate(A(k))=A(-k). The480+122+480 counts are complex fiber dimensions for nonzero k; zero momentum is directly real. Internal complex coefficients were realified before substituting spatial derivatives i*k.',
              'realifying_after_Fourier_negative_control_nonzero': True,
              'all_time_linear_response': 'dual evolves by exp(t Ad); scalar receives its original B through ordered Duhamel integration; primal receives that scalar through C. The two nested ordered integrals solve the displayed exact triangular source equations, with no feedback block removed.',
              'actual_phase_inventory_at_source_momenta': phases,
              'background_linearization_scope': 'The full scalar primitive does not preserve occupied12. This source-point Jacobi splitting retains the actual nonzero cross; it is not an interacting spectrum or a new invariant sector of the nonlinear action.',
              'proper_clock': 'tau=N*t unchanged; matter coefficients retain the certified stationary phase transform, and the original Dirac/phase operators preserve the same projector.',
              'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
              'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in inputs},
              'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_full_linear_split.json').write_text(json.dumps(output, indent=2)+'\n')


if __name__ == '__main__':
    main()
