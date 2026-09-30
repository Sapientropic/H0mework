#!/usr/bin/env python3
"""Retarded response on the actual original source spatial physical phase.

Only certified source matrices and inverse recipes are consumed. Ambient
forcing is projected explicitly; the strict response mouth requires the
original constrained source tangent, and the initial distribution is delta*T.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import json
from pathlib import Path
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from source_spatial_active_phase_splice import dm, mul, field_element, DOMAIN
from source_full_linear_split import HERE, ROOT, ROOT_ID, K, decode, assemble
from source_stabilizer_phase_reduction import canonical_J
from source_lorentz_contact import clean, equal, encode


def zero(A): equal(clean(A), s.zeros(*A.shape))


@lru_cache(maxsize=None)
def read_bound(name):
    path = HERE/name
    record = json.loads(path.read_text())
    assert record['root'] == ROOT_ID
    for group in ('source_sha256', 'input_sha256'):
        for source, expected in record.get(group, {}).items():
            assert hashlib.sha256((ROOT/source).read_bytes()).hexdigest() == expected, source
    return record


@lru_cache(maxsize=2)
def load_common_fiber(sign=1):
    """Actual sparse source factors at either already certified nonzero fiber."""
    assert sign in (-1, 1)
    splice = read_bound('source_spatial_active_phase_splice.json')
    certified = read_bound('independent_source_spatial_active_phase_splice.json')
    assert certified['verdict'] == 'CERTIFIED_ACTUAL_NONZERO_PAIRED_MOMENTUM_SOURCE_COMMON_PHASE_AND_ORIGINAL_INTERTWINING'
    assert certified['source_sha256'] == splice['source_sha256']
    phase = read_bound('source_physical_phase_splice.json')
    read_bound('independent_source_physical_phase_splice.json')
    retained = read_bound('retained_hamiltonian_reduction.json')
    tail_record = read_bound('source_full_linear_split.json')
    data = splice['fibers'][0 if sign == 1 else 1]
    momentum = tuple(map(s.sympify, data['momentum']))
    reference = next(row for row in retained['source_momenta'] if any(s.sympify(k) != 0 for k in row['momentum']))
    original = lambda key: decode(reference[key]) if sign == 1 else clean(decode(reference[key]).conjugate())
    active_X, active_R = decode(data['active_embedding']), decode(data['active_reader'])
    tail_X = mul(decode(phase['original_nonlinear_chart_tangent']), decode(phase['tail_embedding_into_actual1208']))
    tail_omega = decode(phase['tail_original_symplectic_form'])
    entries = tail_omega.todok()
    assert len(entries) == tail_omega.rows == len({i for i, _ in entries}) == len({j for _, j in entries})
    inverse = s.SparseMatrix(tail_omega.rows, tail_omega.cols, {(j, i): 1/value for (i, j), value in entries.items()})
    J = canonical_J(active_X.rows//2)
    tail_R = -mul(inverse, tail_X.T, J)
    X, R = clean(active_X.row_join(tail_X)), clean(active_R.col_join(tail_R))
    T = mul(X, R)
    equal(mul(R, X), s.eye(X.cols)); equal(mul(T, X), X)
    at = lambda A: clean(dm(A.subs(dict(zip(K, momentum)))).to_Matrix())
    blocks = {key: at(decode(value)) for key, value in tail_record['triangular_tail'].items()}
    d, scalar, p = blocks['dual'], blocks['scalar'], blocks['primal']
    tail_A = assemble(d.rows+scalar.rows+p.rows, d.rows+scalar.rows+p.rows,
        [(0, 0, d), (d.rows, d.rows, scalar), (d.rows+scalar.rows, d.rows+scalar.rows, p),
         (d.rows, 0, blocks['dual_to_scalar']), (d.rows+scalar.rows, d.rows, blocks['scalar_to_primal'])])
    tail_H = at(decode(phase['original_tail_Hamiltonian']['original_density_Hamiltonian_hessian']))
    active_A, active_H = original('Hamiltonian_generator'), original('Hamiltonian_energy')
    split_A, split_H = s.diag(active_A, tail_A), s.diag(active_H, tail_H)
    split_omega = s.diag(original('nondegenerate_phase_form'), tail_omega)
    equal(mul(split_omega, split_A), split_H)
    paths = [HERE/name for name in ('source_spatial_active_phase_splice.py', 'source_spatial_active_phase_splice.json',
        'independent_source_spatial_active_phase_splice.json', 'source_physical_phase_splice.json',
        'independent_source_physical_phase_splice.json', 'retained_hamiltonian_reduction.json',
        'source_full_linear_split.json', 'source_stationary_cauchy_orbit.json')]
    return {'sign': sign, 'k': momentum, 'X': X, 'R': R, 'T': T, 'J': J,
        'active_A': active_A, 'active_H': active_H, 'tail_A': tail_A, 'tail_H': tail_H,
        'A_split': split_A, 'H_split': split_H, 'Omega_split': split_omega,
        'active_dimension': active_A.rows, 'tail_dimensions': (d.rows, scalar.rows, p.rows),
        'tail_blocks': blocks, 'source_sha256': splice['source_sha256'], 'input_paths': paths}

from source_full_linear_retarded import Z, decode as laplace_decode, coefficient_conjugate

LAPLACE_FIELD = DOMAIN.frac_field(Z)


@lru_cache(maxsize=65536)
def laplace_element(value):
    value = s.sympify(value)
    if value == Z: return LAPLACE_FIELD.gens[0]
    if not value.has(Z): return LAPLACE_FIELD.convert(field_element(value), DOMAIN)
    if value.is_Add:
        return sum((laplace_element(v) for v in value.args), LAPLACE_FIELD.zero)
    if value.is_Mul:
        result = LAPLACE_FIELD.one
        for v in value.args: result *= laplace_element(v)
        return result
    if value.is_Pow and value.exp.is_Integer:
        return laplace_element(value.base)**int(value.exp)
    raise ValueError('The generated Laplace expression must be rational over the original source field.')


def in_domain(matrix, domain):
    if isinstance(matrix, DM): return matrix.convert_to(domain)
    if domain == DOMAIN: return dm(matrix)
    entries = {}
    for (i, j), value in s.SparseMatrix(matrix).todok().items():
        element = laplace_element(value)
        if element: entries.setdefault(i, {})[j] = element
    return DM(entries, matrix.shape, domain).to_sparse()


def stack(blocks):
    return DM.vstack(*blocks)


def source_rows(blocks, groups, shape, domain):
    rows = {}
    for block, indices in zip(blocks, groups):
        for local, row in block.to_sparse().rep.items(): rows[indices[local]] = dict(row)
    return DM(rows, shape, domain).to_sparse()


def scalar_polynomial(coefficients, z, domain):
    result = domain.zero
    for coefficient in coefficients:
        result = result*z+domain.convert(coefficient, DOMAIN)
    return result


class FrozenActiveResolvent:
    def __init__(self, fiber):
        record = read_bound('source_active_retarded_inverse.json')
        certified = read_bound('independent_source_active_retarded_inverse.json')
        assert certified['source_sha256'] == record['source_sha256'] == fiber['source_sha256']
        source = next(row for row in record['source_fibres'] if any(s.sympify(k) != 0 for k in row['momentum']))
        self.source = source
        self.sign = fiber['sign']; self.A = dm(fiber['active_A'])
        self.groups = source['source_topological_SCCs']
        self.coefficients = []
        for expression in source['leaf_characteristic_polynomials']:
            polynomial = s.Poly(s.sympify(expression, locals={str(Z): Z}), Z)
            coefficients = polynomial.all_coeffs()
            if self.sign == -1: coefficients = [s.conjugate(c) for c in coefficients]
            self.coefficients.append([field_element(c) for c in coefficients])
        self.feeds = {}
        for feed in source['source_DAG_feeds']:
            matrix = decode(feed['matrix'])
            if self.sign == -1: matrix = matrix.conjugate()
            key = feed['target'], feed['source']
            self.feeds[key] = dm(matrix)
            assert (self.feeds[key]-self.A.extract(self.groups[key[0]], self.groups[key[1]])).is_zero_matrix
            assert key[1] < key[0]
        for group, coefficients in zip(self.groups, self.coefficients):
            assert len(coefficients) == len(group)+1 and coefficients[0] == DOMAIN.one
        self.bounds = source['actual_consumer']['source_norm_bound']

    def apply(self, forcing, z, domain):
        forcing = forcing.convert_to(domain)
        result = []
        for index, (group, coefficients) in enumerate(zip(self.groups, self.coefficients)):
            rhs = forcing.extract(group, range(forcing.shape[1]))
            for (target, source), feed in self.feeds.items():
                if target == index: rhs += feed.convert_to(domain)*result[source]
            A = self.A.extract(group, group).convert_to(domain)
            current = numerator = rhs
            for c in coefficients[1:-1]:
                current = A*current+rhs.scalarmul(domain.convert(c, DOMAIN))
                numerator = numerator.scalarmul(z)+current
            denominator = scalar_polynomial(coefficients, z, domain)
            if denominator == domain.zero:
                raise ValueError('The chosen Laplace point is a generated source pole.')
            result.append(numerator.scalarmul(domain.one/denominator))
        return source_rows(result, self.groups, forcing.shape, domain)


class FrozenMatterResolvent:
    def __init__(self, record, momentum):
        self.groups = [row['indices'] for row in record['source_components']]
        self.leaf_of_group = [row['inverse_leaf'] for row in record['source_components']]
        self.n = record['complex_dimension']; self.k = momentum
        self.leaves = [(laplace_decode(row['numerator']), s.sympify(row['denominator'], locals={str(Z): Z, **dict(zip(map(str, K), K))}))
                       for row in record['exact_inverse_leaves']]
        self.off = laplace_decode(record['original_between_block_Yukawa'])
        assert record['source_and_target_block_sets_disjoint']
        self.cache = {}

    def diagonal_apply(self, forcing, laplace, domain, conjugate_branch):
        output = []
        for group, index in zip(self.groups, self.leaf_of_group):
            key = (index, str(laplace), str(domain), conjugate_branch)
            if key not in self.cache:
                numerator, denominator = self.leaves[index]
                if conjugate_branch:
                    numerator = coefficient_conjugate(numerator).subs(dict(zip(K, [-k for k in K])), simultaneous=True)
                    denominator = s.conjugate(denominator).xreplace({s.conjugate(Z): Z}).subs(dict(zip(K, [-k for k in K])), simultaneous=True)
                point = dict(zip(K, self.k))
                if laplace is not None: point[Z] = laplace
                den = denominator.subs(point)
                value = field_element(den) if domain == DOMAIN else laplace_element(den)
                if value == domain.zero: raise ValueError('The chosen source matter pole has no inverse.')
                self.cache[key] = in_domain(numerator.subs(point), domain).scalarmul(domain.one/value)
            output.append(self.cache[key]*forcing.extract(group, range(forcing.shape[1])))
        return source_rows(output, self.groups, forcing.shape, domain)

    def complex_apply(self, forcing, laplace, domain, conjugate_branch):
        first = self.diagonal_apply(forcing, laplace, domain, conjugate_branch)
        off = self.off.conjugate() if conjugate_branch else self.off
        return first+self.diagonal_apply(in_domain(off, domain)*first, laplace, domain, conjugate_branch)

    def real_apply(self, forcing, laplace, domain):
        real = forcing.extract(range(self.n), range(forcing.shape[1]))
        imaginary = forcing.extract(range(self.n, 2*self.n), range(forcing.shape[1]))
        i = domain.convert(field_element(s.I), DOMAIN)
        plus = self.complex_apply(real+imaginary.scalarmul(i), laplace, domain, False)
        minus = self.complex_apply(real-imaginary.scalarmul(i), laplace, domain, True)
        return stack([(plus+minus).scalarmul(domain.one/2), (plus-minus).scalarmul(domain.one/(2*i))])


class FrozenTailResolvent:
    def __init__(self, fiber):
        record = read_bound('source_full_linear_retarded.json')
        certified = read_bound('independent_source_full_linear_retarded.json')
        assert record['source_sha256'] == certified['source_sha256'] == fiber['source_sha256']
        self.k = fiber['k']; self.fiber = fiber; self.record = record
        self.dual = FrozenMatterResolvent(record['dual_inverse'], self.k)
        self.primal = FrozenMatterResolvent(record['primal_inverse'], self.k)
        self.B = dm(fiber['tail_blocks']['dual_to_scalar'])
        self.C = dm(fiber['tail_blocks']['scalar_to_primal'])
        scalar = read_bound('scalar_canonical_phase.json')
        self.N = field_element(s.sympify(scalar['source_lapse']))
        self.scalar_R = dm(laplace_decode(scalar['scalar_coordinate_embedding']))
        self.gram = self.scalar_R.transpose()*self.scalar_R
        self.gram_inverse = self.gram.inv()
        self.scalar_L = dm(fiber['tail_blocks']['scalar'][61:, :61]).scalarmul(DOMAIN.one/self.N)
        self.numerator70 = laplace_decode(scalar['original_Green_numerator'])
        self.denominator = s.sympify(scalar['original_Green_denominator'].replace('lambda', str(Z)),
                                    locals={str(Z): Z, **dict(zip(map(str, K), K))})
        self.scalar_cache = {}

    def scalar_apply(self, forcing, laplace, z, domain):
        key = (str(laplace), str(domain))
        N = domain.convert(self.N, DOMAIN)
        if key not in self.scalar_cache:
            point = dict(zip(K, self.k))
            if laplace is not None: point[Z] = laplace
            raw = in_domain(self.numerator70.subs(point), domain)
            R, Gi = self.scalar_R.convert_to(domain), self.gram_inverse.convert_to(domain)
            Q = (Gi*R.transpose()*raw*R).scalarmul(domain.one/N)
            den = self.denominator.subs(point)
            denominator = field_element(den) if domain == DOMAIN else laplace_element(den)
            if denominator == domain.zero: raise ValueError('The chosen source scalar pole has no inverse.')
            self.scalar_cache[key] = Q.scalarmul(domain.one/denominator)
        Q = self.scalar_cache[key]
        fq, fp = forcing.extract(range(61), range(forcing.shape[1])), forcing.extract(range(61, 122), range(forcing.shape[1]))
        G, Gi, L = self.gram.convert_to(domain), self.gram_inverse.convert_to(domain), self.scalar_L.convert_to(domain)
        q = Q*(fq.scalarmul(z)-(Gi*fp).scalarmul(N))
        p = (L*Q*fq).scalarmul(N)+(G*Q*Gi*fp).scalarmul(z)
        return stack([q, p])

    def apply(self, forcing, laplace, z, domain):
        fd = forcing.extract(range(480), range(forcing.shape[1]))
        fs = forcing.extract(range(480, 602), range(forcing.shape[1]))
        fp = forcing.extract(range(602, 1082), range(forcing.shape[1]))
        dual = self.dual.real_apply(fd, laplace, domain)
        scalar = self.scalar_apply(fs+self.B.convert_to(domain)*dual, laplace, z, domain)
        primal = self.primal.real_apply(fp+self.C.convert_to(domain)*scalar, laplace, domain)
        return stack([dual, scalar, primal])


class SourceCommonRetardedPhase:
    def __init__(self, sign=1):
        self.fiber = load_common_fiber(sign)
        self.X, self.R, self.T = [dm(self.fiber[key]) for key in ('X', 'R', 'T')]
        self.A = dm(self.fiber['A_split'])
        self.active = FrozenActiveResolvent(self.fiber)
        self.tail = FrozenTailResolvent(self.fiber)
        self.beta_active = s.sympify(self.active.bounds['beta'])
        self.beta_tail = s.sympify(self.tail.record['global_bounds']['beta'])
        self.beta = s.Max(self.beta_active, self.beta_tail)

    def generator_action(self, vector):
        if not isinstance(vector, DM): vector = dm(vector)
        domain = vector.domain
        return self.X.convert_to(domain)*(self.A.convert_to(domain)*(self.R.convert_to(domain)*vector))

    def projected_resolvent(self, ambient_forcing, laplace=None):
        """Return both the admitted T f and its response; no silent admission.

        laplace=None gives the exact rational action over the source K(z).
        At an algebraic Laplace value the result stays in the source field.
        """
        domain = LAPLACE_FIELD if laplace is None else DOMAIN
        z = LAPLACE_FIELD.gens[0] if laplace is None else field_element(laplace)
        forcing = in_domain(ambient_forcing, domain)
        R, X = self.R.convert_to(domain), self.X.convert_to(domain)
        split = R*forcing
        n = self.fiber['active_dimension']
        active = self.active.apply(split.extract(range(n), range(split.shape[1])), z, domain)
        tail = self.tail.apply(split.extract(range(n, split.shape[0]), range(split.shape[1])), laplace, z, domain)
        return {'admitted_forcing': X*split, 'response': X*stack([active, tail]),
                'split_response': stack([active, tail]), 'projection_defect': forcing-X*split}

    def resolvent(self, compatible_forcing, laplace=None):
        result = self.projected_resolvent(compatible_forcing, laplace)
        if not result['projection_defect'].is_zero_matrix:
            raise ValueError('This source forcing is outside range T; use projected_resolvent to read its explicit admitted projection.')
        return result['response']


def selected_values(vector, count=8):
    nonzero = sorted(vector.rep)
    rows = sorted(set([0, vector.shape[0]-1, *nonzero[:count], *nonzero[-count:]]))
    return {'rows': rows, 'values': encode(vector.extract(rows, [0]).to_Matrix()),
            'whole_vector_dimension': vector.shape[0]}


def actual_consumer(sign):
    model = SourceCommonRetardedPhase(sign); fiber = model.fiber
    n = model.T.shape[0]
    seed = s.Matrix([s.Rational((7*j+2)%17-8, 31)+s.I*s.Rational((11*j+3)%19-9, 37) for j in range(n)])
    if sign == -1: seed = seed.conjugate()
    ambient = dm(seed); forcing = model.T*ambient
    assert not (ambient-forcing).is_zero_matrix
    z = s.Integer(model.active.bounds['integer_upper'])+1+sign*s.I
    assert s.simplify(s.re(z)-model.beta_active) > 0 and s.simplify(s.re(z)-model.beta_tail) > 0
    response = model.resolvent(forcing, z)
    zz = field_element(z)
    assert (response.scalarmul(zz)-model.generator_action(response)-forcing).is_zero_matrix
    assert (model.T*response-response).is_zero_matrix
    projected = model.projected_resolvent(ambient.scalarmul(zz)-model.generator_action(ambient), z)
    assert (projected['response']-forcing).is_zero_matrix
    try:
        model.resolvent(ambient, z)
    except ValueError as error:
        assert 'outside range T' in str(error)
    else:
        raise AssertionError('The strict forcing consumer silently admitted an incompatible source.')
    override = model.projected_resolvent(ambient, z)
    assert (override['admitted_forcing']-forcing).is_zero_matrix
    assert (override['response']-response).is_zero_matrix
    print('PASS complete physical forcing, both projected inverse orientations and explicit incompatible-forcing control', fiber['k'], flush=True)
    # Consume the original nonzero dual->scalar->primal response within the
    # complete same-source carrier, without replacing the full tail inverse.
    witness = model.tail.record['actual_two_stage_time_consumer']
    column = witness['dual_initial_coordinate']; total = model.A.shape[0]
    dual = DM({fiber['active_dimension']+column: {0: DOMAIN.one}}, (total, 1), DOMAIN)
    physical_dual = model.X*dual
    cascade = model.resolvent(physical_dual, z)
    split_cascade = model.R*cascade
    base = fiber['active_dimension']
    assert not split_cascade.extract(range(base+480, base+602), [0]).is_zero_matrix
    assert not split_cascade.extract(range(base+602, total), [0]).is_zero_matrix
    assert (cascade.scalarmul(zz)-model.generator_action(cascade)-physical_dual).is_zero_matrix
    # The jump and each source kernel are exact on every column, not inferred
    # from the displayed forcing. The generic inverse identities consume the
    # already paid active/tail mouths and these checked actual X/R products.
    assert (model.R*model.X-DM.eye((model.A.shape[0],)*2, DOMAIN)).is_zero_matrix
    assert (model.X*model.R-model.T).is_zero_matrix
    assert (model.T*model.T-model.T).is_zero_matrix
    assert (model.T*model.X-model.X).is_zero_matrix
    assert (model.R*model.T-model.R).is_zero_matrix
    print('PASS same physical initial jump T, whole-source two-stage response and all-column projector factors', flush=True)
    result = {'momentum': list(map(str, fiber['k'])), 'laplace': str(z),
        'source_active_beta': str(model.beta_active), 'source_tail_beta': str(model.beta_tail),
        'common_safe_halfplane': 'Re(z)>'+str(model.beta),
        'ambient_forcing_recipe': 'u_j=((7j+2) mod17-8)/31+i*((11j+3) mod19-9)/37; minus partner conjugates this whole real-field Fourier amplitude',
        'compatible_forcing_recipe': 'f=T(k) u, generated by the same certified source projection',
        'response_readout': selected_values(response), 'whole1214_left_and_right_projected_residuals_zero': True,
        'strict_incompatible_forcing_rejected': True, 'explicit_projection_changes_actual_source': True,
        'whole_response_constraint_TG_checked': True,
        'dual_forcing_coordinate_in_tail': column, 'nonzero_scalar_and_primal_responses': True,
        'two_stage_response_readout': selected_values(cascade), 'all_column_XR_RX_T_identities': True}
    return result, response, cascade, model


def main():
    started = time.monotonic()
    positive, response_p, cascade_p, model_p = actual_consumer(1)
    negative, response_m, cascade_m, model_m = actual_consumer(-1)
    zero(response_m.to_Matrix()-response_p.to_Matrix().conjugate())
    zero(cascade_m.to_Matrix()-cascade_p.to_Matrix().conjugate())
    print('PASS complete physical retarded response and original dual cascade obey the actual opposite-momentum reality', flush=True)
    paths = [Path(__file__), HERE/'source_spatial_active_phase_splice.py',
        HERE/'source_active_retarded_inverse.py', HERE/'source_active_retarded_inverse.json',
        HERE/'independent_source_active_retarded_inverse.json', HERE/'source_full_linear_retarded.py',
        HERE/'source_full_linear_retarded.json', HERE/'independent_source_full_linear_retarded.json',
        HERE/'scalar_canonical_phase.json', HERE/'CayleyHamiltonRetarded.lean']+model_p.fiber['input_paths']
    result = {'root': ROOT_ID, 'source_sha256': model_p.fiber['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest() for path in paths},
        'scope': 'SOURCE_COMMON_PHYSICAL_RETARDED_RESPONSE_AND_PROJECTED_INITIAL_DISTRIBUTION_ON_SIGNED_NONZERO_FIBERS',
        'public_API': {'load_common_fiber': 'load_common_fiber(sign) gives actual sparse X,R,T,Asplit,Hsplit,original source metadata without any new charpoly or whole symbolic projector reconstruction',
            'resolvent': 'SourceCommonRetardedPhase(sign).resolvent(f,z) requires T f=f; z=None evaluates the exact source rational function over K(z)',
            'projected_resolvent': 'Explicitly returns admitted_forcing=T u, response=G u and projection_defect=u-T u for an ambient input'},
        'generic_physical_inverse': {'G': 'X diag(Gactive,Gtail) R', 'A': 'X diag(Aactive,Atail) R',
            'paid_inputs': 'Generated active SCC synthetic Cayley-Hamilton inverse and complete1082 triangular source inverse; source X/R with RX=I and XR=T.',
            'two_sided': '(z I1214-A)G=G(z I1214-A)=T; T G=G T=G',
            'algebra': 'Move (zI-A) through X or R using RX=I, apply each paid block inverse, then consume XR=T. Both orders use the actual same-source factors.'},
        'retarded_distribution': {'ordinary_positive_time': 'U(t)=X diag(exp(t Aactive),exp(t Atail)) R for t>0',
            'zero_past': 'U_ret(t)=0 for t<0', 'initial_right_limit_and_jump': 'U(0+)=XR=T',
            'equation': '(partial_t-A)U_ret=delta(t)T',
            'forcing_responsibility': 'An ambient f produces T f. The original f itself is recovered only for f in range T; the strict API rejects other inputs and the explicit projection API records the changed source.',
            'actual_onshell_current_to_phase_forcing_installed': False,
            'same_original_orbit': 'This is the stationary representation of the already certified actual Cauchy phase orbit. Original-time response needs the two original canonical phase endpoints; no clock reparametrization or static state interpretation is introduced.'},
        'common_convergence': {'halfplane': 'Re(z)>max(beta_active,153sqrt30/625) at each signed source momentum',
            'bound': 'The actual X/R contribute finite source matrix factors. The paid active exp(beta_active*t) bound and the paid tail exp(beta_tail*t) times its degree2 source polynomial give absolute Laplace convergence on the stated common half-plane.',
            'initial_projector_is_not_I1214': True},
        'actual_consumers': [positive, negative], 'minus_momentum_conjugate_laplace_response_checked': True,
        'whole1082_scalar_dual_cross_or_growth_modes_removed': False,
        'interacting_composite_measure_or_proton_lifetime_generated': False,
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED', 'elapsed_seconds': round(time.monotonic()-started, 3)}
    (HERE/'source_common_retarded_phase.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS same-source common physical retarded phase', result['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__': main()
