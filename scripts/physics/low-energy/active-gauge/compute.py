#!/usr/bin/env python3
"""Exact second jet of the original, unreduced active Dirac-dual action.

All 289 real primitive coordinates remain independent. Derivative coordinates
are generated for A, omega, the scalar and primal matter. The dual is genuinely
independent, with no complex conjugation inserted into its pairing.

This finite source-coordinate calculation is not a Lean identification theorem,
a gauge quotient, or a determination of physical poles.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from dataclasses import dataclass
from functools import lru_cache
import importlib.util
import hashlib
import itertools
import json
from pathlib import Path
import sys
import time

import sympy as s

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
sys.path.insert(0, str(HERE.parent / 'nonlinear-contact'))
import exact_readout as source
from slice_checks import PAIRS, ETA, J, W, GAMMA, COLOR, source_matrices, wedge_matrix

spec = importlib.util.spec_from_file_location('source_active_carrier', HERE.parent / 'active-sector/compute.py')
active = importlib.util.module_from_spec(spec)
spec.loader.exec_module(active)

F = s.QQ.algebraic_field(s.sqrt(2), s.sqrt(15))


@dataclass(frozen=True)
class Number:
    real: object
    imag: object

    def __add__(self, other):
        other = number(other)
        return Number(self.real + other.real, self.imag + other.imag)

    __radd__ = __add__

    def __neg__(self):
        return Number(-self.real, -self.imag)

    def __sub__(self, other):
        return self + -number(other)

    def __mul__(self, other):
        other = number(other)
        if not self.imag and not other.imag:
            return Number(self.real * other.real, F.zero)
        return Number(self.real * other.real - self.imag * other.imag,
                      self.real * other.imag + self.imag * other.real)

    __rmul__ = __mul__

    def __bool__(self):
        return bool(self.real or self.imag)

    def real_part(self):
        return Number(self.real, F.zero)


@lru_cache(None)
def number(value):
    if isinstance(value, Number):
        return value
    value = s.sympify(value)
    return Number(F.from_sympy(s.re(value)), F.from_sympy(s.im(value)))


ZERO, ONE = number(0), number(1)


class Jet:
    """The degree <= 2 quotient of the real first-jet polynomial algebra."""
    __slots__ = ('terms',)

    def __init__(self, terms=None):
        self.terms = {key: value for key, value in (terms or {}).items() if value}

    @staticmethod
    def cast(value):
        return value if isinstance(value, Jet) else Jet({(): number(value)})

    @staticmethod
    def variable(index):
        return Jet({(index,): ONE})

    def __add__(self, other):
        terms = self.terms.copy()
        for key, value in Jet.cast(other).terms.items():
            terms[key] = terms.get(key, ZERO) + value
        return Jet(terms)

    __radd__ = __add__

    def __neg__(self):
        return Jet({key: -value for key, value in self.terms.items()})

    def __sub__(self, other):
        return self + -Jet.cast(other)

    def __rsub__(self, other):
        return Jet.cast(other) + -self

    def __mul__(self, other):
        terms = {}
        for left, a in self.terms.items():
            for right, b in Jet.cast(other).terms.items():
                if len(left) + len(right) <= 2:
                    key = tuple(sorted(left + right))
                    terms[key] = terms.get(key, ZERO) + a * b
        return Jet(terms)

    __rmul__ = __mul__

    def __bool__(self):
        return bool(self.terms)

    def real_part(self):
        return Jet({key: value.real_part() for key, value in self.terms.items()})

    def grade(self, degree):
        return Jet({key: value for key, value in self.terms.items() if len(key) == degree})


def matrix(rows, cols, entry):
    return [[Jet.cast(entry(i, j)) for j in range(cols)] for i in range(rows)]


def fixed(m):
    return matrix(m.rows, m.cols, lambda i, j: m[i, j])


def add(a, b):
    return [[x+y for x, y in zip(ar, br)] for ar, br in zip(a, b)]


def scale(c, a):
    return [[x*c for x in row] for row in a]


def transpose(a):
    return list(map(list, zip(*a)))


def multiply(a, b):
    rows = [[(j, value) for j, value in enumerate(row) if value] for row in b]
    out = matrix(len(a), len(b[0]), lambda i, j: 0)
    for i, row in enumerate(a):
        for k, value in enumerate(row):
            if value:
                for j, other in rows[k]:
                    out[i][j] = out[i][j] + value*other
    return out


def constant_part(a):
    return [[x.grade(0) for x in row] for row in a]


def grade(a, degree):
    return [[x.grade(degree) for x in row] for row in a]


def wedge(e):
    return matrix(6, 6, lambda i, j:
        e[PAIRS[i][0]][PAIRS[j][0]]*e[PAIRS[i][1]][PAIRS[j][1]] -
        e[PAIRS[i][0]][PAIRS[j][1]]*e[PAIRS[i][1]][PAIRS[j][0]])


def inverse_second_jet(a, constant_inverse):
    u = fixed(constant_inverse)
    b, c = grade(a, 1), grade(a, 2)
    ub = multiply(u, b)
    return add(add(u, scale(-1, multiply(ub, u))),
               add(multiply(multiply(ub, ub), u), scale(-1, multiply(multiply(u, c), u))))


def determinant(a):
    n = len(a)
    result = Jet()
    for permutation in itertools.permutations(range(n)):
        value = Jet.cast(source.sign(permutation))
        for i, j in enumerate(permutation):
            value = value*a[i][j]
        result = result+value
    return result


def adjugate(a):
    return matrix(len(a), len(a), lambda mu, internal:
        (-1)**(mu+internal)*determinant(
            [[a[i][j] for j in range(len(a)) if j != mu] for i in range(len(a)) if i != internal]))


class Coordinates:
    def __init__(self):
        self.fields = []
        self.groups = {}
        self.jets = []
        self.jet_indices = {}

    def group(self, name, shape):
        entries = {}
        for coordinates in itertools.product(*(range(n) for n in shape)):
            index = len(self.fields)
            self.fields.append({'group': name, 'coordinate': list(coordinates)})
            entries[coordinates] = index
        self.groups[name] = entries
        return entries

    def value(self, group, *coordinates, derivative=-1):
        field = self.groups[group][coordinates]
        key = (field, derivative)
        if key not in self.jet_indices:
            self.jet_indices[key] = len(self.jets)
            self.jets.append(key)
        return Jet.variable(self.jet_indices[key])


def build(root):
    source_matrices(root)
    names, vacuum, degrees, hashes = source.parse_source(root)
    core = root/'Lean/SaturationMonoid/PhysicsCore'
    for filename in ['StageNineDiracDualFormNativeMotherAction.lean', 'StageNineDiracKineticLocalSpinDensity.lean',
                     'StageNineMatterCovariantDerivativeAffine.lean', 'DiracExteriorMatterAction.lean',
                     'DiracCliffordRepresentation.lean', 'RawLorentzianMetricHodgeRecovery.lean',
                     'ProofFreeRicherAnholonomicSource.lean', 'StageNineTopologicalFourFormPairing.lean',
                     'StageNineTopologicalGravityCurvatureVariancePairing.lean', 'StageNineLorentzConnectionVariation.lean',
                     'Stage9C/Material/SpinPair/Actual.lean', 'Stage9C/Material/SpinPair/Spinor.lean',
                     'Stage9C/Material/SpinPair/Phase.lean', 'Stage9C/Material/SpinPair/ColorDoublet.lean',
                     'LowEnergy/Evolution/Generator.lean', 'LowEnergy/Evolution/Fields.lean']:
        path = core/filename
        hashes[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
    raw = source.generators([(0, 1, 2), (3, 4)])
    labels = [item[0] for item in raw]
    fundamental = [s.Matrix(m)*(s.I if imaginary else 1) for _, imaginary, m in raw]
    rho4 = [active.realify(active.exterior(t, 4)) for t in fundamental]
    b4 = list(itertools.combinations(range(7), 4))
    vc = s.Matrix([vacuum.get(word, 0) for word in b4])
    v = vc.col_join(s.zeros(35, 1))
    orbit = s.Matrix.hstack(*[a*v for a in rho4])
    pivots = orbit.rref()[1]
    inclusion = orbit[:, list(pivots)]
    assert inclusion.cols == 9
    gram = s.Matrix(12, 12, lambda i, j: s.re(-s.trace(fundamental[i]*fundamental[j])))
    native = gram.copy()
    assert labels[-1] == 'Y' and native[-1, -1] == 2
    native[-1, -1] = 1
    brackets = {}
    inverse_gram = gram.inv()
    for a in range(12):
        for b in range(12):
            commutator = fundamental[a]*fundamental[b]-fundamental[b]*fundamental[a]
            coefficients = inverse_gram*s.Matrix([s.re(-s.trace(t*commutator)) for t in fundamental])
            for c, value in enumerate(coefficients):
                if value:
                    brackets[a, b, c] = value
            assert sum((coefficients[c]*fundamental[c] for c in range(12)), s.zeros(7)) == commutator
    h_actions = [t[:3, :3]+t[5, 5]*s.eye(3) for t in fundamental]
    color_coeff = []
    for small in COLOR:
        t = s.diag(small, s.zeros(5))
        color_coeff.append(inverse_gram*s.Matrix([s.re(-s.trace(g*t)) for g in fundamental]))
    spin, sigma = s.sqrt(2), s.Rational(1, 2)
    n, alpha = 3*s.sqrt(30)/25, 3*s.sqrt(2)/5
    frequency = s.simplify(3*n*(spin-alpha)/2)
    e0 = s.diag(n, 1, 1, 1)
    exterior0 = wedge_matrix(e0)
    hodge0 = exterior0.inv()*J*exterior0
    gamma5 = s.diag(-1, -1, 1, 1)
    # Source phases and their sign are independently checked before co-rotation.
    u = s.symbols('u', nonzero=True)
    rotation = s.diag(u, u, 1/u, 1/u)
    for gamma in GAMMA:
        assert rotation*gamma*rotation == gamma
    for a, b in PAIRS:
        assert rotation*(GAMMA[a]*GAMMA[b]) == (GAMMA[a]*GAMMA[b])*rotation
    rotation_rate = -s.I*frequency*gamma5*rotation
    assert s.I*rotation*GAMMA[0]*rotation_rate == frequency*GAMMA[0]*gamma5

    coordinates = Coordinates()
    for group, shape in [('scalar_J', (9,)), ('gauge_A', (4, 12)), ('coframe', (4, 4)),
                         ('primal_H', (2, 4, 3)), ('dual_H', (2, 4, 3)),
                         ('Lorentz', (4, 6)), ('gravity_B', (6, 6)),
                         ('multiplier', (6, 6)), ('gauge_B', (6, 12))]:
        coordinates.group(group, shape)
    assert len(coordinates.fields) == 289
    q = coordinates.value
    e = matrix(4, 4, lambda i, j: e0[i, j]+q('coframe', i, j))
    exterior = wedge(e)
    hodge = multiply(multiply(inverse_second_jet(exterior, exterior0.inv()), fixed(J)), exterior)
    # A0 is the literal source color SU(2), expanded in the full native P286 basis.
    a0 = s.zeros(4, 12)
    for mu in range(1, 4):
        for c in range(12):
            a0[mu, c] = alpha*color_coeff[mu-1][c]
    connection = matrix(4, 12, lambda mu, c: a0[mu, c]+q('gauge_A', mu, c))
    curvature = matrix(6, 12, lambda pair, c:
        q('gauge_A', PAIRS[pair][1], c, derivative=PAIRS[pair][0])-
        q('gauge_A', PAIRS[pair][0], c, derivative=PAIRS[pair][1])+
        sum((connection[PAIRS[pair][0]][a]*connection[PAIRS[pair][1]][b]*value
             for (a, b, out), value in brackets.items() if out == c), Jet()))
    f0 = s.Matrix(6, 12, lambda pair, c: s.simplify(sum(
        (a0[PAIRS[pair][0], a]*a0[PAIRS[pair][1], b]*value
         for (a, b, out), value in brackets.items() if out == c), s.S.Zero)))
    gauge_b0 = -hodge0*f0/sigma
    gauge_b = matrix(6, 12, lambda pair, c: gauge_b0[pair, c]+q('gauge_B', pair, c))
    hodge_b = multiply(hodge, gauge_b)
    gauge_action = Jet()
    for a, b in itertools.product(range(12), repeat=2):
        if native[a, b]:
            for i, j in itertools.product(range(6), repeat=2):
                if W[i, j]:
                    gauge_action += native[a, b]*W[i, j]*(gauge_b[i][a]*curvature[j][b]-
                        sigma/2*gauge_b[i][a]*hodge_b[j][b])
    print('generated gauge BF / coframe constitutive / original background contact', flush=True)

    z = matrix(9, 1, lambda i, j: q('scalar_J', i))
    eta = multiply(fixed(inclusion), z)
    scalar_covariant = []
    for mu in range(4):
        dz = matrix(9, 1, lambda i, j: q('scalar_J', i, derivative=mu))
        # Only the first covariant jet enters the quadratic scalar action because D0 v=0.
        vector = multiply(fixed(inclusion), dz)
        for c in range(12):
            vector = add(vector, multiply(fixed(rho4[c]),
                add(scale(a0[mu, c], eta), scale(q('gauge_A', mu, c), fixed(v)))))
        scalar_covariant.append(vector)
    scalar_action = -n*sum((eta[i][0]*eta[i][0] for i in range(70)), Jet())
    inverse_metric = [-1/n**2, 1, 1, 1]
    for mu in range(4):
        scalar_action += n*s.Rational(1, 2)*inverse_metric[mu]*sum(
            (entry[0]*entry[0] for entry in scalar_covariant[mu]), Jet())
    print('generated scalar J / gauge bidirectional kinetic block', flush=True)

    # The Lorentz primitive consists of lowered antisymmetric internal pairs.
    lorentz_basis = []
    for a, b in PAIRS:
        generator = s.zeros(4)
        generator[a, b], generator[b, a] = ETA[a, a], -ETA[b, b]
        lorentz_basis.append(generator)
    omega0 = s.zeros(4, 6)
    for mu in range(1, 4):
        omega0[mu, mu+2] = spin
    omega = matrix(4, 6, lambda mu, pair: omega0[mu, pair]+q('Lorentz', mu, pair))
    omega_matrix = [sum_matrices([scale(omega[mu][pair], fixed(lorentz_basis[pair]))
                                 for pair in range(6)], 4, 4) for mu in range(4)]
    gravity_curvature = matrix(6, 6, lambda i, j: 0)
    for pair, (mu, nu) in enumerate(PAIRS):
        curvature_matrix = add(multiply(omega_matrix[mu], omega_matrix[nu]),
                               scale(-1, multiply(omega_matrix[nu], omega_matrix[mu])))
        for internal, (a, b) in enumerate(PAIRS):
            gravity_curvature[internal][pair] = (ETA[a, a]*curvature_matrix[a][b]+
                q('Lorentz', nu, internal, derivative=mu)-q('Lorentz', mu, internal, derivative=nu))
    curvature0 = s.Matrix(6, 6, lambda i, j: F.to_sympy(gravity_curvature[i][j].terms.get((), ZERO).real))
    gravity_b0 = J*exterior0
    signs = [-1, -1, -1, 1, 1, 1]
    multiplier0 = J*gravity_b0-s.diag(*signs)*curvature0
    gravity_b = matrix(6, 6, lambda i, j: gravity_b0[i, j]+q('gravity_B', i, j))
    multiplier = matrix(6, 6, lambda i, j: multiplier0[i, j]+q('multiplier', i, j))
    dual_b, simple = multiply(fixed(J), gravity_b), multiply(fixed(J), exterior)
    gravity_action = Jet()
    for internal, i, j in itertools.product(range(6), repeat=3):
        if W[i, j]:
            gravity_action += W[i, j]*(gravity_b[internal][i]*gravity_curvature[internal][j]-
                s.Rational(1, 2)*signs[internal]*gravity_b[internal][i]*dual_b[internal][j]+
                signs[internal]*multiplier[internal][i]*(gravity_b[internal][j]-simple[internal][j]))
    print('generated full gravity BF / simplicity / Lorentz / coframe block', flush=True)

    prepared = s.Matrix([0, 1, 0, -1, 0, 0, 0, 1, 0, -1, 0, 0])
    primal = matrix(12, 1, lambda i, j: prepared[i]+
                    q('primal_H', 0, i//3, i%3)+s.I*q('primal_H', 1, i//3, i%3))
    dual = matrix(1, 12, lambda i, j: spin*prepared[j]+
                  q('dual_H', 0, j//3, j%3)+s.I*q('dual_H', 1, j//3, j%3))
    gamma = [s.kronecker_product(g, s.eye(3)) for g in GAMMA]
    chirality = s.kronecker_product(gamma5, s.eye(3))
    momentum = adjugate(e)
    dirac_action = Jet()
    for mu in range(4):
        connection_matrix = sum_matrices([scale(omega[mu][pair], fixed(s.kronecker_product(
            GAMMA[a]*GAMMA[b]/2, s.eye(3)))) for pair, (a, b) in enumerate(PAIRS)], 12, 12)
        for c in range(12):
            connection_matrix = add(connection_matrix, scale(connection[mu][c],
                fixed(s.kronecker_product(s.eye(4), h_actions[c]))))
        derivative = matrix(12, 1, lambda i, j:
            q('primal_H', 0, i//3, i%3, derivative=mu)+s.I*q('primal_H', 1, i//3, i%3, derivative=mu))
        covariant = add(derivative, multiply(connection_matrix, primal))
        for internal in range(4):
            kinetic = scale(s.I, multiply(fixed(gamma[internal]), covariant))
            if mu == 0:
                kinetic = add(kinetic, scale(frequency, multiply(fixed(gamma[internal]*chirality), primal)))
            dirac_action += momentum[mu][internal]*multiply(dual, kinetic)[0][0].real_part()
    print('generated independent-dual/primal H, gauge, Lorentz and all 16 coframe couplings', flush=True)
    actions = {'gravity': gravity_action, 'gauge': gauge_action, 'scalar': scalar_action, 'Dirac': dirac_action}
    total = sum(actions.values(), Jet())
    assert all(not value.imag for value in total.terms.values())
    # A constant-coefficient first jet has Euler background equal to its undifferentiated linear coefficients.
    unwanted = {coordinates.fields[coordinates.jets[key[0]][0]]['group']+str(coordinates.jets[key[0]]): value
                for key, value in total.terms.items() if len(key) == 1 and coordinates.jets[key[0]][1] == -1}
    assert not unwanted, {key: stringify(value) for key, value in unwanted.items()}
    print('PASS: all 289 original background Euler coordinates vanish without filling target rows', flush=True)
    contact_action = Jet()
    for a, b, i, j in itertools.product(range(12), range(12), range(6), range(6)):
        if native[a, b] and W[i, j] and gauge_b0[i, a]:
            contact_action += native[a, b]*W[i, j]*gauge_b0[i, a]*curvature[j][b].grade(2)
    assert contact_action
    ward_data = {'inclusion': inclusion, 'orbit': orbit, 'a0': a0, 'gauge_b0': gauge_b0,
                 'brackets': brackets, 'h_actions': h_actions, 'prepared': prepared,
                 'n': n, 'spin': spin, 'alpha': alpha, 'sigma': sigma,
                 'color_coeff': color_coeff, 'lorentz_basis': lorentz_basis,
                 'omega0': omega0, 'e0': e0, 'v': v, 'rho4': rho4,
                 'contact_action': contact_action}
    return coordinates, actions, total, ward_data, {'source_sha256': hashes, 'basis_names': names, 'degrees': degrees,
        'native_P286_labels': labels, 'J_independent_columns': list(pivots), 'source_lapse': str(n),
        'source_frequency': str(frequency), 'source_gauge_scale': str(alpha), 'source_coupling': str(sigma)}


def sum_matrices(matrices, rows, cols):
    result = matrix(rows, cols, lambda i, j: 0)
    for value in matrices:
        result = add(result, value)
    return result


@lru_cache(None)
def stringify(value):
    return str(F.to_sympy(value.real)+s.I*F.to_sympy(value.imag))


def fourier_hessian(coordinates, action):
    coefficients = {}
    for key, value in action.terms.items():
        if len(key) != 2:
            continue
        left, right = key
        for row, col in [(left, right), (right, left)]:
            i, a = coordinates.jets[row]
            j, b = coordinates.jets[col]
            power = [0]*4
            if a >= 0:
                power[a] += 1
            if b >= 0:
                power[b] += 1
            index = (i, j, tuple(power))
            coefficients[index] = coefficients.get(index, ZERO)+(-value if a >= 0 else value)
    return {key: value for key, value in coefficients.items() if value}


def ward_check(coordinates, operator, data, require_zero=True):
    """Generate the source's delta A=[X,A]-dX and the other primitive gauge legs."""
    zero_power = (0, 0, 0, 0)
    inclusion, orbit = data['inclusion'], data['orbit']
    orbit_coordinates = (inclusion.T*inclusion).inv()*inclusion.T*orbit
    tangents = {}

    def put(group, index, generator, coefficient, powers=zero_power):
        if coefficient:
            tangents[coordinates.groups[group][index], generator, powers] = number(coefficient)

    for generator in range(12):
        for j in range(9):
            put('scalar_J', (j,), generator, orbit_coordinates[j, generator])
        for mu, c in itertools.product(range(4), range(12)):
            value = sum(data['a0'][mu, b]*data['brackets'].get((generator, b, c), 0) for b in range(12))
            put('gauge_A', (mu, c), generator, value)
            if c == generator:
                power = [0]*4
                power[mu] = 1
                put('gauge_A', (mu, c), generator, -1, tuple(power))
        for pair, c in itertools.product(range(6), range(12)):
            value = sum(data['gauge_b0'][pair, b]*data['brackets'].get((generator, b, c), 0) for b in range(12))
            put('gauge_B', (pair, c), generator, value)
        internal = s.kronecker_product(s.eye(4), data['h_actions'][generator])
        primal = internal*data['prepared']
        dual = -data['spin']*data['prepared'].T*internal
        for index in range(12):
            for part, component in enumerate([s.re, s.im]):
                put('primal_H', (part, index//3, index%3), generator, component(primal[index]))
                put('dual_H', (part, index//3, index%3), generator, component(dual[index]))
    columns = defaultdict(list)
    for (field, generator, power), value in tangents.items():
        columns[field].append((generator, power, value))
    product = {}
    for (i, j, power), coefficient in operator.items():
        for generator, other_power, value in columns[j]:
            index = (i, generator, tuple(a+b for a, b in zip(power, other_power)))
            product[index] = product.get(index, ZERO)+coefficient*value
    product = {key: value for key, value in product.items() if value}
    breaking = -2*data['n']*inclusion.T*orbit
    expected = {(coordinates.groups['scalar_J'][(i,)], j, zero_power): number(breaking[i, j])
                for i, j in itertools.product(range(9), range(12)) if breaking[i, j]}
    difference = {key: product.get(key, ZERO)-expected.get(key, ZERO) for key in product.keys() | expected.keys()}
    if not require_zero:
        assert any(difference.values()), 'Negative control unexpectedly satisfies the original Ward identity'
        return sum(bool(value) for value in difference.values())
    assert not any(difference.values()), [(key, stringify(value)) for key, value in difference.items() if value]
    assert breaking.rank() == 9
    print('PASS: source Ward H(p)T(p) equals exactly the rank-nine fixed-v potential torque; all other rows cancel', flush=True)
    return {'source_primitive_gauge_tangent': [[i, j, list(power), stringify(value)]
                for (i, j, power), value in sorted(tangents.items())],
            'H_p_times_T_p': [[i, j, list(power), stringify(value)]
                for (i, j, power), value in sorted(product.items())],
            'fixed_v_potential_torque_rank': 9,
            'on_shell_scalar_J_zero_generated': True,
            'source_unbroken_gauge_parameter_dimension': 3}


def homogeneous_check(coordinates, operator, data):
    """Differentiate the source normal-form generator and its actual nine-field write."""
    a, h, alpha, b, theta = s.symbols('a H alpha b theta', real=True)
    state = [a, h, alpha, b, theta]
    spin, sigma, n0, alpha0 = (data[name] for name in ['spin', 'sigma', 'n', 'alpha'])
    torsion = spin/a**2
    energy = b*b+alpha**4
    denominator = 6*spin*(torsion-alpha)/a+3*a**3+3*a*h*h-3*a*torsion**2
    clock = s.sqrt(3*a*energy/(4*sigma*denominator))
    generator = s.Matrix([clock*h,
        (-energy/(4*sigma*clock)+clock*(2*spin*(torsion-alpha)/a**2-3*a*a-h*h+torsion**2))/(2*a),
        a*b/clock, 4*sigma*clock*spin/a-2*a*alpha**3/clock,
        3*clock*(torsion-alpha)/(2*a)])
    seed = {a: 1, h: 0, alpha: alpha0, b: 0, theta: 0}
    jacobian = generator.jacobian(state).subs(seed).applyfunc(s.simplify)
    delta_n = [s.simplify(s.diff(clock, x).subs(seed)) for x in state]
    lift = s.zeros(289, 5)

    def put(group, coordinate, column, value):
        lift[coordinates.groups[group][coordinate], column] = s.simplify(value)

    for j in range(5):
        put('coframe', (0, 0), j, delta_n[j])
    for mu in range(1, 4):
        put('coframe', (mu, mu), 0, 1)
        for c in range(12):
            put('gauge_A', (mu, c), 2, data['color_coeff'][mu-1][c])
            electric = alpha0**2/(sigma*n0)
            for j in range(5):
                value = electric*((1 if j == 0 else 0)+2/alpha0*(1 if j == 2 else 0)-delta_n[j]/n0)
                put('gauge_B', (mu-1, c), j, value*data['color_coeff'][mu-1][c])
            put('gauge_B', (mu+2, c), 3, data['color_coeff'][mu-1][c]/sigma)
        put('Lorentz', (mu, mu-1), 1, -1)
        put('Lorentz', (mu, mu+2), 0, -2*spin)
    gamma5 = s.kronecker_product(s.diag(-1, -1, 1, 1), s.eye(3))
    phase = -s.I*gamma5*data['prepared']
    for group, weight in [('primal_H', 1), ('dual_H', spin)]:
        for index in range(12):
            put(group, (0, index//3, index%3), 0, -s.Rational(3, 2)*weight*data['prepared'][index])
            put(group, (1, index//3, index%3), 4, weight*s.im(phase[index]))
    # Actual algebraic writes: B_g=*int(e wedge e), lambda=*int B_g-raise R(omega).
    omega0 = [sum((data['omega0'][mu, pair]*data['lorentz_basis'][pair]
                   for pair in range(6)), s.zeros(4)) for mu in range(4)]
    delta_omega = [[sum((lift[coordinates.groups['Lorentz'][(mu, pair)], column]*data['lorentz_basis'][pair]
                        for pair in range(6)), s.zeros(4)) for column in range(5)] for mu in range(4)]
    omega_rate = [[sum((delta_omega[mu][column]*jacobian[column, j] for column in range(5)), s.zeros(4))
                   for j in range(5)] for mu in range(4)]
    signs = s.diag(-1, -1, -1, 1, 1, 1)
    for column in range(5):
        de = s.Matrix(4, 4, lambda i, j: lift[coordinates.groups['coframe'][(i, j)], column])
        e0 = data['e0']
        dexterior = s.Matrix(6, 6, lambda i, j:
            de[PAIRS[i][0], PAIRS[j][0]]*e0[PAIRS[i][1], PAIRS[j][1]]+
            e0[PAIRS[i][0], PAIRS[j][0]]*de[PAIRS[i][1], PAIRS[j][1]]-
            de[PAIRS[i][0], PAIRS[j][1]]*e0[PAIRS[i][1], PAIRS[j][0]]-
            e0[PAIRS[i][0], PAIRS[j][1]]*de[PAIRS[i][1], PAIRS[j][0]])
        bg = J*dexterior
        curvature = s.zeros(6)
        for pair, (mu, nu) in enumerate(PAIRS):
            dcurvature = ((omega_rate[nu][column] if mu == 0 else s.zeros(4))-
                (omega_rate[mu][column] if nu == 0 else s.zeros(4))+
                delta_omega[mu][column]*omega0[nu]+omega0[mu]*delta_omega[nu][column]-
                delta_omega[nu][column]*omega0[mu]-omega0[nu]*delta_omega[mu][column])
            for internal, (i, j) in enumerate(PAIRS):
                curvature[internal, pair] = ETA[i, i]*dcurvature[i, j]
        multiplier = J*bg-signs*curvature
        for i, j in itertools.product(range(6), repeat=2):
            put('gravity_B', (i, j), column, bg[i, j])
            put('multiplier', (i, j), column, multiplier[i, j])
    assert lift.rank() == 5
    flows = [(lift*jacobian**degree).applyfunc(s.simplify) for degree in range(3)]
    residual = [[ZERO for _ in range(5)] for _ in range(289)]
    for (i, j, powers), coefficient in operator.items():
        if any(powers[1:]):
            continue
        for column in range(5):
            residual[i][column] += coefficient*number(flows[powers[0]][j, column])
    assert all(not value for row in residual for value in row), [
        (i, j, stringify(value)) for i, row in enumerate(residual) for j, value in enumerate(row) if value]
    x = s.symbols('X')
    characteristic = s.factor(jacobian.charpoly(x).as_expr())
    assert s.expand(characteristic-x*(x*x+s.Rational(648, 125))*(x*x-s.Rational(50, 3))) == 0
    print('PASS: original generated homogeneous five-state Jacobian and full nine-field lift solve all 289 linearized rows', flush=True)
    return {'source_homogeneous_Jacobian': [[str(value) for value in row] for row in jacobian.tolist()],
            'source_homogeneous_field_lift': [[i, j, str(value)] for (i, j), value in s.SparseMatrix(lift).todok().items()],
            'source_homogeneous_characteristic': str(characteristic),
            'source_homogeneous_289_by_5_intertwining_zero': True}


def encoded_operator(operator):
    return [[i, j, list(power), stringify(value)] for (i, j, power), value in sorted(operator.items())]


def algebraic_schur(coordinates, operator, groups):
    """Compute, verify and retain the actual constant algebraic inverse and write-back."""
    zero_power = (0, 0, 0, 0)
    eliminated = sorted(i for group in groups for i in coordinates.groups[group].values())
    position = {i: j for j, i in enumerate(eliminated)}
    keep = sorted({i for key in operator for i in key[:2]}-set(eliminated))
    auxiliary = s.zeros(len(eliminated))
    for (i, j, power), value in operator.items():
        if i in position and j in position:
            assert power == zero_power, ('Derivative in an allegedly algebraic diagonal block', groups, i, j, power)
            auxiliary[position[i], position[j]] = F.to_sympy(value.real)
    inverse = auxiliary.inv(method='DM')
    assert auxiliary*inverse == s.eye(len(eliminated))
    inv_rows = defaultdict(list)
    for (i, j), value in s.SparseMatrix(inverse).todok().items():
        inv_rows[i].append((j, number(value)))
    right = defaultdict(list)
    left = []
    for (i, j, power), value in operator.items():
        if i in position and j not in position:
            right[position[i]].append((j, power, value))
        elif i not in position and j in position:
            left.append((i, position[j], power, value))
    write_back = {}
    for a in range(len(eliminated)):
        for b, inverse_value in inv_rows[a]:
            for j, power, value in right[b]:
                key = (eliminated[a], j, power)
                write_back[key] = write_back.get(key, ZERO)-inverse_value*value
    write_back = {key: value for key, value in write_back.items() if value}
    by_auxiliary = defaultdict(list)
    for (i, j, power), value in write_back.items():
        by_auxiliary[i].append((j, power, value))
    reduced = {key: value for key, value in operator.items() if key[0] not in position and key[1] not in position}
    for i, a, power, value in left:
        for j, other_power, written in by_auxiliary[eliminated[a]]:
            key = (i, j, tuple(x+y for x, y in zip(power, other_power)))
            reduced[key] = reduced.get(key, ZERO)+value*written
    reduced = {key: value for key, value in reduced.items() if value}
    for (i, j, powers), coefficient in reduced.items():
        assert reduced.get((j, i, powers), ZERO) == ((-1)**sum(powers))*coefficient
    print('PASS: source algebraic Schur', '+'.join(groups), len(eliminated), 'variables ->', len(keep), flush=True)
    receipt = {'eliminated_groups': groups, 'eliminated_fields': eliminated,
               'algebraic_block_inverse': [[eliminated[i], eliminated[j], str(value)]
                    for (i, j), value in s.SparseMatrix(inverse).todok().items()],
               'write_back_auxiliary_from_retained': encoded_operator(write_back),
               'remaining_real_coordinates': len(keep)}
    return reduced, receipt


def ward_eliminate(coordinates, operator, data, ward):
    """Pay the invertible row operation before removing the nine scalar coordinates."""
    zero_power = (0, 0, 0, 0)
    scalar = sorted(coordinates.groups['scalar_J'].values())
    broken = data['orbit'].rref()[1]
    assert len(broken) == 9
    t = {(i, j, tuple(power)): number(s.sympify(value))
         for i, j, power, value in ward['source_primitive_gauge_tangent'] if i < 121 and j in broken}
    # The selected gauge columns are the source orbit basis itself: T_J = identity.
    for row, field in enumerate(scalar):
        for col, generator in enumerate(broken):
            assert t.get((field, generator, zero_power), ZERO) == number(int(row == col))
    # The nine new equations are T_broken(-p)^T H(p). This is an elementary invertible row change.
    rows = defaultdict(list)
    for (i, j, power), coefficient in operator.items():
        rows[i].append((j, power, coefficient))
    new_scalar_rows = {}
    for (i, generator, power), coefficient in t.items():
        for j, other_power, value in rows[i]:
            key = (scalar[broken.index(generator)], j, tuple(a+b for a, b in zip(power, other_power)))
            new_scalar_rows[key] = new_scalar_rows.get(key, ZERO)+((-1)**sum(power))*coefficient*value
    new_scalar_rows = {key: value for key, value in new_scalar_rows.items() if value}
    assert all(j in scalar and power == zero_power for (_, j, power) in new_scalar_rows)
    torque = s.Matrix(9, 9, lambda i, j: F.to_sympy(new_scalar_rows.get((scalar[i], scalar[j], zero_power), ZERO).real))
    inverse_torque = torque.inv(method='DM')
    assert torque*inverse_torque == s.eye(9)
    # After the invertible row change the upper-right block is zero; the exact Schur is this principal block.
    reduced = {key: value for key, value in operator.items() if key[0] not in scalar and key[1] not in scalar}
    assert len({i for key in reduced for i in key[:2]}) == 112
    print('PASS: invertible source Ward row operation generates 9 scalar constraints, then exact 121 -> 112 elimination', flush=True)
    return reduced, {'broken_parameter_columns': list(broken),
                     'Ward_row_operation_scalar_diagonal_is_identity': True,
                     'generated_scalar_constraint_rows': encoded_operator(new_scalar_rows),
                     'scalar_constraint_inverse': [[str(value) for value in row] for row in inverse_torque.tolist()],
                     'original_scalar_equations_preserved_by_invertible_row_change': True}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    started = time.monotonic()
    coordinates, actions, total, ward_data, provenance = build(args.root)
    operator = fourier_hessian(coordinates, total)
    for (i, j, powers), coefficient in operator.items():
        assert operator.get((j, i, powers), ZERO) == ((-1)**sum(powers))*coefficient
    ward = ward_check(coordinates, operator, ward_data)
    homogeneous = homogeneous_check(coordinates, operator, ward_data)
    negative = {'remove_background_B_bracket_contact': ward_check(coordinates,
        fourier_hessian(coordinates, total-ward_data['contact_action']), ward_data, require_zero=False)}
    reduced, elimination = operator, []
    for groups in [['gauge_B'], ['gravity_B', 'multiplier'], ['Lorentz']]:
        reduced, step = algebraic_schur(coordinates, reduced, groups)
        elimination.append(step)
    assert len({i for key in reduced for i in key[:2]}) == 121
    ward_check(coordinates, reduced, ward_data)
    final, ward_elimination = ward_eliminate(coordinates, reduced, ward_data, ward)
    assert all(rho*ward_data['v'] == s.zeros(70, 1) for rho in [
        sum((ward_data['a0'][mu, c]*ward_data['rho4'][c] for c in range(12)), s.zeros(70)) for mu in range(4)])
    radial_norm = (ward_data['v'].T*ward_data['v'])[0]
    assert radial_norm == 4 and s.simplify(2*ward_data['n']**2) == s.Rational(108, 125)
    sectors = Counter()
    for (i, j, _), coefficient in operator.items():
        sectors[coordinates.fields[i]['group']+' / '+coordinates.fields[j]['group']] += 1
    blocks = {name: [[list(key), stringify(value)] for key, value in sorted(action.terms.items()) if len(key) == 2]
              for name, action in actions.items()}
    result = {'scope': 'EXACT_SOURCE_COORDINATE_UNREDUCED_ACTIVE_ACTION_SECOND_JET', **provenance, **ward, **homogeneous,
        'actual_background': {'coframe': [[str(v) for v in row] for row in ward_data['e0'].tolist()],
            'gauge_connection': [[str(v) for v in row] for row in ward_data['a0'].tolist()],
            'lowered_Lorentz_connection': [[str(v) for v in row] for row in ward_data['omega0'].tolist()],
            'primal_H': [str(v) for v in ward_data['prepared']], 'dual_multiple': str(ward_data['spin']),
            'source_color_generators': [[str(v) for v in column] for column in ward_data['color_coeff']]},
        'real_fields': len(coordinates.fields), 'fields': coordinates.fields,
        'jet_coordinates': [{'field': f, 'derivative': d} for f, d in coordinates.jets],
        'derivative_minus_one_means': 'undifferentiated value',
        'quadratic_action_blocks': blocks,
        'quadratic_convention': 'coefficient of epsilon^2; Hessian differentiates this quadratic polynomial',
        'Fourier_convention': 'derivative p=(lambda,i*k1,i*k2,i*k3); Euler=partial_q L - d_mu partial_dq L',
        'Fourier_Jacobi_entries': encoded_operator(operator),
        'algebraic_Schur_steps': elimination,
        'primitive_121_Fourier_Jacobi_entries': encoded_operator(reduced),
        'Ward_constraint_elimination': ward_elimination,
        'equivalent_112_Fourier_Jacobi_entries': encoded_operator(final),
        'nonzero_Fourier_block_monomials': dict(sorted(sectors.items())),
        'checks': {'all_289_background_Euler_coordinates_zero': True,
                   'formal_adjoint_H_p_transpose_eq_H_minus_p': True,
                   'source_rotation_gamma_rotation': True,
                   'source_rotation_spin_commutation': True,
                   'rotation_includes_live_inverse_coframe_phase_term': True},
        'negative_control_nonzero_Ward_coefficients': negative,
        'separate_original_radial_source_check': {'norm_squared': str(radial_norm),
            'background_covariant_derivative_zero': True, 'homogeneous_growth_rate_squared': '108/125',
            'belongs_to_active_J': False},
        'auxiliaries_eliminated': True, 'gauge_quotient_performed': False,
        'physical_poles_determined': False, 'Lean_action_Hessian_identification': False,
        'elapsed_seconds': round(time.monotonic()-started, 3)}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n')
    print('PASS:', len(coordinates.fields), 'real fields;', len(coordinates.jets), 'first-jet coordinates;',
          len(operator), 'nonzero Fourier monomials;', result['elapsed_seconds'], 'seconds')


if __name__ == '__main__':
    main()
