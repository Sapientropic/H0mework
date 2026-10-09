#!/usr/bin/env python3
"""Complete two-probe Gram/mean radial kernels from the same packet vectors."""
from fractions import Fraction
from functools import lru_cache
import gzip
import hashlib
import json
from math import lcm
from pathlib import Path
import sys
import time
import sympy as s
from sympy.polys.fields import field
from sympy.polys.rings import ring

sys.dont_write_bytecode = True
sys.set_int_max_str_digits(0)
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
ROOT = HERE.parents[4]
from algebra import SphereAlgebra
from wave import QuadraticSphere, WaveVector

RF, xf = field('x', s.QQ_I)
RI, xi = ring('x', s.ZZ_I)
XR = RF.ring.gens[0]
Z4 = (RF.zero,)*4


def constant(value):
    return RF.new(RF.ring.ground_new(s.QQ_I.from_sympy(s.expand(s.sympify(value)))))


def plus(*values):
    return tuple(sum((value[i] for value in values), RF.zero) for i in range(4))


def scaled(value, coefficients):
    if not isinstance(value, type(xf)):
        value = constant(value)
    return tuple(value*coefficient for coefficient in coefficients)


def derivative(value):
    return RF.new(value.numer.diff(0)*value.denom-value.numer*value.denom.diff(0), value.denom**2)


def star_poly(poly):
    return poly.ring.from_dict({powers: poly.ring.domain.dtype(coef.x, -coef.y) for powers, coef in poly.items()})


def conjugate(values):
    return tuple(RF.new(star_poly(value.numer), star_poly(value.denom)) for value in values)


def encode(values):
    return [str(value.as_expr()) for value in values]


def endpoint_order(value):
    if not value:
        return None
    order = min(power[0] for power in value.numer)-min(power[0] for power in value.denom)
    infinity = value.numer.degree()-value.denom.degree()
    assert order >= 0 and infinity <= 1, (order, infinity)
    return [order, infinity]


def reduce_ball(coefficients):
    # x=r²/2, t=b'/r, u=(b''-b'/r)/r².
    # One ODE step handles b*u. The t² contribution uses an additional
    # integration by parts with boundary delta*b*b', before the shared bt step.
    aa, bt, bu, tt = [coefficients.get(key, Z4) for key in ['b2', 'bt', 'bu', 't2']]
    A = plus(aa, scaled(-1/(2*xf), bu), scaled(1/(2*xf), tt))
    B = plus(bt, scaled(-5/(2*xf), bu), scaled(2/xf, tt), tuple(-derivative(v) for v in tt))
    weight = plus(A, scaled(-1/(4*xf), B), tuple(-derivative(v)/2 for v in B))
    endpoints = {'bt_after_ODE_and_tt_IBP': [endpoint_order(v) for v in B],
                 'tt_first_boundary': [endpoint_order(v) for v in tt]}
    return weight, endpoints


class AngularGram:
    def __init__(self, A, Q, D, F):
        self.A, self.Q, self.D, self.F = A, Q, D, F
        self.groups = {}
        self.pairs = {}
        self.dr = self.radial(D)
        self.fr = self.radial(F)

    def radial(self, poly):
        assert all(not any(powers[:3]) for powers in poly)
        return RF.ring.from_dict({(powers[3],): value for powers, value in poly.items()})

    def grouped(self, key, vector):
        if key in self.groups:
            return self.groups[key]
        scale = 1
        degree = 0
        for pair in vector.num:
            for poly in pair:
                for powers, coefficient in poly.items():
                    scale = lcm(scale, int(coefficient.x.denominator), int(coefficient.y.denominator))
                    degree = max(degree, sum(powers[:3]))
        components = []
        for pair in vector.num:
            entries = []
            for poly in pair:
                groups = {}
                for powers, coefficient in poly.items():
                    angular, radial = powers[:3], powers[3]
                    re, im = coefficient.x*scale, coefficient.y*scale
                    assert re.denominator == im.denominator == 1
                    groups.setdefault(angular, {})[radial,] = s.ZZ_I.dtype(int(re), int(im))
                entries.append({powers: RI.from_dict(terms) for powers, terms in groups.items()})
            components.append(entries)
        result = scale, degree, components
        self.groups[key] = result
        return result

    def raw(self, leftkey, left, rightkey, right):
        key = leftkey, rightkey
        if key in self.pairs:
            return self.pairs[key]
        if (rightkey, leftkey) in self.pairs:
            answer = tuple(RF.new(star_poly(value.numer), star_poly(value.denom))
                for value in self.pairs[rightkey, leftkey])
            self.pairs[key] = answer
            return answer
        sl, dl, gl = self.grouped(leftkey, left)
        sr, dr, gr = self.grouped(rightkey, right)
        top_even = dl+dr-(dl+dr) % 2
        angular_denominator = int(s.factorial2(top_even+1))

        @lru_cache(None)
        def moment(powers):
            if any(power % 2 for power in powers):
                return 0, 0
            degree = sum(powers)
            value = s.prod(s.factorial2(power-1) for power in powers)*angular_denominator/s.factorial2(degree+1)
            assert value.is_Integer
            return int(value), degree//2

        def pair(one, two):
            out = RI.zero
            for pa, a in one.items():
                conjugated = star_poly(a)
                for pb, b in two.items():
                    mul, degree = moment(tuple(x+y for x, y in zip(pa, pb)))
                    if mul:
                        out += mul*xi**degree*conjugated*b
            return out

        numerators = [RI.zero, RI.zero]
        for one, two in zip(gl, gr):
            numerators[0] += pair(one[0], two[0])+15*pair(one[1], two[1])
            numerators[1] += pair(one[0], two[1])+pair(one[1], two[0])
        denominator = (star_poly(self.dr)**left.d*self.dr**right.d*
            self.fr**(left.f+right.f))*s.QQ_I.dtype(sl*sr*angular_denominator, 0)
        values = []
        for numerator in numerators:
            p = RF.ring.from_dict({powers: s.QQ_I.dtype(value.x, value.y) for powers, value in numerator.items()})
            values.append(RF.new(p, denominator))
        self.pairs[key] = tuple(values)
        return tuple(values)


def main():
    began = time.monotonic()
    raw = gzip.decompress((HERE/'vectors.json.gz').read_bytes())
    data = json.loads(raw)
    receipt = json.loads((HERE/'vectors.json').read_text())
    assert hashlib.sha256(raw).hexdigest() == receipt['uncompressed_sha256']
    A = SphereAlgebra(s.QQ_I)
    Q = QuadraticSphere(A)
    F = A.decode_polynomial(data['packet_denominator'])
    N2 = s.Rational(data['lapse_squared'])
    accumulated = {}
    endpoint_records = {}
    source_physical = {}
    for block in data['blocks']:
        sign = block['chirality']
        D = A.decode_polynomial(block['D'])
        gram = AngularGram(A, Q, D, F)
        g = WaveVector.decode(Q, D, F, block['g'])
        vectors = {('W', (), 'b'): g}
        descriptors = {('W', ()): {'order': 0, 'parts': ['b']}}
        for kind in ['B', 'C']:
            for record in block['jets'][kind]:
                axes = tuple(record['axes'])
                parts = [name for name in ['b', 't', 'u'] if name in record]
                descriptors[kind, axes] = {'order': record['order'], 'parts': parts}
                for name in parts:
                    vectors[kind, axes, name] = WaveVector.decode(Q, D, F, record[name])

        def prefactor(left, right):
            coefficient = N2
            degree = 0
            for kind, axes in [left, right]:
                if kind != 'W':
                    coefficient *= s.Rational(sign)/N2
                    degree += int(kind == 'B')-len(axes)
            coefficient *= s.Rational(2)**(degree//2)
            assert coefficient.is_Rational
            return coefficient, degree % 2

        def pair_weights(left, right):
            coefficient, radical = prefactor(left, right)
            result = {}
            for lp in descriptors[left]['parts']:
                for rp in descriptors[right]['parts']:
                    key = {'bb': 'b2', 'bt': 'bt', 'tb': 'bt', 'bu': 'bu', 'ub': 'bu', 'tt': 't2'}.get(lp+rp)
                    assert key is not None
                    lk, rk = (*left, lp), (*right, rp)
                    r0, r15 = gram.raw(lk, vectors[lk], rk, vectors[rk])
                    weight = list(Z4)
                    weight[radical], weight[radical+2] = coefficient*r0, coefficient*r15
                    result[key] = plus(result.get(key, Z4), tuple(weight))
            return result

        def record(name, *pairs):
            coeffs = {}
            for left, right in pairs:
                for key, value in pair_weights(left, right).items():
                    coeffs[key] = plus(coeffs.get(key, Z4), value)
            value, endpoints = reduce_ball(coeffs)
            accumulated[name] = plus(accumulated.get(name, Z4), value)
            endpoint_records.setdefault(name, []).append({'chirality': sign, **endpoints})

        record('packet_norm', (('W', ()), ('W', ())))
        for kind in ['B', 'C']:
            for descriptor in block['jets'][kind]:
                axes = tuple(descriptor['axes'])
                name = 'mean_'+kind+'_'+('base' if not axes else ''.join(map(str, axes)))
                record(name, (('W', ()), (kind, axes)))
        print('PASS original packet mean jets from actual source block', sign, flush=True)
        orders = [(), (0,), (1,), (2,), (0, 0), (0, 1), (0, 2), (1, 1), (1, 2), (2, 2)]
        for axes in orders:
            label = 'base' if not axes else ''.join(map(str, axes))
            record('N0_right_'+label, (('B', ()), ('B', axes)))
            record('N1_right_'+label, (('C', ()), ('B', axes)), (('B', ()), ('C', axes)))
        for i in range(3):
            for j in range(3):
                record('N0_mixed_'+str(i)+str(j), (('B', (i,)), ('B', (j,))))
                record('N1_mixed_'+str(i)+str(j), (('C', (i,)), ('B', (j,))), (('B', (i,)), ('C', (j,))))
        print('PASS complete0/1/2 right and mixed9 two-probe Gram kernels for source block', sign, flush=True)
    # Left-only probe jets are the exact Hermitian reversal of the same whole
    # ordered Gram, after both chiral source blocks have been combined.
    for key, value in list(accumulated.items()):
        if key.startswith('N0_right_') or key.startswith('N1_right_'):
            accumulated[key.replace('_right_', '_left_')] = conjugate(value)
    for kind in ['N0', 'N1']:
        for i in range(3):
            for j in range(3):
                assert accumulated[f'{kind}_mixed_{i}{j}'] == conjugate(accumulated[f'{kind}_mixed_{j}{i}'])
    assert len(accumulated) == 79
    for kind in ['B', 'C']:
        for axis in range(3):
            assert not any(accumulated[f'mean_{kind}_{axis}'])
    exact_path = FQ/'packet-noise/source-kernel-receipt.json'
    exact = json.loads(exact_path.read_text())['exact_source']
    r = s.Symbol('r', nonnegative=True)
    xx = s.Symbol('x')
    norm = s.sympify(exact['zero_transfer_raw_norm_integrand'], locals={'r': r}).subs(r*r, 2*xx)
    assert accumulated['packet_norm'][0] == RF.from_expr(s.cancel(norm))
    assert all(not value for value in accumulated['packet_norm'][1:])
    norms = [key for key, values in accumulated.items() if any(values)]
    weights = [{'name': key, 'radical_components': encode(value), 'identically_zero': not any(value),
                'endpoint_checks': endpoint_records.get(key, 'Hermitian reversal of corresponding right kernel')}
               for key, value in sorted(accumulated.items())]
    result = {'scope': 'STRIKE_COMPLETE_NATIVE_LAPLACE_PROBE_GRAM_AND_MEAN_RADIAL_KERNELS',
        'source_sha256': data['source_sha256'],
        'input_sha256': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [HERE/'vectors.json.gz', HERE/'vectors.json', exact_path]},
        'radial_variable': 'x=|physical p|²/2; all physical probe factors are included in each weight',
        'radical_basis': ['1', 'sqrt2', 'sqrt15', 'sqrt30'],
        'raw_measure': 'entire d³p/(2pi)³ times the original normalized position-ball b(|p|)²',
        'normalization': 'packet_norm integrates to n²; each raw Gram and mean integrates its weight then divides by same n²; no blockwise centering',
        'gram_scope': 'N0=<B_k psi,B_l psi>; N1=<C_k psi,B_l psi>+<B_k psi,C_l psi>; complete left6/right6 and mixed9 plus lower jets',
        'connected_N0': 'raw_ab - conjugate(muB_a)*muB_b, after full momentum integrals and both chiral blocks',
        'connected_N1': 'raw_ab - conjugate(muC_a)*muB_b - conjugate(muB_a)*muC_b; actual means and complex cross retained',
        'ball_reduction': 'bsecond+4bprime/r+b=0. In x=r²/2, A=alpha-delta_bu/(2x)+delta_tt/(2x); B=beta-5delta_bu/(2x)+2delta_tt/x-delta_tt_prime; final A-B/(4x)-Bprime/2.',
        'endpoints': 'r B b²/2 and delta_tt b bprime vanish at0 and infinity by actual exact rational orders, finite b at0, b/bprime=O(r^-2) at infinity',
        'physical_frequency': data['physical_frequency'], 'fixed_packet_preparation_and_P': True,
        'weights': weights, 'nonzero_weight_names': norms,
        'elapsed_seconds': round(time.monotonic()-began, 3)}
    (HERE/'kernels.json').write_text(json.dumps(result, separators=(',', ':'))+'\n')
    print('PASS actual entire-halfline rational kernel producer',len(weights),'weights, nonzero',len(norms),result['elapsed_seconds'],flush=True)


if __name__ == '__main__':
    main()
