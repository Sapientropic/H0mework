"""Exact momentum polynomials modulo v1²+v2²+v3²=x, with shared denominators."""
from functools import lru_cache
import sympy as s
from sympy.polys.rings import ring


class SphereAlgebra:
    def __init__(self, domain):
        self.domain = domain
        self.ring, self.v1, self.v2, self.v3, self.x = ring('v1,v2,v3,x', domain)
        self.v = (self.v1, self.v2, self.v3)
        self.zero = self.ring.zero
        self.one = self.ring.one

    def scalar(self, value):
        return self.ring.ground_new(self.domain.from_sympy(s.expand(s.sympify(value))))

    def expression(self, value):
        return self.ring.from_expr(s.sympify(value))

    def normal(self, poly):
        out = {}
        for powers, value in poly.items():
            i, j, k, m = powers
            if k < 2:
                out[powers] = out.get(powers, self.domain.zero)+value
            elif k == 2:
                for pp, coefficient in [((i, j, 0, m+1), value),
                        ((i+2, j, 0, m), -value), ((i, j+2, 0, m), -value)]:
                    out[pp] = out.get(pp, self.domain.zero)+coefficient
            else:
                reduced = self.ring.from_dict({(i, j, k % 2, m): value})*self.radial_power(k//2)
                for pp, coefficient in reduced.items():
                    out[pp] = out.get(pp, self.domain.zero)+coefficient
        return self.ring.from_dict({pp: value for pp, value in out.items() if value})

    @lru_cache(None)
    def radial_power(self, degree):
        return (self.x-self.v1*self.v1-self.v2*self.v2)**degree

    def mul(self, left, right):
        return self.normal(left*right)

    def partial(self, poly, axis):
        return self.normal(poly.diff(self.v[axis])+2*self.v[axis]*poly.diff(self.x))

    def star(self, poly):
        return self.ring.from_dict({powers: self.domain.dtype(value.x, -value.y)
                                    for powers, value in poly.items()})

    def angular(self, poly):
        out = {}
        for (i, j, k, m), value in poly.items():
            if i % 2 or j % 2 or k % 2:
                continue
            degree = i+j+k
            weight = s.factorial2(i-1)*s.factorial2(j-1)*s.factorial2(k-1)/s.factorial2(degree+1)
            power = (0, 0, 0, m+degree//2)
            out[power] = out.get(power, self.domain.zero)+value*self.domain.from_sympy(weight)
        return self.ring.from_dict({power: value for power, value in out.items() if value})

    def zero_matrix(self, n=4, m=4):
        return [[self.zero for _ in range(m)] for _ in range(n)]

    def identity(self, n=4):
        return [[self.one if i == j else self.zero for j in range(n)] for i in range(n)]

    def from_matrix(self, matrix):
        return [[self.scalar(matrix[i, j]) for j in range(matrix.cols)] for i in range(matrix.rows)]

    def add(self, *matrices):
        n, m = len(matrices[0]), len(matrices[0][0])
        return [[sum((M[i][j] for M in matrices), self.zero) for j in range(m)] for i in range(n)]

    def scale(self, value, matrix):
        if not isinstance(value, type(self.zero)):
            value = self.scalar(value)
        return [[self.mul(value, entry) for entry in row] for row in matrix]

    def matmul(self, left, right):
        n, k, m = len(left), len(right), len(right[0])
        assert len(left[0]) == k
        return [[self.normal(sum((left[i][j]*right[j][l] for j in range(k)), self.zero))
                 for l in range(m)] for i in range(n)]

    def is_zero(self, matrix):
        return all(not entry for row in matrix for entry in row)

    def encode(self, matrix):
        return {'shape': [len(matrix), len(matrix[0])], 'entries':
            [[i, j, list(powers), str(self.domain.to_sympy(coefficient))]
             for i, row in enumerate(matrix) for j, entry in enumerate(row)
             for powers, coefficient in sorted(entry.items())]}

    def decode(self, record):
        out = self.zero_matrix(*record['shape'])
        for i, j, powers, coefficient in record['entries']:
            out[i][j] += self.ring.from_dict({tuple(powers): self.domain.from_sympy(s.sympify(coefficient))})
        return out

    def encode_polynomial(self, poly):
        return [[list(powers), str(self.domain.to_sympy(coefficient))]
                for powers, coefficient in sorted(poly.items())]

    def decode_polynomial(self, record):
        return self.ring.from_dict({tuple(powers): self.domain.from_sympy(s.sympify(value))
                                   for powers, value in record})


class SharedMatrix:
    """Numerator matrix over SphereAlgebra, divided by one source D(x)^power."""
    def __init__(self, alg, denominator, numerator, power=0):
        self.alg = alg
        self.denominator = denominator
        self.numerator = numerator
        self.power = power

    def scaled(self, scalar):
        return SharedMatrix(self.alg, self.denominator, self.alg.scale(scalar, self.numerator), self.power)

    def plus(self, other):
        assert self.alg is other.alg and self.denominator == other.denominator
        power = max(self.power, other.power)
        return SharedMatrix(self.alg, self.denominator, self.alg.add(
            self.alg.scale(self.denominator**(power-self.power), self.numerator),
            self.alg.scale(self.denominator**(power-other.power), other.numerator)), power)

    def left(self, matrix):
        return SharedMatrix(self.alg, self.denominator, self.alg.matmul(matrix, self.numerator), self.power)

    def right(self, matrix):
        return SharedMatrix(self.alg, self.denominator, self.alg.matmul(self.numerator, matrix), self.power)

    def encode(self):
        return {'D_power': self.power, 'numerator': self.alg.encode(self.numerator)}
