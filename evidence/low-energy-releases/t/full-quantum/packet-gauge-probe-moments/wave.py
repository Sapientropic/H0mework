"""The source wavepacket over Q(i)[sqrt15], keeping shared radial denominators."""
from algebra import SphereAlgebra
import sympy as s


class QuadraticSphere:
    def __init__(self, alg):
        self.alg = alg
        self.zero = (alg.zero, alg.zero)

    def scalar(self, rational, radical=0):
        return self.alg.scalar(rational), self.alg.scalar(radical)

    def add(self, *values):
        return tuple(sum((value[i] for value in values), self.alg.zero) for i in range(2))

    def scale(self, coefficient, value):
        if not isinstance(coefficient, type(self.alg.zero)):
            coefficient = self.alg.scalar(coefficient)
        return tuple(self.alg.mul(coefficient, part) for part in value)

    def mul(self, left, right):
        return (self.alg.mul(left[0], right[0])+15*self.alg.mul(left[1], right[1]),
                self.alg.mul(left[0], right[1])+self.alg.mul(left[1], right[0]))

    def star(self, value):
        return tuple(self.alg.star(part) for part in value)

    def partial(self, value, axis):
        return tuple(self.alg.partial(part, axis) for part in value)

    def matvec(self, matrix, vector):
        return [self.add(*(self.scale(matrix[i][j], vector[j]) for j in range(len(vector))))
                for i in range(len(matrix))]

    def encode(self, vector):
        return [[self.alg.encode_polynomial(value[0]), self.alg.encode_polynomial(value[1])] for value in vector]

    def decode(self, record):
        return [(self.alg.decode_polynomial(value[0]), self.alg.decode_polynomial(value[1])) for value in record]


class WaveVector:
    def __init__(self, quadratic, D, F, numerator, d=0, f=1):
        self.Q = quadratic
        self.A = quadratic.alg
        self.D = D
        self.F = F
        self.num = numerator
        self.d = d
        self.f = f

    def scaled(self, value):
        return WaveVector(self.Q, self.D, self.F, [self.Q.scale(value, v) for v in self.num], self.d, self.f)

    def plus(self, other):
        assert self.Q is other.Q and self.D == other.D and self.F == other.F
        d, f = max(self.d, other.d), max(self.f, other.f)
        left = self.D**(d-self.d)*self.F**(f-self.f)
        right = self.D**(d-other.d)*self.F**(f-other.f)
        return WaveVector(self.Q, self.D, self.F,
            [self.Q.add(self.Q.scale(left, u), self.Q.scale(right, v)) for u, v in zip(self.num, other.num)], d, f)

    def operator(self, matrix, d_power):
        return WaveVector(self.Q, self.D, self.F, self.Q.matvec(matrix, self.num), self.d+d_power, self.f)

    def packet_partial(self, axis):
        assert self.d == 0
        denominator_derivative = self.A.partial(self.F, axis)
        numerator = [self.Q.add(self.Q.scale(self.F, self.Q.partial(value, axis)),
                               self.Q.scale(-self.f*denominator_derivative, value)) for value in self.num]
        return WaveVector(self.Q, self.D, self.F, numerator, 0, self.f+1)

    def encode(self):
        return {'D_power': self.d, 'F_power': self.f, 'numerator': self.Q.encode(self.num)}

    @staticmethod
    def decode(Q, D, F, record):
        return WaveVector(Q, D, F, Q.decode(record['numerator']), record['D_power'], record['F_power'])
