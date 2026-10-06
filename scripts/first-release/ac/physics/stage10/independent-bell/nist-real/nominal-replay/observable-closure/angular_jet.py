"""Directed second angular derivatives for mean-value contraction of gradient boxes."""
from fractions import Fraction as F


class Jet:
    def __init__(self, value, gradient=None, hessian=None):
        self.value = value
        self.I = type(value)
        self.gradient = gradient or [self.I.point(0) for _ in range(4)]
        self.hessian = hessian or [[self.I.point(0) for _ in range(4)] for _ in range(4)]

    @classmethod
    def variable(cls, index, value):
        gradient = [type(value).point(int(i == index)) for i in range(4)]
        return cls(value, gradient)

    def cast(self, value):
        return value if isinstance(value, Jet) else Jet(value if isinstance(value, self.I) else self.I.point(F(value)))

    def __add__(self, other):
        other = self.cast(other)
        return Jet(self.value+other.value,
                   [a+b for a, b in zip(self.gradient, other.gradient)],
                   [[self.hessian[i][j]+other.hessian[i][j] for j in range(4)] for i in range(4)])

    __radd__ = __add__

    def __neg__(self):
        return Jet(-self.value, [-x for x in self.gradient], [[-x for x in row] for row in self.hessian])

    def __sub__(self, other):
        return self+-self.cast(other)

    def __rsub__(self, other):
        return self.cast(other)+-self

    def __mul__(self, other):
        other = self.cast(other)
        return Jet(self.value*other.value,
                   [self.gradient[i]*other.value+self.value*other.gradient[i] for i in range(4)],
                   [[self.hessian[i][j]*other.value+self.gradient[i]*other.gradient[j]+
                     self.gradient[j]*other.gradient[i]+self.value*other.hessian[i][j]
                     for j in range(4)] for i in range(4)])

    __rmul__ = __mul__

    def compose(self, value, first, second):
        return Jet(value, [first*x for x in self.gradient],
                   [[second*self.gradient[i]*self.gradient[j]+first*self.hessian[i][j]
                     for j in range(4)] for i in range(4)])

    def reciprocal(self):
        inv = self.value.reciprocal()
        return self.compose(inv, -inv.square(), 2*inv.square()*inv)

    def __truediv__(self, other):
        return self*self.cast(other).reciprocal()

    def __rtruediv__(self, other):
        return self.cast(other)*self.reciprocal()
