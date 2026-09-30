"""Exact rational interval operations; every displayed decimal rounds outward."""
from fractions import Fraction as F
from math import isqrt


class Box:
    def __init__(self, low, high=None):
        self.lo = F(low)
        self.hi = F(low if high is None else high)
        assert self.lo <= self.hi

    @staticmethod
    def of(value):
        return value if isinstance(value, Box) else Box(value)

    def __add__(self, other):
        other = self.of(other)
        return Box(self.lo+other.lo, self.hi+other.hi)

    __radd__ = __add__

    def __neg__(self):
        return Box(-self.hi, -self.lo)

    def __sub__(self, other):
        return self+-self.of(other)

    def __rsub__(self, other):
        return self.of(other)+-self

    def __mul__(self, other):
        other = self.of(other)
        values = [a*b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return Box(min(values), max(values))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.of(other)
        assert other.lo > 0 or other.hi < 0
        return self*Box(1/other.hi, 1/other.lo)

    def __rtruediv__(self, other):
        return self.of(other)/self

    def square(self):
        lower = 0 if self.lo <= 0 <= self.hi else min(self.lo**2, self.hi**2)
        return Box(lower, max(self.lo**2, self.hi**2))

    def __pow__(self, exponent):
        assert isinstance(exponent, int) and exponent >= 0
        if exponent == 0:
            return Box(1)
        half = self**(exponent//2)
        result = half.square()
        return result*self if exponent % 2 else result

    def sqrt(self, bits=240):
        assert self.lo >= 0
        def floor(value):
            return isqrt((value.numerator << (2*bits))//value.denominator)
        return Box(F(floor(self.lo), 1 << bits), F(floor(self.hi)+1, 1 << bits))

    def grow(self, radius):
        radius = F(radius)
        assert radius >= 0
        return Box(self.lo-radius, self.hi+radius)

    def intersect(self, other):
        return Box(max(self.lo, other.lo), min(self.hi, other.hi))

    def rounded(self, digits=50):
        scale = 10**digits
        lower = (self.lo.numerator*scale)//self.lo.denominator
        upper = -((-self.hi.numerator*scale)//self.hi.denominator)
        result = Box(F(lower, scale), F(upper, scale))
        assert result.lo <= self.lo <= self.hi <= result.hi
        return result

    def decimals(self, digits=35):
        scale = 10**digits
        def render(value, upper):
            numerator = value.numerator*scale
            integer = -((-numerator)//value.denominator) if upper else numerator//value.denominator
            sign = '-' if integer < 0 else ''
            integer = abs(integer)
            return sign+str(integer//scale)+'.'+str(integer % scale).zfill(digits)
        return [render(self.lo, False), render(self.hi, True)]

    def record(self, digits=35):
        short = self.rounded(55)
        return {'rational': [str(short.lo), str(short.hi)], 'decimal': short.decimals(digits)}


def complex_product(first, second):
    return (first[0]*second[0]-first[1]*second[1],
            first[0]*second[1]+first[1]*second[0])


def arctangent(value, terms):
    value = F(value)
    assert 0 < value < 1 and terms > 0
    partial = sum((-1)**n*value**(2*n+1)/F(2*n+1) for n in range(terms))
    next_term = (-1)**terms*value**(2*terms+1)/F(2*terms+1)
    return Box(min(partial, partial+next_term), max(partial, partial+next_term))


def pi_box():
    # tan(4 atan(1/5)-atan(1/239))=1, in the principal positive tangent interval.
    x = F(1, 5)
    twice = 2*x/(1-x*x)
    four = 2*twice/(1-twice*twice)
    assert (four-F(1, 239))/(1+four/F(239)) == 1
    return (16*arctangent(F(1, 5), 80)-4*arctangent(F(1, 239), 24)).rounded(70)
