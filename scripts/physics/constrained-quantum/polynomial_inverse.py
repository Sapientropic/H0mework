"""Fraction-free inverse over Q(i)[x,q], using exact FLINT polynomials."""
from __future__ import annotations

from dataclasses import dataclass

from flint import fmpq, fmpq_mpoly_ctx
import sympy as s

CONTEXT = fmpq_mpoly_ctx.get(("x", "q"))
X, Q = s.symbols("x q")


@dataclass(frozen=True)
class GaussianPolynomial:
    real: object
    imag: object

    @classmethod
    def from_expr(cls, value):
        real, imag = {}, {}
        for powers, coefficient in s.Poly(value, X, Q).terms():
            for part, table in [(s.re(coefficient), real), (s.im(coefficient), imag)]:
                if part:
                    assert part.is_Rational
                    a, b = part.as_numer_denom()
                    table[powers] = fmpq(int(a), int(b))
        return cls(CONTEXT.from_dict(real), CONTEXT.from_dict(imag))

    def __bool__(self):
        return bool(self.real) or bool(self.imag)

    def __add__(self, other):
        return GaussianPolynomial(self.real+other.real, self.imag+other.imag)

    def __sub__(self, other):
        return GaussianPolynomial(self.real-other.real, self.imag-other.imag)

    def __mul__(self, other):
        return GaussianPolynomial(self.real*other.real-self.imag*other.imag,
                                  self.real*other.imag+self.imag*other.real)

    def exact_quotient(self, other):
        if not other.imag:
            return GaussianPolynomial(self.real/other.real, self.imag/other.real)
        norm = other.real*other.real+other.imag*other.imag
        return GaussianPolynomial((self.real*other.real+self.imag*other.imag)/norm,
                                  (self.imag*other.real-self.real*other.imag)/norm)

    def expression(self):
        terms = []
        for unit, part in [(s.Integer(1), self.real), (s.I, self.imag)]:
            for powers, coefficient in part.to_dict().items():
                terms.append(unit*s.Rational(str(coefficient))*X**powers[0]*Q**powers[1])
        return s.Add(*terms)


ZERO = GaussianPolynomial.from_expr(0)
ONE = GaussianPolynomial.from_expr(1)


def inverse_den(matrix):
    """Return N,d with both A*N=dI and N*A=dI, checked in the native ring."""
    size = matrix.rows
    original = [[GaussianPolynomial.from_expr(matrix[i,j]) for j in range(size)] for i in range(size)]
    work = [row[:] + [ONE if i == j else ZERO for j in range(size)] for i, row in enumerate(original)]
    previous = ONE
    for pivot_index in range(size):
        row = next(i for i in range(pivot_index, size) if work[i][pivot_index])
        work[pivot_index], work[row] = work[row], work[pivot_index]
        pivot = work[pivot_index][pivot_index]
        for i in range(size):
            if i == pivot_index:
                continue
            multiplier = work[i][pivot_index]
            for j in range(2*size):
                if j == pivot_index:
                    continue
                work[i][j] = (pivot*work[i][j]-multiplier*work[pivot_index][j]).exact_quotient(previous)
            work[i][pivot_index] = ZERO
        previous = pivot
    denominator = work[0][0]
    numerator = [row[size:] for row in work]
    for i in range(size):
        for j in range(size):
            assert not (work[i][j]-(denominator if i == j else ZERO))
            for left, right in [(original, numerator), (numerator, original)]:
                value = ZERO
                for k in range(size):
                    value = value + left[i][k]*right[k][j]
                assert not (value-(denominator if i == j else ZERO))
    return s.SparseMatrix(size, size, {(i,j): value.expression()
        for i, row in enumerate(numerator) for j, value in enumerate(row) if value}), denominator.expression()
