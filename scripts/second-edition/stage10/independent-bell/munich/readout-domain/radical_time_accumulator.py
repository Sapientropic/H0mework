"""Exact common-grid contraction of complete radical field vectors.

Each scalar enclosure is dyadic.  Root products and matrix entries are
accumulated as integers; rational reduction occurs once at the output.
Neither vectors nor small modes are removed, and the scalar error uses the
same complete-image radical entry norm as the original field consumer.
"""
from fractions import Fraction as Q
from math import gcd, lcm

import atomic_dipole as dipole
import atomic_full_forward as full


def _require(condition, message):
    if not condition:
        raise ValueError(message)


class RadicalTimeAccumulator:
    def __init__(self, vectors, *, scalar_bits=192, norm_bits=None):
        norm_bits = scalar_bits if norm_bits is None else norm_bits
        _require(type(vectors) in (tuple, list) and type(scalar_bits) is int and
                 type(norm_bits) is int and 64 <= scalar_bits <= 512 and 64 <= norm_bits <= 512,
                 'complete vector inventory and registered scalar precision required')
        denominator = 1
        for vector in vectors:
            _require(type(vector) is dict and all(type(key) is tuple and len(key) == 2 and
                     type(key[0]) is int and key[0] >= 0 and key[1] == 0 and
                     type(value) is dipole.ComplexRadical for key, value in vector.items()),
                     'complete exact radical column vectors required')
            for value in vector.values():
                for part in (value.real, value.imag):
                    for root, coefficient in part.terms:
                        denominator = lcm(denominator, coefficient.denominator)
        compiled = []
        for vector in vectors:
            rows = []
            for (row, column), value in sorted(vector.items()):
                real, imag = dict(value.real.terms), dict(value.imag.terms)
                terms = tuple((root, int(real.get(root, Q(0))*denominator),
                                int(imag.get(root, Q(0))*denominator))
                              for root in sorted(set(real)|set(imag)))
                if terms:
                    rows.append((row, terms))
            compiled.append(tuple(rows))
        self._vectors = tuple(compiled)
        self._denominator = denominator**2
        self._scalar_bits, self._norm_bits = scalar_bits, norm_bits
        self._matrix = {}
        self._scalar_error_numerator = 0
        self._root_upper = {}

    def _weight(self, enclosure):
        quantum = 1 << self._scalar_bits
        centre = getattr(enclosure, 'centre', None)
        error = getattr(enclosure, 'error', None)
        _require(type(centre) is tuple and len(centre) == 2 and
                 all(type(value) is Q for value in centre) and type(error) is Q and error >= 0,
                 'exact complex scalar enclosure required')
        values = (*centre, error)
        _require(all((value*quantum).denominator == 1 for value in values),
                 'scalar centre and error must lie on their registered dyadic grid')
        return tuple(int(value*quantum) for value in values)

    def _image(self, left, right):
        _require(type(left) is int and type(right) is int and
                 0 <= left < len(self._vectors) and 0 <= right < len(self._vectors),
                 'original vector addresses required')
        image = {}
        for row, a in self._vectors[left]:
            for column, b in self._vectors[right]:
                terms = {}
                for r, ar, ai in a:
                    for s, br, bi in b:
                        common = gcd(r, s)
                        root = (r//common)*(s//common)
                        real, imag = terms.get(root, (0, 0))
                        terms[root] = (real+common*(ar*br+ai*bi),
                                       imag+common*(ai*br-ar*bi))
                if any(real or imag for real, imag in terms.values()):
                    image[row, column] = {root: value for root, value in terms.items() if any(value)}
        return image

    def add_outer(self, left, right, enclosure):
        image = RadicalTimeAccumulator._image(self, left, right)
        RadicalTimeAccumulator._add_image(self, image, enclosure)

    def _add_image(self, image, enclosure):
        a, b, error = RadicalTimeAccumulator._weight(self, enclosure)
        norm = 0
        for (row, column), terms in image.items():
            for root, (real, imag) in terms.items():
                if root not in self._root_upper:
                    upper = full._sqrt(root, self._norm_bits)[1]
                    self._root_upper[root] = int(upper*(1 << self._norm_bits))
                norm += (abs(real)+abs(imag))*self._root_upper[root]
                key = row, column, root
                old_real, old_imag = self._matrix.get(key, (0, 0))
                self._matrix[key] = (old_real+a*real-b*imag, old_imag+a*imag+b*real)
        self._scalar_error_numerator += error*norm

    def result(self):
        denominator = self._denominator*(1 << self._scalar_bits)
        rows = {}
        for (row, column, root), (real, imag) in self._matrix.items():
            if not (real or imag):
                continue
            r, s = rows.setdefault((row, column), ({}, {}))
            if real:
                r[root] = Q(real, denominator)
            if imag:
                s[root] = Q(imag, denominator)
        matrix = {key: dipole.ComplexRadical(dipole.Radical(real), dipole.Radical(imag))
                  for key, (real, imag) in rows.items()}
        error = Q(self._scalar_error_numerator, denominator*(1 << self._norm_bits))
        return matrix, error


class RadicalMatrixTimeAccumulator(RadicalTimeAccumulator):
    """The same exact scalar contraction for complete tensor image matrices."""
    def __init__(self, matrices, *, scalar_bits=192, norm_bits=None):
        _require(type(matrices) in (tuple, list), 'complete image matrix inventory required')
        denominator = 1
        for matrix in matrices:
            _require(type(matrix) is dict and all(type(key) is tuple and len(key) == 2 and
                     all(type(i) is int and i >= 0 for i in key) and type(value) is dipole.ComplexRadical
                     for key, value in matrix.items()), 'complete exact radical matrices required')
            for value in matrix.values():
                for part in (value.real, value.imag):
                    for root, coefficient in part.terms:
                        denominator = lcm(denominator, coefficient.denominator)
        RadicalTimeAccumulator.__init__(self, [], scalar_bits=scalar_bits, norm_bits=norm_bits)
        self._denominator = denominator
        images = []
        for matrix in matrices:
            image = {}
            for key, value in matrix.items():
                real, imag = dict(value.real.terms), dict(value.imag.terms)
                terms = {root: (int(real.get(root, Q(0))*denominator),
                                int(imag.get(root, Q(0))*denominator))
                         for root in set(real)|set(imag)}
                if terms:
                    image[key] = terms
            images.append(image)
        self._images = tuple(images)

    def add_matrix(self, index, enclosure):
        _require(type(index) is int and 0 <= index < len(self._images), 'original image matrix address required')
        RadicalTimeAccumulator._add_image(self, self._images[index], enclosure)


def _matrix_family(matrices, dimension):
    _require(type(matrices) in (tuple, list), 'complete local matrix family required')
    denominator = 1
    for matrix in matrices:
        _require(type(matrix) is dict and all(type(key) is tuple and len(key) == 2 and
                 all(type(i) is int and 0 <= i < dimension for i in key) and
                 type(value) is dipole.ComplexRadical for key, value in matrix.items()),
                 'complete local radical matrices and source dimension required')
        for value in matrix.values():
            for part in (value.real, value.imag):
                for root, coefficient in part.terms:
                    denominator = lcm(denominator, coefficient.denominator)
    result = []
    for matrix in matrices:
        image = {}
        for key, value in matrix.items():
            r, s = dict(value.real.terms), dict(value.imag.terms)
            terms = {root: (int(r.get(root, Q(0))*denominator),
                            int(s.get(root, Q(0))*denominator)) for root in set(r)|set(s)}
            if terms:
                image[key] = terms
        result.append(image)
    return denominator, tuple(result)


def _integer_product(first, second):
    result = {}
    by_row = {}
    for (row, column), terms in second.items():
        by_row.setdefault(row, []).append((column, terms))
    for (row, middle), a in first.items():
        for column, b in by_row.get(middle, ()):
            terms = result.setdefault((row, column), {})
            for r, (ar, ai) in a.items():
                for s, (br, bi) in b.items():
                    common = gcd(r, s)
                    root = (r//common)*(s//common)
                    real, imag = terms.get(root, (0, 0))
                    terms[root] = (real+common*(ar*br-ai*bi), imag+common*(ar*bi+ai*br))
    return {key: {root: pair for root, pair in terms.items() if any(pair)}
            for key, terms in result.items() if any(any(pair) for pair in terms.values())}


def _integer_adjoint(matrix):
    return {(j, i): {root: (r, -s) for root, (r, s) in terms.items()}
            for (i, j), terms in matrix.items()}


def _integer_tensor_add(target, first, second, dimension):
    for (i, j), a in first.items():
        for (k, l), b in second.items():
            terms = target.setdefault((dimension*i+k, dimension*j+l), {})
            for r, (ar, ai) in a.items():
                for s, (br, bi) in b.items():
                    common = gcd(r, s)
                    root = (r//common)*(s//common)
                    real, imag = terms.get(root, (0, 0))
                    terms[root] = (real+common*(ar*br-ai*bi), imag+common*(ar*bi+ai*br))


class RadicalTensorTimeAccumulator(RadicalTimeAccumulator):
    """Stream complete signed tensor sandwiches with cached local images."""
    def __init__(self, operators_a, operators_b, tensor_terms, *, dimension=33,
                 scalar_bits=192, norm_bits=None):
        _require(type(dimension) is int and dimension > 0 and type(tensor_terms) in (tuple, list) and
                 tensor_terms and all(type(pair) in (tuple, list) and len(pair) == 2 for pair in tensor_terms),
                 'complete signed tensor inventory and source dimension required')
        da, a = _matrix_family(operators_a, dimension)
        db, b = _matrix_family(operators_b, dimension)
        fa, factors_a = _matrix_family([pair[0] for pair in tensor_terms], dimension)
        fb, factors_b = _matrix_family([pair[1] for pair in tensor_terms], dimension)
        RadicalTimeAccumulator.__init__(self, [], scalar_bits=scalar_bits, norm_bits=norm_bits)
        self._denominator = da*da*fa*db*db*fb
        self._operators = (a, b)
        self._adjoints = (tuple(map(_integer_adjoint, a)), tuple(map(_integer_adjoint, b)))
        self._factors = (factors_a, factors_b)
        self._local_cache = ({}, {})
        self._dimension = dimension

    def _local(self, side, left, right, factor):
        _require(type(side) is int and side in (0, 1) and type(left) is int and type(right) is int and
                 0 <= left < len(self._operators[side]) and 0 <= right < len(self._operators[side]),
                 'original local operator addresses required')
        key = left, right, factor
        cache = self._local_cache[side]
        if key not in cache:
            cache[key] = _integer_product(_integer_product(self._operators[side][left], self._factors[side][factor]),
                                           self._adjoints[side][right])
        return cache[key]

    def add_tensor(self, left, right, enclosure):
        _require(type(left) in (tuple, list) and type(right) in (tuple, list) and
                 len(left) == len(right) == 2, 'two complete source operator address pairs required')
        image = {}
        for factor in range(len(self._factors[0])):
            a = RadicalTensorTimeAccumulator._local(self, 0, left[0], right[0], factor)
            b = RadicalTensorTimeAccumulator._local(self, 1, left[1], right[1], factor)
            _integer_tensor_add(image, a, b, self._dimension)
        image = {key: {root: pair for root, pair in terms.items() if any(pair)}
                 for key, terms in image.items() if any(any(pair) for pair in terms.values())}
        RadicalTimeAccumulator._add_image(self, image, enclosure)
