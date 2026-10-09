#!/usr/bin/env python3
"""Exact source coefficient arithmetic for the compact causal consumers."""
import gzip
import hashlib
import json
from pathlib import Path
import sys
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
FQ = HERE.parent
sys.path.insert(0, str(FQ / 'packet-gauge-kernel'))
import propagation as old

x, U = s.symbols('x U', real=True)
QQ = s.QQ_I
R = QQ.poly_ring(x)
c = 6*s.sqrt(15)/25
radicals = [s.S(1), s.sqrt(2), s.sqrt(15), s.sqrt(30)]
clean, encode = old.clean, old.encode


def read(path):
    raw = path.read_bytes()
    return json.loads(gzip.decompress(raw) if path.suffix == '.gz' else raw)


def matrix(record):
    return old.matrix(record, {'x': x, 'U': U})


def zero(rows, cols, domain=QQ):
    return DM({}, (rows, cols), domain)


def split(M):
    out = [s.MutableSparseMatrix(M.rows, M.cols, {}) for _ in range(4)]
    for (i, j), value in s.SparseMatrix(M).todok().items():
        remaining = s.expand(value)
        for a, radical in enumerate(radicals[1:], 1):
            coefficient = remaining.coeff(radical)
            if coefficient:
                out[a][i, j] = coefficient
                remaining -= radical*coefficient
        out[0][i, j] = s.expand(remaining)
    return [DM.from_Matrix(v).convert_to(R) for v in out]


def pack(parts):
    return DM.hstack(*parts)


def unpack(M, columns=6):
    return [M.extract(range(M.shape[0]), range(a*columns, (a+1)*columns)) for a in range(4)]


def constant_parts(parts):
    return [v.convert_to(QQ) for v in parts]


def plus(a, b):
    return [v+w for v, w in zip(a, b)]


def scale(a, value):
    return [v.scalarmul(QQ(value)) for v in a]


def product(a, b):
    shape = (a[0].shape[0], b[0].shape[1])
    out = [zero(*shape) for _ in range(4)]
    for i in range(4):
        for j in range(4):
            if a[i].is_zero_matrix or b[j].is_zero_matrix:
                continue
            factor = (2 if (i & j & 1) else 1)*(15 if (i & j & 2) else 1)
            out[i ^ j] += a[i].matmul(b[j]).scalarmul(QQ(factor))
    return out


def physical(parts, order):
    # Conversion of axial displacement derivatives to physical s derivatives.
    if order == 0:
        return parts
    if order == 2:
        return scale(parts, s.Rational(1, 2))
    out = [zero(*parts[0].shape) for _ in range(4)]
    for a, M in enumerate(parts):
        factor = 1 if (a & 1) else s.Rational(1, 2)
        out[a ^ 1] = M.scalarmul(QQ(factor))
    return out


def join(parts):
    return clean(sum((r*M.to_Matrix() for r, M in zip(radicals, parts)),
                     s.zeros(*parts[0].shape)))


def eval_poly(p, point):
    if not p:
        return QQ.zero
    value = QQ.zero
    for j in range(p.degree(), -1, -1):
        value = value*point+p.get((j,), QQ.zero)
    return value


def evaluate(M, point):
    return DM({i: {j: eval_poly(p, point) for j, p in row.items()}
               for i, row in M.to_dod().items()}, M.shape, QQ)


def coefficients(M):
    out = {}
    for i, row in M.to_dod().items():
        for j, poly in row.items():
            for (power,), value in poly.items():
                out.setdefault(power, {}).setdefault(i, {})[j] = value
    return {power: DM(dod, M.shape, QQ) for power, dod in out.items()}


def laurent(num, den, low):
    """Exact coefficients at infinity; the finite upper degree is paid by num/den."""
    d = den.degree()
    lead = den[(d,)]
    out = {}
    top = -10**6
    for i, row in num.to_dod().items():
        for j, poly in row.items():
            high = poly.degree()-d
            top = max(top, high)
            values = {}
            for power in range(high, low-1, -1):
                value = poly.get((power+d,), QQ.zero)
                for k in range(1, min(d, high-power)+1):
                    value -= den.get((d-k,), QQ.zero)*values.get(power+k, QQ.zero)
                value /= lead
                values[power] = value
                if value:
                    out.setdefault(power, {}).setdefault(i, {})[j] = value
    return {power: DM(dod, num.shape, QQ) for power, dod in out.items()}, top


def insert_block(M, indices, rows=103):
    return DM({indices[i]: row for i, row in M.to_dod().items()}, (rows, M.shape[1]), QQ)


def normalize(num, den):
    num, den = num.cancel_denom(den)
    lc = den.LC
    if lc != QQ.one:
        num = num.scalarmul(R.convert(1/lc))
        den = den/lc
    return num, den

