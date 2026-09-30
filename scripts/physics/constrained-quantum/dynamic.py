#!/usr/bin/env python3
"""Actual on-shell transition currents and four-block transfer responses.

The frequency is the difference of the two generated leg energies.  A
Laplace-frequency continuation must transport the Ward source too; changing
the inverse's frequency alone is not a retarded source solution.
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path

import sympy as s
from sympy.polys.matrices import DomainMatrix

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ROOT = HERE.parents[3]
ROOT_ID = (
    "positiveSmoothUnifiedSource; repaired Dirac-dual; SpinPair.actual; "
    "visit10/tick16/materialEntry -> tick17 unchanged"
)
P = s.symbols("p0:4")


def decode(record):
    return s.SparseMatrix(*record["shape"], {
        (int(i), int(j)): s.sympify(value) for i, j, value in record["entries"]
    })


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.simplify)


def equal(left, right):
    assert not clean(left - right).todok()


def encode(matrix):
    return {"shape": list(matrix.shape), "entries": [
        [int(i), int(j), str(value)]
        for (i, j), value in sorted(clean(matrix).todok().items())
    ]}


def read(relative):
    return json.loads((BASE / relative).read_text())


@dataclass(frozen=True)
class Leg:
    vector: s.MatrixBase
    momentum: s.MatrixBase
    frequency: s.Expr
    derivative: s.MatrixBase
    degree: int


@dataclass(frozen=True)
class Transition:
    transfer: s.MatrixBase
    current: s.MatrixBase
    scalar: s.MatrixBase


class SourceExchange:
    def __init__(self):
        self.vertices = read("matter-vertices/receipt.json")
        self.exchange = read("matter-vertices/exchange.json")
        self.scalar = read("scalar-exchange/receipt.json")
        self.modes = read("matter-modes/source.json")
        self.active = read("active-gauge/receipt.json")
        assert self.vertices["source_sha256"] == self.modes["source_sha256"]
        for receipt in [self.vertices, self.modes, self.active, self.scalar]:
            for key in ["source_sha256", "input_sha256", "source_hashes"]:
                for name, digest in receipt.get(key, {}).items():
                    assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
        self.N = s.sympify(self.vertices["source_lapse"])
        self.omega = s.sympify(self.vertices["source_frequency"])
        self.clock = s.sympify(self.modes["time_scale"])
        self.D = decode(self.vertices["full_stationary_Dirac_operator"])
        self.S = s.SparseMatrix(252, 252, {
            (((index // 63 + 2) % 4) * 63 + index % 63, index): 1
            for index in range(252)
        })
        raw = {item["field"]: decode(item["operator"])
               for item in self.vertices["active_289_bosonic_source_operators"]}
        self.order = self.exchange["source_field_indices"]
        self.V = [raw[field] for field in self.order]
        self.Y = [decode(item["operator"]) for item in self.vertices["primitive_vertices"]
                  if item["group"] == "scalar"]
        self.maps = {key: decode(self.exchange[key]) for key in [
            "canonical_operator", "independent_dual_operator",
            "canonical_source_map", "independent_dual_source_map",
            "local_source_compatibility_map", "total_contact_kernel",
            "contact_field_response", "canonical_field_lift", "independent_dual_field_lift",
        ]}
        self.scalar_ward = decode(next(item["source_map"] for item in
            self.exchange["source_contact_terms"] if item["groups"] == ["scalar_Ward"]))
        self.injection = s.SparseMatrix(289, 97, {
            (row, column): 1 for column, row in enumerate(self.order)
        })
        self.domain = s.QQ.algebraic_field(s.sqrt(2), s.sqrt(15), s.I)

    def at(self, key, transfer):
        return clean(self.maps[key].subs(dict(zip(P, transfer))))

    def leg(self, degree, scaled_momentum):
        """Positive-helicity right singlet, with physical k=sqrt(2)*q."""
        q = s.Matrix(scaled_momentum)
        radius = s.sqrt((q.T * q)[0])
        assert radius.is_positive
        block = next(item for item in self.modes["blocks"] if item["kind"] == "singlet"
                     and item["chirality"] == 1 and item["degree"] == degree)
        frame = decode(self.modes["source_isometry"])[:, block["first_column"]:block["first_column"]+2]
        sigma = [decode(item) for item in self.modes["singlet_spatial"]]
        projector = clean((s.eye(2) + sum((q[i]*sigma[i]/radius for i in range(3)), s.zeros(2)))/2)
        column = next(i for i in range(2) if projector[:, i] != s.zeros(2, 1))
        spin = projector[:, column]
        spin = clean(spin/s.sqrt((spin.H*spin)[0]))
        vector = clean(frame*spin)
        small = decode(self.modes["singlet_constant"]) + sum(
            (q[i]*sigma[i] for i in range(3)), s.zeros(2))
        energy = s.simplify(self.clock*(spin.H*small*spin)[0])
        momentum = s.sqrt(2)*q
        derivative = s.Matrix([-s.I*(energy-self.omega*block["phase_charge"]),
                               *[s.I*k for k in momentum]])
        symbol = self.D.subs(dict(zip(P, derivative)))
        equal(symbol*vector, s.zeros(252, 1))
        equal(vector.H*self.S*symbol, s.zeros(1, 252))
        equal(vector.H*vector, s.ones(1, 1))
        return Leg(vector, momentum, energy, derivative, degree)

    def transition(self, outgoing, incoming):
        def current(operator):
            left = operator.subs(dict(zip(P, incoming.derivative)))
            right = operator.subs(dict(zip(P, outgoing.derivative)))
            return s.simplify(s.sqrt(2)/2 *
                (outgoing.vector.H*(self.S*left+right.H*self.S)*incoming.vector)[0])
        transfer = clean(incoming.derivative-outgoing.derivative)
        j = s.Matrix([current(v) for v in self.V])
        z = s.Matrix([current(v) for v in self.Y])
        equal(self.at("local_source_compatibility_map", transfer)*j, s.zeros(9, 1))
        equal(decode(self.scalar["full_scalar_source_split_active_map"])*z, j[:9, :])
        return Transition(transfer, j, z)

    def solve(self, matrix, rhs):
        """Exact regular transfer response, without deleting singular directions."""
        scale = next((value for value in rhs if value != 0), s.Integer(1))
        A = DomainMatrix.from_Matrix(matrix).convert_to(self.domain)
        # External spin normalization multiplies the entire source column.
        # Factor it out instead of enlarging the operator's number field.
        b = DomainMatrix.from_Matrix(clean(rhs/scale)).convert_to(self.domain)
        numerator, denominator = A.solve_den(b, method="rref")
        assert denominator != self.domain.zero
        result = clean(scale*numerator.to_Matrix()/self.domain.to_sympy(denominator))
        equal(matrix*result, rhs)
        return result

    def action(self, transfer):
        H = s.MutableSparseMatrix(289, 289, {})
        for i, j, powers, value in self.active["Fourier_Jacobi_entries"]:
            H[i, j] += s.sympify(value)*s.prod(transfer[mu]**power for mu, power in enumerate(powers))
        return clean(H)

    def response(self, transition):
        r, j = transition.transfer, transition.current
        f79 = self.at("canonical_source_map", r)*j
        f24 = self.at("independent_dual_source_map", r)*j
        x79 = self.solve(self.at("canonical_operator", r), f79)
        x24 = self.solve(self.at("independent_dual_operator", r), f24)
        field = clean(self.at("contact_field_response", r)*j
            + self.at("canonical_field_lift", r)*x79
            + self.at("independent_dual_field_lift", r)*x24)
        equal(self.action(r)*field, self.injection*j)
        scalar_p = dict(zip(s.symbols("u r1 r2 r3"), [r[0]/(self.N*s.sqrt(2)),
                                                         *[v/s.sqrt(2) for v in r[1:]]]))
        peripheral = decode(self.scalar["full_scalar_source_split_peripheral_map"])*transition.scalar
        numerator = decode(self.scalar["peripheral_scalar_green_numerator"]).subs(scalar_p)
        denominator = s.simplify(s.sympify(self.scalar["peripheral_scalar_green_denominator"]).subs(scalar_p))
        assert denominator != 0
        scalar_response = clean(numerator*peripheral/denominator)
        operator = decode(self.scalar["normalized_full_scalar_operator"]).subs(scalar_p)
        equal(self.N*operator*scalar_response, peripheral)
        return {"f79": f79, "f24": f24, "x79": x79, "x24": x24,
                "field289": field, "peripheral_source": peripheral,
                "peripheral_response": scalar_response}

    def bilinear(self, left, right, response):
        equal(left.transfer, -right.transfer)
        r = right.transfer
        return [s.simplify(value) for value in [
            (left.current.T*self.at("total_contact_kernel", r)*right.current)[0],
            (self.at("canonical_source_map", -r)*left.current).dot(response["x79"]),
            (self.at("independent_dual_source_map", -r)*left.current).dot(response["x24"]),
            (left.scalar.T*response["peripheral_response"])[0],
        ]]


def main():
    source = SourceExchange()
    families = [
        ("original_elastic", [(0, 0, s.Rational(1, 2)), (s.Rational(1, 2), 0, 0),
                              (0, 0, -s.Rational(1, 2)), (-s.Rational(1, 2), 0, 0)]),
        ("energy_transfer", [(0, 0, s.Rational(3, 4)), (s.Rational(3, 8), 0, 0),
                             (0, 0, -s.Rational(1, 4)), (-s.Rational(3, 8), 0, s.Rational(1, 2))]),
    ]
    results = []
    for name, momenta in families:
        legs = [source.leg(degree, q) for degree, q in zip([4, 4, 2, 2], momenta)]
        equal(legs[0].momentum+legs[2].momentum, legs[1].momentum+legs[3].momentum)
        assert s.simplify(legs[0].frequency+legs[2].frequency-legs[1].frequency-legs[3].frequency) == 0
        first = source.transition(legs[1], legs[0])
        second = source.transition(legs[3], legs[2])
        equal(first.transfer, -second.transfer)
        equal(source.transition(legs[3], legs[0]).current, s.zeros(97, 1))
        equal(source.transition(legs[1], legs[2]).current, s.zeros(97, 1))
        response = source.response(first)
        opposite = source.response(second)
        pieces = source.bilinear(second, first, response)
        reverse = source.bilinear(first, second, opposite)
        assert all(s.simplify(a-b) == 0 for a, b in zip(pieces, reverse))
        amplitude = s.simplify(-sum(pieces))
        if name == "original_elastic":
            old = read("onshell-sources/receipt.json")
            equal(first.current, decode(old["first_transition_current"]))
            equal(response["field289"], decode(old["full_289_positive_green_response"]))
            assert s.simplify(amplitude-s.sympify(old["elastic_direct_tree_kernel"])) == 0
        else:
            assert first.transfer[0] != 0
        shifted = first.transfer.copy()
        shifted[0] += 1
        wrong_ward = clean(source.at("local_source_compatibility_map", shifted)*first.current)
        assert wrong_ward != s.zeros(9, 1)
        results.append({"name": name, "scaled_momenta": [[str(v) for v in q] for q in momenta],
            "transfer": encode(first.transfer), "first_current": encode(first.current),
            "second_current": encode(second.current),
            "response": {key: encode(value) for key, value in response.items()},
            "opposite_response": {key: encode(value) for key, value in opposite.items()},
            "bilinear_blocks": dict(zip(["contact", "canonical79", "dual24", "scalar61"], map(str, pieces))),
            "coordinate_direct_kernel": str(amplitude),
            "action_normalized_direct_kernel": str(s.simplify(amplitude/2)),
            "frozen_current_frequency_shift_ward_defect": encode(wrong_ward),
            "all289_rows": True, "ward_compatible": True, "opposite_transfer_reciprocity": True})
        print("PASS", name, "four blocks, both289 responses, Ward and reciprocal tree coefficient", flush=True)
    output = {"root": ROOT_ID, "scope": "ON_SHELL_TRANSFER_DEPENDENT_FOUR_BLOCK_RESPONSE",
        "source_sha256": source.vertices["source_sha256"],
        "samples": results,
        "retarded_consumer": "causal.py: same-source fixed-section zero-past preparation",
        "lifetime_status": "SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED"}
    (HERE/"dynamic.json").write_text(json.dumps(output, indent=2)+"\n")


if __name__ == "__main__":
    main()
