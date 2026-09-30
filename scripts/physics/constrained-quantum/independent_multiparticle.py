#!/usr/bin/env python3
"""Raw252/Sylvester/direct-linear-solve audit of a whole doublet consumer."""
from __future__ import annotations

import gzip
import hashlib
import json
from pathlib import Path
import time

from flint import fmpq, fmpq_mat
import sympy as s

from dynamic import SourceExchange, decode, ROOT_ID
import world_momentum as world

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ROOT = HERE.parents[3]
P = s.symbols("p0:4")
RADICALS = [s.Integer(1), s.sqrt(2), s.sqrt(15), s.sqrt(30)]


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def equal(left, right):
    assert not clean(left-right).todok()


class ExactMatrix:
    """Eight rational components; fixed-point solves use realification."""
    def __init__(self, rows, columns, parts=None):
        self.rows, self.cols = rows, columns
        self.parts = {k: value for k, value in (parts or {}).items()
                      if value != fmpq_mat(rows, columns)}

    @classmethod
    def from_matrix(cls, matrix):
        parts = {}
        for (i, j), value in s.SparseMatrix(matrix).todok().items():
            rest = s.expand(value)
            terms = {}
            for k in (3, 2, 1):
                terms[k] = rest.coeff(RADICALS[k])
                rest = s.expand(rest-terms[k]*RADICALS[k])
            terms[0] = rest
            assert s.expand(sum(a*RADICALS[k] for k, a in terms.items())-value) == 0
            for k, a in terms.items():
                for bit, rational in ((0, s.re(a)), (4, s.im(a))):
                    assert rational.is_Rational, (value, rational)
                    if rational:
                        parts.setdefault(k+bit, fmpq_mat(matrix.rows, matrix.cols))[i, j] = fmpq(str(rational))
        return cls(matrix.rows, matrix.cols, parts)

    @classmethod
    def identity(cls, size):
        matrix = fmpq_mat(size, size)
        for i in range(size):
            matrix[i, i] = 1
        return cls(size, size, {0: matrix})

    def __add__(self, other):
        assert (self.rows, self.cols) == (other.rows, other.cols)
        parts = dict(self.parts)
        for k, value in other.parts.items():
            parts[k] = parts[k]+value if k in parts else value
        return ExactMatrix(self.rows, self.cols, parts)

    def __sub__(self, other):
        return self+other.scale(-1)

    def __matmul__(self, other):
        assert self.cols == other.rows
        parts = {}
        for a, left in self.parts.items():
            for b, right in other.parts.items():
                common = a & b
                weight = (2 if common & 1 else 1)*(15 if common & 2 else 1)*(-1 if common & 4 else 1)
                key = a ^ b
                value = weight*(left*right)
                parts[key] = parts[key]+value if key in parts else value
        return ExactMatrix(self.rows, other.cols, parts)

    def scale(self, value):
        scalar = ExactMatrix.from_matrix(s.Matrix([[value]]))
        parts = {}
        for a, left in self.parts.items():
            for b, right in scalar.parts.items():
                common = a & b
                weight = (2 if common & 1 else 1)*(15 if common & 2 else 1)*(-1 if common & 4 else 1)
                key = a ^ b
                term = (weight*right[0, 0])*left
                parts[key] = parts[key]+term if key in parts else term
        return ExactMatrix(self.rows, self.cols, parts)

    def transpose(self):
        return ExactMatrix(self.cols, self.rows, {k: value.transpose() for k, value in self.parts.items()})

    def extract(self, rows, columns):
        return ExactMatrix(len(rows), len(columns), {k: fmpq_mat(len(rows), len(columns),
            [value[i, j] for i in rows for j in columns]) for k, value in self.parts.items()})

    def assert_equal(self, other):
        assert not (self-other).parts

    def solve_gaussian(self, rhs):
        """Direct QQ solve of [Re A,-Im A;Im A,Re A], not N/d readout."""
        assert self.rows == self.cols and set(self.parts) <= {0, 4}
        n = self.rows
        real = self.parts.get(0, fmpq_mat(n, n))
        imag = self.parts.get(4, fmpq_mat(n, n))
        realified = fmpq_mat(2*n, 2*n)
        for i in range(n):
            for j in range(n):
                realified[i, j] = realified[n+i, n+j] = real[i, j]
                realified[i, n+j], realified[n+i, j] = -imag[i, j], imag[i, j]
        inverse = realified.inv()
        inverse_complex = ExactMatrix(n, n, {
            0: fmpq_mat(n, n, [inverse[i, j] for i in range(n) for j in range(n)]),
            4: fmpq_mat(n, n, [inverse[n+i, j] for i in range(n) for j in range(n)])})
        (self@inverse_complex).assert_equal(ExactMatrix.identity(n))
        result = inverse_complex@rhs
        (self@result).assert_equal(rhs)
        return result


def native(matrix):
    return ExactMatrix.from_matrix(matrix)


def flatten(vertices):
    rows, cols = vertices[0].shape
    return s.SparseMatrix(len(vertices), rows*cols, {(a, i*cols+j): value
        for a, vertex in enumerate(vertices) for (i, j), value in vertex.todok().items()})


def original_flow(source, block, ki, ko, full_H, frame, metric):
    columns = list(range(block["first_column"], block["first_column"]+block["dimension"]))
    F = frame[:, columns]
    gram = clean(F.H*metric*F)
    assert gram.is_diagonal() and all(gram[i, i] > 0 for i in range(gram.rows))
    R = s.diag(*[1/s.sqrt(gram[i, i]) for i in range(gram.rows)])
    equal(R.H*gram*R, s.eye(gram.rows))
    def hamiltonian(k):
        large = clean(full_H[0]+sum((k[j]*full_H[j+1] for j in range(3)), s.zeros(252)))
        small = clean(F.H*large*F)
        equal(large*F, F*small)
        equal(small.H, small)
        equal(R*small, small*R)
        return small
    Hi, Ho = hamiltonian(ki), hamiltonian(ko)
    vertices = []
    for V in source.V:
        V0 = clean(V.subs(dict(zip(P, [0]*4))))
        D0 = clean(V.diff(P[0]))
        Vi = clean(V0+sum((s.I*ki[j]*V.diff(P[j+1]) for j in range(3)), s.zeros(252)))
        Vo = clean(V0+sum((s.I*ko[j]*V.diff(P[j+1]) for j in range(3)), s.zeros(252)))
        current = clean(s.sqrt(2)/2*(F.H*(source.S*Vi+Vo.H*source.S)*F
            -s.I*(F.H*source.S*D0*F)*Hi+s.I*Ho*(F.H*D0.H*source.S*F)))
        vertices.append(clean(R.H*current*R))
    for V in source.Y:
        equal(F.H*source.S*V, s.zeros(F.cols, 252))
    initial = flatten(vertices)
    m = Hi.rows
    generator = clean(s.I*(s.kronecker_product(Ho, s.eye(m))-s.kronecker_product(s.eye(m), Hi.T)))
    derivative = clean(generator*initial.T).T
    transfer = s.Matrix([0, *[s.I*v for v in ki-ko]])
    C = source.at("local_source_compatibility_map", transfer)
    Ct = source.maps["local_source_compatibility_map"].diff(P[0])
    equal(C*initial+Ct*derivative, s.zeros(9, m*m))
    equal(source.at("independent_dual_source_map", transfer)*initial, s.zeros(24, m*m))
    equal(initial[:9, :], s.zeros(9, m*m))
    # Independent projector construction from each actual finite Hamiltonian.
    def resolution(H):
        eigenvalues = list(H.eigenvals())
        assert len(eigenvalues) == m
        answer = []
        for energy in eigenvalues:
            projection = s.eye(m)
            for other in eigenvalues:
                if other != energy:
                    projection = clean(projection*(H-other*s.eye(m))/(energy-other))
            equal(H*projection, energy*projection)
            equal(projection*projection, projection)
            answer.append((s.simplify(energy), projection))
        equal(sum((projector for _, projector in answer), s.zeros(m)), s.eye(m))
        return answer
    rates = {}
    for eo, po in resolution(Ho):
        for ei, pi in resolution(Hi):
            rate = s.simplify(s.I*(eo-ei))
            value = native(flatten([clean(po*vertex*pi) for vertex in vertices]))
            rates[rate] = rates.get(rate, ExactMatrix(97, m*m))+value
    rates = {rate: value for rate, value in rates.items() if value.parts}
    total = ExactMatrix(97, m*m)
    for value in rates.values():
        total = total+value
    total.assert_equal(native(initial))
    return {"ki": ki, "ko": ko, "initial": native(initial), "generator": native(generator),
            "rates": rates, "dimension": m, "block": block}


def components(matrix):
    remaining = set(range(matrix.rows)); answer = []
    entries = matrix.todok()
    while remaining:
        stack = [min(remaining)]; group = set()
        while stack:
            i = stack.pop()
            if i in group:
                continue
            group.add(i)
            stack.extend(j for a, j in entries if a == i and j not in group)
            stack.extend(a for a, j in entries if j == i and a not in group)
        remaining -= group
        answer.append(sorted(group))
    return answer


def verify_uniform_boundary(exchange, quotient, clock, axial):
    x, q = s.symbols("x q")
    at = dict(zip(P, [clock*x, 0, 0, s.I*s.sqrt(2)*q]))
    C = decode(exchange["local_source_compatibility_map"])
    Ct = clean(C.diff(P[0]))
    C = clean(C.subs(at))
    fields = exchange["source_field_indices"]
    E = s.SparseMatrix(97, 9, {(fields.index(field), j): 1
        for j, field in enumerate(quotient["fixed_section_removed_original_fields"])})
    minor = clean(C*E)
    assert not minor.free_symbols and minor.det() != 0
    boundary = clean(E*minor.inv()*Ct)
    equal(boundary, decode(axial["source_boundary_coefficient"]))
    equal(C*boundary, Ct)
    equal(Ct*boundary, s.zeros(9, 97))
    equal(decode(exchange["independent_dual_source_map"]).subs(at)*boundary, s.zeros(24, 97))
    equal(boundary[:9, :], s.zeros(9, 97))


class DirectResponse:
    def __init__(self, source, finite, quotient, scales):
        self.source, self.finite, self.quotient = source, finite, quotient
        self.scale = s.diag(*scales)
        self.cache = {}
        self.response_count = 0

    def solve(self, operator, rhs):
        result = [fmpq_mat(operator.rows, rhs.cols) for _ in range(8)]
        source_operator = native(operator)
        for ids in components(operator):
            force = rhs.extract(ids, list(range(rhs.cols)))
            if not force.parts:
                continue
            solved = source_operator.extract(ids, ids).solve_gaussian(force)
            for part, value in solved.parts.items():
                for i, row in enumerate(ids):
                    for j in range(rhs.cols):
                        result[part][row, j] = value[i, j]
        answer = ExactMatrix(operator.rows, rhs.cols, dict(enumerate(result)))
        (source_operator@answer).assert_equal(rhs)
        return answer

    def response(self, flow, x):
        key = (id(flow), x)
        if key in self.cache:
            return self.cache[key]
        source = self.source
        size = flow["dimension"]**2
        # Rationalize by the source clock so the 16x16 Sylvester matrix is QQ(i).
        sylvester = ExactMatrix.identity(size).scale(x)-flow["generator"].scale(1/source.clock)
        current = sylvester.solve_gaussian(flow["initial"].transpose().scale(1/source.clock)).transpose()
        frame = world.paired_frame(flow["ki"]-flow["ko"], self.finite)
        L, Li = native(frame["field"]), native(frame["inverse"])
        Ls = L.extract(source.order, source.order)
        Lsi = Li.extract(source.order, source.order)
        transfer = s.Matrix([source.clock*x, 0, 0, s.I*s.sqrt(2)*frame["q"]])
        ward = source.at("local_source_compatibility_map", transfer)
        Ct = source.maps["local_source_compatibility_map"].diff(P[0])
        E = s.SparseMatrix(97, 9, {(source.order.index(field), j): 1
            for j, field in enumerate(self.quotient["fixed_section_removed_original_fields"])})
        minor = clean(ward*E)
        assert not minor.free_symbols and minor.det() != 0
        correction = native(clean(E*minor.inv()))
        axis_raw = Ls.transpose()@current
        initial_axis = Ls.transpose()@flow["initial"]
        boundary_axis = correction@native(Ct)@initial_axis
        prepared_axis = axis_raw-boundary_axis
        (native(ward)@prepared_axis).assert_equal(ExactMatrix(9, size))
        prepared = Lsi.transpose()@prepared_axis
        boundary = Lsi.transpose()@boundary_axis
        prepared.assert_equal(current-boundary)
        A = source.at("canonical_operator", transfer)
        B = source.at("independent_dual_operator", transfer)
        force79 = native(source.at("canonical_source_map", transfer))@prepared_axis
        force24 = native(source.at("independent_dual_source_map", transfer))@prepared_axis
        assert not force24.parts
        canonical = clean(self.scale*A*self.scale/source.N)
        x79 = (native(self.scale)@self.solve(canonical, native(self.scale)@force79)).scale(1/source.N)
        x24 = self.solve(clean(B/source.N), force24).scale(1/source.N)
        axis_field = (native(source.at("contact_field_response", transfer))@prepared_axis
            +native(source.at("canonical_field_lift", transfer))@x79
            +native(source.at("independent_dual_field_lift", transfer))@x24)
        field = L@axis_field
        world_transfer = s.Matrix([source.clock*x, *[s.I*v for v in flow["ki"]-flow["ko"]]])
        Cworld = native(source.at("local_source_compatibility_map", world_transfer))
        (Cworld@current).assert_equal(native(Ct)@flow["initial"])
        (Cworld@prepared).assert_equal(ExactMatrix(9, size))
        (Cworld@boundary).assert_equal(native(Ct)@flow["initial"])
        assert not (native(Ct)@boundary).parts
        (native(source.action(world_transfer))@field).assert_equal(native(source.injection)@prepared)
        assert not prepared.extract(list(range(9)), list(range(size))).parts
        self.response_count += 1
        self.cache[key] = field.extract(source.order, list(range(size)))
        return self.cache[key]


def main():
    started = time.monotonic()
    path = HERE/"multiparticle-kernel.json.gz"
    payload = gzip.decompress(path.read_bytes())
    candidate = json.loads(payload)
    assert candidate["root"] == ROOT_ID
    for name, digest in candidate["input_sha256"].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
    source = SourceExchange()
    assert candidate["source_sha256"] == source.vertices["source_sha256"]
    for name in ["independent_free_current.json", "independent_all_momentum.json",
                 "independent-all-momentum-causal.json"]:
        receipt = json.loads((HERE/name).read_text())
        assert receipt["root"] == ROOT_ID
        for dependency, digest in receipt["input_sha256"].items():
            assert hashlib.sha256((ROOT/dependency).read_bytes()).hexdigest() == digest, dependency
    modes = source.modes
    phase_path = BASE/"full-phase/receipt.json"
    phase = json.loads(phase_path.read_text())
    assert phase["source_sha256"] == source.vertices["source_sha256"]
    Q = decode(phase["phase_generator"])
    full_H = [clean(source.clock*decode(modes["original_H_constant"])-source.omega*Q),
              *[clean(source.clock/s.sqrt(2)*decode(row)) for row in modes["original_H_spatial"]]]
    frame = decode(modes["source_isometry"])
    chirality = clean(s.kronecker_product(s.diag(-1, -1, 1, 1), s.eye(63)))
    metric = clean(s.sqrt(2)*chirality*Q)
    focused = candidate["focused_family"]
    ki, ko = decode(focused["physical_incoming_first"]), decode(focused["physical_outgoing_first"])
    blocks = [focused["first_source_block"], focused["second_source_block"]]
    assert all(block in modes["blocks"] for block in blocks)
    first = original_flow(source, blocks[0], ki, ko, full_H, frame, metric)
    second = original_flow(source, blocks[1], -ki, -ko, full_H, frame, metric)
    assert first["dimension"] == second["dimension"] == 4
    print("PASS independent raw252 two complete97x16 currents, source Noether metric, Lagrange spectral resolutions", flush=True)
    finite_path = BASE/"active-gauge/rotation/finite.json"
    quotient_path = BASE/"active-gauge/quotient.json"
    soft_path = BASE/"soft-phase/receipt.json"
    finite = json.loads(finite_path.read_text())
    quotient = json.loads(quotient_path.read_text())
    soft = json.loads(soft_path.read_text())
    response = DirectResponse(source, finite, quotient, list(map(s.sympify, soft["field_scaling"])))
    x = s.sympify(focused["dimensionless_Laplace_x"])
    axial_path = HERE/"all-momentum.json.gz"
    axial = json.loads(gzip.decompress(axial_path.read_bytes()))
    verify_uniform_boundary(source.exchange, quotient, source.clock, axial)
    inverse_witness = json.loads((HERE/"independent_all_momentum.json").read_text())
    assert inverse_witness["candidate_gzip_sha256"] == hashlib.sha256(axial_path.read_bytes()).hexdigest()
    pole_radius = s.re(x)-1
    assert pole_radius > 0
    pole_bound_count = 0
    q_absolute = s.simplify(s.sqrt(((ki-ko).T*(ki-ko))[0]/2))
    # Opposite q need separate checks: the source denominators are not all even.
    for signed_q in [q_absolute, -q_absolute]:
        denominators = [b["denominator"] for key in ["canonical_blocks", "independent_dual_blocks"]
                        for b in axial[key]]+[axial["peripheral_scalar_denominator"]]
        for text in denominators:
            variable = s.Symbol("x")
            polynomial = s.Poly(s.sympify(text, locals={"q": signed_q}), variable).monic()
            bound = sum((abs(s.re(value))+abs(s.im(value)))*pole_radius**power[0]
                        for power, value in polynomial.terms() if power[0] < polynomial.degree())
            assert pole_radius**polynomial.degree() > bound
            pole_bound_count += 1
    reports = []
    def ordered(field_flow, reader_flow, pieces, saved):
        assert len(pieces) == len(reader_flow["rates"])
        total = ExactMatrix(16, 16)
        seen = set()
        for piece in pieces:
            rate = s.sympify(piece["reader_rate"])
            assert rate in reader_flow["rates"] and rate not in seen
            assert s.re(rate) == 0
            seen.add(rate)
            shifted = s.simplify(x-rate/source.clock)
            assert s.simplify(shifted-s.sympify(piece["source_laplace_x"])) == 0
            actual = response.response(field_flow, shifted).transpose()@reader_flow["rates"][rate]
            actual.assert_equal(native(decode(piece["coefficient"])))
            total = total+actual
            print("PASS independent direct-source ordered piece", shifted, "all256 coefficients and full289 rows", flush=True)
        total.assert_equal(native(decode(saved)))
        reports.append({"reader_rates": len(seen), "all_256_coefficients_per_rate": True,
                        "direct_16d_Sylvester_and_raw_source_solve": True, "all289_rows_per_rate": True})
        return total
    forward = ordered(first, second, focused["first_ordered_factored_rate_terms"], focused["first_ordered_coefficients"])
    reverse = ordered(second, first, focused["second_ordered_factored_rate_terms"], focused["second_ordered_coefficients"])
    combined = (forward+reverse.transpose()).scale(-s.Rational(1, 2))
    combined.assert_equal(native(decode(focused["full_normalized_quartic_coefficients"])))
    assert combined.parts
    wrong = response.response(first, x).transpose()@second["initial"]
    assert (forward-wrong).parts
    assert candidate["lifetime_status"] == "SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED"
    assert candidate["full_interacting_continuum_Hamiltonian"] == "SOURCE_NATIVE_PRODUCER_REQUIRED"
    paths = [path, phase_path, finite_path, quotient_path, soft_path, axial_path,
             BASE/"matter-modes/source.json", BASE/"matter-vertices/receipt.json",
             BASE/"matter-vertices/exchange.json", BASE/"active-gauge/receipt.json",
             HERE/"independent_free_current.json", HERE/"independent_all_momentum.json",
             HERE/"independent-all-momentum-causal.json"]
    output = {"verdict": "CERTIFIED_COMPLETE_NONAXIS_DOUBLET_ORDERED_QUARTIC_CONSUMER",
        "root": ROOT_ID, "source_sha256": source.vertices["source_sha256"],
        "candidate_payload_sha256": hashlib.sha256(payload).hexdigest(),
        "input_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        "algorithm": "raw252 vertices/full original H; source Noether Gram; actual4d characteristic polynomial and Lagrange projectors; direct16d Sylvester solve; raw79 block QQ realification inverse, not supplied N/d; full289 equations; every saved ordered coefficient",
        "candidate_module_imported": False, "candidate_inverse_numerators_used": False,
        "candidate_spectral_projectors_used": False,
        "complete_current_columns_per_flow": 16, "current_fields": 97,
        "all_original_scalar70_currents_zero": True, "initial_Ward_delta_completion_checked": True,
        "all_q_boundary_dual24_zero": True, "all_q_boundary_active_scalar9_zero": True,
        "source_field_variance": "source L^-T, field L, invariant transpose pairing",
        "ordered_consumers": reports, "direct_response_count": response.response_count,
        "separate_positive_and_negative_radius_pole_bounds_checked": pole_bound_count,
        "strict_bosonic_root_radius": str(pole_radius),
        "quartic_normalization": "-1/2 after source Noether normalization on all four external indices",
        "omitted_reader_phase_negative_control_nonzero": True,
        "generic_coverage": "consumes the separately certified whole216 current/all-momentum causal producers; this receipt independently certifies the complete finite doublet consumer",
        "full_interacting_continuum_Hamiltonian": "SOURCE_NATIVE_PRODUCER_REQUIRED",
        "lifetime_status": "SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED",
        "elapsed_seconds": round(time.monotonic()-started, 3)}
    (HERE/"independent_multiparticle.json").write_text(json.dumps(output, indent=2)+"\n")
    print("PASS independent whole doublet quartic consumer", output["elapsed_seconds"], "seconds", flush=True)


if __name__ == "__main__":
    main()
