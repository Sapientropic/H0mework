#!/usr/bin/env python3
"""Consistent initial data and the original Ward quotient of the retained action.

All reductions are exact over the source algebraic field at the supplied real
momentum. Matter remains part of the original mixed Jacobi action; no common
bosonic CCR is assigned to this phase space. Its characteristic polynomial
describes that linearized action, not an interacting composite pole.
"""
from __future__ import annotations

import hashlib
import json
import re
import time

import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from dynamic import HERE, BASE, ROOT, ROOT_ID

K = s.symbols('k1:4', real=True)
P = s.symbols('p0:4')
LAM = s.Symbol('source_laplace')
DOMAIN = s.QQ.algebraic_field(s.sqrt(2), s.sqrt(15), s.I)
LOCALS = {str(v): v for v in (*K, *P, LAM)}


def parse(value):
    return s.sympify(re.sub(r'\blambda\b', str(LAM), value), locals=LOCALS)


def decode(record):
    return s.SparseMatrix(*record['shape'], {(i, j): parse(v) for i, j, v in record['entries']})


def encode(matrix):
    if isinstance(matrix, DM):
        matrix = matrix.to_Matrix()
    return {'shape': list(matrix.shape), 'entries': [[i, j, str(s.expand(v))]
        for (i, j), v in sorted(s.SparseMatrix(matrix).todok().items())]}


def dm(matrix):
    return DM.from_Matrix(matrix).convert_to(DOMAIN).to_sparse()


def zero(matrix):
    assert matrix.is_zero_matrix


def null(matrix):
    # Normalize each basis vector before the next elimination. Keeping a
    # common determinant denominator here causes enormous algebraic integers.
    return matrix.nullspace(divide_last=True).transpose()


def identity(size):
    return DM.eye((size, size), DOMAIN).to_sparse()


def adjoint(matrix):
    return dm(matrix.to_Matrix().conjugate().T)


def particular(matrix, rhs):
    """Generate an actual exact solution, using independent pivot rows/columns."""
    rows = matrix.transpose().rref()[1]
    columns = matrix.rref()[1]
    values = matrix.extract(rows, columns).inv()*rhs.extract(rows, range(rhs.shape[1]))
    result = DM({i: values.rep[j] for j, i in enumerate(columns) if j in values.rep},
                (matrix.shape[1], rhs.shape[1]), DOMAIN)
    zero(matrix*result-rhs)
    return result


class RetainedHamiltonianReduction:
    def __init__(self, momentum):
        self.momentum = tuple(map(s.sympify, momentum))
        assert len(self.momentum) == 3
        assert all(not v.free_symbols and v.is_real for v in self.momentum)
        path = HERE/'retained_matter_action.json'
        self.record = json.loads(path.read_bytes())
        assert self.record['root'] == ROOT_ID
        for key in ('source_sha256', 'input_sha256'):
            for name, digest in self.record[key].items():
                assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
        substitute = dict(zip(K, self.momentum))
        self.omega242 = dm(decode(self.record['presymplectic_form']).subs(substitute))
        self.energy242 = dm(decode(self.record['Legendre_energy_hessian']).subs(substitute))
        kinetic = dm(decode(self.record['retained_time_coefficients'][2]))
        columns = kinetic.rref()[1]
        assert len(columns) == 51
        velocity = dm(s.SparseMatrix(121, 51, {(i, j): 1 for j, i in enumerate(columns)}))
        self.velocity_readback = particular(kinetic*velocity, kinetic)
        zero(self.velocity_readback*velocity-identity(51))
        self.section = dm(s.diag(s.eye(121), velocity.to_Matrix()))
        self.retraction = dm(s.diag(s.eye(121), self.velocity_readback.to_Matrix()))
        zero(self.retraction*self.section-identity(172))
        zero(self.omega242*(identity(242)-self.section*self.retraction))
        zero(self.energy242*(identity(242)-self.section*self.retraction))
        self.omega = adjoint(self.section)*self.omega242*self.section
        self.energy = adjoint(self.section)*self.energy242*self.section
        zero(adjoint(self.omega)+self.omega)
        zero(adjoint(self.energy)-self.energy)
        C = identity(172)
        self.chain = []
        for _ in range(173):
            B, F = self.omega*C, self.energy*C
            constraint = null(B.transpose()).transpose()*F
            rank = len(constraint.rref()[1])
            self.chain.append({'carrier_dimension': C.shape[1], 'new_constraints': rank})
            if rank == 0:
                break
            C = C*null(constraint)
        else:
            raise AssertionError('strictly descending finite consistency chain did not terminate')
        self.consistent = C
        self.generator = particular(B, F)
        self.free_derivatives = null(B)
        self.restricted_omega = adjoint(C)*self.omega*C
        self.restricted_energy = adjoint(C)*self.energy*C
        zero(self.restricted_omega*self.generator-self.restricted_energy)
        zero(adjoint(self.generator)*self.restricted_omega+self.restricted_omega*self.generator)
        self.gauge = null(self.restricted_omega)
        zero(self.restricted_energy*self.gauge)

        # The radical must be generated by the original nine Ward functions
        # and their time derivatives, not by an independently chosen gauge.
        U = decode(self.record['normal_coordinate_change'])
        gauge_symbol = U[:, 112:121].subs(dict(zip(P, [LAM, *[s.I*k for k in self.momentum]])))
        degree = max(s.degree(v, LAM) for v in gauge_symbol.todok().values())
        jet = s.SparseMatrix.vstack(gauge_symbol, LAM*gauge_symbol)
        jet_coefficients = [dm(jet.applyfunc(lambda v: s.expand(v).coeff(LAM, n)))
                            for n in range(degree+2)]
        ward_coefficients = [self.retraction*value for value in jet_coefficients]
        previous = DM.zeros((172, 9), DOMAIN)
        ward_coordinates = []
        for coefficient in ward_coefficients:
            zero(self.omega*previous-self.energy*coefficient)
            coordinates = particular(C, coefficient)
            zero(self.restricted_omega*coordinates)
            ward_coordinates.append(coordinates)
            previous = coefficient
        zero(self.omega*previous)
        ward_span = DM.hstack(*ward_coordinates)
        assert len(ward_span.rref()[1]) == self.gauge.shape[1]
        self.ward_coordinates = ward_coordinates

        # Quotient by precisely that source radical. The complement is a
        # computational section; the projected evolution does not depend on it.
        quotient = null(self.gauge.transpose()).transpose()
        quotient_section = particular(quotient, identity(quotient.shape[0]))
        self.quotient = quotient
        self.quotient_section = quotient_section
        self.physical_generator = quotient*self.generator*quotient_section
        zero(quotient*self.generator-self.physical_generator*quotient)
        zero(quotient*self.free_derivatives)
        self.physical_omega = adjoint(quotient_section)*self.restricted_omega*quotient_section
        self.physical_energy = adjoint(quotient_section)*self.restricted_energy*quotient_section
        assert len(self.physical_omega.rref()[1]) == self.physical_omega.shape[0]
        zero(self.physical_omega*self.physical_generator-self.physical_energy)
        zero(adjoint(self.physical_generator)*self.physical_omega+
             self.physical_omega*self.physical_generator)

    def report(self):
        return {
            'momentum': list(map(str, self.momentum)),
            'velocity_quotient_section': encode(self.section),
            'velocity_quotient_retraction': encode(self.retraction),
            'consistent_initial_data_chain': self.chain,
            'consistent_initial_data_embedding': encode(self.consistent),
            'consistent_generator': encode(self.generator),
            'free_derivative_directions': encode(self.free_derivatives),
            'original_Ward_jet_coordinates': list(map(encode, self.ward_coordinates)),
            'original_Ward_radical_dimension': self.gauge.shape[1],
            'quotient_map': encode(self.quotient),
            'quotient_section': encode(self.quotient_section),
            'Hamiltonian_generator': encode(self.physical_generator),
            'nondegenerate_phase_form': encode(self.physical_omega),
            'Hamiltonian_energy': encode(self.physical_energy),
            'dynamic_quotient_dimension': self.physical_generator.shape[0],
            'all_original_source_equations_and_Ward_coverage_checked': True,
        }


def main():
    started = time.monotonic()
    dynamic = json.loads((HERE/'dynamic.json').read_bytes())
    actual = next(row for row in dynamic['samples'] if row['name'] == 'energy_transfer')
    transfer = decode(actual['transfer'])
    source_momentum = tuple(s.simplify(v/s.I) for v in transfer[1:, 0])
    reports = []
    for momentum in ((0, 0, 0), source_momentum):
        reduction = RetainedHamiltonianReduction(momentum)
        report = reduction.report()
        coefficients = reduction.physical_generator.charpoly()
        polynomial = s.Poly.from_list([DOMAIN.to_sympy(v) for v in coefficients], LAM)
        report['linearized_characteristic_polynomial'] = str(s.factor(polynomial.as_expr()))
        reports.append(report)
        print('PASS exact retained Hamiltonian quotient', momentum, reduction.chain,
              'Ward radical', reduction.gauge.shape[1], 'quotient', polynomial.degree(), flush=True)

    # A direct consumer of the generated126 time generator: compare the
    # independently generated canonical79 and dual24 divisors at zero k.
    spectrum_path = BASE/'canonical-active/spectrum/receipt.json'
    spectrum = json.loads(spectrum_path.read_bytes())
    units = json.loads((BASE/'matter-modes/source.json').read_bytes())
    clock = parse(units['time_scale'])
    u = s.Symbol('u')
    expected = s.Poly(1, LAM)
    for group in ('canonical_q_zero_factors', 'complement_q_zero_factors'):
        for factor, multiplicity in spectrum[group].items():
            expected *= s.Poly(s.sympify(factor).subs(u, LAM/clock), LAM).monic()**multiplicity
    actual = s.Poly(parse(reports[0]['linearized_characteristic_polynomial']), LAM)
    assert s.expand(actual.as_expr()-expected.monic().as_expr()) == 0
    assert actual.degree() == expected.degree() == 126
    print('PASS actual126 generator characteristic equals original canonical79 plus dual24 divisors at zero momentum', flush=True)
    paths = [HERE/'retained_hamiltonian_reduction.py', HERE/'retained_matter_action.json',
             HERE/'independent_retained_matter_action.json', HERE/'dynamic.json',
             spectrum_path, BASE/'matter-modes/source.json']
    output = {
        'root': ROOT_ID, 'source_sha256': reduction.record['source_sha256'],
        'input_sha256': {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'scope': 'ORIGINAL_RETAINED_ACTION_CONSISTENT_INITIAL_DATA_AND_WARD_HAMILTONIAN_QUOTIENT_AT_SOURCE_MOMENTA',
        'source_momenta': reports,
        'zero_momentum_divisor_identity': 'det(lambda I-A126)=monic(det A79(lambda,0)*det B24(lambda,0))',
        'quantum_scope': 'homogeneous classical mixed Jacobi dynamics and original Ward quotient; full252 CAR, interacting spectral measure and the sourced distributional evolution remain downstream',
        'momentum_scope': 'the two displayed exact momenta; no uniform momentum rank theorem asserted',
        'lifetime_status': 'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds': round(time.monotonic()-started, 3),
    }
    (HERE/'retained_hamiltonian_reduction.json').write_text(json.dumps(output, separators=(',', ':'))+'\n')
    print('PASS original Ward-generated Hamiltonian reduction', output['elapsed_seconds'], 'seconds', flush=True)


if __name__ == '__main__':
    main()
