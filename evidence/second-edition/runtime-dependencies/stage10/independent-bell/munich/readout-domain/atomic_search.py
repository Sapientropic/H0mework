"""Fast raw-field search; accepted candidates are checked by the exact producer.

The search evaluates the adjoint of the same full 33-state generator.  It has
no measured-effect input and produces no numerical certificate.
"""
from functools import lru_cache
from math import sqrt

import numpy as np
from scipy import sparse
from scipy.sparse.linalg import expm_multiply

import atomic_dipole as dipole
import atomic_full_forward as exact

N = len(dipole.STATES)


def radical(value):
    return sum(float(coefficient) * sqrt(root) for root, coefficient in value.terms)


def complex_value(value):
    if isinstance(value, dipole.Radical):
        return radical(value)
    return radical(value.real) + 1j * radical(value.imag)


def matrix(entries):
    if not entries:
        return sparse.csr_matrix((N, N), dtype=complex)
    rows, columns, values = zip(*[(i, j, complex_value(value)) for (i, j), value in entries.items()])
    return sparse.csr_matrix((values, (rows, columns)), shape=(N, N))


@lru_cache(maxsize=2)
def terms(convention):
    return {(line, q): matrix(entries) for line, q, entries in dipole.hamiltonian_terms(convention)}


@lru_cache(maxsize=2)
def jumps(regime):
    return tuple((jump.label[:2], matrix(jump.matrix)) for jump in
                 dipole.natural_jumps(regime, dict.fromkeys(exact.WIDTHS, 1)))


def dissipator(jump):
    identity = sparse.eye(N, dtype=complex, format="csr")
    loss = jump.getH() @ jump
    return (sparse.kron(jump.conjugate(), jump, format="csr") -
            (sparse.kron(identity, loss, format="csr") +
             sparse.kron(loss.T, identity, format="csr")) / 2)


class Kernel:
    def __init__(self, template):
        if type(template) is not exact.Segment:
            raise TypeError("raw full-atom Segment required")
        self.template = template
        self.identity = sparse.eye(N, dtype=complex, format="csr")
        state_mode = set(template.detunings) == set(dipole.STATES)
        energies = [radical(template.detunings[state if state_mode else (state.family, state.f)])
                    for state in dipole.STATES]
        self.diagonal = sparse.diags(-np.asarray(energies), format="csr")
        self.bath = sparse.csr_matrix((N * N, N * N), dtype=complex)
        for label, jump in jumps(template.radiation_regime):
            self.bath += float(template.gammas[label]) * dissipator(jump)
        for state, rate in template.ion_rates.items():
            if rate:
                jump = sparse.csr_matrix(([1], ([dipole.ION], [dipole.INDEX[state]])), shape=(N, N))
                self.bath += float(rate) * dissipator(jump)
        bridge = dipole.source_qubit_bridge()
        self.embedding = np.zeros((N, 2), dtype=complex)
        for column, name in enumerate(("u_x", "d_x")):
            for index, value in bridge[name].items():
                self.embedding[index, column] = complex_value(value)

    def generator(self, fields_r, fields_c, r=1, c=1):
        for field in (fields_r, fields_c):
            if set(field) != set(dipole.Q_COMPONENTS) or not all(np.isfinite(value) for value in field.values()):
                raise ValueError("finite explicit three-component fields required")
        if not np.isfinite(r) or not np.isfinite(c):
            raise ValueError("finite reduced Rabi amplitudes required")
        hamiltonian = self.diagonal.copy()
        for line, field, amplitude in (("D1", fields_r, r), ("D2", fields_c, c)):
            for q in dipole.Q_COMPONENTS:
                excitation = amplitude * field[q] * terms(self.template.field_convention)[line, q]
                hamiltonian += excitation + excitation.getH()
        return (-1j * (sparse.kron(self.identity, hamiltonian, format="csr") -
                       sparse.kron(hamiltonian.T, self.identity, format="csr")) + self.bath)

    def ion_effect(self, fields_r, fields_c, *, r=1, c=1, duration=None):
        duration = float(self.template.duration if duration is None else duration)
        if not np.isfinite(duration) or duration < 0:
            raise ValueError("nonnegative finite duration required")
        generator = self.generator(fields_r, fields_c, r, c)
        observable = np.zeros(N * N, dtype=complex)
        observable[dipole.ION * (N + 1)] = 1
        evolved = expm_multiply(duration * generator.getH(), observable,
                                traceA=duration * generator.diagonal().conjugate().sum())
        effect = self.embedding.conj().T @ evolved.reshape((N, N), order="F") @ self.embedding
        if np.max(np.abs(effect - effect.conj().T)) > 1e-10:
            raise ArithmeticError("search adjoint response lost Hermiticity")
        return (effect + effect.conj().T) / 2


def observable_coordinates(effect, background, efficiency):
    if not 0 <= background <= 1 or not 0 <= efficiency <= 1 or effect.shape != (2, 2):
        raise ValueError("physical detector variables and 2x2 ion effect required")
    k = (1 - background) * efficiency
    return np.asarray([1 - 2 * background - k * np.trace(effect).real,
                       -2 * k * effect[0, 1].real,
                       2 * k * effect[0, 1].imag,
                       -k * (effect[0, 0] - effect[1, 1]).real])


def joint_table(alice, bob):
    answer = []
    if np.shape(alice) != (2, 4) or np.shape(bob) != (2, 4):
        raise ValueError("two same-device setting observables per side required")
    for h in (0, 1):
        for a in (0, 1):
            for b in (0, 1):
                first, second = alice[a], bob[b]
                correlation = (first[0] * second[0] - (1 - 2 * h) *
                               (first[1] * second[1] + first[2] * second[2]) - first[3] * second[3])
                answer.append([(1 + (1 - 2 * x) * first[0] + (1 - 2 * y) * second[0] +
                                (1 - 2 * x) * (1 - 2 * y) * correlation) / 4
                               for x in (0, 1) for y in (0, 1)])
    return np.asarray(answer)
