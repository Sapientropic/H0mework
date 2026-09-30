#!/usr/bin/env python3
"""Independent coefficient audit; never imports either candidate compute.py.

Exterior actions use creation/annihilation bit signs. Dirac determinants use
the chiral off-diagonal blocks, rather than the candidate's 8x8 determinant.
"""
from __future__ import annotations

import argparse
import itertools
import json
import re
from pathlib import Path

import sympy as s


def decode(payload, symbols):
    return s.SparseMatrix(*payload["shape"], {
        (row, col): s.sympify(value.replace("lambda", "lam"), locals=symbols)
        for row, col, value in payload["entries"]})


def realify(matrix):
    result = s.MutableSparseMatrix(2 * matrix.rows, 2 * matrix.cols, {})
    for (row, col), value in s.SparseMatrix(matrix).todok().items():
        real, imag = s.expand_complex(value).as_real_imag()
        result[row, col] = real
        result[row, col + matrix.cols] = -imag
        result[row + matrix.rows, col] = imag
        result[row + matrix.rows, col + matrix.cols] = real
    return s.SparseMatrix(result)


def basis(degree):
    return list(itertools.combinations(range(7), degree))


def exterior(matrix, degree):
    words = basis(degree)
    masks = [sum(1 << index for index in word) for word in words]
    indices = {mask: index for index, mask in enumerate(masks)}
    result = s.MutableSparseMatrix(len(words), len(words), {})
    for col, occupied in enumerate(masks):
        for old in range(7):
            if not occupied & (1 << old):
                continue
            removed = occupied ^ (1 << old)
            removal_sign = (-1) ** ((occupied & ((1 << old) - 1)).bit_count())
            for new in range(7):
                if removed & (1 << new):
                    continue
                creation_sign = (-1) ** ((removed & ((1 << new) - 1)).bit_count())
                result[indices[removed | (1 << new)], col] += (
                    removal_sign * creation_sign * matrix[new, old])
    return s.SparseMatrix(result)


def wedge_sign(first, second):
    return (-1) ** sum(left > right for left in first for right in second)


def equal(left, right):
    difference = s.SparseMatrix(left - right)
    assert all(s.cancel(value) == 0 for value in difference.todok().values())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    core = root / "Lean/SaturationMonoid/PhysicsCore"
    directory = root / "Verification/physics/low-energy-phenomenology"
    mixed = json.loads((directory / "mixed-symbol/results.json").read_text())
    active = json.loads((directory / "active-sector/receipt.json").read_text())
    full = json.loads((directory / "mixed-symbol/symbol.json").read_text())
    names = ["colorZeroIndex", "colorOneIndex", "colorTwoIndex", "weakZeroIndex",
             "weakOneIndex", "hyperPlusIndex", "hyperMinusIndex"]
    source = (core / "SU7ExteriorYukawaMassSpectrum.lean").read_text()
    scalar_text = source.split("def finiteGenerationScalarSubset :", 1)[1].split("\ndef ", 1)[0]
    terms = re.findall(r"\|\s*[01],\s*[01]\s*=>\s*\{([^}]+)\}", scalar_text)
    vacuum = {tuple(sorted(names.index(name.strip()) for name in term.split(","))): 1
              for term in terms}
    assert len(vacuum) == 4
    clifford = (core / "DiracCliffordRepresentation.lean").read_text()
    gamma = []
    for name in ("Zero", "One", "Two", "Three"):
        text = clifford.split(f"def diracGamma{name} : DiracMatrix :=", 1)[1].split("]", 1)[0]
        text = text.split("!![", 1)[1].replace("Complex.I", "I")
        gamma.append(s.SparseMatrix([[s.sympify(x.strip()) for x in row.split(",")]
                                    for row in text.split(";")]))
    assert all(gamma[j] ** 2 == (-1 if j == 0 else 1) * s.eye(4) for j in range(4))
    rotation = [gamma[2] * gamma[3], gamma[3] * gamma[1], gamma[1] * gamma[2]]
    p = [s.Matrix([[0, s.I/2], [s.I/2, 0]]),
         s.Matrix([[0, s.Rational(1, 2)], [-s.Rational(1, 2), 0]]),
         s.diag(s.I/2, -s.I/2)]
    background = [s.diag(matrix, s.zeros(5)) for matrix in p]
    actions = {degree: [exterior(matrix, degree) for matrix in background] for degree in (6, 2, 4)}
    b2, b4, b6 = basis(2), basis(4), basis(6)
    y = s.MutableSparseMatrix(7, 21, {})
    for col, pair in enumerate(b2):
        for word in vacuum:
            if not set(pair).intersection(word):
                y[b6.index(tuple(sorted(pair + word))), col] += wedge_sign(pair, word)
    yi = s.MutableSparseMatrix(63, 63, {})
    yi[:7, 7:28] = y
    Y = s.kronecker_product(s.diag(0, 0, 1, 1), yi)
    M = s.MutableSparseMatrix(252, 35, {})
    for spin, pair, coefficient in ((2, (1, 5), 1), (3, (0, 5), -1)):
        for col, word in enumerate(b4):
            if not set(pair).intersection(word):
                M[63 * spin + b6.index(tuple(sorted(pair + word))), col] = (
                    coefficient * wedge_sign(pair, word))
    M = s.SparseMatrix(M)
    N, alpha, kappa = s.symbols("N alpha kappa", positive=True, real=True)
    lam, k1, k2, k3 = s.symbols("lam k1 k2 k3", real=True)
    symbols = {str(x): x for x in (N, alpha, kappa, lam, k1, k2, k3)}
    symbols["I"] = s.I
    momenta = (k1, k2, k3)
    MR, YR = realify(M), realify(Y)
    B = s.diag(s.eye(252), -s.eye(252))
    Msharp = MR.T * B
    equal(y, decode(mixed["internal_yukawa"], symbols))
    equal(Y, decode(mixed["whole_yukawa"], symbols))
    equal(M, decode(mixed["scalar_to_primal"], symbols))
    equal(Msharp, decode(mixed["independent_dual_to_scalar"], symbols))
    assert Y.rank() == 10 and M.rank() == 9 and MR.rank() == 18
    equal(B * YR.T * B, realify(Y.T))
    # Negative control: complex-linear dual evaluation and Hermitian evaluation disagree.
    imaginary = s.Matrix([0, 1])
    assert (imaginary.T * s.diag(1, -1) * imaginary)[0] == -1
    assert (imaginary.T * imaginary)[0] == 1
    C = s.MutableSparseMatrix(1078, 1078, {})
    C[:70, 574:] = Msharp
    C[70:574, :70] = MR
    C[70:574, 70:574] = YR
    C[574:, 574:] = realify(Y.T)
    C = s.SparseMatrix(C)
    equal(C, decode(mixed["mixed_off_diagonal"], symbols))
    equal(C*C, decode(mixed["mixed_square"], symbols))
    assert C*C*C == s.zeros(1078) and (MR*Msharp).rank() == 18
    internal = [s.diag(actions[6][j], actions[2][j], actions[4][j]) for j in range(3)]
    coefficient = [s.I*s.kronecker_product(gamma[0], s.eye(63))/N] + [
        s.I*s.kronecker_product(gamma[j+1], s.eye(63)) for j in range(3)]
    connection = sum((s.I*s.kronecker_product(gamma[j+1], s.eye(63)) *
                      (kappa/2*s.kronecker_product(rotation[j], s.eye(63)) +
                       alpha*s.kronecker_product(s.eye(4), internal[j])) for j in range(3)),
                     s.zeros(252))
    DR = lam*realify(coefficient[0]) + realify(connection)
    DRdual = -lam*realify(coefficient[0].T) + realify(connection.T)
    for j in range(3):
        DR += s.I*momenta[j]*realify(coefficient[j+1])
        DRdual -= s.I*momenta[j]*realify(coefficient[j+1].T)
    KR = (lam**2/N**2-2)*s.eye(70) - sum(
        ((s.I*momenta[j]*s.eye(70)+alpha*realify(actions[4][j]))**2 for j in range(3)),
        s.zeros(70))
    D = s.diag(KR, DR, DRdual, cls=s.SparseMatrix)
    equal(decode(full["symbol"], symbols), D+C)
    order = mixed["topological_coordinate_permutation"]
    assert sorted(order) == list(range(1078))
    block = {}; cursor = 0
    for label, size in enumerate(mixed["topological_block_sizes"]):
        for coordinate in order[cursor:cursor+size]:
            block[coordinate] = label
        cursor += size
    assert cursor == 1078
    assert all(block[row] > block[col] for row, col in C.todok())
    assert all(block[row] == block[col] for row, col in D.todok())
    arrows = {(block[col], block[row]) for row, col in C.todok()}
    assert arrows == {(0, 4), (0, 5), (2, 6), (5, 6)}
    assert not any((left, middle) in arrows and (middle, right) in arrows and
                   (right, last) in arrows for left, middle, right, last in itertools.product(range(7), repeat=4))
    # Bare nilpotence is insufficient when G can exchange source grades.
    badC = s.Matrix([[0, 1], [0, 0]])
    badG = s.Matrix([[0, 1], [1, 0]])
    assert badC**3 == s.zeros(2) and badC*badG*badC*badG*badC != s.zeros(2)
    bad_inverse = badG-badG*badC*badG+badG*badC*badG*badC*badG
    assert (badG+badC)*bad_inverse != s.eye(2)
    # Source Clifford matrices give a chiral off-diagonal symbol. Compute its two small determinants.
    singlet = s.I*gamma[0]*lam/N-sum((gamma[j+1]*momenta[j] for j in range(3)), s.zeros(4))
    singlet += sum((s.I*kappa/2*gamma[j+1]*rotation[j] for j in range(3)), s.zeros(4))
    doublet = s.kronecker_product(singlet, s.eye(2)) + sum(
        (s.I*alpha*s.kronecker_product(gamma[j+1], p[j]) for j in range(3)), s.zeros(8))
    determinants = []
    for matrix, half in ((singlet, 2), (doublet, 4)):
        assert matrix[:half, :half] == s.zeros(half)
        assert matrix[half:, half:] == s.zeros(half)
        determinants.append(s.expand(matrix[:half, half:].det(method="bareiss") *
                                     matrix[half:, :half].det(method="bareiss")))
    factors = {name: s.sympify(value.replace("lambda", "lam"), locals=symbols)
               for name, value in mixed["compact_dirac_factors"].items()}
    assert s.cancel(determinants[0]-factors["F0"]) == 0
    assert s.cancel(determinants[1]-factors["Fplus"]*factors["Fminus"]) == 0
    # This similarity separates internal complex structure from the external Fourier i.
    for matrix in coefficient[:2]:
        small = matrix.extract(list(range(0, 252, 63)), list(range(0, 252, 63)))
        transform = s.BlockMatrix([[s.eye(4), s.I*s.eye(4)], [s.eye(4), -s.I*s.eye(4)]]).as_explicit()
        equal(transform*realify(small), s.diag(small, s.conjugate(small))*transform)
    for degree, multiplicity in mixed["graded_multiplicities"].items():
        degree = int(degree)
        permutation = mixed["representation_permutations"][str(degree)]
        for j in range(3):
            equal(actions[degree][j].extract(permutation, permutation),
                  s.diag(s.zeros(multiplicity["singlets"]), *([p[j]]*multiplicity["doublets"])))
    assert sum(item["singlets"] for item in mixed["graded_multiplicities"].values()) == 31
    assert sum(item["doublets"] for item in mixed["graded_multiplicities"].values()) == 16
    print("PASS mixed: full stored 1078 symbol independently reconstructed; nonzero M and two-step rank 18")
    print("PASS mixed: full k determinants by chiral block product; wrong pairing and non-preserving G controls")

    # Generate all 12 P286 directions independently of the candidate generator factory.
    generators = []
    for group in ((0, 1, 2), (3, 4)):
        for left, right in itertools.combinations(group, 2):
            generators.append((f"A{left}{right}", s.SparseMatrix(7, 7, {(left, right): 1, (right, left): -1})))
            generators.append((f"S{left}{right}", s.SparseMatrix(7, 7, {(left, right): s.I, (right, left): s.I})))
        for left in group[:-1]:
            generators.append((f"D{left}-{group[-1]}", s.SparseMatrix(7, 7, {(left, left): s.I, (group[-1], group[-1]): -s.I})))
    generators.append(("Y", s.diag(0, 0, 0, 0, 0, s.I, -s.I)))
    assert [name for name, _ in generators] == active["p286_labels"]
    assert s.Matrix.hstack(*[s.Matrix(matrix).reshape(49, 1) for _, matrix in generators]).rank() == 12
    H = decode(active["H_inclusion"], symbols)
    assert [b2[index] for index in range(21) if any(H[index, col] for col in range(3))] == [(0, 5), (1, 5), (2, 5)]
    P2 = H*H.T
    P = s.kronecker_product(s.eye(4), s.diag(s.zeros(7), P2, s.zeros(35)))
    equal(P2, decode(active["H_internal_projection"], symbols))
    equal(P, decode(active["H_whole_spin_projection"], symbols))
    assert P.rank() == 12 and P*Y == s.zeros(252) and Y*P == s.zeros(252)
    preparations = [decode(column, symbols) for column in active["independent_background_phase_columns"]]
    expected_preparations = []
    for upper, lower in ((1, 0), (0, 1)):
        vector = s.zeros(252, 1)
        for spin, color, value in ((0, 1, upper), (1, 0, -upper), (2, 1, lower), (3, 0, -lower)):
            vector[63*spin+7+b2.index((color, 5))] = value
        expected_preparations.append(vector)
    assert preparations == expected_preparations
    for i, (_, generator) in enumerate(generators):
        rho = exterior(generator, 2)
        expected = generator[:3, :3]+generator[5, 5]*s.eye(3)
        equal(rho*H, H*expected)
        equal(expected, decode(active["p286_H_actions"][i], symbols))
        equal(P2*rho, rho*P2)
    old = s.diag(*[int(word in ((0, 5), (1, 5))) for word in b2])
    color_cross = dict(generators)["A02"]
    old_leak = (s.eye(21)-old)*exterior(color_cross, 2)*old
    equal(old_leak, decode(active["old_doublet_leakage"], symbols))
    assert old_leak != s.zeros(21)
    mother_cross = s.SparseMatrix(7, 7, {(0, 3): 1, (3, 0): -1})
    mother_leak = (s.eye(21)-P2)*exterior(mother_cross, 2)*P2
    equal(mother_leak, decode(active["full_mother_leakage"], symbols))
    assert mother_leak != s.zeros(21)
    all_actions = [s.eye(63)] + [s.diag(exterior(t, 6), exterior(t, 2), exterior(t, 4)) for _, t in generators]
    Q = s.SparseMatrix(s.eye(252)-P)
    for internal in all_actions:
        for row, col in itertools.product(range(4), repeat=2):
            T = s.SparseMatrix(s.kronecker_product(s.SparseMatrix(4, 4, {(row, col): 1}), internal))
            for psi in preparations:
                assert Q*(T*psi) == s.zeros(252, 1)
                assert (psi.T*T)*Q == s.zeros(1, 252)
    assert active["two_sided_spin_gauge_action_basis_checks"] == 13*16
    v = s.Matrix([vacuum.get(word, 0) for word in b4])
    complex_orbit = s.Matrix.hstack(*[exterior(t, 4)*v for _, t in generators])
    orbit = complex_orbit.applyfunc(s.re).col_join(complex_orbit.applyfunc(s.im))
    equal(orbit, decode(active["scalar_orbit"], symbols))
    J = decode(active["J_basis"], symbols)
    PJ = J*(J.T*J).inv()*J.T
    equal(PJ, decode(active["J_projector"], symbols))
    equal(J.T*J, decode(active["J_Gram"], symbols))
    assert orbit.rank() == J.rank() == 9 and (s.eye(70)-PJ).rank() == 61
    equal(PJ*orbit, orbit)
    assert MR*PJ == s.zeros(504, 70) and PJ*Msharp == s.zeros(70, 504)
    compact_rows = [part*252+spin*63+entry
                    for part in range(2) for spin in (2, 3) for entry in range(7)]
    equal(MR.extract(compact_rows, range(70)), decode(active["M_real"], symbols))
    equal(Msharp.extract(range(70), compact_rows), decode(active["M_sharp"], symbols))
    restrictions = []
    for j in range(3):
        action = realify(actions[4][j])
        assert action*PJ == PJ*action
        small = (J.T*J).inv()*J.T*action*J
        equal(small, decode(active["background_scalar_J_actions"][j], symbols))
        restrictions.append(small)
    casimir = -sum((matrix*matrix for matrix in restrictions), s.zeros(9))
    equal(casimir, decode(active["background_J_Casimir"], symbols))
    assert casimir.eigenvals() == {s.Integer(0): 5, s.Rational(3, 4): 4}
    projection_doublets = 4*casimir/3
    momentum_action = sum((momenta[j]*restrictions[j] for j in range(3)), s.zeros(9))
    p2 = k1*k1+k2*k2+k3*k3
    equal(momentum_action**2, -p2*projection_doublets/4)
    equal((s.eye(9)-projection_doublets)*momentum_action, s.zeros(9))
    x = s.Symbol("x")
    assert s.expand(momentum_action.charpoly(x).as_expr()-x**5*(x*x+p2/4)**2) == 0
    # Independent component arithmetic and exterior-factor subtraction.
    primitive = 9+4*12+4*4+2*(2*4*3)
    auxiliary = 4*6+6*6+6*6+6*12
    outer = 61+2*(2*4*(63-3))
    assert primitive == active["active_real_dimension"] == 121
    assert auxiliary == sum(active["algebraic_fields_still_registered"].values()) == 168
    assert primitive+auxiliary == active["unreduced_Lorentz_admissible_active_real_dimension"] == 289
    assert primitive+auxiliary+(64-24) == 329
    assert outer == active["outer_real_dimension"] == 1021
    assert outer+primitive == 70+2*504+48+16
    assert active["outer_diagonal_factor_exponents"] == {"Ks":30-5, "Kd":20-2, "F0":4*(31-1), "Fplus_Fminus":4*(16-1)}
    print("PASS active: all P286 coefficients, H current legs, real J split and characteristic factors")
    print("PASS active: dimensions 121 / 289 / 329, exterior 1021; factors 25 / 18 / 120 / 60")
    for group, checks in (("mixed-symbol", ["source_gamma_parse", "bit_exterior_reconstruction", "all_1078_symbol_entries", "independent_dual_sign_control", "inserted_G_counterexample", "nonzero_M_rank_9", "two_step_rank_18", "chiral_block_all_momentum_determinants", "grade_permutation_identity"]),
                          ("active-sector", ["all_12_P286_coefficients", "all_208_two_sided_current_coefficients", "real_J_projection", "J_characteristic_polynomial", "M_J_and_J_Msharp_zero", "121_289_329_1021_counts", "outer_factor_subtraction"])):
        output = directory/group/"audit"/"independent-receipt.json"
        output.write_text(json.dumps({"status":"PASS", "checks":checks,
                                      "source":"actual original coefficient matrices",
                                      "full_nine_field_physical_poles_certified":False}, indent=2)+"\n")


if __name__ == "__main__":
    main()
