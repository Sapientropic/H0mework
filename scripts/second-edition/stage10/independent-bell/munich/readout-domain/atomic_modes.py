"""Check a full-atom exponential trial curve by its raw-generator residual.

The modes need not be eigenvectors.  Unital completely positive adjoint
evolution contracts operator norm.  Entry l1 bounds therefore certify the
curve without repeating a stiff integration or trusting its final effect.
"""
from fractions import Fraction as Q
from math import factorial

import atomic_dipole as dipole
import atomic_full_forward as full


def adjoint_integer_action(generator, matrix):
    result, by_row, by_column = {}, {}, {}
    for (i, j), (real, imag) in matrix.items():
        by_row.setdefault(i, []).append((j, real, imag))
        by_column.setdefault(j, []).append((i, real, imag))
        loss = generator.half_exit_integer[i] + generator.half_exit_integer[j]
        full._add(result, (i, j), -loss * real, -loss * imag)
    for i, j, a, b in generator.h_integer:
        for other, real, imag in by_row.get(j, ()):
            full._add(result, (i, other), -a * imag - b * real, a * real - b * imag)
        for other, real, imag in by_column.get(i, ()):
            full._add(result, (other, j), a * imag + b * real, -a * real + b * imag)
    for i, j, source_i, source_j, a, b in generator.recycle_integer:
        real, imag = matrix.get((i, j), (0, 0))
        full._add(result, (source_i, source_j), a * real + b * imag, a * imag - b * real)
    return result


def _round(value, quantum):
    return Q(full._round_nearest(value.numerator * quantum, value.denominator), quantum)


def complex_exponential(real, imag, *, bits=160, order=48):
    real, imag = full.exact(real), full.exact(imag)
    if type(bits) is not int or not 64 <= bits <= 1024 or type(order) is not int or not 24 <= order <= 128:
        raise ValueError("registered scalar-exponential precision/order required")
    if real > Q(1, 2):
        raise ValueError("bounded mode growth required")
    scale, squarings = 1, 0
    while (abs(real) + abs(imag)) / scale > Q(1, 2):
        scale *= 2
        squarings += 1
    a, b = real / scale, imag / scale
    x, y, tx, ty = Q(1), Q(0), Q(1), Q(0)
    for index in range(1, order + 1):
        tx, ty = (a * tx - b * ty) / index, (b * tx + a * ty) / index
        x, y = x + tx, y + ty
    quantum = 1 << bits
    radius = abs(a) + abs(b)
    # exp(radius)<=2 for radius<=1/2; each real rounding costs <=1/(2Q).
    error = 2 * radius ** (order + 1) / factorial(order + 1) + Q(1, quantum)
    x, y = _round(x, quantum), _round(y, quantum)
    for _ in range(squarings):
        norm = abs(x) + abs(y)
        x, y = _round(x * x - y * y, quantum), _round(2 * x * y, quantum)
        # Every exact intermediate has modulus<=exp(1/2), hence entry-l1<=3.
        error = error * (norm + 3) + Q(1, quantum)
    return (x, y), error


def _matrix(entries, quantum):
    if type(entries) is not list:
        raise ValueError("sparse full-atom mode entries required")
    result = {}
    for row in entries:
        if type(row) is not list or len(row) != 4:
            raise ValueError("mode entry must contain i,j,real,imag")
        i, j, real, imag = row
        if (any(type(value) is not int for value in row) or not 0 <= i < full.DIMENSION or
                not 0 <= j < full.DIMENSION or (i, j) in result or (real, imag) == (0, 0)):
            raise ValueError("canonical complete-atom sparse mode required")
        result[i, j] = real, imag
    return result


def certify(segment, modes, *, mode_bits=60, coefficient_bits=160, exponential_bits=160):
    if type(segment) is not full.Segment or type(modes) is not list or not modes:
        raise ValueError("raw full-atom Segment and nonempty trial modes required")
    if type(mode_bits) is not int or not 32 <= mode_bits <= 256:
        raise ValueError("mode dyadic precision outside declared range")
    quantum = 1 << mode_bits
    generator = full.Generator(segment, coefficient_bits)
    initial, final, residual_sum, exponential_error = {}, {}, Q(0), Q(0)
    records = []
    for item in modes:
        if type(item) is not dict or set(item) != {"lambda", "matrix"}:
            raise ValueError("raw mode identity required; target effect is not input")
        if type(item["lambda"]) is not list or len(item["lambda"]) != 2 or any(type(value) is not int for value in item["lambda"]):
            raise ValueError("dyadic complex mode exponent required")
        lr, li = item["lambda"]
        if Q(lr, quantum) * segment.duration > Q(1, 2):
            raise ValueError("bounded mode growth required")
        matrix = _matrix(item["matrix"], quantum)
        action = adjoint_integer_action(generator, matrix)
        norm, residual = Q(0), Q(0)
        for key in set(matrix) | set(action):
            a, b = matrix.get(key, (0, 0))
            u, v = action.get(key, (0, 0))
            real = Q(u, generator.denominator * quantum) - Q(lr * a - li * b, quantum ** 2)
            imag = Q(v, generator.denominator * quantum) - Q(li * a + lr * b, quantum ** 2)
            residual += abs(real) + abs(imag)
            norm += Q(abs(a) + abs(b), quantum)
            full._add(initial, key, Q(a, quantum), Q(b, quantum))
        scalar, error = complex_exponential(Q(lr, quantum) * segment.duration,
                                            Q(li, quantum) * segment.duration, bits=exponential_bits)
        for key, (a, b) in matrix.items():
            full._add(final, key, (a * scalar[0] - b * scalar[1]) / quantum,
                      (b * scalar[0] + a * scalar[1]) / quantum)
        residual_sum += residual
        exponential_error += norm * error
        records.append({"entry_norm_bound": str(norm), "residual_entry_norm_bound": str(residual),
                        "scalar_exponential_error": str(error)})
    initial_error = sum((abs(real - int(key == (dipole.ION, dipole.ION))) + abs(imag)
                         for key, (real, imag) in initial.items()), Q(0))
    if (dipole.ION, dipole.ION) not in initial:
        initial_error += 1
    # Re(lambda)*T<=1/2 gives exp(Re(lambda)*t)<=2 throughout the raw segment.
    residual_error = 2 * segment.duration * residual_sum
    coefficient_error = segment.duration * generator.generator_difference_bound
    error = initial_error + residual_error + coefficient_error + exponential_error
    hermitian = {}
    for i, j in set(final) | {(j, i) for i, j in final}:
        a, b = final.get((i, j), (0, 0))
        c, d = final.get((j, i), (0, 0))
        full._add(hermitian, (i, j), (a + c) / 2, (b - d) / 2)
    ground = [dipole.INDEX[dipole.State("ground", 1, m)] for m in (-1, 0, 1)]
    effect = []
    for i in ground:
        row = []
        for j in ground:
            real, imag = hermitian.get((i, j), (Q(0), Q(0)))
            row.append({"real": [str(real - error), str(real + error)],
                        "imag": [str(imag - error), str(imag + error)]})
        effect.append(row)
    return {"schema": "stage10-full-atom-mode-enclosure/v1", "physical_dimension": full.DIMENSION,
            "observable_complex_coordinates": full.COMPLEX_COORDINATES,
            "raw_program": segment.record(), "raw_program_sha256": full._program_digest([segment.record()]),
            "mode_bits": mode_bits, "coefficient_bits": coefficient_bits, "exponential_bits": exponential_bits,
            "modes": len(modes), "mode_error_records": records,
            "initial_operator_error": str(initial_error), "residual_operator_error": str(residual_error),
            "coefficient_operator_error": str(coefficient_error), "exponential_operator_error": str(exponential_error),
            "operator_error_bound": str(error), "ground_basis": ground, "ground_F1_ion_effect": effect,
            "observable_center": [[i, j, str(real), str(imag)] for (i, j), (real, imag) in sorted(hermitian.items())],
            "true_generator_is_lindblad": True, "error_transport": "unital CP adjoint operator-norm contraction",
            "eigenvector_correctness_assumed": False, "actual_hardware_identity_asserted": False}
