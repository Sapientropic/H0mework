"""c0002 analytic candidate finder for the unchanged four-component objective.

This module reads no records and grants no numerical verdict. Its fixed search
interior is a finder domain; the complete source/effect carrier remains frozen.
"""
from __future__ import annotations

import math

from model import encode
from primary import (COMPONENT_WEIGHTS, CONTEXTS, TerminalObjective, float_source_table,
                     polar_effects, rational_candidate)


VERSION = "stage10-munich-readout-c0002"
EFFECT_BOUNDS = ((-.99, .99), (0., .999999), (-math.pi, math.pi))
BOUNDS = EFFECT_BOUNDS * 4
MAX_ITERATIONS = 1500
OPTIONS = {"ftol": 1e-12, "gtol": 1e-7, "maxls": 50}


def _radical_inverse(number, base):
    answer, scale = 0., 1. / base
    while number:
        number, digit = divmod(number, base)
        answer += digit * scale
        scale /= base
    return answer


def search_starts():
    angles = (0., math.pi / 2, math.pi / 4, -math.pi / 4)
    starts = [tuple(value for angle in angles for value in (0., radius, angle))
              for radius in (.95, .65)]
    starts.append((0., 0., 0.) * 4)
    primes = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for number in range(1, 33):
        values = [_radical_inverse(number, prime) for prime in primes]
        starts.append(tuple(value for offset in range(0, 12, 3) for value in (
            .8 * (2 * values[offset] - 1), .15 + .8 * values[offset + 1],
            math.pi * (2 * values[offset + 2] - 1))))
    return tuple(starts)


SEARCH_DECLARATION = {
    "candidate_generation_version": VERSION, "optimizer": "scipy.optimize.minimize/L-BFGS-B",
    "required_scipy_version": "1.13.1", "jacobian": "analytic_full_four_component_softmax_and_12_polar_coordinates",
    "abs_mu_subgradient_at_zero": "0", "bounds_per_effect": [list(pair) for pair in EFFECT_BOUNDS],
    "max_iterations_per_start": MAX_ITERATIONS, **OPTIONS,
    "starts_count": 35, "starts": [list(start) for start in search_starts()],
    "start_construction": "unchanged_rd0001_two_nominal_radii;zero_gain;Halton_indices_1_to_32",
    "candidate_order": "declared_start_order_without_terminal_value_sorting",
    "primitive_rationalization": "unchanged_primary_rational_candidate_40_bits_and_exact_cone",
    "terminal_objective": "unchanged_primary.TerminalObjective",
    "strict_interior_bounds_change_full_source_domain": False,
    "search_is_numerical_verdict": False, "search_failure_is_global_rejection": False,
}


def source_jacobian(parameters):
    """Source q and dq/d(mu,r,angle), in frozen context/outcome order."""
    parameters = tuple(float(value) for value in parameters)
    if len(parameters) != 12 or any(not math.isfinite(value) for value in parameters):
        raise ValueError("Twelve finite polar coordinates required")
    effects = polar_effects(parameters)
    table = float_source_table(effects)
    local = []
    for offset in range(0, 12, 3):
        mu, radius, angle = parameters[offset:offset + 3]
        cap = 1 - abs(mu)
        length = radius * cap
        sine, cosine = math.sin(angle), math.cos(angle)
        mu_sign = 1 if mu > 0 else -1 if mu < 0 else 0
        # At the absolute-value cusp the registered symmetric subgradient is zero.
        local.append(((1., 0., 0.),
                      (-radius * mu_sign * sine, cap * sine, length * cosine),
                      (-radius * mu_sign * cosine, cap * cosine, -length * sine)))
    result = []
    for h, a, b in CONTEXTS:
        first, second = effects[a], effects[2 + b]
        rows = []
        for x, y in ((0, 0), (0, 1), (1, 0), (1, 1)):
            sx, sy, sh = 1 - 2 * x, 1 - 2 * y, 1 - 2 * h
            first_derivative = (sx * (1 + sy * second[0]) / 4,
                                -sx * sy * sh * second[1] / 4, -sx * sy * second[2] / 4)
            second_derivative = (sy * (1 + sx * first[0]) / 4,
                                 -sx * sy * sh * first[1] / 4, -sx * sy * first[2] / 4)
            gradient = [0.] * 12
            for effect, derivative in ((a, first_derivative), (2 + b, second_derivative)):
                for coordinate in range(3):
                    gradient[3 * effect + coordinate] = sum(
                        derivative[primitive] * local[effect][primitive][coordinate] for primitive in range(3))
            rows.append(tuple(gradient))
        result.append(tuple(rows))
    return table, tuple(result)


class AnalyticObjective(TerminalObjective):
    """The frozen objective with exact symbolic derivatives evaluated in float."""
    def probability_gradient(self, probabilities):
        if len(probabilities) != 8 or any(len(row) != 4 or any(q <= 0 or not math.isfinite(q) for q in row)
                                          for row in probabilities):
            raise ValueError("All source probabilities must be strictly positive and finite for this finder")
        components = self.component_logs(probabilities)
        peak = max(components)
        terms = tuple(float(weight) * math.exp(component - peak)
                      for weight, component in zip(COMPONENT_WEIGHTS, components))
        total = sum(terms)
        mixture = tuple(term / total for term in terms)
        gradients = []
        for counts, q in zip(self.counts.rows, probabilities):
            parity_counts = (counts[0] + counts[3], counts[1] + counts[2])
            parity_mass = (q[0] + q[3], q[1] + q[2])
            alice_counts = (counts[0] + counts[1], counts[2] + counts[3])
            alice_mass = (q[0] + q[1], q[2] + q[3])
            bob_counts = (counts[0] + counts[2], counts[1] + counts[3])
            bob_mass = (q[0] + q[2], q[1] + q[3])
            row_gradient = []
            for index, number in enumerate(counts):
                x, y = divmod(index, 2)
                c = x ^ y
                full = -number / q[index]
                conditional = full + parity_counts[c] / parity_mass[c]
                alice = -alice_counts[x] / alice_mass[x]
                bob = -bob_counts[y] / bob_mass[y]
                row_gradient.append(sum(weight * derivative for weight, derivative in
                                        zip(mixture, (conditional, alice, bob, full))))
            gradients.append(tuple(row_gradient))
        return peak + math.log(total), tuple(gradients)

    def value_gradient(self, parameters):
        probabilities, jacobian = source_jacobian(parameters)
        value, q_gradient = self.probability_gradient(probabilities)
        gradient = tuple(math.fsum(q_gradient[row][outcome] * jacobian[row][outcome][coordinate]
                                  for row in range(8) for outcome in range(4)) for coordinate in range(12))
        if not math.isfinite(value) or any(not math.isfinite(number) for number in gradient):
            raise ValueError("Nonfinite analytic objective or gradient")
        return value, gradient


def projected_gradient(parameters, gradient):
    """One-step projection residual, including active bound stationarity."""
    return tuple(value - min(high, max(low, value - derivative))
                 for value, derivative, (low, high) in zip(parameters, gradient, BOUNDS))


def _point(parameters):
    answer = tuple(float(value) for value in parameters)
    if len(answer) != 12 or any(not math.isfinite(value) or not low <= value <= high
                               for value, (low, high) in zip(answer, BOUNDS)):
        raise ValueError("Point outside the fixed c0002 finder bounds")
    return answer


def search_terminal(counts, starts=None, *, max_iterations=MAX_ITERATIONS):
    """Generate exact legal primitives; optimizer outcomes never certify prefixes."""
    import scipy
    from scipy.optimize import minimize
    if scipy.__version__ != SEARCH_DECLARATION["required_scipy_version"]:
        raise ValueError("c0002 requires the frozen scipy solver version")
    if type(max_iterations) is not int or max_iterations <= 0:
        raise ValueError("Positive iteration limit required")
    starts = tuple(_point(start) for start in (search_starts() if starts is None else starts))
    objective = AnalyticObjective(counts)
    results = []
    for number, start in enumerate(starts, 1):
        initial_value, initial_gradient = objective.value_gradient(start)
        result = minimize(objective.value_gradient, start, method="L-BFGS-B", jac=True, bounds=BOUNDS,
                          options={"maxiter": max_iterations, **OPTIONS})
        point = _point(result.x)
        final_value, final_gradient = objective.value_gradient(point)
        displacement = tuple(value - original for value, original in zip(point, start))
        movement = max(map(abs, displacement))
        initial_projected = max(map(abs, projected_gradient(start, initial_gradient)))
        final_projected = max(map(abs, projected_gradient(point, final_gradient)))
        stationary_start = initial_projected <= OPTIONS["gtol"]
        primitive = encode(rational_candidate(point))
        results.append({
            "primitive": primitive, "approximate_terminal_log_e": final_value,
            "optimizer_success": bool(result.success), "optimizer_status": int(result.status),
            "optimizer_iterations": int(result.nit), "optimizer_function_evaluations": int(result.nfev),
            "optimizer_iteration_limit": max_iterations,
            "candidate_generation_version": VERSION, "candidate_start_index": number,
            "analytic_gradient_used": True, "optimizer_moved": movement > 1e-12,
            "primitive_moved": primitive != encode(rational_candidate(start)),
            "optimizer_stationary_before_search": stationary_start,
            "candidate_generation_status": "moved" if movement > 1e-12 else
                                           "stationary_start" if stationary_start else "unmoved_nonstationary_result",
            "parameter_displacement": list(displacement), "parameter_max_displacement": movement,
            "initial_parameters": list(start), "final_parameters": list(point),
            "initial_terminal_log_e": initial_value, "terminal_objective_improvement": initial_value - final_value,
            "initial_projected_gradient_max": initial_projected, "final_projected_gradient_max": final_projected,
            "initial_gradient": list(initial_gradient), "final_gradient": list(final_gradient),
            "numerical_verdict_certified": False, "all_prefix_checked": False,
        })
    return tuple(results)
