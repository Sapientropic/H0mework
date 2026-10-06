"""Independent exact detector fibres and raw-response necessary projections.

The polygon checker clips the physical detector triangle instead of enumerating
pairwise boundary intersections. No producer, pulse solver, or event table is
imported here.
"""
from dataclasses import dataclass
from fractions import Fraction
from math import isqrt


def exact(value):
    if type(value) not in (str, int, Fraction):
        raise ValueError("exact_detector_coordinate_required")
    return Fraction(value)


@dataclass(frozen=True)
class Effect:
    mu: Fraction
    u: Fraction
    z: Fraction

    def __post_init__(self):
        for name in ("mu", "u", "z"):
            object.__setattr__(self, name, exact(getattr(self, name)))
        radius_squared = self.u ** 2 + self.z ** 2
        if not -1 <= self.mu <= 1 or radius_squared > (1 - abs(self.mu)) ** 2:
            raise ValueError("physical_signed_effect_required")


@dataclass(frozen=True)
class AtomicEffect:
    trace: Fraction
    x: Fraction
    z: Fraction

    def __post_init__(self):
        for name in ("trace", "x", "z"):
            object.__setattr__(self, name, exact(getattr(self, name)))
        if not 0 <= self.trace <= 2 or self.x ** 2 + self.z ** 2 > min(self.trace, 2 - self.trace) ** 2:
            raise ValueError("physical_atomic_response_required")


def _effect(value):
    if isinstance(value, Effect):
        return value
    if type(value) is dict:
        if set(value) != {"mu", "u", "z"}:
            raise ValueError("signed_effect_primitive_shape")
        return Effect(**value)
    return Effect(value.mu, value.u, value.z)


def forward(atom, background, efficiency):
    if not isinstance(atom, AtomicEffect):
        atom = AtomicEffect(atom.trace, atom.x, atom.z)
    d, eta = exact(background), exact(efficiency)
    if not 0 <= d <= 1 or not 0 <= eta <= 1:
        raise ValueError("physical_detector_probabilities_required")
    scale = (1 - d) * eta
    return Effect(1 - 2 * d - scale * atom.trace, -scale * atom.x, -scale * atom.z)


def admits(effect, background, detection):
    point, d, k = _effect(effect), exact(background), exact(detection)
    if not 0 <= d <= 1 or not 0 <= k <= 1 - d:
        return False
    if not k:
        return point.mu == 1 - 2 * d and point.u == point.z == 0
    center = (1 - point.mu - 2 * d) / k
    x, z = -point.u / k, -point.z / k
    return 0 <= center <= 2 and x ** 2 + z ** 2 <= min(center, 2 - center) ** 2


def inverse(effect, background, detection):
    point, d, k = _effect(effect), exact(background), exact(detection)
    if k <= 0 or d >= 1 or not admits(point, d, k):
        raise ValueError("positive_legal_detector_factor_required")
    atom = AtomicEffect((1 - point.mu - 2 * d) / k, -point.u / k, -point.z / k)
    eta = k / (1 - d)
    if forward(atom, d, eta) != point:
        raise ValueError("inverse_detector_realization_failed")
    return {"background": d, "detection": k, "fragment_efficiency": eta, "atom": atom}


def interval(row, lower, upper):
    if type(row) not in (list, tuple) or len(row) != 2:
        raise ValueError("two_detector_interval_endpoints_required")
    lo, hi = map(exact, row)
    if not lower <= lo <= hi <= upper:
        raise ValueError("physical_ordered_detector_interval_required")
    return lo, hi


def square_root_lower(value, bits=80):
    value = exact(value)
    if value < 0 or type(bits) is not int or bits < 32:
        raise ValueError("dyadic_root_domain")
    scale = 1 << bits
    root = isqrt((value.numerator << (2 * bits)) // value.denominator)
    bound = Fraction(root, scale)
    if bound * bound > value or Fraction(root + 1, scale) ** 2 <= value:
        raise ValueError("integer_root_certificate_failed")
    return bound


def necessary_bounds(gain_lower, bias_interval):
    g = exact(gain_lower)
    lo, hi = interval(bias_interval, -1, 1)
    if not 0 < g <= 1:
        raise ValueError("positive_whole_confidence_gain_required")
    absolute = max(-lo, hi)
    product_bound = g / ((1 + absolute + g) / 2)
    exposure = product_bound / Fraction(7, 4)
    return {"gain_lower": str(g), "bias_interval": [str(lo), str(hi)],
            "bias_absolute_upper": str(absolute), "eta_lower": str(product_bound),
            "lambda_max_lower": str(product_bound), "eta_times_lambda_max_lower": str(product_bound),
            "eta_times_area_squared_lower": str(exposure), "area_lower_squared": str(exposure),
            "area_lower": str(square_root_lower(exposure)),
            "dark_background_upper": str((1 + absolute - g) / 2), "click_polarity_selected": False}


def confidence_domain(shared_run, bias_run, joint_run):
    """Consume the same source lower bounds with independent group projections."""
    roles = (("alice", 0), ("alice", 1), ("bob", 0), ("bob", 1))
    if shared_run["run"] != bias_run["run"] or shared_run["run"] != joint_run["run"]:
        raise ValueError("same_original_confidence_run_required")
    responses, biases = shared_run["shared_response_envelopes"], bias_run["bias_envelopes"]
    for rows in (responses, biases):
        if (type(rows) is not list or any(type(row["setting"]) is not int for row in rows)
                or tuple((row["side"], row["setting"]) for row in rows) != roles):
            raise ValueError("complete_ordered_original_confidence_roles_required")
    individual = []
    for (side, setting), response, bias in zip(roles, responses, biases):
        gain, _ = interval(response["canonical_gain"], 0, 1)
        row = necessary_bounds(gain, bias["mu_outer_interval"])
        individual.append({"side": side, "setting": setting, **row})
    rays = joint_run["joint_response_rays"]
    if type(rays) is not list or tuple(row["ray"] for row in rays) != ("uniform", "alice", "bob"):
        raise ValueError("all_original_joint_gain_rays_required")
    joint = []
    group_members = {"uniform": roles, "alice": roles[:2], "bob": roles[2:]}
    role_bias = {(row["side"], row["setting"]): exact(row["bias_absolute_upper"]) for row in individual}
    for ray in rays:
        gain, _ = interval(ray["profile_threshold_bracket"], 0, 1)
        if gain <= 0 or ray["entire_lower_orthant_excluded"] is not True:
            raise ValueError("strict_original_joint_orthant_exclusion_required")
        absolute = max(role_bias[role] for role in group_members[ray["ray"]])
        product = gain / ((1 + absolute + gain) / 2)
        exposure = product / Fraction(7, 4)
        joint.append({"ray": ray["ray"], "source_max_gain_strict_lower": str(gain),
                      "group_bias_absolute_upper": str(absolute),
                      "maximum_eta_times_lambda_max_strict_lower": str(product),
                      "maximum_eta_times_area_squared_strict_lower": str(exposure),
                      "maximum_area_strict_lower": str(square_root_lower(exposure))})
    return {"run": shared_run["run"], "individual_hardware_constraints": individual,
            "joint_hardware_constraints": joint}


def hardware_gain_cap(eta_upper, area_squared_upper, bias_absolute_upper):
    eta, exposure, absolute = map(exact, (eta_upper, area_squared_upper, bias_absolute_upper))
    if not 0 <= eta <= 1 or exposure < 0 or not 0 <= absolute <= 1:
        raise ValueError("physical_raw_hardware_upper_box_required")
    product = eta * min(Fraction(1), exposure * Fraction(7, 4))
    return min(Fraction(1), product / (2 - product) * (1 + absolute))


def _clean_boundary(points):
    boundary = []
    for point in points:
        if not boundary or point != boundary[-1]:
            boundary.append(point)
    if len(boundary) > 1 and boundary[0] == boundary[-1]:
        boundary.pop()
    return boundary


def clip_polygon(constraints):
    """Clip the closed detector triangle by exact affine inequalities."""
    rows = []
    for row in constraints:
        if type(row) not in (list, tuple) or len(row) != 3:
            raise ValueError("affine_detector_halfplane_required")
        rows.append(tuple(map(exact, row)))
    polygon = [(Fraction(0), Fraction(0)), (Fraction(0), Fraction(1)), (Fraction(1), Fraction(0))]
    for a, b, c in rows:
        if not polygon:
            break
        result = []
        previous = polygon[-1]
        previous_distance = a * previous[0] + b * previous[1] - c
        for current in polygon:
            current_distance = a * current[0] + b * current[1] - c
            if (previous_distance <= 0) != (current_distance <= 0):
                ratio = previous_distance / (previous_distance - current_distance)
                result.append(tuple(p + ratio * (q - p) for p, q in zip(previous, current)))
            if current_distance <= 0:
                result.append(current)
            previous, previous_distance = current, current_distance
        polygon = _clean_boundary(result)
    vertices = tuple(sorted(set(polygon)))
    if any(any(a * d + b * k > c for a, b, c in rows) or not (0 <= d and 0 <= k and d + k <= 1)
           for d, k in vertices):
        raise ValueError("clipped_detector_vertex_invalid")
    return vertices


def atomic_detector_polygons(gain_lower, bias_interval, bright, dark):
    g = exact(gain_lower)
    lo, hi = interval(bias_interval, -1, 1)
    if not 0 < g <= 1:
        raise ValueError("positive_whole_confidence_gain_required")
    bl, bu = interval(bright, 0, 1)
    dl, du = interval(dark, 0, 1)
    # Interval arithmetic relaxes the dependence of trace and spectral gap.
    # Empty projections exclude the full response box; nonempty projections
    # retain necessary scope and do not certify an empirical joint witness.
    trace_lower, trace_upper = bl + dl, bu + du
    contrast_upper = max(bu - dl, du - bl)
    branches = []
    for polarity, lower, upper in ((1, lo, hi), (-1, -hi, -lo)):
        rows = [(Fraction(-1), Fraction(0), Fraction(0)), (Fraction(0), Fraction(-1), Fraction(0)),
                (Fraction(1), Fraction(1), Fraction(1)), (Fraction(0), -contrast_upper, -g),
                (Fraction(2), trace_lower, 1 - lower), (Fraction(-2), -trace_upper, upper - 1)]
        vertices = clip_polygon(rows)
        branches.append({"polarity": polarity, "constraints": [list(map(str, row)) for row in rows],
                         "vertices": [list(map(str, row)) for row in vertices], "empty": not vertices})
    return {"branches": branches, "entire_atomic_response_box_excluded": all(branch["empty"] for branch in branches),
            "click_polarity_selected": False, "necessary_projection_only": True}
