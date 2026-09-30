"""Generic real Born family and explicit loss transport; never opens event files.

The NIST adapter is a conditional preparation readout, not a source-occurrence
claim. Legacy prediction remains in predict.py. All channel numbers are caller
inputs; this module neither estimates them nor certifies their provenance.
"""
from __future__ import annotations

import math
from fractions import Fraction
from typing import Any, Mapping, Sequence

SCHEMA = "nist-documented-real-instrument/v2"
MOUTH = "SaturationMonoid.PhysicsCore.Stage10.Bell.RealFamily.prediction"
SCOPE = "documented_real_born_conditional"
OUTCOMES = ((1, 1), (1, -1), (-1, 1), (-1, -1))


def _number(value: Any) -> float:
    if isinstance(value, bool):
        raise ValueError("Boolean is not a physical parameter")
    x = float(value)
    if not math.isfinite(x):
        raise ValueError("finite parameters required")
    return x


def _unit_interval(value: Any) -> float:
    x = _number(value)
    if not 0 <= x <= 1:
        raise ValueError("probability parameter outside [0,1]")
    return x


def parameters(c_raw: Any, s_raw: Any) -> tuple[float, float, float, float]:
    """Radially normalize documented coordinates; no fitted normalization slot."""
    c, s = _number(c_raw), _number(s_raw)
    norm = math.hypot(c, s)
    if norm == 0 or not math.isfinite(norm):
        raise ValueError("nonzero finite preparation required")
    c, s = c / norm, s / norm
    return c, s, c*c-s*s, 2*c*s


def polarization_axis(degrees: Any) -> tuple[float, float]:
    """Angle from vertical, in the explicit |0>=V, |1>=H basis."""
    t = 2 * math.radians(_number(degrees))
    return math.sin(t), math.cos(t)


def _axis(value: Sequence[Any]) -> tuple[float, float]:
    if len(value) != 2:
        raise ValueError("XZ axis requires exactly two components")
    x, z = map(_number, value)
    if abs(x*x+z*z-1) > 1e-12:
        raise ValueError("axis must be unit")
    return x, z


def _distribution(values: Sequence[float]) -> list[float]:
    if len(values) != 4 or any(not math.isfinite(p) or p < -1e-14 or p > 1+1e-14
                               for p in values) or abs(math.fsum(values)-1) > 1e-12:
        raise ValueError("invalid probability distribution")
    return list(values)  # No clipping or renormalizing a failed calculation.


def born_probabilities(a: Sequence[Any], b: Sequence[Any],
                       delta: float, chi: float) -> list[float]:
    """Lean RealFamily.probability, with both nonuniform marginals retained."""
    ax, az = _axis(a)
    bx, bz = _axis(b)
    delta, chi = _number(delta), _number(chi)
    if abs(delta*delta+chi*chi-1) > 1e-12:
        raise ValueError("pure real-family shape delta^2+chi^2=1 required")
    return _distribution([(1+delta*(x*az+y*bz)+x*y*(az*bz+chi*ax*bx))/4
                          for x, y in OUTCOMES])


def loss_assignment(latent: int, *, eta_plus: float, eta_minus: float,
                    F0: float, F1: float, background: float = 0) -> dict[int, float]:
    """Assign a port, detect it, then allow background in the no-click branch.

    Keys +1/-1 are detected ports, 0 is no-click. NIST has eta_minus=0.
    Unit efficiencies and zero background recover the legacy F0/F1 kernel.
    """
    if latent not in (-1, 1):
        raise ValueError("latent sign must be +/-1")
    ep, em, f0, f1, d = map(_unit_interval, (eta_plus, eta_minus, F0, F1, background))
    plus_port = f0 if latent == 1 else 1-f1
    plus, minus = ep*plus_port, em*(1-plus_port)
    missing = 1-plus-minus
    return {1: plus+d*missing, -1: minus, 0: (1-d)*missing}


def binary_assignment(latent: int, channel: Mapping[str, Any]) -> dict[int, float]:
    raw = loss_assignment(latent, **channel)
    return {1: raw[1], -1: raw[-1]+raw[0]}


def trial_probabilities(ideal: Sequence[float], channel: Mapping[str, Any]) -> list[float]:
    """One-pair/vacuum trial model. Multipair/grouping error requires a TV bound."""
    ideal = _distribution(ideal)
    q, v = map(_unit_interval, (channel["pair_probability"], channel["visibility"]))
    alice, bob = channel["alice"], channel["bob"]
    ka = {u: binary_assignment(u, alice) for u in (-1, 1)}
    kb = {u: binary_assignment(u, bob) for u in (-1, 1)}
    da, db = _unit_interval(alice["background"]), _unit_interval(bob["background"])
    vacuum_a, vacuum_b = {1: da, -1: 1-da}, {1: db, -1: 1-db}
    latent = [v*p+(1-v)/4 for p in ideal]
    return _distribution([
        q*math.fsum(p*ka[u][x]*kb[w][y] for p, (u, w) in zip(latent, OUTCOMES))
        +(1-q)*vacuum_a[x]*vacuum_b[y] for x, y in OUTCOMES])


RADIUS_KEYS = ("state_tv", "alice_axis_operator", "bob_axis_operator",
               "pair_probability", "visibility", "alice_assignment", "bob_assignment",
               "alice_loss", "bob_loss", "alice_background", "bob_background",
               "model_tv", "drift_tv", "numerical_tv")


def transport_radius(bounds: Mapping[str, str]) -> Fraction:
    """Conservative coupling/TV sum; inputs must be independently covered bounds.

    This algebraic transport does not manufacture confidence coverage or turn
    marginal confidence intervals into a simultaneous region.
    """
    if set(bounds) != set(RADIUS_KEYS):
        raise ValueError("complete named transport bounds required")
    radii = [Fraction(bounds[key]) for key in RADIUS_KEYS]
    if any(r < 0 or r > 1 for r in radii):
        raise ValueError("TV/operator bounds must lie in [0,1]")
    return min(Fraction(1), sum(radii, Fraction(0)))


def error_budget(budget: Mapping[str, str]) -> dict[str, str]:
    alpha, beta, total = (Fraction(budget[k])
                          for k in ("conditional_alpha", "calibration_beta", "total"))
    if (alpha, beta, total) != (Fraction(1, 40), Fraction(1, 100), Fraction(1, 20)):
        raise ValueError("this revision has a fixed, non-reallocated error budget")
    return {"conditional_alpha": str(alpha), "calibration_beta": str(beta),
            "covered_total": str(alpha+beta), "reserve_unused": str(total-alpha-beta)}


def validate_instrument(instrument: Mapping[str, Any]) -> None:
    if instrument.get("schema") != SCHEMA or instrument.get("theorem_mouth") != MOUTH:
        raise ValueError("wrong schema or theorem identity")
    if instrument.get("claim_scope") != SCOPE:
        raise ValueError("generic real preparation is not an original-source claim")
    prep, controls = instrument["preparation"], instrument["controls"]
    if prep.get("basis_order") != ["V", "H"] or prep.get("normalization") != "radial":
        raise ValueError("explicit vertical-first basis and radial normalization required")
    if set(prep["amplitudes"]) != {"VV", "HH"} or "delta" in prep or "chi" in prep:
        raise ValueError("derive delta/chi from the documented pair, never fit them")
    parameters(prep["amplitudes"]["VV"], prep["amplitudes"]["HH"])
    if controls.get("angle_reference") != "vertical_polarizer_degrees":
        raise ValueError("polarization/Bloch angle and basis convention unresolved")
    if controls.get("setting_bits") != {"0": "unprimed", "1": "primed"}:
        raise ValueError("setting coding is fixed, not chosen from results")
    for side in ("alice", "bob"):
        if len(controls[side]) != 2:
            raise ValueError("two documented settings per side required")
        for angle in controls[side]:
            polarization_axis(angle)
    if instrument.get("outcome_policy") != {"click": 1, "no_click": -1,
                                             "discard_no_click": False}:
        raise ValueError("complete trials and deterministic no-click reassignment required")
    if instrument.get("detector_geometry") != "single_transmitted_port":
        raise ValueError("two-port assignment is not the NIST apparatus")


def tables(instrument: Mapping[str, Any]) -> dict[str, Any]:
    validate_instrument(instrument)
    p, controls = instrument["preparation"], instrument["controls"]
    c, s, delta, chi = parameters(p["amplitudes"]["VV"], p["amplitudes"]["HH"])
    left = [polarization_axis(t) for t in controls["alice"]]
    right = [polarization_axis(t) for t in controls["bob"]]
    ideal = [{"a": a, "b": b,
              "probabilities": born_probabilities(left[a], right[b], delta, chi)}
             for a in (0, 1) for b in (0, 1)]
    models = [{"id": "pair_born_reference", "test_eligible": False, "table": ideal}]
    channel = instrument.get("channel")
    if channel is not None:
        if any(_number(channel[side]["eta_minus"]) != 0 for side in ("alice", "bob")):
            raise ValueError("the blocked port has no detector")
        models.append({"id": "conditional_trial_model", "test_eligible": False,
                       "table": [{**row, "probabilities":
                                  trial_probabilities(row["probabilities"], channel)}
                                 for row in ideal]})
    return {"schema": SCHEMA, "claim_scope": SCOPE, "models": models,
            "parameters": {"c": c, "s": s, "delta": delta, "chi": chi},
            "lock_created": False, "test_events_read": 0}
