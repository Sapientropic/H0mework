"""Source-fixed Bell family, committed before the next archive is selected.

Instrument axes are external control settings, not fitted event outcomes.
The optional readout model requires independent calibration provenance.
"""

from __future__ import annotations

import math


OUTCOMES = ((1, 1), (1, -1), (-1, 1), (-1, -1))
CONTEXTS = tuple((h, a, b) for h in (-1, 1) for a in (0, 1) for b in (0, 1))


def axes(values):
    if len(values) != 2 or any(len(axis) != 2 for axis in values):
        raise ValueError("exactly two XZ unit axes per side are required")
    result = tuple(tuple(float(x) for x in axis) for axis in values)
    if any(not all(math.isfinite(x) for x in axis)
           or abs(sum(x*x for x in axis)-1) > 1e-12 for axis in result):
        raise ValueError("each instrument axis must be a finite unit vector")
    return result


def tables(instrument):
    left, right = axes(instrument["alice_axes_xz"]), axes(instrument["bob_axes_xz"])
    ideal = []
    for h, a, b in CONTEXTS:
        ax, az = left[a]
        bx, bz = right[b]
        correlation = -(ax*bx+az*bz) if h == -1 else ax*bx-az*bz
        ideal.append({"herald": h, "a": a, "b": b,
                      "probabilities": [(1+x*y*correlation)/4 for x,y in OUTCOMES]})
    models = [{"id": "ideal_source", "alpha": .025, "table": ideal}]
    calibration = instrument.get("independent_calibration")
    if calibration is not None:
        if not calibration.get("provenance") or not calibration.get("test_events_disjoint"):
            raise ValueError("independent calibration must identify its disjoint source")
        names = ("visibility", "F0_A", "F1_A", "F0_B", "F1_B")
        if any(not math.isfinite(calibration[key]) or not 0 <= calibration[key] <= 1 for key in names):
            raise ValueError("calibration probabilities must lie in [0,1]")
        visibility = calibration["visibility"]
        def assignment(side, reported, latent):
            fidelity = calibration[f"F{0 if latent == 1 else 1}_{side}"]
            return fidelity if reported == latent else 1-fidelity
        reference = []
        for row in ideal:
            latent = [(1-visibility)/4+visibility*p for p in row["probabilities"]]
            probabilities = [math.fsum(p*assignment("A",x,u)*assignment("B",y,v)
                             for p,(u,v) in zip(latent,OUTCOMES)) for x,y in OUTCOMES]
            reference.append({**row,"probabilities":probabilities})
        models.append({"id":"independent_calibration","alpha":.025,"table":reference})
    return {"models":models,"family_alpha_max":.05}
