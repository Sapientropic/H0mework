"""Independent matrix/control checks. No data reader, downloads, or result tables."""
from __future__ import annotations

import math
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import real_family as rf
from nominal_optimum import assess_nominal_replay


def matrix_born(c, s, angle_a, angle_b):
    """Direct tensor projector contraction, independent of the delta/chi formula."""
    def projector(t, sign):
        v = (math.cos(t), math.sin(t)) if sign == 1 else (-math.sin(t), math.cos(t))
        return [[v[i]*v[j] for j in range(2)] for i in range(2)]
    state = (c, 0.0, 0.0, s)
    result = []
    for x, y in rf.OUTCOMES:
        a, b = projector(angle_a, x), projector(angle_b, y)
        result.append(math.fsum(state[i]*a[i//2][j//2]*b[i%2][j%2]*state[j]
                                for i in range(4) for j in range(4)))
    return result


def control_loop(instrument, *, nominal_replay_dir=None, nominal_replay_enabled=True):
    rf.validate_instrument(instrument)
    p, controls = instrument["preparation"], instrument["controls"]
    c, s, delta, chi = rf.parameters(p["amplitudes"]["VV"], p["amplitudes"]["HH"])
    a, ap = [math.radians(float(t)) for t in controls["alice"]]
    b, bp = [math.radians(float(t)) for t in controls["bob"]]
    rows = rf.tables(instrument)["models"][0]["table"]
    pairs = [(a, b), (a, bp), (ap, b), (ap, bp)]
    direct = [matrix_born(c, s, u, v) for u, v in pairs]
    agreement = all(abs(x-y) < 2e-14 for row, expected in zip(rows, direct)
                    for x, y in zip(row["probabilities"], expected))
    def suppressed(c0, s0, pairs0):
        q = [matrix_born(c0, s0, u, v)[0] for u, v in pairs0]
        return q[3] < min(q[:3])
    nominal = assess_nominal_replay(instrument, report_dir=nominal_replay_dir,
                                   enabled=nominal_replay_enabled)
    return {
        "matrix_matches_all_cells": agreement,
        "mirror_geometry": abs(a+b) < 1e-15 and abs(ap+bp) < 1e-15,
        "real_shape": abs(delta*delta+chi*chi-1) < 1e-14,
        "rare_vertical_transmission": c*c < 0.5,
        "primed_destructive_structure": suppressed(c, s, pairs),
        "wrong_basis_rejected": any(abs(u-v) > 1e-12
                                   for u, v in zip(matrix_born(s, c, a, b), direct[0])),
        "wrong_bob_sign_rejected": not suppressed(c, s, [(u, -v) for u, v in pairs]),
        "apparatus_optimum_verified": nominal["verified"],
        "optimum_gate": nominal["status"],
        "nominal_replay": nominal,
        "test_events_read": 0,
    }


if __name__ == "__main__":
    import json
    instrument = json.loads(Path(__file__).with_name("instrument.json").read_text())
    print(json.dumps(control_loop(instrument), indent=2, sort_keys=True))
