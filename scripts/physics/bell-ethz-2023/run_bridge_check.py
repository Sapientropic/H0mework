#!/usr/bin/env python3
"""Standalone phase-bridge check for the ETH 2023 superconducting Bell dataset.

References:
  - S. Storz et al., Nature 617, 265-270 (2023), DOI: 10.1038/s41586-023-05885-0
    (Methods "Optimizing the measurement basis", Fig. 4; Supplement Eq. 7,
    Section II, Table SIV, and Section IX Eqs. 14-16).
  - S. Storz, ETH Research Collection dataset (2023), DOI: 10.3929/ethz-b-000624026.

Stdlib only (Python 3.9+), deterministic, offline. Runs the 12 algebraic unit
tests across all 64 pulse sign/handedness combinations and prints the explicit
correlator and five-way convention degeneracy summary.
"""
from __future__ import annotations

from dataclasses import replace
import hashlib
import json
import math
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[2]
sys.path.insert(0, str(HERE))

import pulse_model as m  # noqa: E402

CUSTODY_METADATA = (
    REPO_ROOT
    / "evidence/first-release/h/physics/stage10/independent-bell/custody/r0002-storz2023-metadata.json"
)
EXPECTED_METADATA_SHA = "3014de202e5c9d99bf286a48f29f35eb57cd1400fcf6884b4375bfb65ccfa61b"


def fmt_vec(vec: tuple[float, ...]) -> str:
    return "(" + ", ".join(f"{x:+.6f}" for x in vec) + ")"


def main() -> int:
    print("=== [1/3] Running 12 algebraic & 64-combination pulse unit tests ===")
    suite = unittest.defaultTestLoader.loadTestsFromName("test_pulse_model")
    result = unittest.TextTestRunner(stream=sys.stdout, verbosity=2).run(suite)
    if not result.wasSuccessful():
        return 1

    print("\n=== [2/3] Evaluating SI Eq. 7 closure at bare nominal angle (gamma = 0, theta = -pi/4) ===")
    theta_nom = -math.pi / 4.0
    alice = m.quarter_station(0.0)
    bob_nom = m.quarter_station(theta_nom)
    corr_nom = m.correlations(0.0, alice, bob_nom)
    s_nom = m.chsh(corr_nom, m.OFFICIAL_CHSH_SIGNS)

    print("Prepared state (SI Eq. 14):  (|eg> + exp(-i*gamma)|ge>) / sqrt(2),  gamma = 0")
    print("SI Eq. 7 sign functional:    S = +E_00 - E_01 + E_10 + E_11")
    print(f"Bare nominal delta = -pi/4:  (E_00, E_01, E_10, E_11) = {fmt_vec(corr_nom)}")
    print(f"                             S_ideal = {s_nom:+.12f}  (exact cancellation: S = 0)")

    print("\n=== [3/3] Five observationally identical ways to invert (E_01, E_10) -> S = 2*sqrt(2) ===")
    candidates = [
        ("1. Reverse Bob azimuth handedness (theta -> +pi/4)",
         0.0, alice, m.quarter_station(-theta_nom)),
        ("2. Shift preparation/inter-node phase (gamma -> +pi/2)",
         -2.0 * theta_nom, alice, bob_nom),
        ("3. Reverse both stations' optional-pulse signs (o_A = o_B = -1)",
         0.0, m.quarter_station(0.0, optional_sign=-1), m.quarter_station(theta_nom, optional_sign=-1)),
        ("4. Complement both raw setting bits (a -> 1-a, b -> 1-b)",
         0.0, replace(alice, setting_xor=1), replace(bob_nom, setting_xor=1)),
        ("5. Setting-conditioned readout flip (x -> (-1)^a x, y -> (-1)^b y)",
         0.0, replace(alice, output_signs=(1, -1)), replace(bob_nom, output_signs=(1, -1))),
    ]
    ref_probs = [m.joint_probabilities(0.0, alice, m.quarter_station(-theta_nom), a, b) for a, b in m.SETTINGS]
    for label, gamma, st_a, st_b in candidates:
        c = m.correlations(gamma, st_a, st_b)
        s_val = m.chsh(c, m.OFFICIAL_CHSH_SIGNS)
        probs = [m.joint_probabilities(gamma, st_a, st_b, a, b) for a, b in m.SETTINGS]
        max_diff = max(abs(p - q) for row_p, row_q in zip(probs, ref_probs) for p, q in zip(row_p, row_q))
        print(f"  {label}")
        print(f"     E = {fmt_vec(c)},  S = {s_val:+.6f} (2*sqrt(2)),  max |Delta P(x,y|a,b)| = {max_diff:.1e}")

    if CUSTODY_METADATA.is_file():
        meta = json.loads(CUSTODY_METADATA.read_text(encoding="utf-8"))
        sha = hashlib.sha256(CUSTODY_METADATA.read_bytes()).hexdigest()
        if sha != EXPECTED_METADATA_SHA:
            raise AssertionError(f"Metadata SHA-256 mismatch: {sha} != {EXPECTED_METADATA_SHA}")
        main_member = next(
            x for x in meta["archive"]["members"] if x["member"].endswith("main_dataset_all_events.txt")
        )
        print(f"\nCustody metadata verified ({CUSTODY_METADATA.name}, sha256={sha[:16]}...):")
        print(f"  Archive DOI: {meta['source']['data_doi']}  |  main_dataset_all_events.txt sha256={main_member['sha256'][:16]}...")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
