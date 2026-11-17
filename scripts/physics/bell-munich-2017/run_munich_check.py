#!/usr/bin/env python3
"""Reproduce the symmetric vs. asymmetric readout audit on the Munich 2017 Bell archive.

Runs all algebraic/martingale unit tests first, then verifies the official Zenodo
archives (DOI: 10.5281/zenodo.22936124, downloading into a temporary cache if not
already present in --archive-dir) and prints the complete sequential e-process,
marginal readout bias, 2D inverse-scale fiber, and CSV schema summary.

Usage:
    python3 scripts/physics/bell-munich-2017/run_munich_check.py
    python3 scripts/physics/bell-munich-2017/run_munich_check.py --tests-only
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import readout_model as m  # noqa: E402
import test_readout_model  # noqa: E402


def print_fiber_range(run_name: str, inst: m.Instrument) -> None:
    print(f"  2D inverse-scale fiber sample s, t in {{0.95, 1.00, 1.05}} (identical 32-cell law):")
    corners = (
        (Fraction(19, 20), Fraction(19, 20)),
        (Fraction(1, 1), Fraction(1, 1)),
        (Fraction(21, 20), Fraction(21, 20)),
    )
    for side_idx, side_label in enumerate(("Alice", "Bob")):
        effects_side = "alice" if side_idx == 0 else "bob"
        for s_idx in (0, 1):
            gains, e0s, e1s = [], [], []
            for s_fac, t_fac in corners:
                scaled = m.scale_fiber(inst, s_fac, t_fac)
                eff = getattr(scaled, effects_side)[s_idx]
                g, e0, e1 = eff.canonical_gain_and_errors()
                gains.append(g)
                e0s.append(e0)
                e1s.append(e1)
            print(
                f"    {side_label} {s_idx}: gain in [{min(gains):.4f}, {max(gains):.4f}], "
                f"e0 in [{min(e0s):.4f}, {max(e0s):.4f}], e1 in [{min(e1s):.4f}, {max(e1s):.4f}]"
            )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--archive-dir",
        type=Path,
        default=None,
        help="Directory containing Bell_2016-04-15.zip and Bell_2016-06-14.zip (downloads from Zenodo if omitted).",
    )
    parser.add_argument(
        "--tests-only",
        action="store_true",
        help="Run algebraic and statistical unit tests only without loading raw ZIPs.",
    )
    args = parser.parse_args()

    suite = unittest.defaultTestLoader.loadTestsFromModule(test_readout_model)
    result = unittest.TextTestRunner(verbosity=1).run(suite)
    if not result.wasSuccessful():
        return 1

    print("\n=== Munich 2017 Entangled-Atom Bell Dataset: Readout & Schema Audit ===")
    print("Paper:   W. Rosenfeld et al., Phys. Rev. Lett. 119, 010402 (2017)")
    print(f"Dataset: {m.ZENODO_RECORD_URL} (DOI: {m.ZENODO_DOI})")

    if args.tests_only:
        return 0

    def evaluate_archives(zdir: Path) -> None:
        for spec in m.ARCHIVES:
            adm = m.admit_archive(spec, zdir, allow_download=True)
            sym = m.score_balanced_complement(adm.trials)
            inst = m.WITNESS_INSTRUMENTS[spec.run]
            asym = m.score_asymmetric_witness(adm.trials, inst)
            emp = m.empirical_chsh_and_biases(adm.trials)
            aud = adm.schema_audit

            print(f"\n--- Run {spec.run} ({spec.filename}, SHA-256 {spec.sha256[:16]}...) ---")
            print(
                f"  Archive rows: lab_1={aud['local1_rows']}, lab_2={aud['local2_rows']} "
                f"(header={aud['lab2_header_fields']} cols vs data=6 cols on {aud['lab2_six_field_data_rows']} rows), "
                f"valid pairs={aud['pair_rows']}, unpaired={aud['unpaired_total']}"
            )
            print(f"  Empirical event-ready CHSH value: S = {emp['chsh_s']:.5f}")
            pa0, pa1 = sym["pooled_counts"]["alice"]  # type: ignore[index]
            pb0, pb1 = sym["pooled_counts"]["bob"]  # type: ignore[index]
            print(
                f"  Pooled outcomes (0 : 1): Alice = {pa0} : {pa1} ({(pa0 - pa1)/(pa0 + pa1):+.4%}), "
                f"Bob = {pb0} : {pb1} ({(pb0 - pb1)/(pb0 + pb1):+.4%})"
            )
            for label, binfo in emp["biases"].items():  # type: ignore[attr-defined]
                ci_lo, ci_hi = m.SIMULTANEOUS_BIAS_BOUNDS[spec.run][label]
                print(
                    f"    {label}: {binfo['count_0']} : {binfo['count_1']} "
                    f"(mu_hat = {binfo['mu_hat']:+.5f}, simultaneous 95% CI [{ci_lo:+.5f}, {ci_hi:+.5f}])"
                )
            verdict_str = (
                f"REJECTED at pair {sym['first_crossing']} (E = {sym['first_crossing_e']:.2f} >= 40)"
                if sym["rejected"]
                else "NOT REJECTED (all prefixes < 40)"
            )
            print(
                f"  Symmetric-readout sequential e-process (alpha = 1/40, threshold 40): {verdict_str}; "
                f"E_max = {sym['max_e']:.2f} (pair {sym['max_prefix']}), E_terminal = {sym['terminal_e']:.2f}"
            )
            print(
                f"  Asymmetric 12D readout witness e-process: "
                f"E_max <= {asym['max_e_upper']:.4f}, E_terminal <= {asym['terminal_e_upper']:.6f} "
                f"(all {asym['trials']} prefixes < 40: {asym['all_below_threshold']})"
            )
            print_fiber_range(spec.run, inst)

    if args.archive_dir is not None:
        evaluate_archives(args.archive_dir)
    else:
        with tempfile.TemporaryDirectory(prefix="munich-bell-2017-") as tmp:
            evaluate_archives(Path(tmp))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
