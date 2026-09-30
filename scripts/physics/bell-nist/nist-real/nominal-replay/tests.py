#!/usr/bin/env python3
"""Regression and consistency tests for the nominal-apparatus replay.

Run:  python3 tests.py        (stdlib only, offline, deterministic)

Covers: symmetry and periodicity of the objective (T1, T2, T4), background-split invariance
(T3), the marginal/joint consistency of the two probability paths (T5, T6), physical controls
(T7: the 2/3 threshold and the product-state bound), and optimiser sanity (T8, T9).
"""

import sys

import independent_replay as IND
import replay as REP

FAILURES = []


def check(name, condition, detail=""):
    status = "PASS" if condition else "FAIL"
    print("%-4s %-56s %s" % (status, name, detail))
    if not condition:
        FAILURES.append(name)


def context(**kwargs):
    base = {"eta_a": 0.747, "eta_b": 0.756, "b_a": 8.9e-07, "b_b": 3.2e-07,
            "n_pairs": 5e-4, "delta_deg": 0.0, "werner": None}
    base.update(kwargs)
    return base


def main():
    frozen = REP.load_frozen()
    opt = frozen["optimizer"]
    ctx = context()
    samples = [(0.1, 3.0, -20.0), (0.2872, 4.2, -25.9), (0.8, 40.0, -70.0)]

    # T1 180-degree periodicity of the analyser axis
    # tolerance is round-off only: a broken identity would differ at the 1e-6 scale of S itself
    worst = max(abs(REP.s_ch(ctx, r, t0 + 180.0, t1) - REP.s_ch(ctx, r, t0, t1))
                for (r, t0, t1) in samples)
    check("T1 S(t0+180,t1) == S(t0,t1)", worst < 1e-15, "worst |delta| = %.2e" % worst)

    # T2 mirror invariance (theta0, theta1) -> (-theta0, -theta1)
    worst = max(abs(REP.s_ch(ctx, r, -t0, -t1) - REP.s_ch(ctx, r, t0, t1)) for (r, t0, t1) in samples)
    check("T2 S(-t0,-t1) == S(t0,t1)", worst < 1e-22, "worst |delta| = %.2e" % worst)

    # T3 background split invariance: only the combination dcr + N*flr is consumed
    n = ctx["n_pairs"]
    variants = {
        "all_flr": context(b_a=n * (ctx["b_a"] / n), b_b=n * (ctx["b_b"] / n)),
        "all_dcr": context(b_a=ctx["b_a"], b_b=ctx["b_b"]),
        "mixed": context(b_a=0.4 * ctx["b_a"] + n * (0.6 * ctx["b_a"] / n),
                         b_b=0.4 * ctx["b_b"] + n * (0.6 * ctx["b_b"] / n)),
    }
    values = {k: REP.s_ch(v, 0.2872, 4.2, -25.9) for k, v in variants.items()}
    check("T3 background split (flr vs dcr) identical",
          len(set(values.values())) == 1,
          "S = " + ", ".join("%s %.18e" % (k, v) for k, v in values.items()))

    # T4 r -> 1/r with theta -> 90 - theta leaves the objective invariant
    worst = max(abs(REP.s_ch(ctx, r, t0, t1) - REP.s_ch(ctx, 1.0 / r, 90.0 - t0, 90.0 - t1))
                for (r, t0, t1) in samples)
    check("T4 S(r,t) == S(1/r, 90-t)", worst < 1e-15, "worst |delta| = %.2e" % worst)

    # T5 summing the joint over a complete Bob basis returns Alice's marginal
    worst = 0.0
    for theta_a in (4.2, -25.9, 61.0):
        for theta_b in (0.0, 13.0, -37.5, 88.0):
            joint_sum = sum(IND.pair_and_singles(0.2872, 0.0, theta_a, tb)[0]
                            for tb in (theta_b, theta_b + 90.0))
            single = IND.pair_and_singles(0.2872, 0.0, theta_a, theta_b)[1]
            worst = max(worst, abs(joint_sum - single))
    check("T5 sum_B joint == p(1|theta_A) (rho_A path)", worst < 1e-15,
          "worst |delta| = %.2e" % worst)

    # T6 the two probability code paths agree (amplitude vs density matrix)
    worst_joint, worst_single = 0.0, 0.0
    for (r, ta, tb) in [(0.15, 3.0, -12.0), (0.2872, 4.2, -25.9), (0.6, 22.0, 41.0)]:
        worst_joint = max(worst_joint,
                          abs(REP.p_joint(r, 0.0, ta, tb) - IND.pair_and_singles(r, 0.0, ta, tb)[0]))
        worst_single = max(worst_single,
                           abs(REP.p_single(r, 0.0, ta) - IND.pair_and_singles(r, 0.0, ta, tb)[1]))
    check("T6 amplitude path == density-matrix path", max(worst_joint, worst_single) < 1e-15,
          "worst |delta| joint %.2e single %.2e" % (worst_joint, worst_single))

    # T7a product state (r -> 0) cannot violate the CH inequality
    worst = max(REP.s_ch(ctx, 1e-6, t0, t1) for t0 in (5.0, 20.0) for t1 in (-30.0, -60.0))
    check("T7a product state gives S <= 0", worst <= 0.0, "max S = %.3e" % worst)

    # T7b the 2/3 efficiency threshold: no violation below it, violation above it
    lo = REP.optimise(context(eta_a=0.60, eta_b=0.60, b_a=0.0, b_b=0.0), opt)["S"]
    hi = REP.optimise(context(eta_a=0.70, eta_b=0.70, b_a=0.0, b_b=0.0), opt)["S"]
    check("T7b no violation at 60% efficiency, violation at 70%", lo < 0.0 < hi,
          "S(0.60) = %.3e  S(0.70) = %.3e" % (lo, hi))

    # T8/T9 optimiser sanity on the frozen centre channel
    centre = REP.optimise(ctx, opt)
    s_doc = REP.s_ch(ctx, 0.276 / 0.961, 4.2, -25.9)
    check("T9 documented point violates (S > 0)", s_doc > 0.0, "S_doc = %.6e" % s_doc)
    check("T8 replayed optimum beats the documented point", centre["S"] > s_doc,
          "S* = %.6e  S_doc = %.6e" % (centre["S"], s_doc))
    neighbours = [REP.s_ch(ctx, centre["r"] + dr, centre["theta0_deg"] + d0, centre["theta1_deg"] + d1)
                  for dr in (0.0, 1e-4, -1e-4) for d0 in (0.0, 0.01, -0.01)
                  for d1 in (0.0, 0.01, -0.01)]
    check("T8b replayed optimum is a local maximum",
          all(v <= centre["S"] for v in neighbours),
          "max neighbour = %.9e  S* = %.9e" % (max(neighbours), centre["S"]))

    print()
    if FAILURES:
        print("FAILED:", ", ".join(FAILURES))
        return 1
    print("all checks passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
