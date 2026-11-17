#!/usr/bin/env python3
"""Generate the house-style readout-audit figure for the Munich 2017 Bell dataset.

Computes sequential anytime-valid e-process trajectories and per-setting marginal
biases directly from the official Zenodo 22936124 archives (`readout_model.py`) and
renders `munich-2017-readout-audit.png` using the paper series' house visual style
(Latin Modern Roman + Computer Modern mathtext, ink/deep-blue/gold with a single
vermilion accent for the April 2016 symmetric-readout rejection).

Usage:
    python3 scripts/physics/bell-munich-2017/plot_munich.py
"""
from __future__ import annotations

import argparse
import itertools
import math
from pathlib import Path
import subprocess
import sys
import tempfile

import matplotlib
matplotlib.use("Agg")
from matplotlib import font_manager, patheffects
from matplotlib.gridspec import GridSpec
from matplotlib.patches import FancyBboxPatch
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import readout_model as m  # noqa: E402

DEFAULT_OUT = HERE / "munich-2017-readout-audit.png"

# House palette (aligned with publish/shared/figure-style/house_style.py)
INK = "#1d2126"
SLATE = "#56606b"
MUTE = "#98a0a9"
HAIR = "#d7dbe0"
DEEP = "#1f4a73"       # 2016-06-14 run & archival structural note
VERMILION = "#c4532d"  # single warm accent: 2016-04-15 symmetric-readout rejection & Bob skew
GOLD = "#b88a1e"       # 12D asymmetric readout-domain witness trajectory
WASH = "#f5f2eb"       # warm paper wash


def _kpse(name: str) -> Path | None:
    try:
        out = subprocess.run(
            ["kpsewhich", name], capture_output=True, text=True, check=True
        ).stdout.strip()
        return Path(out) if out else None
    except (OSError, subprocess.CalledProcessError):
        return None


def configure_house_style() -> None:
    families: list[str] = []
    for name in ("lmroman10-regular.otf", "lmroman10-italic.otf", "lmroman10-bold.otf"):
        path = _kpse(name)
        if path and path.exists():
            font_manager.fontManager.addfont(str(path))
    if _kpse("lmroman10-regular.otf"):
        families.append("Latin Modern Roman")
    families.extend(["STIX Two Text", "DejaVu Serif", "serif"])
    plt.rcParams.update({
        "font.family": families,
        "font.size": 10.5,
        "mathtext.fontset": "cm",
        "axes.unicode_minus": True,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "axes.edgecolor": SLATE,
        "axes.linewidth": 0.8,
        "axes.labelcolor": INK,
        "xtick.color": SLATE,
        "ytick.color": SLATE,
        "xtick.major.width": 0.8,
        "ytick.major.width": 0.8,
        "xtick.major.size": 3.5,
        "ytick.major.size": 3.5,
        "legend.frameon": False,
        "savefig.facecolor": "white",
        "text.color": INK,
    })


def halo(lw: float = 2.8):
    return [patheffects.withStroke(linewidth=lw, foreground="white")]


def fast_asymmetric_trajectory(trials: tuple[m.Trial, ...], inst: m.Instrument) -> list[float]:
    """Fast IEEE-754 log-domain evaluation of the 4-component asymmetric readout e-process."""
    table = {
        k: tuple(float(x) for x in v)
        for k, v in m.full_joint_table(inst).items()
    }
    weights = (1.0 / 6.0, 1.0 / 6.0, 1.0 / 6.0, 0.5)
    counts = {k: [0, 0, 0, 0] for k in itertools.product((0, 1), repeat=3)}
    comp_counts = {k + (p,): [0, 0] for k in itertools.product((0, 1), repeat=3) for p in (0, 1)}
    alice_c = [0, 0]
    bob_c = [0, 0]
    logs = [0.0, 0.0, 0.0, 0.0]
    traj: list[float] = []

    for t in trials:
        q = table[(t.h, t.a, t.b)]
        ev = 2 * t.x + t.y
        parity = t.x ^ t.y
        cl = comp_counts[(t.h, t.a, t.b, parity)]
        pred_comp = (2 * cl[t.x] + 1) / (2 * (cl[0] + cl[1]) + 2)
        mass = q[0] + q[3] if parity == 0 else q[1] + q[2]
        marg_a = q[2 * t.x] + q[2 * t.x + 1]
        marg_b = q[t.y] + q[2 + t.y]
        cur = counts[(t.h, t.a, t.b)]

        f0 = pred_comp * mass / q[ev]
        f1 = ((2 * alice_c[t.x] + 1) / (2 * (alice_c[0] + alice_c[1]) + 2)) / marg_a
        f2 = ((2 * bob_c[t.y] + 1) / (2 * (bob_c[0] + bob_c[1]) + 2)) / marg_b
        f3 = ((2 * cur[ev] + 1) / (2 * sum(cur) + 4)) / q[ev]
        for idx, fac in enumerate((f0, f1, f2, f3)):
            logs[idx] += math.log(fac)
        shift = max(logs)
        e_val = math.exp(shift) * sum(w * math.exp(lv - shift) for w, lv in zip(weights, logs))
        traj.append(e_val)

        cur[ev] += 1
        cl[t.x] += 1
        alice_c[t.x] += 1
        bob_c[t.y] += 1
    return traj


def render_figure(out_path: Path, archive_dir: Path | None, dpi: int) -> None:
    configure_house_style()

    def load_all(zdir: Path):
        apr = m.admit_archive(m.ARCHIVES[0], zdir, allow_download=True)
        jun = m.admit_archive(m.ARCHIVES[1], zdir, allow_download=True)
        return apr, jun

    if archive_dir is not None:
        apr_adm, jun_adm = load_all(archive_dir)
    else:
        with tempfile.TemporaryDirectory(prefix="munich-plot-") as tmp:
            apr_adm, jun_adm = load_all(Path(tmp))

    apr_sym = m.score_balanced_complement(apr_adm.trials)
    jun_sym = m.score_balanced_complement(jun_adm.trials)
    apr_asym_traj = fast_asymmetric_trajectory(apr_adm.trials, m.WITNESS_INSTRUMENTS["2016-04-15"])
    apr_emp = m.empirical_chsh_and_biases(apr_adm.trials)
    jun_emp = m.empirical_chsh_and_biases(jun_adm.trials)

    fig = plt.figure(figsize=(11.9, 6.25), dpi=dpi, facecolor="white")
    gs = GridSpec(
        2, 2, figure=fig,
        width_ratios=[1.08, 1.0],
        height_ratios=[1.05, 0.95],
        left=0.068, right=0.982, bottom=0.108, top=0.754,
        wspace=0.205, hspace=0.265,
    )

    ax_a = fig.add_subplot(gs[:, 0])
    ax_b = fig.add_subplot(gs[0, 1])
    ax_c = fig.add_subplot(gs[1, 1])
    ax_c.axis("off")

    # -----------------------------------------------------------------------
    # Panel (a): Sequential anytime-valid e-process trajectories E_t
    # -----------------------------------------------------------------------
    ax_a.set_title(
        "Anytime-valid sequential e-process across official valid pairs",
        loc="left", fontsize=11.1, color=SLATE, pad=8,
    )
    ax_a.text(0.022, 0.968, "(a)", transform=ax_a.transAxes, fontsize=11.5, color=INK, va="top")

    ax_a.set_yscale("log")
    ax_a.axhspan(40.0, 2800.0, facecolor=WASH, edgecolor="none", zorder=0)
    ax_a.axhline(1.0, color=HAIR, lw=0.9, zorder=1)
    ax_a.axhline(40.0, color=VERMILION, lw=1.05, ls="--", alpha=0.75, zorder=2)

    xs_apr = list(range(1, len(apr_adm.trials) + 1))
    xs_jun = list(range(1, len(jun_adm.trials) + 1))

    # Plot thinned + extrema-preserving polylines so 240-DPI rendering stays crisp
    def thin_indices(vals: list[float], step: int = 8) -> tuple[list[int], list[float]]:
        keep = {0, len(vals) - 1}
        for i in range(0, len(vals), step):
            keep.add(i)
            window = vals[i : min(len(vals), i + step)]
            if window:
                keep.add(i + window.index(max(window)))
                keep.add(i + window.index(min(window)))
        idx_sorted = sorted(keep)
        return [i + 1 for i in idx_sorted], [vals[i] for i in idx_sorted]

    xa_s, ya_s = thin_indices(apr_sym["trajectory"], step=8)  # type: ignore[arg-type]
    xj_s, yj_s = thin_indices(jun_sym["trajectory"], step=8)  # type: ignore[arg-type]
    xa_w, ya_w = thin_indices(apr_asym_traj, step=8)

    ax_a.plot(
        xa_s, ya_s, color=VERMILION, lw=1.95, ls="-", zorder=4,
        label=r"2016-04-15 symmetric readout ($S=2.221$; rejected, $E_{\max}\approx 494.8$)",
    )
    ax_a.plot(
        xj_s, yj_s, color=DEEP, lw=1.75, ls="-", zorder=3,
        label=r"2016-06-14 symmetric readout ($S=2.096$; $\max E \approx 2.17$)",
    )
    ax_a.plot(
        xa_w, ya_w, color=GOLD, lw=1.65, ls=(0, (5, 2.2)), zorder=3,
        label=r"2016-04-15 asymmetric 12D readout witness ($\max E = 1.00$)",
    )

    cross_idx = int(apr_sym["first_crossing"])  # type: ignore[arg-type]
    cross_val = float(apr_sym["first_crossing_e"])  # type: ignore[arg-type]
    peak_idx = int(apr_sym["max_prefix"])  # type: ignore[arg-type]
    peak_val = float(apr_sym["max_e"])  # type: ignore[arg-type]

    ax_a.scatter([cross_idx], [cross_val], s=58, facecolor=VERMILION, edgecolor="white", linewidth=1.0, zorder=6)
    ax_a.scatter([peak_idx], [peak_val], s=66, facecolor=VERMILION, edgecolor="white", linewidth=1.0, zorder=6)

    ax_a.annotate(
        r"crosses $E = 40$ at pair $3{,}974$",
        xy=(cross_idx, cross_val), xytext=(620, 145.0),
        fontsize=9.25, color=VERMILION,
        arrowprops=dict(arrowstyle="->", color=VERMILION, lw=1.0, shrinkA=2, shrinkB=5),
        path_effects=halo(),
    )
    ax_a.annotate(
        r"peak $E_{\max} \approx 494.8$" + "\n" + r"(pair $10{,}136$)",
        xy=(peak_idx, peak_val), xytext=(5950, 760.0),
        fontsize=9.2, color=VERMILION,
        arrowprops=dict(arrowstyle="->", color=VERMILION, lw=1.0, shrinkA=2, shrinkB=5),
        path_effects=halo(),
    )
    ax_a.text(
        180, 29.0,
        r"threshold $E = 40$ ($\alpha = 1/40$)",
        fontsize=8.55, color=VERMILION, ha="left", va="top", path_effects=halo(),
    )
    ax_a.text(
        5600, 4.4e-4,
        r"asymmetric readout witness ($\max E = 1.00$ across all $10{,}201$ pairs)",
        fontsize=8.5, color=GOLD, ha="center", va="bottom", path_effects=halo(),
    )

    ax_a.set_xlim(0, 10500)
    ax_a.set_ylim(2.8e-4, 2600.0)
    ax_a.set_xticks([0, 2000, 4000, 6000, 8000, 10000])
    ax_a.set_xticklabels(["0", "2,000", "4,000", "6,000", "8,000", "10,000"], fontsize=10.0)
    ax_a.set_yticks([1e-3, 1e-2, 1e-1, 1.0, 10.0, 100.0, 1000.0])
    ax_a.set_xlabel("official valid pair index $t$ (acquisition order)", fontsize=10.8, labelpad=4)
    ax_a.set_ylabel(r"sequential evidence $E_t = (E_{J,t} + E_{A,t} + E_{B,t})/3$", fontsize=10.8)

    # -----------------------------------------------------------------------
    # Panel (b): Empirical outcome bias mu_hat = P_hat(0) - P_hat(1)
    # -----------------------------------------------------------------------
    ax_b.set_title(
        r"Single-side outcome bias $\hat{\mu} = \hat{P}(0) - \hat{P}(1)$ ($\pm 1.96\,\mathrm{SE}$)",
        loc="left", fontsize=10.9, color=SLATE, pad=8,
    )
    ax_b.text(0.022, 0.935, "(b)", transform=ax_b.transAxes, fontsize=11.5, color=INK, va="top")

    ax_b.axhline(0.0, color=SLATE, lw=0.85, ls="--", zorder=1)
    ax_b.axhline(0.05, color=HAIR, lw=0.7, ls=":", zorder=0)
    ax_b.axhline(-0.05, color=HAIR, lw=0.7, ls=":", zorder=0)

    channels = ["Alice 0", "Alice 1", "Bob 0", "Bob 1"]
    x_pos = [0.0, 1.0, 2.0, 3.0]
    dx = 0.145

    apr_mu = [float(apr_emp["biases"][ch]["mu_hat"]) for ch in channels]  # type: ignore[index]
    apr_ci = [1.96 * float(apr_emp["biases"][ch]["se_mu"]) for ch in channels]  # type: ignore[index]
    jun_mu = [float(jun_emp["biases"][ch]["mu_hat"]) for ch in channels]  # type: ignore[index]
    jun_ci = [1.96 * float(jun_emp["biases"][ch]["se_mu"]) for ch in channels]  # type: ignore[index]

    ax_b.errorbar(
        [x - dx for x in x_pos], apr_mu, yerr=apr_ci,
        fmt="o", markersize=6.2, color=VERMILION, ecolor=VERMILION,
        elinewidth=1.75, capsize=3.2, capthick=1.2, zorder=4,
        label="2016-04-15 (Apr)",
    )
    ax_b.errorbar(
        [x + dx for x in x_pos], jun_mu, yerr=jun_ci,
        fmt="s", markersize=5.6, color=DEEP, ecolor=DEEP,
        elinewidth=1.65, capsize=3.2, capthick=1.2, zorder=3,
        label="2016-06-14 (Jun)",
    )

    ax_b.text(
        2.36, -0.098,
        r"Apr Bob pooled: $4{,}852 : 5{,}349$ ($-4.87\%,\ 4.9\sigma$)",
        fontsize=8.65, color=VERMILION, ha="center", path_effects=halo(),
    )
    ax_b.text(
        3.14, 0.089,
        r"Jun Bob 1: $+5.31\%$",
        fontsize=8.45, color=DEEP, ha="right", path_effects=halo(),
    )

    ax_b.set_xticks(x_pos)
    ax_b.set_xticklabels(["Alice 0", "Alice 1", "Bob 0", "Bob 1"], fontsize=9.9)
    ax_b.set_yticks([-0.10, -0.05, 0.0, 0.05, 0.10])
    ax_b.set_yticklabels([r"$-0.10$", r"$-0.05$", r"$0$", r"$+0.05$", r"$+0.10$"], fontsize=9.6)
    ax_b.set_xlim(-0.52, 3.52)
    ax_b.set_ylim(-0.116, 0.118)
    ax_b.set_ylabel(r"outcome bias $\hat{\mu}$", fontsize=10.6)
    ax_b.legend(loc="upper left", bbox_to_anchor=(0.09, 1.01), fontsize=8.7, ncol=2, columnspacing=0.9)

    # -----------------------------------------------------------------------
    # Panel (c): Asymmetric ionization/CEM readout & 2D scale fiber card
    # -----------------------------------------------------------------------
    card = FancyBboxPatch(
        (0.005, 0.01), 0.985, 0.95,
        boxstyle="round,pad=0.012,rounding_size=0.018",
        facecolor=WASH, edgecolor=HAIR, linewidth=0.95,
        transform=ax_c.transAxes, zorder=1,
    )
    ax_c.add_patch(card)

    ax_c.text(
        0.032, 0.90,
        "(c)  Significance & asymmetric ionization/CEM readout identifiability:",
        transform=ax_c.transAxes, fontsize=9.75, color=INK, va="top", ha="left",
    )
    ax_c.text(
        0.032, 0.715,
        r"$\bullet$ Local-realist CHSH test unaffected: $S = 2.221$ (Apr) and $2.096$ (Jun) hold without" + "\n"
        r"  symmetric marginals; asymmetric readout ($F_0 \neq F_1$) reconciles all $20{,}403$ pairs." + "\n"
        r"$\bullet$ Exact 2D scale fiber: $(u_A,z_A)\mapsto(su_A,tz_A),\ (u_B,z_B)\mapsto(u_B/s,z_B/t)$ leaves all" + "\n"
        r"  32 cells $P(x,y\mid h,a,b)$ invariant while trading off Alice vs. Bob errors $(e_0,e_1)$.",
        transform=ax_c.transAxes, fontsize=8.45, color=SLATE, va="top", ha="left", linespacing=1.36,
    )

    ax_c.plot([0.032, 0.968], [0.295, 0.295], color=HAIR, lw=0.85, transform=ax_c.transAxes, zorder=2)
    ax_c.text(
        0.032, 0.242,
        "Archive notes (DOI 10.5281/zenodo.22936124): run-matched bright/dark calibrations\n"
        "needed to split $(s,t)$; lab_2.csv has 7 header vs. 6 data cols (0-based pairs index).",
        transform=ax_c.transAxes, fontsize=8.25, color=DEEP, va="top", ha="left", linespacing=1.32,
    )

    # Overall House Header & Legend bar
    fig.text(
        0.068, 0.960,
        "Munich 2017 entangled-atom Bell test: readout asymmetry and scale degeneracy",
        ha="left", va="top", fontsize=13.2, color=INK,
    )
    fig.text(
        0.068, 0.920,
        "Rosenfeld et al., Phys. Rev. Lett. 119, 010402 (2017);   Official raw trial archive Zenodo DOI: 10.5281/zenodo.22936124 (20,403 valid pairs)",
        ha="left", va="top", fontsize=9.4, color=SLATE,
    )

    handles_a, labels_a = ax_a.get_legend_handles_labels()
    fig.legend(
        handles_a, labels_a,
        loc="upper left", bbox_to_anchor=(0.060, 0.890),
        ncol=2, frameon=False, fontsize=8.85, handletextpad=0.45, columnspacing=1.2,
    )

    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, dpi=dpi)
    plt.close(fig)
    try:
        from PIL import Image
        with Image.open(out_path) as im:
            im.convert("RGB").save(out_path, format="PNG", optimize=True)
    except ImportError:
        pass


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=DEFAULT_OUT, help="Output PNG path.")
    parser.add_argument("--archive-dir", type=Path, default=None, help="Directory with Munich Bell ZIPs.")
    parser.add_argument("--dpi", type=int, default=240, help="Rasterization DPI (default: 240).")
    args = parser.parse_args()

    render_figure(args.out.resolve(), args.archive_dir, args.dpi)
    print(f"Wrote {args.out} ({args.out.stat().st_size / 1024:.1f} KB)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
