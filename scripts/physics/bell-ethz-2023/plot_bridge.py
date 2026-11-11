#!/usr/bin/env python3
"""Generate the house-style phase-bridge figure for ETH 2023 Bell dataset (Storz et al., Nature 2023).

Computes all curves and correlators directly from `pulse_model.py` and renders
`ethz-2023-phase-bridge.png` using the paper series' house visual language
(Latin Modern Roman + Computer Modern mathtext, ink/deep-blue/gold with a single
vermilion accent for the bare nominal delta = -pi/4 point).

Usage:
    python3 scripts/physics/bell-ethz-2023/plot_bridge.py
"""
from __future__ import annotations

import argparse
import math
from pathlib import Path
import subprocess
import sys

import matplotlib
matplotlib.use("Agg")
from matplotlib import font_manager, patheffects
from matplotlib.patches import FancyBboxPatch
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import pulse_model as m  # noqa: E402

DEFAULT_OUT = HERE / "ethz-2023-phase-bridge.png"

# House palette (aligned with publish/shared/figure-style/house_style.py)
INK = "#1d2126"
SLATE = "#56606b"
MUTE = "#98a0a9"
HAIR = "#d7dbe0"
DEEP = "#1f4a73"       # SI Eq. 7 curve & maximum-violation reference
VERMILION = "#c4532d"  # single warm accent: bare nominal (gamma=0, theta=-pi/4) -> S=0
GOLD = "#b88a1e"       # inverted off-diagonal sign branch (delta -> -delta)
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


def render_figure(out_path: Path, dpi: int) -> None:
    configure_house_style()

    fig = plt.figure(figsize=(11.9, 6.15), dpi=dpi, facecolor="white")
    gs = GridSpec(
        2, 2, figure=fig,
        width_ratios=[1.08, 1.0],
        height_ratios=[1.08, 0.92],
        left=0.068, right=0.982, bottom=0.110, top=0.775,
        wspace=0.20, hspace=0.25,
    )

    ax_a = fig.add_subplot(gs[:, 0])
    ax_b = fig.add_subplot(gs[0, 1])
    ax_c = fig.add_subplot(gs[1, 1])
    ax_c.axis("off")

    # -----------------------------------------------------------------------
    # Panel (a): CHSH value S(delta) vs net phase delta = gamma + phi_B - phi_A
    # -----------------------------------------------------------------------
    ax_a.set_title(
        "SI Eq. 7 CHSH value vs. combined phase $\\delta = \\gamma + \\phi_B - \\phi_A$",
        loc="left", fontsize=11.2, color=SLATE, pad=8,
    )
    ax_a.text(0.022, 0.965, "(a)", transform=ax_a.transAxes, fontsize=11.5, color=INK, va="top")

    deltas = [-math.pi + 2.0 * math.pi * i / 400.0 for i in range(401)]
    alice0 = m.quarter_station(0.0)
    s_eq7 = [m.chsh(m.correlations(0.0, alice0, m.quarter_station(d)), m.OFFICIAL_CHSH_SIGNS) for d in deltas]
    s_flip = [m.chsh(m.correlations(0.0, alice0, m.quarter_station(-d)), m.OFFICIAL_CHSH_SIGNS) for d in deltas]

    ax_a.axhspan(-2.0, 2.0, facecolor=WASH, edgecolor="none", zorder=0)
    ax_a.axhline(0.0, color=HAIR, lw=0.9, zorder=1)
    ax_a.axhline(2.0, color=MUTE, lw=0.8, ls=":", zorder=1)
    ax_a.axhline(-2.0, color=MUTE, lw=0.8, ls=":", zorder=1)
    tsirelson = 2.0 * math.sqrt(2.0)
    ax_a.axhline(tsirelson, color=HAIR, lw=0.8, ls="--", zorder=1)

    ax_a.axvline(-math.pi / 4.0, color=HAIR, lw=0.8, ls=":", zorder=1)
    ax_a.axvline(math.pi / 4.0, color=HAIR, lw=0.8, ls=":", zorder=1)

    ax_a.plot(
        deltas, s_eq7, color=DEEP, lw=2.2, ls="-", zorder=3,
        label=r"direct SI Eq. 7 + Eq. 14: $S = 2\sqrt{2}\cos(\delta - \pi/4)$",
    )
    ax_a.plot(
        deltas, s_flip, color=GOLD, lw=1.85, ls=(0, (5, 2.2)), zorder=2,
        label=r"off-diagonal inverted ($\delta \mapsto -\delta$): $S = 2\sqrt{2}\cos(\delta + \pi/4)$",
    )

    ax_a.scatter([math.pi / 4.0], [tsirelson], s=62, facecolor=DEEP, edgecolor="white", linewidth=0.95, zorder=6)
    ax_a.scatter([-math.pi / 4.0], [tsirelson], s=48, facecolor="white", edgecolor=GOLD, linewidth=1.5, zorder=5)
    ax_a.scatter(
        [-math.pi / 4.0], [0.0], s=86, facecolor=VERMILION, edgecolor="white", linewidth=1.1, zorder=7,
        label=r"bare nominal $(\gamma=0,\ \theta=-\pi/4 \Rightarrow S=0)$",
    )

    # Annotations placed strictly in open regions with zero curve intersections
    ax_a.annotate(
        "bare nominal setting\n" + r"$\gamma=0,\ \theta=-\pi/4 \Rightarrow S=0$",
        xy=(-math.pi / 4.0, 0.0), xytext=(-0.88, -1.38),
        fontsize=9.6, color=VERMILION,
        arrowprops=dict(arrowstyle="->", color=VERMILION, lw=1.05, shrinkA=2, shrinkB=5),
        path_effects=halo(),
    )
    ax_a.annotate(
        r"SI Eq. 7 peak: $\delta = +\pi/4$ ($2\sqrt{2}$)",
        xy=(math.pi / 4.0, tsirelson), xytext=(0.38, 3.22),
        fontsize=9.3, color=DEEP,
        arrowprops=dict(arrowstyle="->", color=DEEP, lw=0.9, shrinkA=2, shrinkB=4),
        path_effects=halo(),
    )
    ax_a.annotate(
        r"$\delta \mapsto -\delta$ peak: $-\pi/4$",
        xy=(-math.pi / 4.0, tsirelson), xytext=(-2.36, 3.22),
        fontsize=9.2, color=GOLD,
        arrowprops=dict(arrowstyle="->", color=GOLD, lw=0.9, shrinkA=2, shrinkB=4),
        path_effects=halo(),
    )

    ax_a.text(3.04, 2.07, "local bound $|S|=2$", fontsize=8.7, color=SLATE, ha="right", path_effects=halo())
    ax_a.text(3.04, tsirelson - 0.25, r"Tsirelson $2\sqrt{2}$", fontsize=8.7, color=SLATE, ha="right", path_effects=halo())

    tick_vals = [-math.pi, -math.pi / 2, -math.pi / 4, 0.0, math.pi / 4, math.pi / 2, math.pi]
    tick_lbls = [r"$-\pi$", r"$-\frac{\pi}{2}$", r"$-\frac{\pi}{4}$", r"$0$", r"$\frac{\pi}{4}$", r"$\frac{\pi}{2}$", r"$\pi$"]
    ax_a.set_xticks(tick_vals)
    ax_a.set_xticklabels(tick_lbls, fontsize=10.5)
    ax_a.set_xlim(-math.pi, math.pi)
    ax_a.set_ylim(-3.12, 3.62)
    ax_a.set_xlabel(r"combined microwave/source phase $\delta = \gamma + \phi_B - \phi_A$ (rad)", fontsize=11, labelpad=4)
    ax_a.set_ylabel(r"ideal CHSH value $S$", fontsize=11)

    # -----------------------------------------------------------------------
    # Panel (b): Four-cell correlators E_ab at bare nominal vs inverted sign
    # -----------------------------------------------------------------------
    ax_b.set_title(
        "Correlators $E_{ab}$ in SI Eq. 7 ($S = E_{00} - E_{01} + E_{10} + E_{11}$)",
        loc="left", fontsize=11.0, color=SLATE, pad=8,
    )
    ax_b.text(0.022, 0.93, "(b)", transform=ax_b.transAxes, fontsize=11.5, color=INK, va="top")

    c_nom = m.correlations(0.0, alice0, m.quarter_station(-math.pi / 4.0))
    c_inv = m.correlations(0.0, alice0, m.quarter_station(math.pi / 4.0))

    ax_b.axhline(0.0, color=SLATE, lw=0.8, zorder=1)
    inv_sqrt2 = 1.0 / math.sqrt(2.0)
    ax_b.axhline(inv_sqrt2, color=HAIR, lw=0.75, ls=":", zorder=0)
    ax_b.axhline(-inv_sqrt2, color=HAIR, lw=0.75, ls=":", zorder=0)

    xs = [0, 1, 2, 3]
    w = 0.28
    ax_b.bar(
        [x - w / 2 - 0.02 for x in xs], c_nom, width=w,
        color=VERMILION, alpha=0.90, zorder=3,
        label=r"bare nominal ($\delta = -\pi/4 \Rightarrow S = 0$)",
    )
    ax_b.bar(
        [x + w / 2 + 0.02 for x in xs], c_inv, width=w,
        color=DEEP, alpha=0.88, zorder=3,
        label=r"off-diagonal inverted ($S = 2\sqrt{2} \approx 2.83$)",
    )

    eq7_labels = [
        r"$(0,0)$" + "\n" + r"$+E_{00}$",
        r"$(0,1)$" + "\n" + r"$-E_{01}$",
        r"$(1,0)$" + "\n" + r"$+E_{10}$",
        r"$(1,1)$" + "\n" + r"$+E_{11}$",
    ]
    ax_b.set_xticks(xs)
    ax_b.set_xticklabels(eq7_labels, fontsize=9.8)
    ax_b.set_yticks([-inv_sqrt2, 0.0, inv_sqrt2])
    ax_b.set_yticklabels([r"$-1/\sqrt{2}$", r"$0$", r"$+1/\sqrt{2}$"], fontsize=9.8)
    ax_b.set_xlim(-0.58, 3.58)
    ax_b.set_ylim(-1.12, 1.32)
    ax_b.set_ylabel(r"correlator $E_{ab}$", fontsize=10.8)

    ax_b.text(
        1.5, -0.97,
        r"off-diagonal cells swap signs $\Rightarrow \pm 1/\sqrt{2}$ cancel diagonal terms",
        fontsize=8.9, color=VERMILION, ha="center", path_effects=halo(),
    )
    ax_b.legend(loc="upper right", bbox_to_anchor=(1.0, 1.02), fontsize=8.8, ncol=1)

    # -----------------------------------------------------------------------
    # Panel (c): Five-way convention degeneracy & missing archive join
    # -----------------------------------------------------------------------
    card = FancyBboxPatch(
        (0.005, 0.01), 0.985, 0.95,
        boxstyle="round,pad=0.012,rounding_size=0.018",
        facecolor=WASH, edgecolor=HAIR, linewidth=0.95,
        transform=ax_c.transAxes, zorder=1,
    )
    ax_c.add_patch(card)

    ax_c.text(
        0.032, 0.89,
        "(c)  Indistinguishable origins of $(E_{01},E_{10}) \\mapsto (-E_{01},-E_{10})$:",
        transform=ax_c.transAxes, fontsize=9.8, color=INK, va="top", ha="left",
    )
    ax_c.text(
        0.035, 0.69,
        r"1. Bob azimuth handedness ($\theta \mapsto -\theta$)" + "\n"
        r"3. Optional $\pi/2$ pulse signs ($o_A = o_B = -1$)",
        transform=ax_c.transAxes, fontsize=8.7, color=SLATE, va="top", ha="left", linespacing=1.45,
    )
    ax_c.text(
        0.530, 0.69,
        r"2. Source/node offset ($\gamma \mapsto \gamma - 2\theta$; Fig. 5)" + "\n"
        r"4. $(a,b)$ bit complement or readout signs",
        transform=ax_c.transAxes, fontsize=8.6, color=SLATE, va="top", ha="left", linespacing=1.45,
    )

    ax_c.plot([0.032, 0.968], [0.355, 0.355], color=HAIR, lw=0.85, transform=ax_c.transAxes, zorder=2)
    ax_c.text(
        0.032, 0.295,
        "Missing in archive DOI 10.3929/ethz-b-000624026 to fix a blinded forward map:\n"
        "(i) signed controller-to-CSV truth table per $(a,b)$;  (ii) hourly phase-offset\n"
        "calibration log joined to trial rows of main_dataset_all_events.txt.",
        transform=ax_c.transAxes, fontsize=8.55, color=DEEP, va="top", ha="left", linespacing=1.32,
    )

    # Overall House Header & Legend bar
    fig.text(
        0.068, 0.956,
        "ETH 2023 superconducting Bell test: SI Eq. 7 phase-sign closure and archival degeneracy",
        ha="left", va="top", fontsize=13.2, color=INK,
    )
    fig.text(
        0.068, 0.916,
        "Storz et al., Nature 617, 265 (2023), Methods, Fig. 4 & SI Eqs. 7, 14–16;   ETH Research Collection dataset DOI: 10.3929/ethz-b-000624026",
        ha="left", va="top", fontsize=9.5, color=SLATE,
    )

    handles_a, labels_a = ax_a.get_legend_handles_labels()
    fig.legend(
        handles_a, labels_a,
        loc="upper left", bbox_to_anchor=(0.062, 0.884),
        ncol=3, frameon=False, fontsize=9.0, handletextpad=0.45, columnspacing=1.25,
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
    parser.add_argument("--dpi", type=int, default=240, help="Rasterization DPI (default: 240).")
    args = parser.parse_args()

    render_figure(args.out.resolve(), args.dpi)
    print(f"Wrote {args.out} ({args.out.stat().st_size / 1024:.1f} KB)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
