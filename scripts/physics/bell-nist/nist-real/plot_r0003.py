#!/usr/bin/env python3
"""Generate the house-style summary figure for the NIST 2015 nominal replay (r0003).

Computes continuous threshold and efficiency-scaling curves directly from the
SHA-256-pinned `replay.py` implementation and `replay-r0003.json` receipt, and
renders `nist-2015-nominal-replay.png` using the paper series' house visual style
(Latin Modern Roman + Computer Modern mathtext, ink/deep-blue/gold with a single
vermilion accent for the paper's nominal setting).

Usage:
    python3 scripts/physics/bell-nist/nist-real/plot_r0003.py
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

import matplotlib
matplotlib.use("Agg")
from matplotlib import font_manager, patheffects
import matplotlib.patches as patches
import matplotlib.pyplot as plt
from matplotlib.gridspec import GridSpec

REPO_ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent

REPLAY_PY = (
    REPO_ROOT
    / "scripts/first-release/ab/physics/stage10/independent-bell/nist-real/nominal-replay/replay.py"
)
EXPECTED_REPLAY_SHA = "264bb4a516e6fadf2cf39114ff912cae43361de002ae3af62d4d93121ef3eac7"

CRITERION_MD = (
    REPO_ROOT
    / "evidence/first-release/ab/physics/stage10/independent-bell/nist-real/nominal-replay/criterion-r0003.md"
)
EXPECTED_CRITERION_SHA = "2dd6d3e511da35415637edda8a164b1569c055a16ec7d25b99f262c5d86412d6"

ARCHIVED_JSON = (
    REPO_ROOT
    / "evidence/first-release/acceptance/scientific-20261005/nist-nominal-replay/replay-r0003.json"
)
DEFAULT_OUT = HERE / "nist-2015-nominal-replay.png"

# House palette (aligned with publish/shared/figure-style/house_style.py)
INK = "#1d2126"
SLATE = "#56606b"
MUTE = "#98a0a9"
HAIR = "#d7dbe0"
DEEP = "#1f4a73"       # primary model curves & replayed p. 4 optimum
VERMILION = "#c4532d"  # single warm accent: paper's p. 3 nominal setting
GOLD = "#b88a1e"       # secondary diagnostic locus: uniform efficiency scaling
WASH = "#f5f2eb"       # warm paper wash for uncertainty / operating regions


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


def verify_sha256(path: Path, expected: str) -> None:
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise ValueError(f"SHA-256 mismatch for {path}: expected {expected}, got {actual}")


def load_replay_module():
    verify_sha256(REPLAY_PY, EXPECTED_REPLAY_SHA)
    verify_sha256(CRITERION_MD, EXPECTED_CRITERION_SHA)
    spec = importlib.util.spec_from_file_location("replay_r0003", REPLAY_PY)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Unable to load {REPLAY_PY}")
    mod = importlib.util.module_from_spec(spec)
    sys.modules["replay_r0003"] = mod
    spec.loader.exec_module(mod)
    return mod


def compute_plot_data(replay, frozen: dict, archived: dict) -> dict:
    opt = frozen["optimizer"]
    eta_a0 = frozen["channel"]["eta_A"]["center"]
    eta_b0 = frozen["channel"]["eta_B"]["center"]
    n0 = frozen["channel"]["pair_probability"]["center"]
    n_zbg = frozen["diagnostics"]["threshold_check"]["zero_background"]["N"]

    archived_kappas = {
        round(pt["kappa"], 6): pt["optimum"]
        for pt in archived["diagnostics"]["D7_attribution"]["points"]
    }
    kappa_grid = sorted(
        set([round(0.974 + 0.002 * i, 6) for i in range(17)] + [0.980, 0.985, 0.990, 1.000])
    )
    kappa_curve = []
    prev_start = [0.25, 3.8, -25.2]
    for k in kappa_grid:
        ctx = replay.make_context(frozen, k * eta_a0, k * eta_b0, n0)
        if k in archived_kappas:
            best_opt = archived_kappas[k]
            prev_start = [
                best_opt["raw"]["r"],
                best_opt["raw"]["theta0_deg"],
                best_opt["raw"]["theta1_deg"],
            ]
        else:
            cands = []
            for st in (prev_start, [0.287, 4.2, -25.9], [0.315, 4.95, -27.23]):
                val, r, th0, th1 = replay.pattern_search(ctx, st, opt)
                r_c, th0_c, th1_c = replay.canonicalise(r, th0, th1)
                cands.append((
                    val,
                    {
                        "S": val,
                        "r": r_c,
                        "theta0_deg": th0_c,
                        "theta1_deg": th1_c,
                        "raw": {"r": r, "theta0_deg": th0, "theta1_deg": th1},
                    },
                ))
            best_opt = max(cands, key=lambda x: x[0])[1]
            prev_start = [
                best_opt["raw"]["r"],
                best_opt["raw"]["theta0_deg"],
                best_opt["raw"]["theta1_deg"],
            ]
        kappa_curve.append({"kappa": k, "optimum": best_opt})

    eta_grid = sorted(
        set(
            [round(0.655 + 0.0025 * i, 6) for i in range(43)]
            + [0.666667, 0.668448, 0.725, 0.726427, 0.7515]
        )
    )
    zero_bg_curve = []
    prev = [0.05, 1.0, -15.0]
    for eta in eta_grid:
        ctx = replay.make_context(frozen, eta, eta, n_zbg, background=(0.0, 0.0))
        cands = []
        for st in (prev, [0.02, 0.3, -12.0], [0.15, 2.5, -21.0], [0.32, 5.0, -27.3]):
            val, r, th0, th1 = replay.pattern_search(ctx, st, opt)
            r_c, th0_c, th1_c = replay.canonicalise(r, th0, th1)
            cands.append((val, r_c, th0_c, th1_c, [r, th0, th1]))
        best = max(cands, key=lambda x: x[0])
        prev = best[4]
        ctx_5e4 = replay.make_context(frozen, eta, eta, n0, background=(0.0, 0.0))
        s_5e4 = replay.s_ch(ctx_5e4, best[1], best[2], best[3])
        zero_bg_curve.append({"eta": eta, "S_per_trial_N5e4": s_5e4})

    pub_bg_curve = []
    prev = [0.15, 2.2, -21.0]
    for eta in eta_grid:
        ctx = replay.make_context(frozen, eta, eta, n0)
        cands = []
        for st in (prev, [0.05, 0.8, -16.0], [0.227, 3.32, -24.23], [0.315, 4.95, -27.23]):
            val, r, th0, th1 = replay.pattern_search(ctx, st, opt)
            r_c, th0_c, th1_c = replay.canonicalise(r, th0, th1)
            cands.append((val, r_c, th0_c, th1_c, [r, th0, th1]))
        best = max(cands, key=lambda x: x[0])
        prev = best[4]
        pub_bg_curve.append({"eta": eta, "S_per_trial_N5e4": best[0]})

    return {
        "kappa_curve": kappa_curve,
        "zero_bg_curve": zero_bg_curve,
        "pub_bg_curve": pub_bg_curve,
    }


def halo(lw: float = 2.8):
    return [patheffects.withStroke(linewidth=lw, foreground="white")]


def render_figure(archived: dict, curves: dict, out_path: Path, dpi: int) -> None:
    configure_house_style()

    fig = plt.figure(figsize=(11.8, 6.18), dpi=dpi, facecolor="white")
    gs = GridSpec(
        2, 2, figure=fig,
        width_ratios=[1.14, 1.0],
        height_ratios=[1.0, 1.0],
        left=0.072, right=0.980, bottom=0.112, top=0.752,
        wspace=0.215, hspace=0.135,
    )

    ax_a = fig.add_subplot(gs[0, 0])
    ax_b = fig.add_subplot(gs[1, 0], sharex=ax_a)
    ax_c = fig.add_subplot(gs[:, 1])

    doc_r = archived["documented"]["r"]
    doc_t0, doc_t1 = archived["documented"]["alice_angles_deg"]
    box_pts = archived["box_points"]
    center_opt = box_pts[0]["optimum"]
    corners = [p["optimum"] for p in box_pts[1:]]
    band_w = archived["band"]["widened"]
    delta15 = archived["diagnostics"]["variants"]["delta_1.5_deg"]["optimum"]

    k_sub = curves["kappa_curve"]
    k_r = [p["optimum"]["r"] for p in k_sub]
    k_t0 = [p["optimum"]["theta0_deg"] for p in k_sub]
    k_t1 = [p["optimum"]["theta1_deg"] for p in k_sub]
    tick_kappas = [0.980, 0.985, 0.990]
    tick_pts = {p["kappa"]: p for p in k_sub if p["kappa"] in tick_kappas}

    for idx, (ax, y_key, doc_y, ylim, ylabel, panel_tag) in enumerate([
        (ax_a, "theta0_deg", doc_t0, (3.88, 5.34), r"polarizer angle $\theta_0$ (deg)", "(a)"),
        (ax_b, "theta1_deg", doc_t1, (-27.76, -25.44), r"polarizer angle $\theta_1$ (deg)", "(b)"),
    ]):
        # Subtle vertical reference guides tying (a) and (b) together
        ax.axvline(doc_r, color=HAIR, lw=0.8, ls=":", zorder=1)
        ax.axvline(center_opt["r"], color=HAIR, lw=0.8, ls=":", zorder=1)

        # Warm paper wash for the published p. 4 uncertainty box
        r0, r1 = band_w["r"]
        y0, y1 = band_w[y_key]
        rect = patches.Rectangle(
            (r0, y0), r1 - r0, y1 - y0,
            facecolor=WASH, edgecolor=DEEP,
            linewidth=0.95, linestyle=(0, (4, 2.2)), zorder=2,
            label=r"published p. 4 uncertainty box ($\pm 0.3\%\ \eta$, $N$, rounding)" if idx == 0 else None,
        )
        ax.add_patch(rect)

        # Gold diagnostic curve: uniform efficiency scaling
        k_y = k_t0 if idx == 0 else k_t1
        ax.plot(
            k_r, k_y, color=GOLD, lw=1.85, ls=(0, (5, 2.2)), zorder=3,
            label=r"efficiency scaling $(\eta_A,\eta_B)\mapsto \kappa(\eta_A,\eta_B)$" if idx == 0 else None,
        )
        for k_val in tick_kappas:
            pt = tick_pts[k_val]["optimum"]
            ax.scatter(
                [pt["r"]], [pt[y_key]], s=28,
                facecolor="white", edgecolor=GOLD, linewidth=1.35, zorder=4,
            )

        # 16 corner optima + center optimum in DEEP
        ax.scatter(
            [c["r"] for c in corners], [c[y_key] for c in corners],
            s=20, color=DEEP, alpha=0.62, zorder=4,
            label="16 box-corner optima" if idx == 0 else None,
        )
        ax.scatter(
            [center_opt["r"]], [center_opt[y_key]],
            marker="o", s=58, facecolor=DEEP, edgecolor="white", linewidth=0.9, zorder=6,
            label="p. 4 center optimum" if idx == 0 else None,
        )

        # Single warm accent (VERMILION): paper's p. 3 nominal setting
        ax.scatter(
            [doc_r], [doc_y],
            marker="o", s=78, facecolor=VERMILION, edgecolor="white", linewidth=1.1, zorder=7,
            label="paper p. 3 nominal setting" if idx == 0 else None,
        )

        ax.set_xlim(0.258, 0.335)
        ax.set_ylim(*ylim)
        ax.set_ylabel(ylabel, fontsize=11)
        ax.text(
            0.020, 0.915, panel_tag, transform=ax.transAxes,
            fontsize=11.5, color=INK, va="top", ha="left",
        )

    ax_a.set_title(
        "Optimal state and polarizer angles vs. paper p. 3 settings",
        loc="left", fontsize=11.2, color=SLATE, pad=8,
    )
    plt.setp(ax_a.get_xticklabels(), visible=False)
    ax_b.set_xlabel(
        r"state amplitude ratio $r = \mathrm{amp}(\mathrm{VV})/\mathrm{amp}(\mathrm{HH})$ in $(|\mathrm{HH}\rangle + r|\mathrm{VV}\rangle)/\sqrt{1+r^2}$",
        fontsize=11, labelpad=5,
    )

    # Show crystal-tilt direction on (a) in open lower-right space so alternative knob is ruled out visually
    ax_a.scatter(
        [delta15["r"]], [delta15["theta0_deg"]],
        marker="^", s=38, facecolor="white", edgecolor=SLATE, linewidth=1.15, zorder=5,
    )
    ax_a.annotate(
        r"crystal tilt $\delta = 1.5^\circ$" + "\n" + r"($r^* = 0.330$, moves right)",
        xy=(delta15["r"], delta15["theta0_deg"]),
        xytext=(0.3085, 4.34),
        fontsize=8.8, color=SLATE,
        arrowprops=dict(arrowstyle="->", color=SLATE, lw=0.85, shrinkA=2, shrinkB=5),
        path_effects=halo(),
    )

    # Direct, unboxed house-style annotations on (a)
    ax_a.annotate(
        "paper p. 3 nominal\n" + r"$r = 0.287,\ \theta_0 = 4.2^\circ$",
        xy=(doc_r, doc_t0), xytext=(0.2925, 4.01),
        fontsize=9.8, color=VERMILION,
        arrowprops=dict(arrowstyle="->", color=VERMILION, lw=1.0, shrinkA=2, shrinkB=5),
        path_effects=halo(),
    )
    ax_a.annotate(
        "p. 4 center optimum\n" + r"$r^* = 0.315,\ \theta_0^* = 4.95^\circ$" + "\n" + r"($V=0.996$ coincides)",
        xy=(center_opt["r"], center_opt["theta0_deg"]), xytext=(0.2645, 4.86),
        fontsize=9.4, color=DEEP,
        arrowprops=dict(arrowstyle="->", color=DEEP, lw=0.95, shrinkA=3, shrinkB=5),
        path_effects=halo(),
    )
    for k_val, lbl, dx, dy in [
        (0.990, r"$\kappa=0.99$ ($-0.75\%$)", 0.0020, -0.11),
        (0.985, r"$\kappa=0.985$ ($-1.1\%$)", -0.0175, 0.13),
        (0.980, r"$\kappa=0.98$ ($-1.5\%$)", 0.0020, -0.09),
    ]:
        pt = tick_pts[k_val]["optimum"]
        ax_a.text(pt["r"] + dx, pt["theta0_deg"] + dy, lbl, fontsize=8.8, color=GOLD, path_effects=halo())

    # Direct annotations on (b)
    ax_b.annotate(
        "paper p. 3 nominal\n" + r"$r = 0.287,\ \theta_1 = -25.9^\circ$",
        xy=(doc_r, doc_t1), xytext=(0.2935, -25.88),
        fontsize=9.8, color=VERMILION,
        arrowprops=dict(arrowstyle="->", color=VERMILION, lw=1.0, shrinkA=2, shrinkB=5),
        path_effects=halo(),
    )
    ax_b.annotate(
        "p. 4 center optimum\n" + r"$r^* = 0.315,\ \theta_1^* = -27.23^\circ$",
        xy=(center_opt["r"], center_opt["theta1_deg"]), xytext=(0.2645, -27.44),
        fontsize=9.4, color=DEEP,
        arrowprops=dict(arrowstyle="->", color=DEEP, lw=0.95, shrinkA=3, shrinkB=5),
        path_effects=halo(),
    )
    ax_b.text(
        0.2605, -26.62,
        r"$\sim 1\%$ lower $\eta$ brings locus" + "\nalongside p. 3 settings",
        fontsize=9.0, color=GOLD, style="italic", path_effects=halo(),
    )

    # -----------------------------------------------------------------------
    # Panel (c): Model Sanity Check against Paper p. 4 Thresholds
    # -----------------------------------------------------------------------
    ax_c.set_title(
        "Threshold sanity check and CH violation at p. 4 channel",
        loc="left", fontsize=11.2, color=SLATE, pad=8,
    )
    ax_c.text(
        0.022, 0.955, "(c)", transform=ax_c.transAxes,
        fontsize=11.5, color=INK, va="top", ha="left",
    )

    eta_z = [p["eta"] * 100.0 for p in curves["zero_bg_curve"]]
    s_z = [p["S_per_trial_N5e4"] * 1e6 for p in curves["zero_bg_curve"]]
    eta_p = [p["eta"] * 100.0 for p in curves["pub_bg_curve"]]
    s_p = [p["S_per_trial_N5e4"] * 1e6 for p in curves["pub_bg_curve"]]

    ax_c.axhline(0.0, color=HAIR, lw=0.9, zorder=1)
    ax_c.axvspan(74.7, 75.6, facecolor=WASH, edgecolor="none", zorder=0)
    ax_c.axvline(74.7, color=HAIR, lw=0.7, ls=":", zorder=1)
    ax_c.axvline(75.6, color=HAIR, lw=0.7, ls=":", zorder=1)

    ax_c.plot(eta_z, s_z, color=SLATE, lw=1.75, ls=(0, (4.5, 2.2)), zorder=3, label="zero background")
    ax_c.plot(eta_p, s_p, color=DEEP, lw=2.15, ls="-", zorder=4, label="published p. 4 background")

    thr_z = archived["diagnostics"]["D3b_threshold_validation"]["zero_background"]["model_threshold"] * 100.0
    thr_p = archived["diagnostics"]["D3b_threshold_validation"]["published_background"]["model_threshold"] * 100.0

    ax_c.scatter([thr_z], [0.0], s=44, facecolor="white", edgecolor=SLATE, linewidth=1.5, zorder=6)
    ax_c.scatter([thr_p], [0.0], s=48, facecolor="white", edgecolor=DEEP, linewidth=1.7, zorder=6)

    ax_c.annotate(
        f"zero background: {thr_z:.1f}%\n(paper p. 4: $2/3 = 66.7\\%$)",
        xy=(thr_z, 0.0), xytext=(65.95, 0.86),
        fontsize=9.3, color=SLATE,
        arrowprops=dict(arrowstyle="->", color=SLATE, lw=0.9, shrinkA=2, shrinkB=5),
        path_effects=halo(),
    )
    ax_c.annotate(
        f"with background: {thr_p:.1f}%\n(paper p. 4: $72.5\\%$)",
        xy=(thr_p, 0.0), xytext=(66.05, -0.82),
        fontsize=9.3, color=DEEP,
        arrowprops=dict(arrowstyle="->", color=DEEP, lw=0.95, shrinkA=2, shrinkB=5),
        path_effects=halo(),
    )

    eta_mean = 0.5 * (74.7 + 75.6)
    s_opt = archived["diagnostics"]["D1_objective_space"]["S_at_centre_optimum"] * 1e6
    s_doc = archived["diagnostics"]["D1_objective_space"]["S_at_documented_point"] * 1e6

    ax_c.scatter([eta_mean], [s_opt], marker="o", s=56, facecolor=DEEP, edgecolor="white", linewidth=0.9, zorder=7)
    ax_c.scatter([eta_mean], [s_doc], marker="o", s=72, facecolor=VERMILION, edgecolor="white", linewidth=1.0, zorder=8)

    ax_c.annotate(
        f"at p. 4 channel ($\\eta_A=74.7\\%,\\ \\eta_B=75.6\\%$):\n"
        f"replayed optimum: $S_{{\\mathrm{{CH}}}} = +{s_opt:.2f}\\times 10^{{-6}}$\n"
        f"paper p. 3 nominal: $S_{{\\mathrm{{CH}}}} = +{s_doc:.2f}\\times 10^{{-6}}$ ($95\\%$)",
        xy=(eta_mean, 0.5 * (s_opt + s_doc)), xytext=(65.95, 1.98),
        fontsize=9.3, color=INK,
        arrowprops=dict(arrowstyle="->", color=INK, lw=0.9, shrinkA=3, shrinkB=6),
        path_effects=halo(),
    )

    ax_c.text(75.85, 0.12, r"$S_{\mathrm{CH}} > 0$ (violation)", fontsize=8.8, color=SLATE, ha="right", path_effects=halo())
    ax_c.text(75.85, -0.24, r"$S_{\mathrm{CH}} \leq 0$", fontsize=8.8, color=MUTE, ha="right", path_effects=halo())
    ax_c.text(75.15, -1.25, "p. 4\n" + r"$\eta_A,\eta_B$", fontsize=8.8, color=SLATE, ha="center", va="center")

    ax_c.set_xlim(65.5, 76.0)
    ax_c.set_ylim(-1.48, 3.72)
    ax_c.set_xlabel(r"symmetric system efficiency $\eta$ (%)", fontsize=11, labelpad=5)
    ax_c.set_ylabel(r"maximum CH value $\max S_{\mathrm{CH}}$ ($\times 10^{-6}$ per trial, $N=5\times 10^{-4}$)", fontsize=11)
    ax_c.legend(loc="upper left", bbox_to_anchor=(0.06, 0.965), fontsize=9.4, handlelength=2.2)

    # Calm, scholarly house header & frameless legend row
    fig.text(
        0.072, 0.955,
        "NIST 2015 loophole-free Bell test: Christensen Appendix A replay vs. nominal settings",
        ha="left", va="top", fontsize=13.2, color=INK,
    )
    fig.text(
        0.072, 0.916,
        "Shalm et al., Phys. Rev. Lett. 115, 250402 (2015), pp. 3–4;   B. G. Christensen, PhD thesis (UIUC, 2016), App. A, pp. 76–78",
        ha="left", va="top", fontsize=9.6, color=SLATE,
    )

    handles_a, labels_a = ax_a.get_legend_handles_labels()
    fig.legend(
        handles_a, labels_a,
        loc="upper left", bbox_to_anchor=(0.066, 0.884),
        ncol=3, frameon=False, fontsize=9.2, handletextpad=0.45, columnspacing=1.4,
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

    replay = load_replay_module()
    frozen = replay.parse_criterion(CRITERION_MD.read_text(encoding="utf-8"))
    archived = json.loads(ARCHIVED_JSON.read_text(encoding="utf-8"))
    curves = compute_plot_data(replay, frozen, archived)
    render_figure(archived, curves, args.out.resolve(), args.dpi)
    print(f"Wrote {args.out} ({args.out.stat().st_size / 1024:.1f} KB)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
