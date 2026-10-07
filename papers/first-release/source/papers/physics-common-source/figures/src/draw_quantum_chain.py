#!/usr/bin/env python3
"""Structural diagram of Theorems 6.7-6.13; no simulated or experimental data.

Top row: the original action runs to the full-field response (Theorems
6.7-6.9); the middle row ends at the current of Example 1.1 (Theorem 6.10);
the bottom row is the return through the mother action's H289, the complete
half-axis and the static pole (Theorems 6.11-6.13), with a vermilion loop
back to the original field. --lang zh (default) writes the Chinese figure;
--lang en writes the -en set and receipt. Visual language: house_style.py.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch, FancyBboxPatch

ROOT = Path(__file__).resolve().parents[1]
SOURCE = "59409a512c435cad5c5113fdedc91a451af88883"
NAME = "fig6-quantum-construction"
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / 'shared' / 'figure-style'))
from house_style import INK, SLATE, MUTE, HAIR, DEEP, VERMILION, WASH, install

STRINGS = {
    "zh": dict(
        s1="原作用 (3.1)", s1a=r"$\psi$、$\chi$ 分别变分", s1b="四部门 Legendre 图",
        s2="共同量子 Hamiltonian", s2a="61 对 CCR · 504 模 CAR", s2b=r"$H=H_0+Y$，100 维配置",
        s2c=r"耦合 $4W(q)$，$W\geq1$ 源生",
        s3="固定 $R$ 与同一准备", s3a=r"$R=E_{\rm tail}-C_{\rm src}$", s3b=r"同一点 $x_\varepsilon$：11 个字段",
        s3c="近谱与全 Y 截断残差 → 0",
        s4="真变场响应", s4a="289 场向量 · 36 曲率读数", s4b="0、1、2 阶 jet：截断 → 未截",
        s4c="测度与分级投影随场移动",
        t1="定理 6.7", t2="定理 6.8", t3="定理 6.9",
        cur="同一电流的完整量子读数（定理 6.10）",
        cura=r"$P(k)\,Q_a=J_{\rm sp}(k,a)+J_{\rm pair}(k,a)$",
        curb="双传播子响应 = 各通道之和，由同一准备读出",
        reads="同一准备读出",
        fin="§6.3–§6.5 变分 = 8 维期望", fin2="= 256 维 Fock 单粒子元",
        n1=r"单粒子扇区：$J_{\rm pair}=0$",
        b11="定理 6.11", b11a=r"母作用二阶变分 = 同一个 $H_{289}$", b11b="3071 项字典",
        b12="定理 6.12", b12a="五因子电流经完整正半轴", b12b="源生双侧逆回到 289 场方向", b12c=r"谱在 $\operatorname{Re}\lambda=0$",
        b13="定理 6.13", b13a=r"静态留数 $-\kappa^2\varphi\to\rho_{\rm st}(J(0))$",
        b13b=r"$\mathfrak{w}=-c_{114}$", b13c=r"$H\varphi=w_{\rm win}\Leftrightarrow$ 零方向共源为零",
        samecur="同一电流", sameh=r"同一 $H_{289}$", back="回到原场",
        foot="完整证明：补充材料 S1–S8；图中没有外供的耦合、态、余项或反馈",
    ),
    "en": dict(
        s1="original action (3.1)", s1a=r"$\psi$ and $\chi$ varied separately", s1b="four-sector Legendre map",
        s2="common quantum Hamiltonian", s2a="61 CCR pairs · 504-mode CAR", s2b=r"$H=H_0+Y$ on 100 configurations",
        s2c=r"coupling $4W(q)$, $W\geq1$ generated",
        s3="fixed $R$ and one preparation", s3a=r"$R=E_{\rm tail}-C_{\rm src}$", s3b=r"one point $x_\varepsilon$: 11 fields",
        s3c="near-spectral and full-Y residuals → 0",
        s4="genuinely varying field", s4a="289-field vector · 36 curvature readers", s4b="0-, 1-, 2-jets: cut → uncut",
        s4c="measure and graded projections move",
        t1="Theorem 6.7", t2="Theorem 6.8", t3="Theorem 6.9",
        cur="The complete quantum reading of the same current (Theorem 6.10)",
        cura=r"$P(k)\,Q_a=J_{\rm sp}(k,a)+J_{\rm pair}(k,a)$",
        curb="two-propagator response = sum of channels, read by the same preparation",
        reads="read by the same preparation",
        fin="§6.3–§6.5: variation = 8-dim expectation", fin2="= 256-dim Fock one-particle element",
        n1=r"one-particle sector: $J_{\rm pair}=0$",
        b11="Theorem 6.11", b11a=r"second variation = the same $H_{289}$", b11b="3071-term dictionary",
        b12="Theorem 6.12", b12a="five-factor current, complete half-axis", b12b="source two-sided inverses, 289 directions", b12c=r"spectrum on $\operatorname{Re}\lambda=0$",
        b13="Theorem 6.13", b13a=r"static residue $-\kappa^2\varphi\to\rho_{\rm st}(J(0))$",
        b13b=r"$\mathfrak{w}=-c_{114}$", b13c=r"$H\varphi=w_{\rm win}\Leftrightarrow$ null cosources vanish",
        samecur="the same current", sameh=r"the same $H_{289}$", back="back to the original field",
        foot="Complete proofs: Supplement S1–S8; no coupling, state, remainder or feedback is supplied",
    ),
}


def draw(out: Path, dpi: int, lang: str = "zh"):
    install("physics-quantum-chain-20261004", lang)
    s = STRINGS[lang]
    en = lang == "en"
    name = NAME + ("-en" if en else "")
    fig, ax = plt.subplots(figsize=(11.8, 9.6))
    fig.subplots_adjust(left=0, right=1, top=1, bottom=0)
    ax.set(xlim=(0, 1), ylim=(0, 1))
    ax.axis("off")
    labels = []
    box_patches = []
    arrow_segments = []
    owned = {}

    def label(x, y, value, size=14, color=INK, weight="normal", ha="center", owner=None):
        item = ax.text(x, y, value, ha=ha, va="center", fontsize=size, color=color, fontweight=weight)
        labels.append(item)
        if owner is not None:
            owned[item] = owner
        return item

    def box(x, y, w, h, fill="white", edge=HAIR, lw=.9):
        p = FancyBboxPatch((x, y), w, h, boxstyle="round,pad=0.006,rounding_size=0.008",
                           facecolor=fill, edgecolor=edge, linewidth=lw)
        ax.add_patch(p)
        box_patches.append(p)
        return len(box_patches) - 1

    def arrow(start, end, color=SLATE, lw=1.2, style="-|>"):
        ax.add_patch(FancyArrowPatch(start, end, arrowstyle=style, mutation_scale=13,
                                     linewidth=lw, color=color))
        arrow_segments.append((start, end))

    # Top row: action -> Hamiltonian -> R and preparation -> response.
    # Four-line boxes; every line sits inside the frame with margin.
    xs, w, y0, h = [.05, .29, .53, .77], .22, .72, .25
    big, small = (9.5, 8.6) if en else (13.5, 10.5)
    for i, (x, key) in enumerate(zip(xs, ["s1", "s2", "s3", "s4"])):
        bi = box(x, y0, w, h, edge=DEEP if i else HAIR, lw=1.0)
        cx = x + w / 2
        label(cx, y0 + h - .05, s[key], big, DEEP if i else INK, "bold" if i else "normal", owner=bi)
        subs = [k for k in (key + "a", key + "b", key + "c") if k in s]
        for j, k in enumerate(subs):
            label(cx, y0 + h - .105 - j * .058, s[k],
                  small if "$" not in s[k] or en else small + .5,
                  INK if j == 0 else SLATE, owner=bi)
    for i, t in enumerate(["t1", "t2", "t3"]):
        x0 = xs[i] + w + .004
        x1 = xs[i + 1] - .004
        arrow((x0, y0 + h / 2), (x1, y0 + h / 2), DEEP, 1.3)
        label(xs[i + 1] + w / 2, y0 + h + .017, s[t], 9.5 if en else 10, DEEP)

    # Middle row: the same current (vermilion) and the one-particle sector.
    cy, ch = .46, .19
    curbox = box(.31, cy, .68, ch, fill=WASH, edge=VERMILION, lw=1.3)
    label(.65, cy + ch - .042, s["cur"], 10.5 if en else 13.5, VERMILION, "bold", owner=curbox)
    label(.65, cy + ch / 2 - .005, s["cura"], 14 if en else 16, INK, owner=curbox)
    label(.65, cy + .04, s["curb"], 9 if en else 11.5, SLATE, owner=curbox)
    arrow((xs[3] + w / 2, y0 - .006), (xs[3] + w / 2, cy + ch + .006), VERMILION, 1.4)
    arrow((xs[2] + w / 2, y0 - .006), (xs[2] + w / 2 - .02, cy + ch + .006), DEEP, 1.1)
    label(xs[2] + w / 2 + .012, (y0 + cy + ch) / 2, s["reads"], 8.5 if en else 10.5, DEEP, ha="left")

    finbox = box(.05, cy, .22, ch, edge=HAIR)
    label(.16, cy + ch - .04, s["fin"], 8 if en else 10, INK, owner=finbox)
    label(.16, cy + ch - .09, s["fin2"], 8 if en else 10, INK, owner=finbox)
    label(.16, cy + .042, s["n1"], 9.5 if en else 11.5, VERMILION, owner=finbox)
    arrow((.306, cy + .05), (.274, cy + .05), VERMILION, 1.1)

    # Bottom row: the return — mother-action H289, half-axis, static pole.
    by, bh = .135, .24
    bxs, bws = [.05, .30, .68], [.19, .35, .31]
    big2, small2 = (9.5, 8.2) if en else (13, 10)
    for x, bw, key in zip(bxs, bws, ["b11", "b12", "b13"]):
        bi = box(x, by, bw, bh, edge=HAIR)
        cx = x + bw / 2
        label(cx, by + bh - .04, s[key], big2, INK, "bold", owner=bi)
        subs = [k for k in (key + "a", key + "b", key + "c") if k in s]
        for j, k in enumerate(subs):
            label(cx, by + bh - .095 - j * .055, s[k], small2, INK if j == 0 else SLATE, owner=bi)
    # 6.10 -> 6.12 (vermilion: the same current returns to the field).
    midx = bxs[1] + bws[1] / 2
    arrow((midx, cy - .006), (midx, by + bh + .006), VERMILION, 1.4)
    label(midx + .012, (cy + by + bh) / 2, s["samecur"], 8.5 if en else 10.5, VERMILION, ha="left")
    # 6.11 -> 6.12 (the same H289): routed through the free band above the
    # bottom row so the label has whitespace on both sides.
    hy = by + bh + .045
    arrow((bxs[0] + bws[0] / 2, by + bh + .004), (bxs[0] + bws[0] / 2, hy), DEEP, 1.1, style="-")
    arrow((bxs[0] + bws[0] / 2, hy), (bxs[1] + .06, hy), DEEP, 1.1, style="-")
    arrow((bxs[1] + .06, hy), (bxs[1] + .06, by + bh + .004), DEEP, 1.1)
    label((bxs[0] + bws[0] / 2 + bxs[1] + .06) / 2, hy + .022, s["sameh"], 8 if en else 9.5, DEEP)
    arrow((bxs[1] + bws[1] + .004, by + bh / 2), (bxs[2] - .004, by + bh / 2), DEEP, 1.2)

    # Vermilion return loop: 6.13 -> down -> left along the bottom -> up the
    # left margin -> into the original-action box's left edge.
    lx = .022
    rx = bxs[2] + bws[2] / 2
    arrow((rx, by - .006), (rx, .07), VERMILION, 1.4, style="-")
    arrow((rx, .07), (lx, .07), VERMILION, 1.4, style="-")
    arrow((lx, .07), (lx, y0 + h / 2), VERMILION, 1.4, style="-")
    arrow((lx, y0 + h / 2), (xs[0] - .008, y0 + h / 2), VERMILION, 1.4)
    label(.5, .098, s["back"], 9 if en else 11, VERMILION)

    label(.5, .024, s["foot"], 8 if en else 10.5, MUTE)

    fig.set_size_inches(*(fig.get_size_inches() * .85))
    fig.canvas.draw()
    renderer = fig.canvas.get_renderer()
    bounds = {t: t.get_window_extent(renderer) for t in labels}
    assert all(fig.bbox.contains(b.x0, b.y0) and fig.bbox.contains(b.x1, b.y1)
               for b in bounds.values()), "A label exceeds the canvas"
    overlaps = [(labels[i].get_text(), labels[j].get_text()) for i in range(len(labels))
                for j in range(i) if bounds[labels[i]].overlaps(bounds[labels[j]])]
    assert not overlaps, overlaps
    # Owned labels must sit fully inside their box's extent, inset by a margin.
    box_ext = [p.get_window_extent(renderer) for p in box_patches]
    for t, p in owned.items():
        ext = box_ext[p]
        b = bounds[t]
        margin = 4.0
        assert (b.x0 > ext.x0 + margin and b.x1 < ext.x1 - margin
                and b.y0 > ext.y0 + margin and b.y1 < ext.y1 - margin), (
            f"label {t.get_text()!r} not inside its box")
    # Unowned labels must not cross a box's frame or any arrow path.
    def seg_hits_rect(p, q, r):
        x0, y0 = min(p[0], q[0]), min(p[1], q[1])
        x1, y1 = max(p[0], q[0]), max(p[1], q[1])
        if x1 < r.x0 or x0 > r.x1 or y1 < r.y0 or y0 > r.y1:
            return False
        # endpoint inside or the segment crosses an edge
        if r.contains(p[0], p[1]) or r.contains(q[0], q[1]):
            return True
        edges = [((r.x0, r.y0), (r.x1, r.y0)), ((r.x1, r.y0), (r.x1, r.y1)),
                 ((r.x1, r.y1), (r.x0, r.y1)), ((r.x0, r.y1), (r.x0, r.y0))]
        def cross(a, b, c, d):
            def ccw(u, v, w):
                return (w[1] - u[1]) * (v[0] - u[0]) > (v[1] - u[1]) * (w[0] - u[0])
            return ccw(a, c, d) != ccw(b, c, d) and ccw(a, b, c) != ccw(a, b, d)
        return any(cross(p, q, e0, e1) for e0, e1 in edges)
    arrow_disp = [(ax.transData.transform(p), ax.transData.transform(q))
                  for p, q in arrow_segments]
    for t in labels:
        if t in owned:
            continue
        b = bounds[t]
        for i, ext in enumerate(box_ext):
            inside = ext.fully_contains(b.x0, b.y0) and ext.fully_contains(b.x1, b.y1)
            assert not (b.overlaps(ext) and not inside), (
                f"label {t.get_text()!r} crosses the frame of box {i}")
        for p, q in arrow_disp:
            assert not seg_hits_rect(p, q, b), f"label {t.get_text()!r} hits an arrow path"
    out.mkdir(parents=True, exist_ok=True)
    stamp = datetime(2026, 10, 4, tzinfo=timezone.utc)
    for ext in ["svg", "png", "pdf"]:
        path = out / (name + ("-r10.pdf" if ext == "pdf" else "." + ext))
        meta = {"Title": "Complete quantum construction and original-field return"}
        if ext == "pdf":
            meta.update(CreationDate=stamp, ModDate=stamp)
        elif ext == "svg":
            meta.update(Date="2026-10-04")
        fig.savefig(path, dpi=dpi, metadata=meta)
        if ext == "svg":
            path.write_text("\n".join(line.rstrip() for line in path.read_text().splitlines()) + "\n")
    plt.close(fig)
    report = {
        "status": "passed", "source_revision": SOURCE,
        "scope": "Structural diagram; label containment in boxes, no text on frames or arrow paths, pairwise text-overlap checks",
        "labels_checked": len(labels), "dpi": dpi,
        "source_mouths": ["CanonicalPreparationActionCoreDecomposition.physical_action_decomposition",
                          "CanonicalPreparationSourceRemainder.sourceRemainder_selfAdjoint",
                          "CanonicalPreparationSourcePreparedState.sourcePreparation_exists",
                          "CanonicalPreparationYukawaObservedLimit.observed_second_exchange",
                          "CanonicalPreparationElectricPreparedWard.preparedChannels_same_state",
                          "CanonicalSourcePropagationOriginalHessianReturn.nativeActionFourierHessian_original",
                          "CanonicalPreparationSourceAnalyticRegularPoint.sourceRegularDomain_nonempty",
                          "CanonicalPreparationSourceAxisCompatibility.actualAxisField_compatibility"],
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "artifacts": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sorted(out / f for f in [name + "-r10.pdf", name + ".png", name + ".svg"])},
    }
    (out / ("quantum-chain-figure-checks" + ("-en" if en else "") + ".json")).write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "labels_checked")}, ensure_ascii=False))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "vector")
    parser.add_argument("--dpi", type=int, default=240)
    parser.add_argument("--lang", choices=["zh", "en"], default="zh")
    args = parser.parse_args()
    draw(args.output, args.dpi, args.lang)
