#!/usr/bin/env python3
"""Structural diagram of Theorem 8.4; no simulated or experimental data.

--lang zh (default) writes the Chinese figure; --lang en writes the English
set with -en file names and a -en receipt. Visual language: house_style.py.
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
from matplotlib import font_manager
from matplotlib.patches import Ellipse, FancyArrowPatch, FancyBboxPatch

ROOT = Path(__file__).resolve().parents[1]
SOURCE = "cde4b910929d9bc57554aa56f6ade116bc3b8675"
NAME = "fig5-fixed-mother-realization"
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / 'shared' / 'figure-style'))
from house_style import INK, SLATE, MUTE, HAIR, DEEP, VERMILION, WASH, install

STRINGS = {
    "zh": dict(
        title="同一来源，完整形成与恢复",
        subtitle="定理 8.4：世界、完整查询与演化过程",
        root=r"原发生源 $S_\star$", root_sub="原访问与有限求值器",
        image=r"实际程序像 $\mathcal{R}_r$", image_sub="有限地址表 · 原母程序",
        material=r"完成材料 $m\in\widehat{\mathcal{R}_r}$", material_sub="逐输入一致完成",
        formed_from="由同一份材料形成",
        formed=r"形成的完整过程 $P_m$", formed_sub="全部状态、节点与依赖查询",
        original=r"任意原准入过程 $P$", original_sub="原接口与原字段",
        restriction="完整限制",
        formed_result="形成侧的实际结果", formed_result_sub="完整查询结果与下一状态",
        original_result="原运行的实际结果", original_result_sub="同一整账与同一后继",
        step="查询 / 运行步", interchange="恢复交换", depth="全部有限深度",
        joint=r"联合材料：限制 $\circ$ 合并 $=$ 恒等（全部双亲材料空间）",
        commute="交换",
        consumers="原物理运行",
        consumers_sub="既定激活与整条法则 · 运行状态 16 → 17 · 全部有限深度历史",
    ),
    "en": dict(
        title="One source: complete formation and recovery",
        subtitle="Theorem 8.4: worlds, complete inquiries and evolving processes",
        root=r"original generative root $S_\star$", root_sub="original visits and the finite evaluator",
        image=r"actual program image $\mathcal{R}_r$", image_sub="finite address table · original source program",
        material=r"completed material $m\in\widehat{\mathcal{R}_r}$", material_sub="pointwise consistent completion",
        formed_from="formed from the same material",
        formed=r"the formed complete process $P_m$", formed_sub="all states, nodes and dependent inquiries",
        original=r"any originally admitted process $P$", original_sub="original interface and original fields",
        restriction="complete restriction",
        formed_result="actual result on the formed side", formed_result_sub="complete inquiry results and the next state",
        original_result="actual result of the original run", original_result_sub="the same full ledger and the same successor",
        step="query / run step", interchange="recovery interchange", depth="every finite depth",
        joint=r"joint material: restrict $\circ$ combine $=$ identity (all parent material spaces)",
        commute="commutes",
        consumers="The original physical run",
        consumers_sub="established activation and the whole law · run states 16 → 17 · all finite-depth histories",
    ),
}


def draw(out: Path, dpi: int, lang: str = "zh"):
    install("physics-fixed-mother-20260930", lang)
    s = STRINGS[lang]
    en = lang == "en"
    name = NAME + ("-en" if en else "")
    fig, ax = plt.subplots(figsize=(11.8, 8.4))
    fig.subplots_adjust(left=0, right=1, top=1, bottom=0)
    ax.set(xlim=(0, 1), ylim=(0, 1))
    ax.axis("off")
    labels = []

    def label(x, y, value, size=14, color=INK, weight="normal"):
        item = ax.text(x, y, value, ha="center", va="center",
                       fontsize=size, color=color, fontweight=weight)
        labels.append(item)
        return item

    def box(x, y, w, h, fill="white", edge=HAIR):
        ax.add_patch(FancyBboxPatch((x, y), w, h,
                     boxstyle="round,pad=0.006,rounding_size=0.008",
                     facecolor=fill, edgecolor=edge, linewidth=.9))

    def arrow(start, end, color=SLATE, lw=1.2):
        ax.add_patch(FancyArrowPatch(start, end, arrowstyle="-|>",
                     mutation_scale=13, linewidth=lw, color=color))

    # The generation chain is typographic: three stations on one baseline.
    for x, key in [(.175, "root"), (.5, "image"), (.825, "material")]:
        label(x, .925, s[key], 12 if en else 15.5)
        label(x, .878, s[key + "_sub"], 9 if en else 11.5, SLATE)
    arrow((.312, .925), (.36, .925))
    arrow((.645, .925), (.69, .925))
    # This path binds the completed witness to the actual process factory.
    ax.plot([.825, .825, .235], [.848, .80, .80], color=DEEP, lw=1.3)
    arrow((.235, .80), (.235, .742), DEEP, 1.3)
    tag = label(.53, .80, s["formed_from"], 11.5 if en else 12.5, DEEP)
    tag.set_bbox(dict(facecolor="white", edgecolor="none", pad=3))

    # The commutative square: formed side (left) against the original (right).
    box(.06, .59, .35, .14)
    box(.59, .59, .35, .14, fill=WASH, edge=WASH)
    label(.235, .678, s["formed"], 13 if en else 16.5, DEEP)
    label(.235, .630, s["formed_sub"], 9.5 if en else 12, SLATE)
    label(.765, .678, s["original"], 13 if en else 16.5)
    label(.765, .630, s["original_sub"], 9.5 if en else 12, SLATE)
    arrow((.425, .66), (.575, .66))
    label(.5, .703, s["restriction"], 10 if en else 12.5, SLATE)
    label(.5, .615, r"$\mathrm{restrict}(P_m)=P$", 12)

    box(.06, .305, .35, .135)
    box(.59, .305, .35, .135, fill=WASH, edge=WASH)
    label(.235, .388, s["formed_result"], 12.5 if en else 15.5, DEEP)
    label(.235, .342, s["formed_result_sub"], 9.5 if en else 12, SLATE)
    label(.765, .388, s["original_result"], 12.5 if en else 15.5)
    label(.765, .342, s["original_result_sub"], 9.5 if en else 12, SLATE)
    arrow((.235, .575), (.235, .455))
    arrow((.765, .575), (.765, .455))
    # Opaque label backgrounds keep the vertical arrows clear of their text.
    for x in (.235, .765):
        label(x, .515, s["step"], 11 if en else 12, SLATE).set_bbox(
            dict(facecolor="white", edgecolor="none", pad=3))
    arrow((.425, .372), (.575, .372))
    label(.5, .415, s["interchange"], 10 if en else 12.5, SLATE)
    label(.5, .327, s["depth"], 10.5 if en else 11.5, MUTE)
    ax.add_patch(Ellipse((.5, .515), .08, .08 * 11.8 / 8.4, facecolor="white", edgecolor=VERMILION, linewidth=1.4))
    label(.5, .515, s["commute"], 9 if en else 13, VERMILION)

    label(.5, .245, s["joint"], 10.5 if en else 12, SLATE)
    ax.plot([.06, .94], [.19, .19], color=HAIR, lw=.8)
    label(.5, .135, s["consumers"], 13 if en else 14.5, INK)
    label(.5, .085, s["consumers_sub"], 11 if en else 12.5, SLATE)

    # Print scaling as in draw_figures (structural plates use .85): larger printed type.
    fig.set_size_inches(*(fig.get_size_inches() * .85))
    fig.canvas.draw()
    renderer = fig.canvas.get_renderer()
    bounds = [t.get_window_extent(renderer) for t in labels]
    assert all(fig.bbox.contains(b.x0, b.y0) and fig.bbox.contains(b.x1, b.y1)
               for b in bounds), "A label exceeds the canvas"
    assert not [(i, j) for i, a in enumerate(bounds) for j, b in enumerate(bounds[:i])
                if a.overlaps(b)], "Text labels overlap"
    out.mkdir(parents=True, exist_ok=True)
    stamp = datetime(2026, 9, 30, tzinfo=timezone.utc)
    for ext in ["svg", "png", "pdf"]:
        path = out / (name + ("-r10.pdf" if ext == "pdf" else "." + ext))
        meta = {"Title": "Fixed-mother complete realization"}
        if ext == "pdf":
            meta.update(CreationDate=stamp, ModDate=stamp)
        elif ext == "svg":
            meta.update(Date="2026-09-30")
        fig.savefig(path, dpi=dpi, metadata=meta)
        if ext == "svg":
            path.write_text("\n".join(line.rstrip() for line in path.read_text().splitlines()) + "\n")
    plt.close(fig)
    report = {
        "status": "passed", "source_revision": SOURCE,
        "scope": "Structural diagram; label containment and pairwise text-overlap checks only",
        "labels_checked": len(labels), "dpi": dpi,
        "source_mouth": "FixedMotherRealization.root_admission_fixed_mother_complete_realization",
        "generator_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "artifacts": {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sorted(out / f for f in [name + "-r10.pdf", name + ".png", name + ".svg"])},
    }
    (out / ("fixed-mother-figure-checks" + ("-en" if en else "") + ".json")).write_text(
        json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps(report, ensure_ascii=False))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "vector")
    parser.add_argument("--dpi", type=int, default=240)
    parser.add_argument("--lang", choices=["zh", "en"], default="zh")
    args = parser.parse_args()
    draw(args.output, args.dpi, args.lang)
