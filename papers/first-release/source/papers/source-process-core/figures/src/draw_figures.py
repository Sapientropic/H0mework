#!/usr/bin/env python3
"""Reproducible figures for source-process-core.

Usage: python3 figures/src/draw_figures.py [--output-dir DIR] [--dpi 240] [--lang {zh,en}]
Requires matplotlib 3.8+, numpy, TeX Live's Latin Modern (kpsewhich) and
Noto Serif CJK SC. --lang en writes the -en set and its own receipts
(manifest-en.json, render-info-en.json) without touching the Chinese files.

Visual language: shared/figure-style (house_style.py). There is no title
inside a figure; the manuscript caption carries title and reading guide.
VERMILION marks the single object each figure asks the reader to see:
  figure1  the same environment at the first and last ticks and the clash it forces
  figure2  the revised same obligation, where the paper's answer lands
  figure3  the first tick that the start-advancing map deletes
  figure4  the source witness w that every extension keeps
  figure5  the second tick answered directly by the same new root
  figure6  the new responsibility born from the next question
  supp1    the sum of the two certificates, whose relation image is w
  supp2    the payment stage that must decrease strictly
Dashed grey frames mark data supplied as input rather than generated.

All geometry is authored here. Numerical readings are the exact values of
manuscript Examples 4.1/4.2 and Table 3, never fitted or illustrative samples.
Layout runs in a 12-unit-wide coordinate frame; the canvas is 12*scale inches
(PRINT_SCALE for plots, 0.85 for plates) so type prints at ~7 pt or more at
the 164 mm text width.

Editorial corrections, not claims of source-code verification:
 * r_b^s deletes the LAST stock of a fixed-start prefix;
 * d_b^s deletes the FIRST stock and changes the start from s to sigma(s);
 * the Section 8 continuation receives a typed revision as additional input.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Rectangle, FancyBboxPatch, FancyArrowPatch
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / "shared" / "figure-style"))
from house_style import (INK, SLATE, MUTE, HAIR, DEEP, VERMILION, GOLD, WASH,
                         PRINT_SCALE, install)

PLATE = .85
WHITE = "#FFFFFF"


def canvas(height, scale):
    fig = plt.figure(figsize=(12*scale, height*scale))
    ax = fig.add_axes([0, 0, 1, 1])
    ax.set_xlim(0, 12)
    ax.set_ylim(0, height)
    ax.axis("off")
    return fig, ax


def txt(ax, x, y, s, fs=12, color=INK, ha="left", va="center", weight="normal", **kw):
    return ax.text(x, y, s, fontsize=fs, color=color, ha=ha, va=va,
                   fontweight=weight, linespacing=1.4, **kw)


def rect(ax, x, y, w, h, fc=WHITE, ec=HAIR, lw=.9, radius=0, ls="-", **kw):
    if radius:
        p = FancyBboxPatch((x, y), w, h, boxstyle=f"round,pad=0,rounding_size={radius}",
                           facecolor=fc, edgecolor=ec, linewidth=lw, linestyle=ls, **kw)
    else:
        p = Rectangle((x, y), w, h, facecolor=fc, edgecolor=ec, linewidth=lw, linestyle=ls, **kw)
    ax.add_patch(p)
    return p


def line(ax, p, q, color=HAIR, lw=.9, ls="-", z=1):
    ax.plot([p[0], q[0]], [p[1], q[1]], color=color, lw=lw, ls=ls, zorder=z,
            solid_capstyle="butt")


def arrow(ax, p, q, label=None, color=INK, lw=1.2, label_pos=None, fs=11, ha="center", z=2):
    ax.add_patch(FancyArrowPatch(p, q, arrowstyle="-|>", mutation_scale=10,
                                 color=color, linewidth=lw, shrinkA=0, shrinkB=0, zorder=z))
    if label:
        if label_pos is None:
            label_pos = ((p[0]+q[0])/2, (p[1]+q[1])/2+.18)
        txt(ax, *label_pos, label, fs=fs, color=color, ha=ha,
            bbox={"facecolor": WHITE, "edgecolor": "none", "pad": .8}, zorder=z+1)


def dot(ax, x, y, color=DEEP, hollow=False, s=55, z=5):
    ax.scatter([x], [y], s=s, marker="o", facecolor=WHITE if hollow else color,
               edgecolor=color, linewidth=1.4, zorder=z)


def head(ax, x, y, letter, title, fs=11.5, color=SLATE):
    """Panel heading: a small letter and a short phrase, never a figure title."""
    txt(ax, x, y, letter, fs=fs-1, color=color, weight="bold")
    txt(ax, x+.34, y, title, fs=fs, color=color)


def stock(ax, x, y, items, cell=.65, h=.52, fs=14, edge=DEEP, fill=WHITE, faded=(), cut=()):
    for k, s in enumerate(items):
        if k in cut:
            rect(ax, x+k*cell, y, cell, h, fc=WHITE, ec=VERMILION, lw=1.1, ls=(0, (3, 2)))
        else:
            rect(ax, x+k*cell, y, cell, h, fc=fill, ec=HAIR if k in faded else edge, lw=.9)
        txt(ax, x+(k+.5)*cell, y+h/2, s, fs=fs,
            color=MUTE if (k in faded or k in cut) else INK, ha="center")


MANIFEST = []


def save(fig, out, stem, ident, title, caption, claim, kind, dpi, lang="zh"):
    stem = stem + ("-en" if lang == "en" else "")
    files = {}
    for ext in ("svg", "pdf", "png"):
        p = out / f"{stem}.{ext}"
        kw = {"dpi": dpi} if ext == "png" else {}
        if ext == "svg":
            kw["metadata"] = {"Date": None}
        if ext == "pdf":
            kw["metadata"] = {"CreationDate": None, "ModDate": None}
        temporary = p.with_name(p.stem + ".rendering" + p.suffix)
        fig.savefig(temporary, **kw)
        if ext == "svg":
            temporary.write_text("\n".join(l.rstrip() for l in temporary.read_text().splitlines()) + "\n")
        os.replace(temporary, p)
        files[ext] = f"vector/{p.name}"
    MANIFEST.append(dict(id=ident, stem=stem, title=title, caption=caption,
                         claim=claim, kind=kind, role=kind, **files))
    plt.close(fig)


FIG1 = {
 'zh': dict(
    label_a="先看两段各自成立",
    tick=lambda i: f"第 {i} 拍",
    reading="读数",
    word0=r"词 $0$：$0\to0$",
    wordx=r"词 $x$：$0\to1$",
    shared="共享读数 0",
    same_env=r"首末两拍是同一环境 $x\mapsto1$",
    label_b="再要求同一个见证",
    must=r"共同源词 $w$ 必须满足",
    conflict="同一求值函数，两个值",
    first="首拍",
    last="末拍",
    even_if=r"即使中间还有 $\mathrm{ev}_{0}(w)=0$，",
    contradict="首末两项已经矛盾。",
    mtit="局部见证不能拼接成共同源历史",
    mcap="精确数值图（例4.1、表1）。三拍环境为x↦1、x↦0、x↦1。零词实现第一段的0→0，变量词实现第二段的0→1；两词在中间环境同读0。若要求一枚共同源词，其首末读数由同一个求值函数ev₁给出，却分别须为0与1，故不存在这样的词。实线标出被采用的局部段，虚线和空心点补足候选词的其余真实读数；上方括线仅表示首末环境相同。",
    mclaim="局部段的读数相合不足以保证存在贯穿各段的共同源词。"),
 'en': dict(
    label_a="First, each segment holds on its own",
    tick=lambda i: f"tick {i}",
    reading="reading",
    word0=r"word $0$: $0\to0$",
    wordx=r"word $x$: $0\to1$",
    shared="shared reading 0",
    same_env=r"first and last ticks: one environment $x\mapsto1$",
    label_b="Then demand one and the same witness",
    must=r"a common source word $w$ must satisfy",
    conflict="one evaluation function, two values",
    first="first tick",
    last="last tick",
    even_if=r"even with $\mathrm{ev}_{0}(w)=0$ in between,",
    contradict="the first and last already contradict.",
    mtit="Local witnesses cannot be spliced into a common source history",
    mcap="Exact numerical figure (Example 4.1, Table 1). The three-tick environments are x↦1, x↦0, x↦1. The zero word realizes 0→0 on the first segment, the variable word realizes 0→1 on the second; both read 0 in the middle environment. A common source word would have its first and last readings given by one and the same evaluation function ev₁, yet they would have to be 0 and 1, so no such word exists. Solid lines mark the adopted local segments; dashed lines and hollow dots supply the candidate's remaining true readings; the upper bracket only marks that the first and last environments are the same.",
    mclaim="Agreement of readings on local segments does not guarantee a common source word running through all segments."),
}


def figure1(out, dpi, lang="zh"):
    s = FIG1[lang]; en = lang == "en"
    H = 5.8
    fig, ax = canvas(H, PRINT_SCALE)
    head(ax, .48, 5.45, "A", s["label_a"])
    xs = [1.22, 3.65, 6.08]
    y0, y1 = 1.95, 3.5
    for i, x in enumerate(xs):
        line(ax, (x, 1.5), (x, 3.9), HAIR)
        txt(ax, x, 1.1, s["tick"](i), ha="center", fs=11.5, color=SLATE)
        txt(ax, x, .62, [r"$x\mapsto1$", r"$x\mapsto0$", r"$x\mapsto1$"][i], ha="center", fs=14)
    for val, y in [(0, y0), (1, y1)]:
        line(ax, (.95, y), (6.4, y), HAIR)
        txt(ax, .72, y, str(val), fs=13, ha="center")
    txt(ax, .72, 4.0, s["reading"], fs=10.5, color=SLATE, ha="center")
    # Exact candidate readings; only the locally adopted segment is solid.
    line(ax, (xs[0], y1), (xs[1], y0), GOLD, 1.3, (0, (3, 3)))
    line(ax, (xs[1], y0), (xs[2], y0), DEEP, 1.3, (0, (3, 3)))
    line(ax, (xs[0], y0), (xs[1], y0), DEEP, 2.6)
    line(ax, (xs[1], y0), (xs[2], y1), GOLD, 2.6)
    dot(ax, xs[0], y0, DEEP); dot(ax, xs[0], y1, GOLD, True)
    dot(ax, xs[2], y0, DEEP, True); dot(ax, xs[2], y1, GOLD)
    dot(ax, xs[1], y0, DEEP, s=85)
    dot(ax, xs[1], y0, GOLD, s=22)
    txt(ax, 2.2, 2.25, s["word0"], fs=12, color=DEEP, ha="center")
    ang = np.degrees(np.arctan2(y1-y0, xs[2]-xs[1]))
    txt(ax, 4.72, 2.98, s["wordx"], fs=12, color=GOLD, ha="center", rotation=ang,
        rotation_mode="anchor")
    txt(ax, xs[1], 1.6, s["shared"], fs=10.5, color=SLATE, ha="center",
        bbox={"facecolor": WHITE, "edgecolor": "none", "pad": .8}, zorder=4)
    # Equal environment is a bracket, not a causal arrow.
    line(ax, (xs[0], 4.05), (xs[0], 4.4), VERMILION, 1.2)
    line(ax, (xs[0], 4.4), (xs[2], 4.4), VERMILION, 1.2)
    line(ax, (xs[2], 4.05), (xs[2], 4.4), VERMILION, 1.2)
    txt(ax, xs[1], 4.72, s["same_env"], fs=11.5, color=VERMILION, ha="center")
    line(ax, (6.78, .4), (6.78, 5.45), HAIR)
    head(ax, 7.1, 5.45, "B", s["label_b"])
    txt(ax, 7.3, 4.72, s["must"], fs=12)
    rect(ax, 7.2, 2.45, 4.25, 1.85, fc=WASH, ec="none", radius=.06)
    txt(ax, 7.45, 4.0, s["conflict"], fs=10.5, color=VERMILION)
    txt(ax, 7.45, 3.4, r"$\mathrm{ev}_{1}(w)=0$", fs=19, color=VERMILION)
    txt(ax, 11.25, 3.4, s["first"], fs=11, color=SLATE, ha="right")
    txt(ax, 7.45, 2.82, r"$\mathrm{ev}_{1}(w)=1$", fs=19, color=VERMILION)
    txt(ax, 11.25, 2.82, s["last"], fs=11, color=SLATE, ha="right")
    txt(ax, 9.3, 1.85, r"$0\neq1$", fs=24, color=VERMILION, ha="center")
    txt(ax, 7.3, 1.1, s["even_if"], fs=11.5)
    txt(ax, 7.3, .62, s["contradict"], fs=11.5)
    save(fig, out, "figure1-three-tick-counterexample", "figure1",
         s["mtit"], s["mcap"], s["mclaim"], "main", dpi, lang)


FIG2 = {
 'zh': dict(
    levels=[
        dict(name="同一读数", sec="§1.1 · 例 4.1",
             kept="两个词在某个观察下取值相同；\n逐拍可查，也最弱。",
             formula=r"$\mathrm{ev}_0(0)=\mathrm{ev}_0(x)=0$",
             refs="接缝处相同的只是旧值"),
        dict(name="同一源对象", sec="§2–§4",
             kept="整段历史由同一个见证给出；\n每拍（旧值，效应）差由该拍关系解释。",
             formula=r"$\mathrm{range}(\mathrm{rel}_\rho)=\ker(\mathrm{ev}_\rho)$",
             refs="定理 3.9、4.4、4.6、4.7；命题 4.8"),
        dict(name="同一次发生", sec="§5",
             kept="两份忠实实现各自对应根的发生；\n比较由共同发生生成。",
             formula=r"$\varphi_2\circ\varphi_1^{-1}$　逐点唯一",
             refs="命题 5.2；定理 5.3"),
        dict(name="同一笔责任", sec="§6",
             kept="旧行原样保留，激活时恰添一行；\n付款使预算严格下降。",
             formula=r"$\beta_{\mathrm{target}}<\beta_{\mathrm{source}}$",
             refs="命题 6.4；定理 6.7、6.10",
             inp="一般责任输入：\n同债总律"),
        dict(name="修订后的\n同一笔责任", sec="§7–§9",
             kept="最小扩充保留旧账、事实与定理；\n新方向＝首次写入所消费的新行。",
             formula=r"$C_\eta=L_+\sqcup\{\star_\eta\}$",
             refs="定理 7.7、8.4、8.6、8.7、8.12、9.5",
             inp="修订输入：\n有类型修订\n与字段接地"),
    ],
    gaps=["读数相同，源词可以不同：没有一个词读出 0, 0, 1（例 4.1）",
          "同一源过程可有多份实现：哪个事件是哪一次发生？",
          "同一次发生写入账后：旧债由哪一行承接？",
          "旧表达无法指称已登记的需求：修订之后，还是同一笔吗？"],
    mtit="四级同一性",
    mcap="结构示意图。自下而上为四级同一性及修订后的责任：同一读数只比较取值；同一源对象要求整段历史由同一见证给出（定理3.9、4.4、4.6–4.7）；同一次发生由两份忠实实现与共同发生的对应确定（定理5.3）；同一笔责任由整账更新中承接旧行的确定行给出，源程序自生的责任逐步付款（命题6.4、定理6.7、6.10）；修订后，最小扩充把新方向送到首次写入所消费的新行，结清的回答提出下一问，并带走完整时间、全部作用者与两种库存（定理7.7、8.4、8.6–8.7、8.12、9.2–9.8）。级间文字是使下一级成为必要的具体情形；一般责任的同债总律与有类型修订标为输入。",
    mclaim="每一级比前一级多保留一样东西；级间的具体失效说明为什么需要下一级。"),
 'en': dict(
    levels=[
        dict(name="Same reading", sec="§1.1 · Example 4.1",
             kept="two words take equal values\nunder one observation; checked\ntick by tick, and the weakest.",
             formula=r"$\mathrm{ev}_0(0)=\mathrm{ev}_0(x)=0$",
             refs="only the old values agree at the junction"),
        dict(name="Same source\nobject", sec="§2–§4",
             kept="one witness gives the whole history;\neach tick's (old, effect) difference\nis explained by that tick's relations.",
             formula=r"$\mathrm{range}(\mathrm{rel}_\rho)=\ker(\mathrm{ev}_\rho)$",
             refs="Theorems 3.9, 4.4, 4.6, 4.7; Proposition 4.8"),
        dict(name="Same\noccurrence", sec="§5",
             kept="each faithful implementation matches\nthe root's occurrences; the comparison\nis generated by the common occurrence.",
             formula=r"$\varphi_2\circ\varphi_1^{-1}$, pointwise unique",
             refs="Proposition 5.2; Theorem 5.3"),
        dict(name="Same\nobligation", sec="§6",
             kept="old rows kept unchanged; exactly one\nrow added on activation; payment\nstrictly lowers the budget.",
             formula=r"$\beta_{\mathrm{target}}<\beta_{\mathrm{source}}$",
             refs="Proposition 6.4; Theorems 6.7, 6.10",
             inp="general debts:\nsame-debt\nmaster law"),
        dict(name="Same obligation\nafter revision", sec="§7–§9",
             kept="the minimal extension keeps old ledger,\nfacts and theorems; new direction =\nthe new row consumed by the first write.",
             formula=r"$C_\eta=L_+\sqcup\{\star_\eta\}$",
             refs="Theorems 7.7, 8.4, 8.6, 8.7, 8.12, 9.5",
             inp="revision input:\ntyped revision,\nfield grounding"),
    ],
    gaps=["equal readings, different source words: no word reads 0, 0, 1 (Example 4.1)",
          "one source process, several implementations: which event is which occurrence?",
          "once the occurrence writes the ledger: which row carries the old debt?",
          "the old expressions cannot denote a registered demand: after revision, is it the same obligation?"],
    mtit="Four levels of identity",
    mcap="Structural diagram. From bottom to top: the four levels of identity and the obligation after revision. Same reading compares values only; same source object requires one witness for the whole history (Theorems 3.9, 4.4, 4.6–4.7); same occurrence is fixed by the correspondence between two faithful realizations and the common occurrence (Theorem 5.3); same obligation is given by the determined row that carries an old row through a whole-ledger update, and an obligation born from a source program is paid step by step (Proposition 6.4, Theorems 6.7, 6.10); after revision, the minimal extension sends the new direction to the new row consumed by the first write, and a settled answer asks the next question, carrying the complete time, all actors and both inventories (Theorems 7.7, 8.4, 8.6–8.7, 8.12, 9.2–9.8). The text between levels is the concrete situation that makes the next level necessary; the same-debt master law for general debts and the typed revision are marked as inputs.",
    mclaim="Each level keeps one more thing than the one below; the concrete failure between levels explains why the next level is needed."),
}


def figure2(out, dpi, lang="zh"):
    s = FIG2[lang]; en = lang == "en"
    band_h, gap, y0 = 1.2, .6, .12
    H = y0 + 5*band_h + 4*gap + .12
    fig, ax = canvas(H, PLATE)
    # Bands run bottom to top; each gap names the failure that forces the next level.
    top_level = len(s["levels"]) - 1
    for i, lev in enumerate(s["levels"]):
        y = y0 + i*(band_h+gap)
        answer = i == top_level
        accent = VERMILION if answer else DEEP
        rect(ax, .3, y, 11.4, band_h, fc=WASH if answer else WHITE,
             ec=VERMILION if answer else HAIR, lw=1.1 if answer else .9, radius=.06)
        two = "\n" in lev["name"]
        txt(ax, .55, y+(.76 if two else .8), lev["name"], fs=12.5,
            color=VERMILION if answer else INK, weight="bold")
        txt(ax, .55, y+.2, lev["sec"], fs=10, color=SLATE)
        txt(ax, 2.95, y+band_h/2, lev["kept"], fs=10.5 if en else 11.5)
        txt(ax, 6.95, y+.84, lev["formula"], fs=15, color=accent)
        txt(ax, 6.95, y+(.38 if "\n" in lev["refs"] else .3), lev["refs"], fs=10, color=SLATE)
        if "inp" in lev:
            # Dashed grey frame: supplied as input, not generated at this level.
            rect(ax, 10.1, y+.14, 1.45, band_h-.28, fc=WHITE, ec=SLATE, lw=.9,
                 ls=(0, (3, 2)), radius=.05)
            txt(ax, 10.825, y+band_h/2, lev["inp"], fs=10, color=SLATE, ha="center")
        if i < len(s["gaps"]):
            top = y+band_h
            arrow(ax, (.9, top+.06), (.9, top+gap-.06), color=SLATE, lw=1.1)
            txt(ax, 1.15, top+gap/2, s["gaps"][i], fs=10.5 if en else 11, color=SLATE)
    save(fig, out, "figure2-three-layer-overview", "figure2",
         s["mtit"], s["mcap"], s["mclaim"], "main", dpi, lang)


FIG3 = {
 'zh': dict(
    label_a="固定起点的逆极限",
    label_b="沿源后继移位",
    del_last="删末拍",
    keep_start=r"保留起点 $s$",
    d1=r"$d_1^s$：删首拍",
    canonical=r"源词的典范像满足 $T([w]_s)=[w]_{\sigma s}$；完成元素由全部相容的有限读数组成。",
    evo=r"每个完成元素 $z$ 逐拍满足 $\mathrm{old}_i(Tz)=\mathrm{old}_i(z)+\mathrm{eff}_i(z)$，不要求 $z$ 来自某个源词（定理 4.7）。",
    mtit="前缀截短与起点推进",
    mcap="结构示意图（定义4.5，定理4.6–4.7）。A：在pre_b^s(w)=(U₀^s,…,U_b^s)约定下，同起点转移r_b^s:Q_{b+1}(s)→Q_b(s)删去末拍，完成载体为这个固定起点塔的逆极限。B：d_b^s:Q_{b+1}(s)→Q_b(σs)删去首拍并推进起点，诱导线性后继T；两种映射改变不同索引。底部：演化等式对每个完成元素z成立，不要求z来自某个源词。",
    mclaim="前缀截短和时间移位改变不同索引；区分它们后，完成载体上的演化等式具有清楚的类型。"),
 'en': dict(
    label_a="Inverse limit at a fixed start",
    label_b="Shift along the source successor",
    del_last="delete the last tick",
    keep_start=r"the start $s$ is kept",
    d1=r"$d_1^s$: delete the first tick",
    canonical=r"canonical images of source words satisfy $T([w]_s)=[w]_{\sigma s}$; a completion element consists of all compatible finite readings.",
    evo=r"every completion element $z$ satisfies $\mathrm{old}_i(Tz)=\mathrm{old}_i(z)+\mathrm{eff}_i(z)$ tick by tick, whether or not $z$ comes from a source word (Theorem 4.7).",
    mtit="Prefix truncation and start advance",
    mcap="Structural diagram (Definition 4.5, Theorems 4.6–4.7). A: under the convention pre_b^s(w)=(U₀^s,…,U_b^s), the same-start transition r_b^s:Q_{b+1}(s)→Q_b(s) deletes the last tick, and the completion carrier is the inverse limit of this fixed-start tower. B: d_b^s:Q_{b+1}(s)→Q_b(σs) deletes the first tick and advances the start, inducing the linear successor T; the two maps change different indices. Bottom: the evolution equation holds for every completion element z, whether or not z comes from a source word.",
    mclaim="Prefix truncation and time shift change different indices; once they are distinguished, the evolution equation on the completion carrier has clear types."),
}


def figure3(out, dpi, lang="zh"):
    s = FIG3[lang]; en = lang == "en"
    H = 6.0
    fig, ax = canvas(H, PLATE)
    head(ax, .4, 5.7, "A", s["label_a"])
    head(ax, 6.3, 5.7, "B", s["label_b"])
    line(ax, (5.95, 1.55), (5.95, 5.75), HAIR)
    txt(ax, 2.75, 5.08, r"$\widehat C(s)=\lim_{\longleftarrow b}(Q_b(s),r_b^s)$", fs=17, ha="center", color=DEEP)
    rows = [(4.0, r"$Q_2(s)$", 3), (3.02, r"$Q_1(s)$", 2), (2.04, r"$Q_0(s)$", 1)]
    labels = [r"$U_0^s$", r"$U_1^s$", r"$U_2^s$"]
    for y, q, n in rows:
        txt(ax, .55, y, q, fs=15)
        stock(ax, 2.0, y-.29, labels[:n], cell=.8, h=.58, fs=14)
    arrow(ax, (2.4, 4.55), (2.4, 4.33), r"$\mathrm{pr}_2^s$", color=DEEP,
          label_pos=(2.72, 4.47), fs=13, ha="left")
    arrow(ax, (1.45, 3.66), (1.45, 3.36), r"$r_1^s$", color=DEEP, label_pos=(1.08, 3.51), fs=13)
    arrow(ax, (1.45, 2.68), (1.45, 2.38), r"$r_0^s$", color=DEEP, label_pos=(1.08, 2.53), fs=13)
    txt(ax, 4.75, 3.12, s["del_last"], fs=11.5, color=DEEP, ha="center")
    txt(ax, 4.75, 2.72, s["keep_start"], fs=10.5, color=SLATE, ha="center")
    # Shift between different starts: the deleted cell is the FIRST one.
    txt(ax, 6.45, 4.62, r"$Q_2(s)$", fs=15)
    stock(ax, 8.4, 4.33, [r"$U_0^s$", r"$U_1^s$", r"$U_2^s$"], cell=.8, h=.58, fs=14, cut=(0,))
    arrow(ax, (10.0, 4.23), (10.0, 3.67), s["d1"], color=VERMILION,
          label_pos=(9.85, 3.95), fs=11.5, ha="right")
    txt(ax, 6.45, 3.28, r"$Q_1(\sigma s)$", fs=15)
    stock(ax, 9.2, 2.99, [r"$U_0^{\sigma s}$", r"$U_1^{\sigma s}$"], cell=.8, h=.58, fs=14,
          edge=GOLD, fill=WASH)
    txt(ax, 10.0, 2.62, r"$U_i^{\sigma s}=U_{i+1}^{s}$", fs=14, color=GOLD, ha="center")
    txt(ax, 8.95, 1.95, r"$\mathrm{pr}_{b}^{\sigma s}\circ T=d_b^s\circ\mathrm{pr}_{b+1}^{s}$", fs=15, ha="center")
    txt(ax, .45, 1.02, s["canonical"], fs=10 if en else 11, color=SLATE)
    txt(ax, .45, .5, s["evo"], fs=10 if en else 11)
    save(fig, out, "figure3-prefix-tower-and-shift", "figure3",
         s["mtit"], s["mcap"], s["mclaim"], "main", dpi, lang)


FIG4 = {
 'zh': dict(
    label_a="同一词，两个有限窗口",
    witness="源见证",
    read="读取",
    read_longer="再读长一拍",
    rb=r"$r_b^s$：删末拍",
    new="新增",
    label_b="核对这一帧的来源",
    runtime="新增末拍的激活运行时",
    target_tick=r"原 $b$ 预算历史的目标 tick",
    fields_cells=["发生", "整账", "后继"],
    fields_note="逐字段读回同一运行时。",
    label_c="只留下共同读数，会失去哪一件事？",
    at0=r"在 $x\mapsto0$：词 $0$ 与词 $x$ 都读 $0$。",
    at1=r"在 $x\mapsto1$：前者读 $0$，后者读 $1$。",
    moral=r"例 4.1 的共享读数没有指定共同见证；保留 $w$，才有上述沿同一来源的延展。",
    mtit="保留共同源词的历史延展",
    mcap="结构示意图（命题4.8）。给定p=pre_b^s(w)以及它的源词见证w，用同一个w读出更长前缀pre_{b+1}^s(w)；删去新增末拍即回到p。新增末拍的激活运行时等于原b预算历史的目标tick，该等式比较运行时字段，并非将阶段库存U直接当作tick。两条从w出发的箭头都是读取，向上的箭头是有限窗口限制。下方用例4.1提示：读数相同并没有替代保留共同源见证。图中没有从有限商点到完成载体的无条件选取箭头。",
    mclaim="已给定源见证的延展保留同一词；一个裸读数不足以选出这种延展。"),
 'en': dict(
    label_a="One word, two finite windows",
    witness="source\nwitness",
    read="read",
    read_longer="read one\ntick longer",
    rb="$r_b^s$: delete\nthe last tick",
    new="new",
    label_b="Check the source of this frame",
    runtime="the activated runtime of the new last tick",
    target_tick="the target tick of the original\n$b$-budget history",
    fields_cells=["occurrence", "whole ledger", "successor"],
    fields_note="read back field by field to one runtime.",
    label_c="If only the common reading is kept, what is lost?",
    at0=r"at $x\mapsto0$: the words $0$ and $x$ both read $0$.",
    at1=r"at $x\mapsto1$: the former reads $0$, the latter $1$.",
    moral=r"the shared reading of Example 4.1 did not designate a common witness; keeping $w$ gives the extension along the same source above.",
    mtit="History extension keeping the common source word",
    mcap="Structural diagram (Proposition 4.8). Given p=pre_b^s(w) and its source-word witness w, read the longer prefix pre_{b+1}^s(w) with the same w; deleting the newly added last tick returns p. The activated runtime of the new last tick equals the target tick of the original b-budget history; the equation compares runtime fields and does not treat the stage inventory U directly as a tick. Both arrows leaving w are reads, and the upward arrow is a finite-window restriction. The lower part recalls Example 4.1: equal readings did not replace keeping a common source witness. There is no unconditional choice arrow from a finite quotient point to the completion carrier.",
    mclaim="An extension with a given source witness keeps the same word; a bare reading cannot select such an extension."),
}


def figure4(out, dpi, lang="zh"):
    s = FIG4[lang]; en = lang == "en"
    H = 6.75
    fig, ax = canvas(H, PLATE)
    head(ax, .4, 6.45, "A", s["label_a"])
    rect(ax, .55, 3.75, 1.2, 1.75, fc=WASH, ec=VERMILION, lw=1.2, radius=.07)
    txt(ax, 1.15, 4.9, r"$w$", fs=28, color=VERMILION, ha="center")
    txt(ax, 1.15, 4.2, s["witness"], fs=10.5, ha="center", color=VERMILION)
    txt(ax, 3.1, 6.0, r"$p=\mathrm{pre}_b^s(w)$", fs=17, color=DEEP)
    stock(ax, 3.05, 5.0, [r"$U_0^s(w)$", r"$\cdots$", r"$U_b^s(w)$"], cell=1.02, h=.68, fs=13)
    txt(ax, 3.1, 3.9, r"$\mathrm{pre}_{b+1}^s(w)$", fs=17, color=DEEP)
    stock(ax, 3.05, 2.92, [r"$U_0^s(w)$", r"$\cdots$", r"$U_b^s(w)$"], cell=1.02, h=.68, fs=13)
    stock(ax, 6.11, 2.92, [r"$U_{b+1}^s(w)$"], cell=1.2, h=.68, fs=13, edge=GOLD, fill=WASH)
    arrow(ax, (1.82, 5.0), (2.95, 5.3), s["read"], color=DEEP, label_pos=(2.35, 5.5), fs=10.5)
    arrow(ax, (1.82, 4.0), (2.95, 3.3), s["read_longer"], color=DEEP,
          label_pos=(2.2, 3.2) if en else (2.25, 3.3), fs=10.5)
    arrow(ax, (5.7, 3.7), (5.7, 4.88), s["rb"], color=DEEP,
          label_pos=(5.85, 4.3), fs=11, ha="left")
    txt(ax, 6.71, 2.62, s["new"], fs=10.5, color=GOLD, ha="center")
    line(ax, (7.62, 2.45), (7.62, 6.3), HAIR)
    head(ax, 7.85, 6.45, "B", s["label_b"])
    txt(ax, 7.95, 5.72, s["runtime"], fs=10.5)
    for k, f in enumerate(s["fields_cells"]):
        cx = 7.95 + k*1.2
        rect(ax, cx, 4.8, 1.08, .52, fc=WASH, ec=GOLD, lw=.9, radius=.04)
        txt(ax, cx+.54, 5.06, f, fs=9.5 if en else 11, ha="center")
        txt(ax, cx+.54, 4.53, "=", fs=13, ha="center", color=SLATE)
        rect(ax, cx, 3.74, 1.08, .52, fc=WHITE, ec=DEEP, lw=.9, radius=.04)
        txt(ax, cx+.54, 4.0, f, fs=9.5 if en else 11, ha="center")
    txt(ax, 7.95, 3.2 if en else 3.35, s["target_tick"], fs=10.5)
    txt(ax, 7.95, 2.65 if en else 2.9, s["fields_note"], fs=10, color=SLATE)
    line(ax, (.3, 2.2), (11.7, 2.2), HAIR)
    head(ax, .4, 1.8, "C", s["label_c"])
    txt(ax, .55, 1.2, s["at0"], fs=12)
    txt(ax, 6.3, 1.2, s["at1"], fs=12)
    txt(ax, .55, .55, s["moral"], fs=10.5 if en else 11, color=SLATE)
    save(fig, out, "figure4-common-source-history-extension", "figure4",
         s["mtit"], s["mcap"], s["mclaim"], "main", dpi, lang)


FIG5 = {
 'zh': dict(
    label_a="旧世界有事实，旧理论没有表达",
    panel_a="旧查询与准确失败",
    a1="支撑 true；当前载荷 ()；查询 ()",
    a2="旧账：一条行，预算 2；旧主张成立",
    a3="旧表达为空，合法实现为空；障碍 ()",
    a4=r"审计协议携带旧行 → 扎根失败 $\eta$",
    panel_b=r"由 $\eta$ 生成的最小扩充",
    b1=r"支撑 $\mathrm{Bool}\sqcup\{\star_\eta\}$，新支撑 $\star_\eta$",
    b2="关联、责任、主张各添同一新方向",
    b3="迁入旧行：预算 2　｜　新行：预算 0",
    b4="旧事实保留，新主张成立；尚无新动态程序",
    gen="生成",
    label_b="实现数据另行提供，字段接地认回同一个扩充",
    c1=r"有类型修订输入：自然数当前 $n$、写入 $n\mapsto n+1$、两行完整补丁、新活跃根",
    c2="精确接地：新世界、理论面、翻译、初始支撑、旧账、新行、事实、语义变化逐项认回",
    label_c="首拍修订包含两个内部微步；第二拍不再修订",
    nodes=["新根初访", "首次写入目标", "首拍宏后继", "第二拍后继"],
    edges=["首次整账写入", "目标处答案—后继编译", "第二拍直接回答"],
    rows="旧行 2 → 2\n新行 0 → 0",
    auth="两条目标行各获权威\n下一当前均为 2",
    ans="查询 ()\n答案 $\\ast$（单点）",
    pub="首拍公开答案：附着方向；其发生读回首次写入",
    cont="同一新活跃根继续",
    note1="0、1、2、3 是新根的当前，不是查询答案。",
    mtit="两拍修订：从准确失败到新根回答",
    mcap="固定两拍实例（表4、命题8.9）：旧支撑true、查询()、预算2的旧行和空表达/实现理论给出准确失败。最小扩充添加同一失败方向和预算0的新行；自然数动态程序由有类型修订另行提供，经精确字段接地接入。首次写入0→1消费旧、新两行，目标处编译1→2给出修订后新根的当前2；第二拍在同一新根当前2读出单点答案并推进至3。",
    mclaim="同一失败的表达扩充、实际首次写入、完整新根宏后继与第二拍回答逐对象连接；输入身份不被抹去。"),
 'en': dict(
    label_a="The old world has facts; the old theory has no expression",
    panel_a="The old query and the exact failure",
    a1="support true; current payload (); query ()",
    a2="old ledger: one row, budget 2; the old claim holds",
    a3="no old expressions, no lawful realizations;\nobstruction ()",
    a4=r"the audit protocol carries the old row → rooted failure $\eta$",
    panel_b=r"The minimal extension generated by $\eta$",
    b1=r"supports $\mathrm{Bool}\sqcup\{\star_\eta\}$; new support $\star_\eta$",
    b2="incidence, responsibility and claim each\ngain the same new direction",
    b3="migrated old row: budget 2  |  new row: budget 0",
    b4="old facts kept, new claim holds; no dynamical program yet",
    gen="generates",
    label_b="implementation data supplied separately; field grounding recognizes the same extension",
    c1=r"typed revision inputs: natural-number current $n$, write $n\mapsto n+1$, a complete two-row patch, a new living root",
    c2="exact grounding, item by item: new world, theory surface, translation, initial support, old ledger, new row, fact, semantic change",
    label_c="the first-tick revision has two internal micro steps; the second tick revises no more",
    nodes=["new root's\ninitial visit", "first-write\ntarget", "first-tick macro\nsuccessor", "second-tick\nsuccessor"],
    edges=["first whole-ledger write", "answer–next compilation\nat the target", "the second tick\nanswers directly"],
    rows="old row 2 → 2\nnew row 0 → 0",
    auth="each target row gains authority\nboth next currents are 2",
    ans="query ()\nanswer $\\ast$ (unit)",
    pub="the first tick's public answer: the attached direction;\nits occurrence reads back the first write",
    cont="the same new living\nroot continues",
    note1="0, 1, 2, 3 are currents of the new root, not query answers.",
    mtit="The two-tick revision: from the exact failure to the new root's answer",
    mcap="Fixed two-tick instance (Table 4, Proposition 8.9): the old support true, the query (), an old row with budget 2 and an empty expression/realization theory give the exact failure. The minimal extension adds the same failure direction and a new row with budget 0; the natural-number dynamical program is supplied separately by the typed revision and connected through exact field grounding. The first write 0→1 consumes the old and new rows; the compilation 1→2 at the target gives the revised new root's current 2; the second tick reads the unit answer at the same new root's current 2 and advances to 3.",
    mclaim="The expression extension of the same failure, the actual first write, the complete new-root macro successor and the second-tick answer are connected object by object; the identity of inputs is not erased."),
}


def figure5(out, dpi, lang="zh"):
    s = FIG5[lang]; en = lang == "en"
    H = 8.55
    fig, ax = canvas(H, PLATE)
    fa = 10 if en else 11.5
    head(ax, .4, 8.25, "A", s["label_a"])
    rect(ax, .45, 5.75, 4.95, 2.15, fc=WHITE, ec=HAIR, radius=.06)
    txt(ax, .68, 7.6, s["panel_a"], fs=11.5, color=INK, weight="bold")
    # English entries wrap to two lines; their rows are placed individually.
    ya = [7.2, 6.86, 6.42, 5.95] if en else [7.13, 6.73, 6.33, 5.98]
    yb = [7.2, 6.74, 6.33, 5.95] if en else [7.13, 6.73, 6.33, 5.98]
    for y_, key in zip(ya, ["a1", "a2", "a3", "a4"]):
        txt(ax, .68, y_, s[key], fs=fa-.5 if (en and key == "a4") else fa,
            color=SLATE if key == "a4" else INK)
    rect(ax, 6.45, 5.75, 5.1, 2.15, fc=WHITE, ec=DEEP, lw=1.0, radius=.06)
    txt(ax, 6.68, 7.6, s["panel_b"], fs=11.5, color=DEEP, weight="bold")
    for y_, key in zip(yb, ["b1", "b2", "b3", "b4"]):
        txt(ax, 6.68, y_, s[key], fs=fa-.5 if (en and key == "b4") else fa,
            color=DEEP if key == "b4" else INK)
    arrow(ax, (5.5, 6.85), (6.35, 6.85), s["gen"], color=DEEP,
          label_pos=(5.925, 7.12), fs=10.5)
    head(ax, .4, 5.3, "B", s["label_b"])
    rect(ax, .45, 4.02, 11.1, .95, fc=WHITE, ec=SLATE, lw=.9, ls=(0, (3, 2)), radius=.06)
    txt(ax, .68, 4.69, s["c1"], fs=10.5 if en else 11.5)
    txt(ax, .68, 4.3, s["c2"], fs=10 if en else 10.5, color=SLATE)
    head(ax, .4, 3.62, "C", s["label_c"])
    xs = [1.17, 4.38, 7.55, 10.71]
    y = 2.72
    for n, x in enumerate(xs):
        dot(ax, x, y, VERMILION if n == 3 else DEEP, s=85)
        txt(ax, x, y+.36, str(n), fs=17, ha="center")
        txt(ax, x, y-.38, s["nodes"][n], fs=10 if en else 11, ha="center", va="top", color=SLATE)
    for left, right, title, color in zip(xs[:-1], xs[1:], s["edges"], [DEEP, GOLD, VERMILION]):
        arrow(ax, (left+.2, y), (right-.2, y), color=color, lw=1.6)
        txt(ax, (left+right)/2, y+.22, title, fs=10 if en else 11, color=color,
            ha="center", va="bottom")
    ry = 1.65 if en else 1.72
    txt(ax, 2.775, ry, s["rows"], fs=11, ha="center", color=DEEP)
    txt(ax, 5.965, ry, s["auth"], fs=10 if en else 11, ha="center", color=GOLD)
    txt(ax, 9.13, ry, s["ans"], fs=11, ha="center", color=VERMILION)
    by = 1.12
    line(ax, (xs[0], by), (xs[2], by), DEEP, lw=1.2)
    line(ax, (xs[0], by), (xs[0], by+.14), DEEP, lw=1.2)
    line(ax, (xs[2], by), (xs[2], by+.14), DEEP, lw=1.2)
    txt(ax, 4.36, .72 if en else .8, s["pub"], fs=10 if en else 11, ha="center", color=DEEP)
    txt(ax, 9.3, .72 if en else .8, s["cont"], fs=10 if en else 11, ha="center", color=VERMILION)
    txt(ax, .45, .2, s["note1"], fs=10, color=SLATE)
    save(fig, out, "figure5-coproduct-revision-and-continuation", "figure5",
         s["mtit"], s["mcap"], s["mclaim"], "main", dpi, lang)


FIG6 = {
 'zh': dict(
    head_a="原发生交出完整源程序",
    occ="原发生 $o$", occ2="投影读出根树",
    tree="根树 $T(o)$", tree2="有序子树\n重数保留",
    prog=r"$\mathrm{prog}_\kappa T$", prog2="每个节点联合提升原构造子",
    val=r"$\delta_{\mathrm{fold}_\kappa T}$", val2=r"执行迹长 $\beta(T)$",
    e_read="读出", e_gen="生成", e_exec="执行",
    inverse="逆读：只读语法，从不求值",
    zero=r"$\kappa\equiv0$：所有树的执行值都是 $\delta_0$，程序仍单射，逆读仍交回整棵树",
    head_b="执行生出自己的责任，并逐步付款",
    cells=["$B$", "$B-1$", r"$\cdots$", "$1$", "$0$"],
    pay="每一步执行 = 同一数学行上的一次严格付款",
    owner="无旧承担者：旧账整体作为同源余项保留",
    s1="预算 $0$：局部结算",
    s2=r"完成值 $=\mathrm{ev}_\rho(e)$",
    s3=r"收据 $e-\mathrm{const}(\mathrm{ev}_\rho e)\in\ker\mathrm{ev}_\rho$",
    head_c="结清之后，实际动作提出下一问",
    q1=r"实际环境 $\rho'$，增量 $\varepsilon=\rho'-\rho$",
    q2=r"残差请求 $e\ominus e'$",
    q3=r"值 $=\mathrm{eff}_{\rho,\varepsilon}(e)$：答案之后的效应",
    born="新的责任出生",
    born2=r"预算 $r(e)+r(e')+2>0$",
    born3="首步即实际执行",
    nxt="下一帧，同一运行时\n再执行、再付款",
    ex=r"例 8.13：$x$ 在 $x\mapsto1$ 答 $1$；环境移到 $x\mapsto0$，下一问值 $-1$，预算 $3$",
    mtit="从原发生到下一问",
    mcap="结构示意图（定理3.9、6.10、8.12，例8.13）。原发生的投影读出根树T；整树程序被执行β(T)步，只读语法的解析器把程序读回T。每一步执行都是同一数学行上的真实付款，预算依次为B,B−1,…,0；结算处完成值等于原求值，已付迹给出关系收据。实际环境移动后，残差请求的值是效应，预算r(e)+r(e′)+2>0，首步即新的责任出生，下一帧回到同一运行时。图中没有虚线输入框：链上没有外供的总律或修订。",
    mclaim="源程序的执行、逆读、付款与下一问由同一执行债律连成一条无外供输入的链。"),
 'en': dict(
    head_a="The original occurrence hands over a complete source program",
    occ="occurrence $o$", occ2="its projection reads\na rooted tree",
    tree="rooted tree $T(o)$", tree2="ordered subtrees,\nmultiplicity kept",
    prog=r"$\mathrm{prog}_\kappa T$", prog2="each node lifts the\noriginal constructor",
    val=r"$\delta_{\mathrm{fold}_\kappa T}$", val2=r"trace length $\beta(T)$",
    e_read="reads", e_gen="generates", e_exec="executes",
    inverse="inverse reading: syntax only, never evaluates",
    zero=r"$\kappa\equiv0$: every tree executes to $\delta_0$, yet the program stays injective and reads back the whole tree",
    head_b="Execution gives birth to its own obligation and pays it step by step",
    cells=["$B$", "$B-1$", r"$\cdots$", "$1$", "$0$"],
    pay="every execution step = one strict payment on the same mathematical row",
    owner="no prior bearer: the whole old ledger is kept as a same-source remainder",
    s1="budget $0$: local settlement",
    s2=r"completed value $=\mathrm{ev}_\rho(e)$",
    s3=r"receipt $e-\mathrm{const}(\mathrm{ev}_\rho e)\in\ker\mathrm{ev}_\rho$",
    head_c="After settlement, the actual action asks the next question",
    q1=r"actual environment $\rho'$, increment $\varepsilon=\rho'-\rho$",
    q2=r"residual request $e\ominus e'$",
    q3=r"value $=\mathrm{eff}_{\rho,\varepsilon}(e)$: the effect after the answer",
    born="a new obligation is born",
    born2=r"budget $r(e)+r(e')+2>0$",
    born3="its first step is an actual execution",
    nxt="next frame, same\nruntime: execute\nand pay again",
    ex=r"Example 8.13: $x$ answers $1$ at $x\mapsto1$; the environment moves to $x\mapsto0$, the next question has value $-1$ and budget $3$",
    mtit="From the original occurrence to the next question",
    mcap="Structural diagram (Theorems 3.9, 6.10, 8.12, Example 8.13). The projection of the original occurrence reads a rooted tree T; the whole-tree program is executed in β(T) steps, and a syntax-only parser reads the program back to T. Every execution step is a genuine payment on the same mathematical row, with budgets B, B−1, …, 0; at settlement the completed value equals the original evaluation, and the paid trace gives a relation receipt. After the actual environment moves, the residual request has the effect as its value and budget r(e)+r(e′)+2>0; its first step is the birth of a new obligation, and the next frame returns to the same runtime. The figure has no dashed input frame: no master law or revision is supplied along the chain.",
    mclaim="Execution, inverse reading, payment and the next question of a source program form one chain through one execution debt law, with no supplied input."),
}


def figure6(out, dpi, lang="zh"):
    s = FIG6[lang]; en = lang == "en"
    H = 8.35
    fig, ax = canvas(H, PLATE)
    fs = 10 if en else 11
    # A: occurrence -> tree -> program -> value, with the inverse reading underneath.
    head(ax, .4, 8.03, "A", s["head_a"])
    boxes = [(.45, 2.2), (3.2, 2.35), (6.15, 2.45), (9.25, 2.3)]
    yA, hA = 6.2, 1.35
    for (x, w) in boxes:
        rect(ax, x, yA, w, hA, fc=WHITE, ec=DEEP if x > 3 else HAIR, lw=1.0, radius=.06)
    txt(ax, .45+1.1, yA+.98, s["occ"], fs=12, ha="center")
    txt(ax, .45+1.1, yA+.42, s["occ2"], fs=fs-.5, ha="center", color=SLATE)
    # a small rooted tree with ordered children
    rx, ry = 3.2+.5, yA+1.02
    kids = [(3.2+.22, yA+.42), (3.2+.5, yA+.42), (3.2+.78, yA+.42)]
    for kx, ky in kids:
        line(ax, (rx, ry), (kx, ky), DEEP, lw=1.0)
        dot(ax, kx, ky, DEEP, s=28)
    line(ax, kids[2], (3.2+.78, yA+.14), DEEP, lw=1.0)
    dot(ax, 3.2+.78, yA+.14, DEEP, s=22)
    dot(ax, rx, ry, DEEP, s=40)
    txt(ax, 3.2+1.62, yA+.98, s["tree"], fs=11 if en else 12, ha="center")
    txt(ax, 3.2+1.62, yA+.4, s["tree2"], fs=fs-1, ha="center", color=SLATE)
    txt(ax, 6.15+1.225, yA+.98, s["prog"], fs=15, ha="center", color=DEEP)
    txt(ax, 6.15+1.225, yA+.42, s["prog2"], fs=fs-.5, ha="center", color=SLATE)
    txt(ax, 9.25+1.15, yA+.98, s["val"], fs=15, ha="center", color=INK)
    txt(ax, 9.25+1.15, yA+.42, s["val2"], fs=fs, ha="center", color=SLATE)
    ym = yA+hA*.62
    for (x0, w0), (x1, _), lab in zip(boxes[:-1], boxes[1:], [s["e_read"], s["e_gen"], s["e_exec"]]):
        arrow(ax, (x0+w0+.06, ym), (x1-.06, ym), lab, color=DEEP if lab != s["e_read"] else INK,
              label_pos=((x0+w0+x1)/2, ym+.24), fs=9 if en else 10)
    # inverse reading: program back to the tree, below the boxes
    yi = yA-.28
    line(ax, (6.15+1.225, yA), (6.15+1.225, yi), DEEP, lw=1.2)
    line(ax, (6.15+1.225, yi), (3.2+1.175, yi), DEEP, lw=1.2)
    arrow(ax, (3.2+1.175, yi), (3.2+1.175, yA-.02), color=DEEP, lw=1.2)
    txt(ax, 5.3, yi-.24, s["inverse"], fs=fs-.5, ha="center", color=DEEP)
    txt(ax, .45, yi-.6, s["zero"], fs=fs-1 if en else fs-.5, color=SLATE)
    # B: one mathematical row, budgets B ... 0, settlement and receipt.
    yB = 3.05
    head(ax, .4, 4.72, "B", s["head_b"])
    cell = .9
    stock(ax, .7, yB+.62, s["cells"], cell=cell, h=.56, fs=13)
    for k in range(4):
        x = .7+(k+1)*cell
        ax.add_patch(FancyArrowPatch((x-.32, yB+.5), (x+.32, yB+.5), arrowstyle="-|>",
                                     mutation_scale=8, color=GOLD, linewidth=1.1,
                                     connectionstyle="arc3,rad=.45", zorder=3))
    txt(ax, .7, yB+.08, s["pay"], fs=fs-.5, color=GOLD)
    txt(ax, .7, yB-.32, s["owner"], fs=fs-1 if en else fs-.5, color=SLATE)
    rect(ax, 6.15, yB-.2, 5.4, 1.47, fc=WHITE, ec=DEEP, lw=1.0, radius=.06)
    txt(ax, 6.4, yB+.98, s["s1"], fs=fs+.5, color=DEEP, weight="bold")
    txt(ax, 6.4, yB+.5, s["s2"], fs=fs+.5)
    txt(ax, 6.4, yB+.02, s["s3"], fs=fs+.5)
    arrow(ax, (.7+5*cell+.08, yB+.9), (6.07, yB+.9), color=DEEP)
    # C: the loop closes right to left: settled state -> request -> birth -> next frame -> row.
    head(ax, .4, 2.08, "C", s["head_c"])
    yC, hC = .62, 1.18
    rect(ax, 6.4, yC, 5.15, hC, fc=WHITE, ec=HAIR, radius=.06)
    txt(ax, 6.62, yC+.92, s["q1"], fs=fs-.5)
    txt(ax, 6.62, yC+.58, s["q2"], fs=fs)
    txt(ax, 6.62, yC+.22, s["q3"], fs=fs-.5, color=DEEP)
    arrow(ax, (8.9, yB-.26), (8.9, yC+hC+.04), color=DEEP, lw=1.2)
    rect(ax, 2.95, yC, 3.0, hC, fc=WASH, ec=VERMILION, lw=1.2, radius=.06)
    txt(ax, 4.45, yC+.9, s["born"], fs=fs+.5, ha="center", color=VERMILION, weight="bold")
    txt(ax, 4.45, yC+.55, s["born2"], fs=fs-.5, ha="center")
    txt(ax, 4.45, yC+.22, s["born3"], fs=fs-1, ha="center", color=SLATE)
    arrow(ax, (6.34, yC+hC/2), (6.02, yC+hC/2), color=VERMILION, lw=1.4)
    rect(ax, .45, yC, 2.1, hC, fc=WHITE, ec=DEEP, lw=1.0, radius=.06)
    txt(ax, 1.5, yC+hC/2, s["nxt"], fs=fs-1 if en else fs-.5, ha="center", color=DEEP)
    arrow(ax, (2.89, yC+hC/2), (2.61, yC+hC/2), color=DEEP, lw=1.2)
    # the next frame executes and pays again on panel B's row
    line(ax, (.62, yC+hC), (.62, yC+hC+.12), DEEP, lw=1.2)
    line(ax, (.62, yC+hC+.12), (.22, yC+hC+.12), DEEP, lw=1.2)
    line(ax, (.22, yC+hC+.12), (.22, yB+.9), DEEP, lw=1.2)
    arrow(ax, (.22, yB+.9), (.64, yB+.9), color=DEEP, lw=1.2)
    txt(ax, .45, .2, s["ex"], fs=fs-1.5 if en else fs-1, color=SLATE)
    save(fig, out, "figure6-source-program-chain", "figure6",
         s["mtit"], s["mcap"], s["mclaim"], "main", dpi, lang)


SUPP1 = {
 'zh': dict(
    cert1="① 推导证书",
    cert1_note="每个表达式先用自己的规范化推导读回。",
    cert2="② 标量证书",
    cert2_note="剩余形式和由加法与标量模律接住。",
    given=r"给定 $w=\sum_e a_e\delta_e\in\ker(\mathrm{ev}_\rho)$，令 $q_\rho(w)=\sum_e a_e\delta_{\mathrm{const}(\mathrm{ev}_\rho e)}$。",
    laws=r"两族模律：$\delta_v+\delta_u-\delta_{v+u}$　与　$\delta_{av}-a\delta_v$；每条关系均被求值消去。",
    mtit="关系核的两证书分解",
    mcap="证书结构示意图（定理4.4、附录A.3）。给定求值为零的形式词w，qρ(w)表示逐表达式求值后形成的常值形式和。规范化推导的线性延拓给出关系像w−qρ(w)；因evρ(w)=0，剩余qρ(w)由加法关系与标量作用关系给出第二张证书。两张证书相加的关系像正是w，给出ker(evρ)⊆range(relρ)。另一方向逐证据求值为零。",
    mclaim="核中的任何形式词都能由推导证书与标量证书两段显式分解。"),
 'en': dict(
    cert1="① derivation certificate",
    cert1_note="each expression is first read back\nby its own normalization derivation.",
    cert2="② scalar certificate",
    cert2_note="the remaining formal sum is caught by\nthe addition and scalar module laws.",
    given=r"given $w=\sum_e a_e\delta_e\in\ker(\mathrm{ev}_\rho)$, let $q_\rho(w)=\sum_e a_e\delta_{\mathrm{const}(\mathrm{ev}_\rho e)}$.",
    laws=r"the two families of module laws: $\delta_v+\delta_u-\delta_{v+u}$ and $\delta_{av}-a\delta_v$; every relation is erased by evaluation.",
    mtit="The two-certificate decomposition of the relation kernel",
    mcap="Certificate-structure diagram (Theorem 4.4, Appendix A.3). Given a formal word w evaluating to zero, qρ(w) denotes the constant formal sum formed after expression-by-expression evaluation. The linear extension of the normalization derivations gives the relation image w−qρ(w); since evρ(w)=0, the remaining qρ(w) is given a second certificate by the addition and scalar-action relations. The two certificates add up to a relation image of exactly w, giving ker(evρ)⊆range(relρ). The other direction evaluates each piece of evidence to zero.",
    mclaim="Every formal word in the kernel has an explicit two-part decomposition into a derivation certificate and a scalar certificate."),
}


def supp1(out, dpi, lang="zh"):
    s = SUPP1[lang]; en = lang == "en"
    H = 5.75
    fig, ax = canvas(H, PLATE)
    yt = 5.25
    txt(ax, 1.9, yt, r"$\mathrm{Fm}_R(\mathrm{RelIdx})$", fs=16, ha="center")
    txt(ax, 6.0, yt, r"$\mathrm{Fm}_R(\kappa)$", fs=16, ha="center")
    txt(ax, 10.4, yt, r"$V(\kappa)$", fs=16, ha="center")
    arrow(ax, (3.55, yt), (4.95, yt), r"$\mathrm{rel}_\rho$", color=DEEP,
          label_pos=(4.25, yt+.28), fs=13)
    arrow(ax, (7.1, yt), (9.65, yt), r"$\mathrm{ev}_\rho$", color=INK,
          label_pos=(8.375, yt+.28), fs=13)
    txt(ax, 6.0, 4.55, r"$\mathrm{range}(\mathrm{rel}_\rho)=\ker(\mathrm{ev}_\rho)$", fs=18, ha="center", color=DEEP)
    txt(ax, 6.0, 3.88, s["given"], fs=13 if en else 13.5, ha="center")
    # The given kernel element feeds both certificates; the certificates
    # converge on the concluding sum. The fork starts from a junction dot.
    dot(ax, 6.0, 3.47, INK, s=22, z=6)
    arrow(ax, (5.93, 3.44), (3.4, 3.3), color=DEEP, lw=1.1)
    arrow(ax, (6.07, 3.44), (8.6, 3.3), color=GOLD, lw=1.1)
    for x0, w, name, formula, note, c in [
            (.45, 5.3, s["cert1"], r"$\mathrm{rel}_\rho(c_{\mathrm{der}})=w-q_\rho(w)$", s["cert1_note"], DEEP),
            (6.25, 5.3, s["cert2"], r"$\mathrm{rel}_\rho(c_{\mathrm{scl}})=q_\rho(w)$", s["cert2_note"], GOLD)]:
        rect(ax, x0, 1.5, w, 1.7, fc=WHITE, ec=c, lw=.9, radius=.06)
        txt(ax, x0+.25, 2.93, name, fs=11.5, color=c, weight="bold")
        txt(ax, x0+.25, 2.43, formula, fs=17, color=c)
        txt(ax, x0+.25, 1.88, note, fs=10.5 if en else 11)
    arrow(ax, (3.1, 1.46), (5.0, 1.12), color=DEEP, lw=1.1)
    arrow(ax, (8.9, 1.46), (7.0, 1.12), color=GOLD, lw=1.1)
    txt(ax, 6.0, .92, r"$\mathrm{rel}_\rho(c_{\mathrm{der}}+c_{\mathrm{scl}})=w$", fs=19, ha="center", color=VERMILION)
    txt(ax, .5, .3, s["laws"], fs=10.5 if en else 11, color=SLATE)
    save(fig, out, "supp1-two-certificates-kernel", "supp1",
         s["mtit"], s["mcap"], s["mclaim"], "companion", dpi, lang)


SUPP2 = {
 'zh': dict(
    banner="输入：同债良基总律为每个未结算分支提供真实付款宏。",
    budget="预算",
    names=["源当前", "付款源", "付款后", "目标当前"],
    noninc1="不增",
    pay="真实付款",
    strict=r"严格下降（$1>0$）",
    noninc2="不增",
    foot="两侧为恒同边界；零预算处仍需精确结算证据。",
    mtit="付款宏的三段预算复合",
    mcap="精确数值图（定义6.6、定理6.7、表3）。按付款宏边界顺序读出三段不等式：中段是表2的付款1→0，两侧为恒同边界，预算依次为1、1、0、0。一般律是βtarget≤βpaid<βpay≤βsource，两侧也可严格下降，只有中间一段必须严格下降；零预算本身不替代终账回执。",
    mclaim="总律输入下，付款宏中的一段严格下降使三段复合严格下降，并支撑良基递归。"),
 'en': dict(
    banner="Input: the same-debt well-founded master law provides a genuine payment macro for every unsettled branch.",
    budget="budget",
    names=["source current", "payment source", "post-payment", "target current"],
    noninc1="non-increase",
    pay="genuine payment",
    strict=r"strict decrease ($1>0$)",
    noninc2="non-increase",
    foot="the two sides are identity boundaries; zero budget still requires exact settlement evidence.",
    mtit="The three-stage budget composition of a payment macro",
    mcap="Exact numerical figure (Definition 6.6, Theorem 6.7, Table 3). The three-stage inequality is read in the boundary order of the payment macro: the middle stage is the payment 1→0 of Table 2 and the two sides are identity boundaries, so the budgets are 1, 1, 0, 0. The general law is βtarget≤βpaid<βpay≤βsource; the two sides may also strictly decrease, and only the middle stage must decrease strictly; zero budget by itself does not replace a terminal receipt.",
    mclaim="Under the master-law input, one strictly decreasing stage in a payment macro makes the three-stage composite strictly decrease, and supports the well-founded recursion."),
}


def supp2(out, dpi, lang="zh"):
    s = SUPP2[lang]; en = lang == "en"
    H = 5.4
    fig, ax = canvas(H, PRINT_SCALE)
    rect(ax, .45, 4.68, 11.1, .52, fc=WHITE, ec=SLATE, lw=.9, ls=(0, (3, 2)), radius=.05)
    txt(ax, .68, 4.94, s["banner"], fs=10 if en else 11, color=SLATE)
    xs = np.array([1.55, 4.3, 7.1, 9.88]); ys = np.array([3.7, 3.7, 1.98, 1.98])
    for value, y in [(1, ys[0]), (0, ys[2])]:
        line(ax, (1.05, y), (10.7, y), HAIR)
        txt(ax, .73, y, str(value), fs=14, ha="center")
    txt(ax, .73, 4.2, s["budget"], fs=10.5, color=SLATE, ha="center")
    line(ax, (xs[0], ys[0]), (xs[1], ys[1]), DEEP, lw=2.4)
    line(ax, (xs[1], ys[1]), (xs[2], ys[2]), VERMILION, lw=2.8)
    line(ax, (xs[2], ys[2]), (xs[3], ys[3]), DEEP, lw=2.4)
    for k, (x, y) in enumerate(zip(xs, ys)):
        dot(ax, x, y, VERMILION if k in (1, 2) else DEEP, s=45)
    for x, name in zip(xs, s["names"]):
        txt(ax, x, 1.55, name, fs=11 if en else 12, ha="center")
    txt(ax, 2.92, 3.98, s["noninc1"], fs=11.5, color=DEEP, ha="center")
    txt(ax, 5.95, 3.35, s["pay"], fs=11.5, color=VERMILION, ha="left")
    txt(ax, 6.25, 2.95, s["strict"], fs=11.5, color=VERMILION, ha="left")
    txt(ax, 8.49, 2.26, s["noninc2"], fs=11.5, color=DEEP, ha="center")
    txt(ax, 6.0, .92, r"$\beta_{\rm target}\leq\beta_{\rm paid}<\beta_{\rm pay}\leq\beta_{\rm source}\qquad(0\leq0<1\leq1)$", fs=16, ha="center")
    txt(ax, .5, .3, s["foot"], fs=10, color=SLATE)
    save(fig, out, "supp2-same-debt-budget-descent", "supp2",
         s["mtit"], s["mcap"], s["mclaim"], "companion", dpi, lang)


EDITORIAL_NOTE = {
 'zh': "固定起点 prefixRestriction 删末拍，推进起点 dropFirst 删首拍；固定 H 的对应证据见 claims C8。",
 'en': "Fixed start: prefixRestriction deletes the last tick; advancing start: dropFirst deletes the first tick; the corresponding evidence at the fixed H is claims C8.",
}

CURRENT_RENDER = {
    "date": "2026-10-02",
    "scope": "正向链修订：新增图 6（从原发生到下一问），图 2 级内引用补入定理 3.9、6.10、8.12；其余五图与两张补图按同一命令重绘，几何与数据不变。",
    "changes": [
        "图 6：A 原发生→根树→整树程序→执行值，下方逆读箭头与恒零构造子注；B 同一数学行预算 B…0 的逐步付款、局部结算与关系收据；C 残差请求、新的责任出生（朱红）与下一帧。",
        "图 2：同一源对象、同一笔责任与修订三级的引用更新；输入框改注“一般责任输入”与“修订输入”。",
        "朱红：图 6 为结清后的新责任出生；其余各图不变。",
    ],
    "visual_review": [
        "中英各八张 240 dpi PNG 逐张目检：无重叠、无缺字、无截断。",
    ],
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT/"vector")
    parser.add_argument("--dpi", type=int, default=240)
    parser.add_argument("--lang", choices=["zh", "en"], default="zh")
    args = parser.parse_args()
    if args.dpi < 180:
        parser.error("Publication PNG output requires --dpi >= 180")
    install("source-process-core-20260930", args.lang)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for f in [figure1, figure2, figure3, figure4, figure5, figure6, supp1, supp2]:
        f(args.output_dir, args.dpi, args.lang)
        print(f"Rendered {f.__name__}", flush=True)
    suffix = "-en" if args.lang == "en" else ""
    for item in MANIFEST:
        if item["id"] in ("figure3", "figure4"):
            item["editorial_note"] = EDITORIAL_NOTE[args.lang]
    (args.output_dir.parent/f"manifest{suffix}.json").write_text(
        json.dumps(MANIFEST, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
    info = {
        "font_family": list(plt.rcParams["font.family"]),
        "mathtext": plt.rcParams["mathtext.fontset"],
        "style": "shared/figure-style/house_style.py",
        "matplotlib": matplotlib.__version__,
        "dpi": args.dpi, "figures": 8, "svg_text": True,
        "print_scale": {"plots": PRINT_SCALE, "plates": PLATE},
        "minimum_recommended_width_mm": 160,
        "source": "src/draw_figures.py",
    }
    if args.lang == "en":
        info["lang"] = "en"
    info_path = args.output_dir.parent/f"render-info{suffix}.json"
    history = {}
    if info_path.is_file():
        try:
            previous = json.loads(info_path.read_text(encoding="utf-8"))
        except ValueError:
            previous = {}
        history = previous.get("history", {})
        prev = previous.get("current_render")
        if prev and prev.get("date") != CURRENT_RENDER["date"]:
            history[f"render_{prev.get('date')}"] = prev
    info["current_render"] = CURRENT_RENDER
    info["history"] = history
    info_path.write_text(json.dumps(info, ensure_ascii=False, indent=2)+"\n", encoding="utf-8")
    print(f"Manifest: {args.output_dir.parent/f'manifest{suffix}.json'}")


if __name__ == "__main__":
    main()
