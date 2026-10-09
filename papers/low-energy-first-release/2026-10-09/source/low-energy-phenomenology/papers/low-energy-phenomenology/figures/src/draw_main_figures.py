#!/usr/bin/env python3
"""Reproduce the three main figures from frozen source parameters.

Visual language: shared/figure-style (house_style colours and SVG font
stacks). Canvases are 1000 px wide and printed at the ~6 in text width, so no
label is set below 17 px (W/60). Mathematical labels are Matplotlib MathText
(STIX) glyph outlines with the TeX kept in data-tex; plain labels stay
editable SVG text. SVG -> single-page vector PDF by headless Chrome (the same
renderer the manuscript PDF build uses for SVG figures, and one that sees the
CJK serif) -> 1600 px PNG by Poppler.
Requires Matplotlib, PyMuPDF, Poppler and Google Chrome; no research-worktree writes.
"""
from __future__ import annotations
import argparse, csv, json, math, sys
from fractions import Fraction
from pathlib import Path
import matplotlib
from svg_plate import SVGPlate
BASE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BASE.parents[2] / 'shared' / 'figure-style'))
from house_style import INK, SLATE, MUTE, HAIR, DEEP, VERMILION, GOLD, WASH, SVG_FONT_ZH, SVG_FONT_EN
matplotlib.rcParams["mathtext.fontset"] = "stix"
PARAMS = json.loads((BASE / 'data/main-parameters.json').read_text())
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--language', choices=['zh', 'en'], default='zh')
LANG = parser.parse_args().language
FONT = SVG_FONT_EN if LANG == 'en' else SVG_FONT_ZH
TRANSLATIONS = {
    '一个原作用，同一电流': 'One original action, the same current',
    '原 Spin × SU(7) 作用': 'Original Spin × SU(7) action',
    '九个独立场；固定背景与原时间': 'Nine independent fields; fixed background and original time',
    '九场局部发展': 'Local nine-field development',
    '七个齐次初值': 'Seven homogeneous initial data',
    '九类 Euler 残差全为零': 'All nine Euler residuals vanish',
    '真实初值导数 $e^{tJ_0}$': 'Actual derivative $e^{tJ_0}$',
    '耦合传播': 'Coupled propagation',
    '289 个原字段坐标': '289 original field coordinates',
    '103 维忠实传播商': '103-dimensional faithful quotient',
    '79 维制备 + 24 维补块': '79 prepared + 24 complementary',
    '空间物质发展': 'Spatial matter evolution',
    '全部实时间与实幅度': 'All real times and amplitudes',
    '幺正发展 $W_\\epsilon(t,a)$': 'Unitary evolution $W_\\epsilon(t,a)$',
    '原物质读数': 'Original matter readout',
    '$\\mathbb{C}^{252}$ 上的完整乘积': 'Complete products on $\\mathbb{C}^{252}$',
    '独立对偶 $\\chi=s\\psi^\\dagger S$': 'Independent dual $\\chi=s\\psi^\\dagger S$',
    '密度 $a^3\\rho=4\\sqrt{2}$': 'Density $a^3\\rho=4\\sqrt{2}$',
    '实际物质交换': 'Actual matter exchange',
    '158 个顶点；在壳源': '158 vertices; on-shell sources',
    '原时间动能留数': 'Original kinetic residues',
    '恢复全部 289 个场方程': 'Reconstruct all 289 equations',
    '制备电流': 'Prepared current',
    '$K^\\dagger A K$；全部 CAR 词': '$K^\\dagger A K$; every finite CAR word',
    '双侧期望值': 'Two-sided expectation',
    '$\\epsilon=0$ 处的同一响应': 'The same response at $\\epsilon=0$',
    '两条低动量相位支': 'Two low-momentum phase branches',
    '$\\theta$：增长／衰减': '$\\theta$: growth/decay',
    '$\\varphi$：振荡': '$\\varphi$: oscillation',
    '四阶截断（至 $|\\mathbf{k}|^4$）': 'Fourth-order truncation ($|\\mathbf{k}|^4$)',
    '二阶首项（$|\\mathbf{k}|^2$）': 'Leading term ($|\\mathbf{k}|^2$)',
    '有限控制与电流真导数': 'Finite control and the actual current derivative',
    '$\\epsilon=0$：真导数': '$\\epsilon=0$: derivative',
}
TRANSLATIONS['$L^2(\\mathbb{R}^3,\\mathbb{C}^{12})$；规范控制'] = '$L^2(\\mathbb{R}^3,\\mathbb{C}^{12})$; control'
def tr(value):
    return TRANSLATIONS.get(str(value), str(value)) if LANG == 'en' else str(value)
MANIFEST: list[dict] = []
W, MIN_SIZE = 1000, 17
def SVG(title, height):
    return SVGPlate(title, height, base=BASE, source_commit=PARAMS['source_commit'],
                    translate=tr, font=FONT, suffix='-en' if LANG == 'en' else '',
                    manifest=MANIFEST)


def neg(v):
    return v.replace('-', '−')


def axes(g, xmin, xmax, ymin, ymax, xticks, yticks, xlabel, ylabel, bottom=400):
    left, right, top = 92, 965, 48
    X = lambda x: left+(x-xmin)/(xmax-xmin)*(right-left)
    Y = lambda y: bottom-(y-ymin)/(ymax-ymin)*(bottom-top)
    for v, label in yticks:
        g.line(left, Y(v), right, Y(v), stroke=HAIR, width=1)
        g.text(left-12, Y(v)+6, label, 18, 'end', fill=SLATE)
    for v, label in xticks:
        g.line(X(v), bottom, X(v), bottom+6, stroke=SLATE, width=1.2)
        g.text(X(v), bottom+28, label, 18, 'middle', fill=SLATE)
    g.line(left, top-8, left, bottom, stroke=SLATE, width=1.2); g.line(left, bottom, right, bottom, stroke=SLATE, width=1.2)
    if ymin < 0 < ymax: g.line(left, Y(0), right, Y(0), stroke=MUTE, width=1.3)
    g.text(left+10, top+4, ylabel, 20)
    g.text(right, bottom+56, xlabel, 20, 'end')
    return X, Y


# Figure 1: three developments of one action return to one response (the accent).
g = SVG('一个原作用，同一电流', 632)
g.box(245, 18, 510, 88, '原 Spin × SU(7) 作用', ['九个独立场；固定背景与原时间'])
g.line(370, 106, 175, 152, arrow=True); g.line(500, 106, 500, 152, arrow=True); g.line(630, 106, 825, 152, arrow=True)
g.box(40, 158, 270, 140, '九场局部发展', ['七个齐次初值', '九类 Euler 残差全为零', '真实初值导数 $e^{tJ_0}$'])
g.box(365, 158, 270, 140, '耦合传播', ['289 个原字段坐标', '103 维忠实传播商', '79 维制备 + 24 维补块'])
g.box(690, 158, 270, 140, '空间物质发展', ['$L^2(\\mathbb{R}^3,\\mathbb{C}^{12})$；规范控制', '全部实时间与实幅度', '幺正发展 $W_\\epsilon(t,a)$'])
g.line(310, 228, 363, 228, arrow=True)
g.text(336, 216, '$J$', MIN_SIZE, 'middle', fill=SLATE)
for x in (175, 500, 825):
    g.line(x, 298, x, 345, arrow=True)
g.box(40, 350, 270, 118, '原物质读数', ['$\\mathbb{C}^{252}$ 上的完整乘积', '独立对偶 $\\chi=s\\psi^\\dagger S$', '密度 $a^3\\rho=4\\sqrt{2}$'])
g.box(365, 350, 270, 118, '实际物质交换', ['158 个顶点；在壳源', '原时间动能留数', '恢复全部 289 个场方程'])
g.box(690, 350, 270, 118, '制备电流', ['$K^\\dagger A K$；全部 CAR 词', '$B=-\\sqrt{2}\\,QT$', '双侧期望值'])
g.line(175, 468, 175, 496); g.line(825, 468, 825, 496); g.line(175, 496, 825, 496)
g.line(500, 468, 500, 528, arrow=True)
g.box(120, 532, 760, 86, '$\\epsilon=0$ 处的同一响应', (['Derivative of $W$ = Duhamel; current derivative = Kubo = source readout'] if LANG == 'en' else ['$W$ 的导数 = Duhamel 算子；电流的导数 = Kubo 积分 = 同源量子读数']),
      fill=WASH, edge=VERMILION, title_fill=VERMILION, lw=2)
g.save('main-01-common-current')

# Figure 2: exact rational coefficients, local expansion only.
g = SVG('两条低动量相位支', 520)
X, Y = axes(g, 0, 0.5, -0.105, 0.095, [(x, f'{x:.1f}') for x in [0, .1, .2, .3, .4, .5]],
            [(x, neg(f'{x:.2f}')) for x in [-.10, -.05, 0, .05]], '$|\\mathbf{k}|$', '$\\lambda^2$')
colors = {'phi': DEEP, 'theta': VERMILION}
coeffs = {'phi': PARAMS['soft']['lambda_phi_squared'], 'theta': PARAMS['soft']['lambda_theta_squared']}
rows = []
for name in ('phi', 'theta'):
    a, b = map(lambda v: float(Fraction(v)), coeffs[name])
    xs = [.5*i/500 for i in range(501)]
    g.path([(X(k), Y(a*k*k)) for k in xs], colors[name], 1.6, '7 5')
    g.path([(X(k), Y(a*k*k+b*k**4)) for k in xs], colors[name], 3)
    rows.extend({'branch': name, 'k': f'{k:.12g}', 'quadratic': f'{a*k*k:.15g}', 'quartic': f'{a*k*k+b*k**4:.15g}'} for k in xs)
g.text(690, 92, '$\\theta$：增长／衰减', 20, fill=VERMILION)
g.text(690, 356, '$\\varphi$：振荡', 20, fill=DEEP)
g.line(100, 488, 140, 488, stroke=INK, width=3); g.text(150, 494, '四阶截断（至 $|\\mathbf{k}|^4$）', 18)
g.line(520, 488, 560, 488, stroke=INK, width=1.6, dash='7 5'); g.text(570, 494, '二阶首项（$|\\mathbf{k}|^2$）', 18)
g.save('main-02-soft-phases')
if LANG == 'zh':
    with (BASE/'data/soft-phase-curves.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator='\n'); writer.writeheader(); writer.writerows(rows)

# Figure 3: finite current divided by epsilon; the zero-amplitude derivative is the accent.
g = SVG('有限控制与电流真导数', 520)
X, Y = axes(g, 0, 2*math.pi, -.08, 2.13, [(0, '0'), (math.pi/2, '$\\pi/2$'), (math.pi, '$\\pi$'), (3*math.pi/2, '$3\\pi/2$'), (2*math.pi, '$2\\pi$')],
            [(x, f'{x:g}') for x in [0, .5, 1, 1.5, 2]], '$\\omega t$', '$\\omega J_\\epsilon(t)/(\\sqrt{2}\\,\\epsilon)$')
xs = [2*math.pi*i/800 for i in range(801)]
rows = []
ratio_colors = [GOLD, SLATE, DEEP]
for ratio, color in zip(PARAMS['finite_current']['amplitude_ratios'], ratio_colors):
    a = float(Fraction(ratio)); ys = [(1-math.cos(2*x*math.sqrt(1+a*a)))/(1+a*a) for x in xs]
    g.path([(X(x), Y(y)) for x, y in zip(xs, ys)], color, 2.2)
    rows.extend({'epsilon_over_omega': ratio, 'omega_t': f'{x:.12g}', 'normalized_current_quotient': f'{y:.15g}'} for x, y in zip(xs, ys))
g.path([(X(x), Y(1-math.cos(2*x))) for x in xs], VERMILION, 2.8, '8 5')
for i, (label, color, dash) in enumerate([('$\\epsilon/\\omega=1$', GOLD, None), ('$1/2$', SLATE, None), ('$1/4$', DEEP, None),
                                          ('$\\epsilon=0$：真导数', VERMILION, '8 5')]):
    xx = 100+205*i; g.line(xx, 488, xx+36, 488, stroke=color, width=2.6, dash=dash); g.text(xx+46, 494, label, 18)
g.save('main-03-finite-current')
if LANG == 'zh':
    with (BASE/'data/finite-current-curves.csv').open('w', newline='') as f:
        writer = csv.DictWriter(f, fieldnames=list(rows[0]), lineterminator='\n'); writer.writeheader(); writer.writerows(rows)
(BASE/('main-figure-manifest-en.json' if LANG == 'en' else 'main-figure-manifest.json')).write_text(json.dumps({'parameters': 'data/main-parameters.json', 'figures': MANIFEST}, ensure_ascii=False, indent=2)+'\n')
print(json.dumps({'generated': len(MANIFEST), 'formats_per_figure': 3, 'rasterizer': 'pdftoppm'}, indent=2))
