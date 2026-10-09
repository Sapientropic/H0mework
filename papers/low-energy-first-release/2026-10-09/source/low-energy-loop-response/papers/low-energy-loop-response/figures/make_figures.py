#!/usr/bin/env python3
"""Editable SVG figures, using fixed Case 2 result intervals (units 1e-20).

Colours and font stacks come from the series house style
(shared/figure-style). Canvases are 1000 px wide and printed at the ~6 in text
width, so no label is set below 17 px (W/60). PNG previews use headless Chrome
and Poppler, as in the paper's PDF pipeline.
"""
from pathlib import Path
from html import escape
import argparse, math, re, sys
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / 'shared' / 'figure-style'))
from house_style import (INK, SLATE, MUTE, HAIR, DEEP, VERMILION, GOLD, WASH,
                         SVG_FONT_ZH, SVG_FONT_EN, SVG_FONT_MATH)

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--lang', choices=('zh', 'en'), default='zh')
parser.add_argument('--svg-only', action='store_true', help='write editable SVGs without rasterizing')
args = parser.parse_args()
SUFFIX = '-en' if args.lang == 'en' else ''
FONT = SVG_FONT_EN if args.lang == 'en' else SVG_FONT_ZH

# Keep the approved geometry and numerical content in one drawing source.
EN = {
    '同一原作用，两条支路与完整五项': 'One original action, two branches and all five terms',
    '原作用 · 同一来源': 'Original action',
    '独立对偶 *ψ*、*χ*': 'Independent duals *ψ*, *χ*',
    '原背景、源与准备': 'Background, source, *P*',
    '289 场 / 252 维物质': '289 fields / 252D matter',
    '有序词支路': 'Ordered-word branch',
    'P_{6} 分级 → 合法 Dirac 传播词': 'P_{6}-graded legal Dirac propagator words',
    '先乘完整词，再选择评价': 'Multiply the full word; then evaluate',
    '裸迹 252 ≠ 准备态 1': 'Bare trace 252 ≠ prepared-state value 1',
    '闭迹简化 ≠ 开放输出消失': 'Trace reduction ≠ zero open output',
    '单向标量闭迹 0；返回读数 −1': 'One-way scalar trace 0; return −1',
    '中途准备投影 → 0': 'Intermediate state projection → 0',
    '完整 dΓ / Fock 词返回原评价': 'Full dΓ / Fock word → original readout',
    '原场支路': 'Original field branch',
    '289 → 103 → 有理 *S*_{55}': '289 → 103 → rational *S*_{55}',
    '场／外源回写 *HF* = *JS*': 'Field / source readback *HF* = *JS*',
    '原点：61 维二阶 → 5 维轻核': 'At 0: 61D order 2 → 5D light kernel',
    '原量子准备与真实时间': 'Original state and real time',
    '全空间 *P*；双 Laplace 积分': 'Full-space *P*; double Laplace integral',
    '原 *S*_{01} / d*x*^{1}，两个同源半幅': '*S*_{01} / d*x*^{1}; two halves, same source',
    '原方程生成变化': 'Original equations → variations',
    'Ward 补源 → 两条 *G* 腿': 'Ward source completion → two *G* legs',
    '电流算子变化 → 读出接触': 'Current variation → reader contact',
    'Duhamel → 两条量子源腿': 'Duhamel → two quantum source legs',
    '量子源左腿': 'Left source leg',
    '量子 Gram 第一槽': 'Quantum Gram slot 1',
    '固定窗': 'Fixed window',
    '量子源右腿': 'Right source leg',
    '量子 Gram 第二槽': 'Quantum Gram slot 2',
    '读出接触': 'Reader contact',
    '读出算子的变化': 'Reader variation',
    '移动交集': 'Moving intersection',
    '传播左腿': 'Left propagation',
    '共轭场传播变化': 'Conjugate *G* varies',
    '传播右腿': 'Right propagation',
    '场传播变化': 'Field *G* varies',
    '固定窗源项 + 移动交集的场／接触项': 'Fixed-window source terms + moving-intersection field / contact terms',
    '体积分与两类通量均保留；*K* = *K*_{G} + ½ *S*_{N} + *K*_{C}': 'Body + both fluxes retained; *K* = *K*_{G} + ½ *S*_{N} + *K*_{C}',
    '保留 |*d*| · 完整复 Gram · 全方向积分与混合项界 → raw、connected：两负一正': 'Retain |*d*| · full complex Gram · full angular integral + mixed bounds → raw / connected: two negative, one positive',
    '两球交集与球面通量': 'The two-ball intersection and boundary fluxes',
    '入射球 |*y*| ≤ *B*': 'Incident ball |*y*| ≤ *B*',
    '观察球 |*y* − *d*| ≤ *B*': 'Observation ball |*y* − *d*| ≤ *B*',
    '深色交集：保留的积分域；朱红边界：两类通量所在的球面': 'Dark lens: retained domain; vermilion boundary: sphere supporting both fluxes',
    '常量核也有尖点': 'Even a constant kernel has a cusp',
    'Vol(两球交集) = 4π*B*^{3}/3 − π*B*^{2}|*s*| + π|*s*|^{3}/12': 'Vol(lens) = 4π*B*^{3}/3 − π*B*^{2}|*s*| + π|*s*|^{3}/12',
    '二次系数不是完整尖窗响应的原点 Hessian': 'Quadratic coefficient ≠ origin Hessian of the full cusp response',
    '固定输入，沿真实径向端点展开': 'Fixed input; expand the exact radial endpoint',
    'body：½ ∫_{球} Re *R*_{dd}': 'body: ½ ∫_{ball} Re *R*_{dd}',
    'first flux：½ ∫_{球面} *u* Re *R*_{d}': 'first flux: ½ ∫_{sphere} *u* Re *R*_{d}',
    'zeroth flux：¼ ∫_{球面} [*u*^{2} ∂_{r} Re *R*_{0} + (3*u*^{2}−1) Re *R*_{0}/*B*]': 'zeroth flux: ¼ ∫_{sphere} [*u*^{2} ∂_{r} Re *R*_{0} + (3*u*^{2}−1) Re *R*_{0}/*B*]',
    '仿射场检验：*a*(*k*) = [1 + (2+i)*k*_{3}] *b*，*b*^{T}*Qb* = 4': 'Affine-field check: *a*(*k*) = [1 + (2+i)*k*_{3}] *b*,  *b*^{T}*Qb* = 4',
    '球面通量 = 非零梯度能量 → 二次系数 0': 'Boundary flux = nonzero gradient energy → quadratic coefficient 0',
    '删掉球面通量，会凭空制造负二次项。全部体积与表面积使用 (2π)^{−3} 原测度。': 'Deleting the flux creates a spurious negative quadratic term. Volume and area retain the original (2π)^{−3} measure.',
    '对角区间、混合项包围与零分离': 'Diagonal intervals, mixed-entry enclosures and separation from zero',
    '所有包围与 0 分离': 'All enclosures avoid zero',
    '对角区间与混合项包围（单位 10^{−20}）': 'Diagonal intervals and mixed-entry enclosures (units 10^{−20})',
    '|*K*_{*ij*}| < 2.299243 × 10^{−22}（raw）；< 2.281948 × 10^{−22}（connected），*i* ≠ *j*': '|*K*_{*ij*}| < 2.299243 × 10^{−22} (raw); < 2.281948 × 10^{−22} (connected), *i* ≠ *j*',
    '连续缩放混合部分，无特征值过零 → 惯性（负, 正, 零）= (2, 1, 0)': 'Scale mixed entries; no eigenvalue crosses 0 → inertia (negative, positive, zero) = (2, 1, 0)',
}


def translated_label(s):
    if args.lang == 'en' and re.search('[\u4e00-\u9fff]', s):
        return EN[s]
    return s

W = 1000
MIN_SIZE = 17


def rich(s, size):
    """Escape text; `_{..}` / `^{..}` become sub/superscript tspans, `*..*` italic."""
    segs, pos = [], 0  # (text, baseline shift in em of the base size, small, italic)
    for m in re.finditer(r'([_^])\{([^}]*)\}|\*([^*]+)\*', s):
        segs.append((s[pos:m.start()], 0, False, False))
        if m.group(3):
            segs.append((m.group(3), 0, False, True))
        else:  # scripts may themselves carry *italic* runs
            shift = .3 if m.group(1) == '_' else -.4
            for k, part in enumerate(m.group(2).split('*')):
                segs.append((part, shift, True, k % 2 == 1))
        pos = m.end()
    segs.append((s[pos:], 0, False, False))
    if len(segs) == 1:
        return escape(s)
    out, cur = [], 0.0
    for t, sh, small, it in segs:
        if not t:
            continue
        attrs = ''
        if sh != cur:  # dy is in em of the tspan's own size; scripts are 70 %
            attrs += f' dy="{(sh - cur) / (.7 if small else 1):.3f}em"'; cur = sh
        if small: attrs += f' font-size="{size * .7:.1f}"'
        if it: attrs += f' font-style="italic" font-family="{SVG_FONT_MATH}"'
        out.append(f'<tspan{attrs}>{escape(t)}</tspan>')
    return ''.join(out)


class SVG:
    def __init__(self, h, title):
        self.h = h
        self.s = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{h}" viewBox="0 0 {W} {h}" role="img">',
                  f'<title>{escape(translated_label(title))}</title>',
                  f'<rect width="100%" height="100%" fill="white"/>',
                  f'<g font-family="{FONT}" fill="{INK}">']

    def text(self, x, y, s, size=MIN_SIZE, fill=INK, anchor='start', weight='normal', math=False):
        assert size >= MIN_SIZE, (s, size)
        family = f' font-family="{SVG_FONT_MATH}"' if math else ''
        self.s.append(f'<text x="{x}" y="{y}" font-size="{size}" fill="{fill}" text-anchor="{anchor}" '
                      f'font-weight="{weight}"{family}>{rich(translated_label(str(s)), size)}</text>')

    def rect(self, x, y, w, h, fill='white', stroke=HAIR, rx=6, width=1.2):
        self.s.append(f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="{rx}" fill="{fill}" stroke="{stroke}" stroke-width="{width}"/>')

    def line(self, x1, y1, x2, y2, stroke=SLATE, width=1.6, arrow=False, dash=''):
        if arrow:  # stop the shaft at the arrow base and draw the head as a polygon
            L = math.hypot(x2 - x1, y2 - y1); ux, uy = (x2 - x1) / L, (y2 - y1) / L
            bx, by = x2 - 10 * ux, y2 - 10 * uy
            self.s.append(f'<polygon points="{x2:.1f},{y2:.1f} {bx - 4.5 * uy:.1f},{by + 4.5 * ux:.1f} '
                          f'{bx + 4.5 * uy:.1f},{by - 4.5 * ux:.1f}" fill="{stroke}"/>')
            x2, y2 = bx, by
        self.s.append(f'<line x1="{x1}" y1="{y1}" x2="{x2:.1f}" y2="{y2:.1f}" stroke="{stroke}" stroke-width="{width}"'
                      + (f' stroke-dasharray="{dash}"' if dash else '') + '/>')

    def box(self, x, y, w, h, title, lines, accent=DEEP, title_fill=INK, size=MIN_SIZE):
        self.rect(x, y, w, h)
        self.s.append(f'<rect x="{x}" y="{y + 3}" width="4" height="{h - 6}" fill="{accent}"/>')
        self.text(x + 16, y + 29, title, 19, title_fill, weight='600')
        for i, t in enumerate(lines):
            self.text(x + 16, y + 56 + 25 * i, t, size)

    def save(self, name):
        self.s.append('</g></svg>')
        path = Path(name)
        (HERE / f'{path.stem}{SUFFIX}{path.suffix}').write_text('\n'.join(self.s) + '\n')


# Figure 1: two branches from the same action; the five-term row is the accent.
s = SVG(640, '同一原作用，两条支路与完整五项')
s.box(20, 20, 200, 125, '原作用 · 同一来源', ['独立对偶 *ψ*、*χ*', '原背景、源与准备', '289 场 / 252 维物质'])
s.box(260, 20, 320, 125, '有序词支路', ['P_{6} 分级 → 合法 Dirac 传播词', '先乘完整词，再选择评价', '裸迹 252 ≠ 准备态 1'])
s.box(620, 20, 360, 125, '闭迹简化 ≠ 开放输出消失', ['单向标量闭迹 0；返回读数 −1', '中途准备投影 → 0', '完整 dΓ / Fock 词返回原评价'])
s.line(220, 82, 260, 82, arrow=True); s.line(580, 82, 620, 82, arrow=True)
s.line(120, 145, 120, 168); s.line(120, 168, 830, 168)
for x in [170, 500, 830]:
    s.line(x, 168, x, 190, arrow=True)
s.box(20, 190, 300, 125, '原场支路', ['289 → 103 → 有理 *S*_{55}', '场／外源回写 *HF* = *JS*', '原点：61 维二阶 → 5 维轻核'])
s.box(350, 190, 300, 125, '原量子准备与真实时间', ['全空间 *P*；双 Laplace 积分', 'raw / mean / connected', '原 *S*_{01} / d*x*^{1}，两个同源半幅'])
s.box(680, 190, 300, 125, '原方程生成变化', ['Ward 补源 → 两条 *G* 腿', '电流算子变化 → 读出接触', 'Duhamel → 两条量子源腿'])
legs = [('量子源左腿', ['量子 Gram 第一槽', '固定窗']), ('量子源右腿', ['量子 Gram 第二槽', '固定窗']),
        ('读出接触', ['读出算子的变化', '移动交集']), ('传播左腿', ['共轭场传播变化', '移动交集']),
        ('传播右腿', ['场传播变化', '移动交集'])]
for x in [170, 500, 830]:
    s.line(x, 315, x, 338)
s.line(110, 338, 890, 338)
for j, (a, b) in enumerate(legs):
    x = 20 + j * 195
    s.line(x + 90, 338, x + 90, 362, arrow=True)
    s.box(x, 362, 180, 105, a, b, accent=VERMILION, title_fill=VERMILION)
    s.line(x + 90, 467, x + 90, 500, arrow=True)
s.rect(20, 500, 960, 120, fill=WASH, stroke=HAIR)
s.text(40, 534, '固定窗源项 + 移动交集的场／接触项', 21, weight='600')
s.text(40, 568, '体积分与两类通量均保留；*K* = *K*_{G} + ½ *S*_{N} + *K*_{C}', 18)
s.text(40, 600, '保留 |*d*| · 完整复 Gram · 全方向积分与混合项界 → raw、connected：两负一正', 18)
s.save('fig01-two-branches.svg')

# Figure 2: the lens and its spherical boundary, where the flux terms live.
s = SVG(570, '两球交集与球面通量')
cy, r, c1, c2 = 215, 130, 160, 247
hx, hy = (c1 + c2) / 2, math.sqrt(r * r - ((c2 - c1) / 2) ** 2)
s.s.append(f'<circle cx="{c1}" cy="{cy}" r="{r}" fill="{WASH}" stroke="{SLATE}" stroke-width="1.6"/>')
s.s.append(f'<circle cx="{c2}" cy="{cy}" r="{r}" fill="none" stroke="{DEEP}" stroke-width="1.6"/>')
lens = (f'M{hx:.2f},{cy - hy:.2f} A{r},{r} 0 0 0 {hx:.2f},{cy + hy:.2f} '
        f'A{r},{r} 0 0 0 {hx:.2f},{cy - hy:.2f} Z')
s.s.append(f'<path d="{lens}" fill="{DEEP}" fill-opacity="0.55" stroke="{VERMILION}" stroke-width="3.2"/>')
s.line(c1, cy, c2, cy, stroke='white', width=2, arrow=True)
s.text((c1 + c2) / 2, cy - 14, '*d* = *s n*', 19, 'white', 'middle', math=True)
s.text(30, 68, '入射球 |*y*| ≤ *B*', 19, SLATE)
s.text(c2 + 20, 378, '观察球 |*y* − *d*| ≤ *B*', 19, DEEP, 'middle')
s.text(30, 410, '深色交集：保留的积分域；朱红边界：两类通量所在的球面', 17)
s.box(440, 40, 540, 125, '常量核也有尖点', ['Vol(两球交集) = 4π*B*^{3}/3 − π*B*^{2}|*s*| + π|*s*|^{3}/12',
                                             '0 ≤ |*s*| ≤ 2*B*', '二次系数不是完整尖窗响应的原点 Hessian'])
s.box(440, 190, 540, 125, '固定输入，沿真实径向端点展开', ['body：½ ∫_{球} Re *R*_{dd}', 'first flux：½ ∫_{球面} *u* Re *R*_{d}',
                                                   'zeroth flux：¼ ∫_{球面} [*u*^{2} ∂_{r} Re *R*_{0} + (3*u*^{2}−1) Re *R*_{0}/*B*]'])
s.rect(20, 432, 960, 122, fill=WASH, stroke=HAIR)
s.text(40, 467, '仿射场检验：*a*(*k*) = [1 + (2+i)*k*_{3}] *b*，*b*^{T}*Qb* = 4', 19)
s.text(40, 503, '球面通量 = 非零梯度能量 → 二次系数 0', 21, VERMILION, weight='600')
s.text(40, 537, '删掉球面通量，会凭空制造负二次项。全部体积与表面积使用 (2π)^{−3} 原测度。', 17)
s.save('fig02-lens-flux.svg')

# Figure 3: diagonal intervals and Gershgorin enclosures; the accent is zero.
s = SVG(590, '对角区间、混合项包围与零分离')
x0, x1, lo, hi = 230, 960, -2.05, 2.55
xp = lambda v: x0 + (x1 - x0) * (v - lo) / (hi - lo)
top, bottom = 40, 392
for v in [-2, -1, 1, 2]:
    s.line(xp(v), top, xp(v), bottom, HAIR, 1, dash='4 5')
    s.text(xp(v), bottom + 26, str(v).replace('-', '−'), 18, SLATE, 'middle')
s.line(x0, bottom, x1, bottom, SLATE, 1.2)
intervals = {'raw': [(-1.355200, -1.309214), (2.140271, 2.186257), (-1.742600, -1.696614)],
             'connected': [(-1.297332, -1.251692), (2.139655, 2.185295), (-1.701494, -1.655854)]}
mixed = {'raw': .02299243, 'connected': .02281948}
for si, (sector, values) in enumerate(intervals.items()):
    col, band = (DEEP, '#c9d5e1') if si == 0 else (GOLD, '#eadbb6')
    for j, (a, b) in enumerate(values):
        y = 72 + si * 180 + j * 52; m = mixed[sector]
        s.text(20, y + 6, f'{sector} / *e*_{{{j + 1}}}', 19, col)
        s.line(xp(a - 2 * m), y, xp(b + 2 * m), y, band, 16)
        s.line(xp(a), y, xp(b), y, col, 7)
        for v in (a, b):
            s.line(xp(v), y - 9, xp(v), y + 9, col, 2)
        label = f'[{a:.6f}, {b:.6f}]'.replace('-', '−'); cx = (xp(a) + xp(b)) / 2
        s.text(min(cx, 978), y - 16, label, 17, col, 'end' if cx + 95 > 978 else 'middle')
s.line(xp(0), top - 8, xp(0), bottom, VERMILION, 2.6)
s.text(xp(0), bottom + 26, '0', 18, VERMILION, 'middle')
s.text(xp(0) + 10, top + 2, '所有包围与 0 分离', 18, VERMILION)
s.text((x0 + x1) / 2, bottom + 56, '对角区间与混合项包围（单位 10^{−20}）', 18, SLATE, 'middle')
s.rect(20, 480, 960, 96, fill=WASH, stroke=HAIR)
s.text(40, 515, '|*K*_{*ij*}| < 2.299243 × 10^{−22}（raw）；< 2.281948 × 10^{−22}（connected），*i* ≠ *j*', 18)
s.text(40, 553, '连续缩放混合部分，无特征值过零 → 惯性（负, 正, 零）= (2, 1, 0)', 19, weight='600')
s.save('fig03-inertia.svg')

# PNG previews go through the same renderer as the PDF build: headless Chrome
# prints the SVG to a one-page PDF at its own size, Poppler rasterizes it at 2x.
# (cairosvg lays out consecutive tspans differently and misplaces math runs.)
import os, re, shutil, signal, subprocess, tempfile, time
if args.svg_only:
    print(f'Wrote 3 editable SVG files ({args.lang})')
    sys.exit(0)
chrome = Path('/Applications/Google Chrome.app/Contents/MacOS/Google Chrome')
pdftoppm = shutil.which('pdftoppm') or '/opt/homebrew/bin/pdftoppm'
for stem in ['fig01-two-branches', 'fig02-lens-flux', 'fig03-inertia']:
    name = f'{stem}{SUFFIX}'
    svg = (HERE / f'{name}.svg').read_text()
    w, h = map(int, re.search(r'width="(\d+)" height="(\d+)"', svg).groups())
    out = HERE / f'{name}.png'; out.unlink(missing_ok=True)
    with tempfile.TemporaryDirectory(ignore_cleanup_errors=True) as work:
        page = Path(work) / 'page.html'
        page.write_text(f'<!doctype html><meta charset="utf-8"><style>@page{{size:{w}px {h}px;margin:0}}'
                        f'html,body{{margin:0;padding:0}}svg{{display:block}}</style>' + svg)
        raw = Path(work) / 'raw.pdf'
        proc = subprocess.Popen([str(chrome), '--headless', '--disable-gpu', '--no-first-run', '--no-pdf-header-footer',
                                 f'--user-data-dir={work}/profile', f'--print-to-pdf={raw}', page.as_uri()],
                                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
        start = time.monotonic()
        while not (raw.exists() and raw.stat().st_size > 1000) and time.monotonic() - start < 40: time.sleep(.2)
        time.sleep(.5)
        if proc.poll() is None: os.killpg(proc.pid, signal.SIGTERM)
        proc.wait(timeout=10)
        subprocess.run([pdftoppm, '-png', '-singlefile', '-scale-to-x', str(2 * w), '-scale-to-y', '-1',
                        str(raw), str(HERE / name)], check=True, capture_output=True)
    assert out.exists() and out.stat().st_size > 1000, name
print(f'Wrote 3 editable SVG and PNG files ({args.lang})')
