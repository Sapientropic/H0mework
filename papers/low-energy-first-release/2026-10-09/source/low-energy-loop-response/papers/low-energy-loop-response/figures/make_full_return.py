#!/usr/bin/env python3
"""Draw only Case 2 Figure 4, in Chinese and English, without touching Figures 1–3."""
from pathlib import Path
from html import escape
import argparse
import os
import shutil
import signal
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[2] / 'shared' / 'figure-style'))
from house_style import INK, SLATE, HAIR, DEEP, VERMILION, WASH
from svg_text import line as text_line, text_width

W, H = 1000, 1180


class Figure:
    def __init__(self, lang):
        self.lang = lang
        title = self.choose(('完整四动量 Schur、实际有序准备与全原场返回',
                             'Full four-momentum Schur, actual ordered preparation and full field return'))
        self.items = [
            f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" '
            f'viewBox="0 0 {W} {H}" role="img" xml:lang="{lang}">',
            f'<title>{escape(title)}</title>',
            '<defs><marker id="arrow" markerWidth="10" markerHeight="8" refX="9" refY="4" '
            'orient="auto" markerUnits="userSpaceOnUse"><path d="M0,0 L10,4 L0,8 Z" '
            f'fill="{SLATE}"/></marker></defs>',
            '<rect width="100%" height="100%" fill="white"/>',
        ]

    def choose(self, value):
        return value[0 if self.lang == 'zh' else 1] if isinstance(value, tuple) else value

    def text(self, x, y, value, size=17, color=INK, weight=400, anchor='start', max_width=960):
        text = self.choose(value)
        assert size >= 17
        width = text_width(text, size)
        assert width <= max_width, (self.lang, text, round(width, 1), max_width)
        self.items.append(text_line(x, y, text, size, color, weight, anchor))

    def rect(self, x, y, w, h, fill='white', accent=DEEP):
        self.items.append(f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="6" '
                          f'fill="{fill}" stroke="{HAIR}" stroke-width="1.2"/>')
        self.items.append(f'<rect x="{x}" y="{y+3}" width="4" height="{h-6}" fill="{accent}"/>')

    def box(self, x, y, w, h, title, lines, fill='white', accent=DEEP):
        self.rect(x, y, w, h, fill, accent)
        self.text(x+16, y+29, title, 19, weight=600, max_width=w-32)
        for i, content in enumerate(lines):
            self.text(x+16, y+56+25*i, content, max_width=w-32)

    def arrow(self, x1, y1, x2, y2):
        self.items.append(f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" '
                          f'stroke="{SLATE}" stroke-width="1.6" marker-end="url(#arrow)"/>')

    def save(self):
        name = 'fig04-full-return' + ('-en' if self.lang == 'en' else '')
        (HERE / f'{name}.svg').write_text('\n'.join(self.items + ['</svg>']) + '\n')
        return name


def draw(lang):
    s = Figure(lang)
    s.box(20, 20, 960, 86,
          ('原作用密度的真实二导数', 'Actual second derivative of the original action density'),
          [('Fourier Hessian：{i:K}{sub:nat}({i:p}) = {i:H}{sub:289}({i:p})；同一原约束 Green',
            'Fourier Hessian: {i:K}{sub:nat}({i:p}) = {i:H}{sub:289}({i:p}); the same original constrained Green')],
          fill=WASH)

    s.text(20, 138, ('Q5 · 五个原点模与完整四动量 Schur',
                     'Q5 · Five origin modes and the full four-momentum Schur'), 19, weight=600)
    s.box(20, 154, 400, 119,
          ('5 个模；98 维坐标补空间', 'Five modes; 98D coordinate complement'),
          ['98 = 45 + 21 + 32',
           ('{i:p} ∈ ℂ{sup:4}；det {i:A}({i:p}) ≠ 0', '{i:p} ∈ ℂ{sup:4}; det {i:A}({i:p}) ≠ 0'),
           ('原源生成原点附近的非空域', 'The source generates a nonempty domain near 0')])
    s.arrow(420, 214, 470, 214)
    s.box(470, 154, 510, 119,
          ('完整 Schur 与原场／原源恢复图', 'Exact Schur; field and source recovery maps'),
          ['{i:E}({i:p}), {i:L}({i:p}), {i:N}{sub:eff}({i:p}), {i:G}{sub:c}({i:p})',
           '{i:E c} = {i:L s};  {i:x} = {i:N}{sub:eff}{i:c} + {i:G}{sub:c}{i:s}',
           ('四复动量上的完整有理恒等式', 'Full rational identity in four complex momenta')])
    s.arrow(725, 273, 725, 302)
    s.box(20, 302, 960, 116,
          ('实际电流 → 清分母 Green → 全 289 原场',
           'Actual current → cleared Green → all 289 original fields'),
          [('Ward 共源 {i:κ} = {i:F}(−{i:p}){sup:T}{i:J}；清分母原方程保留同一 {i:d}({i:p})',
            'Ward co-source {i:κ} = {i:F}(−{i:p}){sup:T}{i:J}; the cleared original equation retains the same {i:d}({i:p})'),
           ('完整恢复：接触 + 活跃（5 + 98）+ 九零方向；原场与原源同返',
            'Full recovery: contact + active (5 + 98) + nine null directions; the original field and source return together')])

    s.text(20, 466, ('Q6 · 原配置准备：先形成完整有序五因子',
                     'Q6 · Original configuration preparation: form the complete ordered five-factor word'),
           19, weight=600)
    factors = [
        (('左时间', 'Left time'), '{i:V}{isub:ρ}({i:t})'),
        (('左物质逆', 'Left inverse'), '{i:R}{sub:+}({i:ρh}(0))'),
        (('raw／Noether', 'Raw / Noether'), '{i:B}{sub:raw} / {i:N}{sub:f}'),
        (('右物质逆', 'Right inverse'), '{i:R}{sub:−}({i:ρh}(0))'),
        (('右时间', 'Right time'), '{i:U}{isub:ρ}({i:t})'),
    ]
    for i, (title, formula) in enumerate(factors):
        x = 20+198*i
        s.rect(x, 484, 168, 88)
        s.text(x+84, 513, title, 19, weight=600, anchor='middle', max_width=148)
        s.text(x+84, 543, formula, 20, anchor='middle', max_width=148)
        if i < 4:
            s.arrow(x+168, 528, x+198, 528)
    s.text(20, 607,
           ('五处真实变化：两时间、两 inverse、各自原 reader contact；完整词之后才施加读数',
            'Five actual variations: two time, two inverse, each reader contact; evaluate the full word'),
           18)
    s.arrow(500, 624, 500, 632)
    s.items.append(f'<line x1="245" y1="632" x2="755" y2="632" stroke="{SLATE}" stroke-width="1.6"/>')
    s.arrow(245, 632, 245, 645)
    s.arrow(755, 632, 755, 645)

    s.box(20, 645, 450, 154,
          ('原准备读口：实场半轴算子', 'Original readout: real-field half-axis operator'),
          ['{i:𝒥}{sub:∞}: ℝ{sup:289} → ℂ{sup:289}',
           ('独立 {i:z}/{i:w}；Im {i:z}, Im {i:w} ≠ 0', 'Independent {i:z}/{i:w}; Im {i:z}, Im {i:w} ≠ 0'),
           ('Re {i:λ} > 0；{i:t} ≥ 0；保留初共源', 'Re {i:λ} > 0; {i:t} ≥ 0; initial co-source retained'),
           ('完整实线性算子；算子范数尾界', 'Full real-linear operator; operator-norm tail')])
    s.box(530, 645, 450, 154,
          ('实际创建与同背景的差读口', 'Actual creation and its original background'),
          [('原背景 {i:v}{isub:ε}；创建单位态 {i:u}{isub:ε}；{i:z} = {i:w} = {i:ζ}',
            'Original {i:v}{isub:ε}; created unit {i:u}{isub:ε}; {i:z} = {i:w} = {i:ζ}'),
           '{i:ℓ}({i:A}) = −〈{i:u}{isub:ε}, {i:A u}{isub:ε}〉 + 〈{i:v}{isub:ε}, {i:A v}{isub:ε}〉',
           ('同一非线性有序核；原 Euler 号', 'Same nonlinear ordered kernel; original Euler sign'),
           ('两真实 quadrature 恢复完整复信号', 'Two real quadratures → full complex signal')])
    s.arrow(245, 799, 245, 840)
    s.arrow(755, 799, 755, 840)

    s.box(20, 840, 450, 170,
          ('完整时间源的回读', 'Full time-source readback'),
          [('原 time jets：0 / 1 / 2', 'Original time jets: 0 / 1 / 2'),
           ('有限窗：bulk − [{i:B}{isub:λ}({i:T}) − {i:B}{isub:λ}(0)]', 'Finite window: bulk − [{i:B}{isub:λ}({i:T}) − {i:B}{isub:λ}(0)]'),
           ('半轴：bulk + {i:B}{isub:λ}(0)；末端趋零', 'Half-axis: bulk + {i:B}{isub:λ}(0); terminal tends to zero'),
           ('用原源方程回读全部 289 行', 'The original source equation recovers all 289 rows')])
    s.box(530, 840, 450, 170,
          ('完整 289 × 289 响应', 'The full 289 × 289 response'),
          [('非线性来源：0 ≤ {i:T} < {i:τ}({i:d}, {i:k}, {i:P}, {i:a})',
            'Nonlinear source: 0 ≤ {i:T} < {i:τ}({i:d}, {i:k}, {i:P}, {i:a})'),
           ('母 Euler 导数：[ {i:W}{sub:T}{i:K}{sub:nat}({i:P}) − {i:Π}{sub:T} ] {i:a}',
            'Mother Euler derivative: [ {i:W}{sub:T}{i:K}{sub:nat}({i:P}) − {i:Π}{sub:T} ] {i:a}'),
           ('线性化半轴：{i:Δ} = Re {i:λ} − {i:γ}({i:P}) > 0',
            'Linearized half-axis: {i:Δ} = Re {i:λ} − {i:γ}({i:P}) > 0'),
           ('完整 {i:Π}{sub:∞} 存在，保算子范数尾界',
            'Full {i:Π}{sub:∞} exists, with an operator-norm tail')],
          fill=WASH, accent=VERMILION)
    s.arrow(245, 1010, 245, 1054)
    s.arrow(755, 1010, 755, 1054)
    s.box(20, 1054, 960, 102,
          ('同一 H／Green：实际量子 forcing 返回全 289 原场',
           'Same H / Green: the actual quantum forcing returns to all 289 fields'),
          [('实际读口 {i:j}{sub:T} = {i:Π}{sub:T}{i:a}；原准备读口 {i:j}{sub:∞} = {i:𝒥}{sub:∞}{i:f}',
            'Actual readout: {i:j}{sub:T} = {i:Π}{sub:T}{i:a}; original readout: {i:j}{sub:∞} = {i:𝒥}{sub:∞}{i:f}'),
           ('原 regular 域：{i:x} = {i:𝒢}({i:P}{sub:k}){i:j}；保留原 Green 接触项与九相容共源',
            'Original regular domain: {i:x} = {i:𝒢}({i:P}{sub:k}){i:j}; retain the Green contact part and all nine compatibility co-sources')],
          fill=WASH)
    return s.save()


def rasterize(name):
    chrome = Path('/Applications/Google Chrome.app/Contents/MacOS/Google Chrome')
    pdftoppm = shutil.which('pdftoppm') or '/opt/homebrew/bin/pdftoppm'
    with tempfile.TemporaryDirectory(ignore_cleanup_errors=True) as work:
        page, raw = Path(work)/'page.html', Path(work)/'figure.pdf'
        page.write_text(f'<!doctype html><meta charset="utf-8"><style>@page{{size:{W}px {H}px;margin:0}}'
                        'html,body{margin:0;padding:0}svg{display:block}</style>' +
                        (HERE/f'{name}.svg').read_text())
        proc = subprocess.Popen([str(chrome), '--headless', '--disable-gpu', '--no-first-run',
                                 '--no-pdf-header-footer', f'--user-data-dir={work}/profile',
                                 f'--print-to-pdf={raw}', page.as_uri()], stdout=subprocess.DEVNULL,
                                stderr=subprocess.DEVNULL, start_new_session=True)
        started = time.monotonic()
        while not (raw.exists() and raw.stat().st_size > 1000) and time.monotonic()-started < 40:
            time.sleep(.2)
        time.sleep(.5)
        if proc.poll() is None:
            os.killpg(proc.pid, signal.SIGTERM)
        proc.wait(timeout=10)
        if not raw.exists():
            raise RuntimeError('Chrome did not produce '+name)
        subprocess.run([pdftoppm, '-png', '-singlefile', '-scale-to-x', str(2*W), '-scale-to-y', '-1',
                        str(raw), str(HERE/name)], check=True, capture_output=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lang', choices=('zh', 'en', 'both'), default='both')
    parser.add_argument('--svg-only', action='store_true')
    args = parser.parse_args()
    for lang in ('zh', 'en') if args.lang == 'both' else (args.lang,):
        name = draw(lang)
        if not args.svg_only:
            rasterize(name)
        print('Wrote '+name+('.svg' if args.svg_only else '.svg / .png'))


if __name__ == '__main__':
    main()
