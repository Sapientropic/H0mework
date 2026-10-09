#!/usr/bin/env python3
"""Editable SVG readouts of exact JSON; no empirical fit or unit calibration.

Visual language: shared/figure-style (house_style colours and SVG font
stacks); titles and scope notes live in the manuscript captions. Canvases are
1000 px wide, so no label is set below 17 px (W/60).
"""
import argparse, hashlib, html, json, math, re, sys
from fractions import Fraction
from pathlib import Path
import xml.etree.ElementTree as ET
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / 'shared' / 'figure-style'))
from house_style import INK, SLATE, MUTE, HAIR, DEEP, VERMILION, GOLD, SVG_FONT_ZH, SVG_FONT_EN, SVG_FONT_MATH
W, MIN_SIZE = 1000, 17
LANG = 'zh'
TRANSLATIONS = {
    '指定库存的三条仿射读数': 'Three affine readouts of the specified inventory',
    '归一化 U(1)：*t*_{Y} = *Y*/2': 'Normalized U(1): *t*_{Y} = *Y*/2',
    '*ℓ* = 0：*I*_{3} = *I*_{2} = 1，*I*_{1} = 1/2': '*ℓ* = 0: *I*_{3} = *I*_{2} = 1; *I*_{1} = 1/2',
    '本征值': 'Eigenvalue', '重数': 'Multiplicity',
    'native P286 标量—规范裸二次块': 'Native P286 bare scalar-gauge quadratic block',
    '*R* = *B*^{−1}*K* 的本征值': 'Eigenvalues of *R* = *B*^{−1}*K*',
    '联合真空的 Yukawa 奇异值': 'Yukawa singular values of the joint vacuum',
    '*YY*^{†} 的本征值（奇异值平方）': 'Eigenvalues of *YY*^{†} (squared singular values)',
}
def tr(value):
    return TRANSLATIONS.get(str(value),str(value)) if LANG == 'en' else str(value)


def rich(s, size):
    """Escape text; `_{..}` / `^{..}` become script tspans, `*..*` italic (math face)."""
    segs, pos = [], 0
    for m in re.finditer(r'([_^])\{([^}]*)\}|\*([^*]+)\*', s):
        segs.append((s[pos:m.start()], 0, False, False))
        if m.group(3):
            segs.append((m.group(3), 0, False, True))
        else:
            shift = .3 if m.group(1) == '_' else -.4
            for k, part in enumerate(m.group(2).split('*')):
                segs.append((part, shift, True, k % 2 == 1))
        pos = m.end()
    segs.append((s[pos:], 0, False, False))
    if len(segs) == 1:
        return html.escape(s)
    out, cur = [], 0.0
    for t, sh, small, it in segs:
        if not t:
            continue
        attrs = ''
        if sh != cur:  # dy is in em of the tspan's own size; scripts are 70 %
            attrs += f' dy="{(sh - cur) / (.7 if small else 1):.3f}em"'; cur = sh
        if small: attrs += f' font-size="{size * .7:.1f}"'
        if it: attrs += f' font-style="italic" font-family="{SVG_FONT_MATH}"'
        out.append(f'<tspan{attrs}>{html.escape(t)}</tspan>')
    return ''.join(out)


def txt(x, y, value, size=18, anchor='start', weight='normal', fill=INK):
    assert size >= MIN_SIZE, (value, size)
    return (f'<text x="{x:.2f}" y="{y:.2f}" font-size="{size}" text-anchor="{anchor}" font-weight="{weight}" '
            f'fill="{fill}">{rich(tr(value), size)}</text>')


def line(x1, y1, x2, y2, width=1.5, dash='', color=SLATE):
    return (f'<line x1="{x1:.2f}" y1="{y1:.2f}" x2="{x2:.2f}" y2="{y2:.2f}" stroke="{color}" '
            f'stroke-width="{width}"' + (f' stroke-dasharray="{dash}"' if dash else '') + '/>')


def start(h, title):
    return [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{h}" viewBox="0 0 {W} {h}">',
            f'<title>{html.escape(tr(title))}</title>', '<rect width="100%" height="100%" fill="white"/>',
            f'<g font-family="{SVG_FONT_EN if LANG == 'en' else SVG_FONT_ZH}" fill="{INK}">']


def finish(parts, name, out):
    parts += ['</g></svg>']
    name = name.replace('.svg','-en.svg') if LANG == 'en' else name
    target = out/name; target.write_text('\n'.join(parts)+'\n'); ET.parse(target)
    return hashlib.sha256(target.read_bytes()).hexdigest()


def running(data, out):
    rows = data['running']['samples']
    assert len(rows) >= 2 and all(-12 <= r['log_mu_ratio'] <= 4 for r in rows)
    parts = start(575, '指定库存的三条仿射读数')
    x0, x1, y0, y1 = 90, 960, 470, 70
    px = lambda x: x0+(x+12)/16*(x1-x0)
    py = lambda y: y0-y/1.8*(y0-y1)
    for y in (0, .3, .6, .9, 1.2, 1.5, 1.8):
        parts += [line(x0, py(y), x1, py(y), .8, color=HAIR), txt(x0-12, py(y)+6, f'{y:g}', 18, 'end', fill=SLATE)]
    for x in (-12, -8, -4, 0, 4):
        parts += [line(px(x), y0, px(x), y0+6, 1.2), txt(px(x), y0+28, str(x).replace('-', '−'), 18, 'middle', fill=SLATE)]
    parts += [line(x0, y1-10, x0, y0, 1.2), line(x0, y0, x1, y0, 1.2), line(px(0), y1, px(0), y0, 1, '2 6', MUTE)]
    parts += [txt(x0+10, y1-22, '1/*g*^{2}', 20), txt(x1, y0+54, 'ln(*μ*/*μ*^{∗})', 20, 'end')]
    specs = [('inverse_g3_squared', 'SU(3)', '', DEEP), ('inverse_g2_squared', 'SU(2)', '12 6', GOLD),
             ('inverse_g1_squared', '归一化 U(1)：*t*_{Y} = *Y*/2', '3 6', SLATE)]
    for index, (key, label, dash, color) in enumerate(specs):
        points = ' '.join(f'{px(r["log_mu_ratio"]):.3f},{py(r[key]):.3f}' for r in rows)
        parts.append(f'<polyline points="{points}" fill="none" stroke="{color}" stroke-width="3"'
                     + (f' stroke-dasharray="{dash}"' if dash else '') + '/>')
        lx = 150+index*230
        parts += [line(lx, 555, lx+44, 555, 3, dash, color), txt(lx+54, 561, label, 18)]
    # The accent: at ℓ = 0, I₃ = I₂ = 1 but I₁ = 1/2, so the three never meet.
    parts += [line(px(0), py(.5), px(0), py(1), 3.2, color=VERMILION),
              f'<circle cx="{px(0):.2f}" cy="{py(1):.2f}" r="5" fill="{VERMILION}"/>',
              f'<circle cx="{px(0):.2f}" cy="{py(.5):.2f}" r="5" fill="{VERMILION}"/>',
              txt(px(0)+14, py(.75)+6, '*ℓ* = 0：*I*_{3} = *I*_{2} = 1，*I*_{1} = 1/2', 18, fill=VERMILION)]
    return finish(parts, 'fig1-fixed-inventory-running.svg', out)


def spectrum(out, name, title, entries, maximum, xlabel):
    """One row per eigenvalue: bar length = value, right column = multiplicity; zero rows are the accent."""
    row = 62
    h = 160+row*(len(entries)-1)
    parts = start(h, title)
    left, right, top = 200, 800, 60
    bottom = top+row*(len(entries)-1)
    px = lambda x: left+x/maximum*(right-left)
    parts += [txt(170, 26, '本征值', 18, 'end', fill=SLATE), txt(900, 26, '重数', 18, 'middle', fill=SLATE)]
    for tick in range(math.floor(maximum)+1):
        parts += [line(px(tick), top-18, px(tick), bottom+18, .8, '3 6', HAIR),
                  txt(px(tick), bottom+46, tick, 18, 'middle', fill=SLATE)]
    for i, (value, label, count) in enumerate(entries):
        y = top+i*row; color = VERMILION if value == 0 else DEEP
        parts += [txt(170, y+7, label, 20, 'end', fill=color), line(left, y, px(value), y, 3.5, color=color),
                  f'<circle cx="{px(value):.2f}" cy="{y:.2f}" r="6.5" fill="white" stroke="{color}" stroke-width="2.5"/>',
                  txt(900, y+7, count, 20, 'middle', fill=color)]
    parts += [line(left, top-18, left, bottom+18, 1.2), txt(right, bottom+86, xlabel, 19, 'end')]
    return finish(parts, name, out)


def main():
    global LANG
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--language', choices=['zh','en'], default='zh')
    parser.add_argument('--receipt', type=Path, required=True); parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args(); LANG = args.language; args.output.mkdir(parents=True, exist_ok=True)
    data = json.loads(args.receipt.read_text())
    if data['status'] != 'EXACT_SUBORDINATE_READOUT_NOT_EMPIRICAL_PARTICLE_IDENTIFICATION':
        raise ValueError('Unrecognized evidence scope')
    generated = {'fig1-fixed-inventory-running.svg': running(data, args.output)}
    native = data['native_P286_scalar_gauge_block']
    entries = [(float(Fraction(f['root'])), f['root'], f['multiplicity']) for f in native['linear_factors']]
    entries += [(r['approximation'], f"{r['approximation']:.6f}", 1) for r in native['positive_root_intervals']]
    entries.sort(); assert sum(e[2] for e in entries) == 12 and native['rank'] == 9
    name = 'fig2-native-p286-quadratic-spectrum.svg'
    generated[name] = spectrum(args.output, name, 'native P286 标量—规范裸二次块', entries, 3.2, '*R* = *B*^{−1}*K* 的本征值')
    entries = sorted((float(Fraction(k)), k, v) for k, v in data['yukawa']['squared_singular_values'].items())
    name = 'fig3-joint-yukawa-spectrum.svg'
    generated[name] = spectrum(args.output, name, '联合真空的 Yukawa 奇异值', entries, 4.5, '*YY*^{†} 的本征值（奇异值平方）')
    meta = {'receipt_sha256': hashlib.sha256(args.receipt.read_bytes()).hexdigest(), 'scope': data['status'],
            'svg_sha256': {(n.replace('.svg','-en.svg') if LANG == 'en' else n): h for n,h in generated.items()}, 'renderer': 'Python stdlib; editable SVG, house_style serif stacks'}
    (args.output/('figure-manifest-en.json' if LANG == 'en' else 'figure-manifest.json')).write_text(json.dumps(meta, ensure_ascii=False, indent=2)+'\n')
    print('PASS: three SVGs, parsed XML, exact multiplicities, provenance manifest')


if __name__ == '__main__': main()
