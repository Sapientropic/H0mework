#!/usr/bin/env python3
"""Draw docs/assets/ci-wall.svg and ci-wall.en.svg: the run that took the whole
Lean selection green, as a wall of shards.

The eleven stages run left to right, as CI runs them; each column holds that
stage's parallel shards, one cell each, read from tools/ci_layout.tsv. The cells
are laid wet in indigo, stage after stage, and dry to green; once the last stage
has dried the selection is stamped with a vermilion seal reading 核, both the
kernel and the check. Lettering and seal outline come from banner.py so the two
figures share their types, paper and ink.

RUN names the run being recorded. When a later change to the selection goes
green across every stage, point RUN at that run and regenerate.

Usage: python3 docs/assets/ci_wall.py   (deterministic; rewrites both SVGs)
"""
from __future__ import annotations

from collections import defaultdict
from pathlib import Path

from fontTools.pens.boundsPen import BoundsPen

from banner import Face, seal_outline

ROOT = Path(__file__).resolve().parents[2]
RUN = {"id": 39025063045, "commit": "279d795d", "jobs": 66,
       "zh_date": "2026-10-17", "en_date": "17 Oct 2026"}
W, H = 960, 300

TEXT = {
    "zh": {
        "title": "Lean 完整选集：全部阶段通过",
        "eyebrow": "Lean 4 · 完整选集 · {zh_date}",
        "unit": "个模块，全部通过内核检查",
        "facts": "{stages} 个阶段 · {shards} 个分片 · {jobs} 个 job 全绿",
        "axis": "阶段依次推进，每格是一个并行分片",
    },
    "en": {
        "title": "Lean full selection: every stage green",
        "eyebrow": "Lean 4 · full selection · {en_date}",
        "unit": "modules, every one kernel-checked",
        "facts": "{stages} stages · {shards} shards · {jobs} jobs green",
        "axis": "stages run in sequence; each cell is a parallel shard",
    },
}

STYLE = """
    :root { --paper:#f5efe3; --ink:#3a332b; --seal-ink:#b0302a; --wet:#3c679f; --dry:#5c8a60;
            --shade:#6b5236; --shade-a:.1; }
    .paper { fill:var(--paper); }
    .ink { fill:var(--ink); }
    .later { animation:fade 1s ease-out backwards; }
    .cell { fill:var(--dry); transform-box:fill-box; transform-origin:50% 100%;
            animation:lay .4s cubic-bezier(.2,.8,.3,1) backwards, dry 2.2s ease-out backwards; }
    .sealink { fill:var(--seal-ink); }
    .stamp { transform-box:fill-box; transform-origin:center; animation:stamp .45s cubic-bezier(.3,0,.2,1) backwards; }
    @keyframes fade { from { opacity:0; } }
    @keyframes lay { from { opacity:0; transform:scaleY(.2); } }
    @keyframes dry { 0% { fill:var(--wet); } }
    @keyframes stamp { 0% { transform:scale(1.35); opacity:0; } 70% { transform:scale(.97); opacity:1; } }
    @media (prefers-color-scheme: dark) {
      :root { --paper:#15171a; --ink:#dcd3c2; --seal-ink:#c9463a; --wet:#8cb4e6; --dry:#7fb383;
              --shade:#000; --shade-a:.45; }
    }
    @media (prefers-reduced-motion: reduce) { * { animation:none !important; } }
"""


def selection():
    """Shards per stage and the module count, as CI lays them out."""
    stages, modules = defaultdict(set), 0
    for row in (ROOT / "tools/ci_layout.tsv").read_text().splitlines():
        part = row.split("\t")[0]
        stages[int(part[1:].split("-")[0])].add(part)
        modules += 1
    return [len(stages[s]) for s in sorted(stages)], modules


class Setter:
    """Mixed lettering: Fell for Latin, Noto Serif for Han and full-width marks. Below
    display size the figures are Noto's too: Fell's old-style 1 and 0 read as ı and o."""

    def __init__(self):
        self.fell, self.song = Face("IMFeENrm28P.otf"), Face("NotoSerifCJKsc-Regular.otf")

    def face(self, ch, size):
        if ch.isdigit() and size < 40:
            return self.song
        return self.fell if ord(ch) < 0x2000 and ord(ch) in self.fell.cmap else self.song

    def line(self, text, size, x, y):
        paths = []
        for ch in text:
            d, adv = self.face(ch, size).glyph(ch, size, x, y)
            if d:
                paths.append(d)
            x += adv
        return paths, x

    def width(self, text, size):
        return self.line(text, size, 0, 0)[1]


def seal_glyph(face, ch, box):
    """The glyph centred in a box-sized square, as one path."""
    pen = BoundsPen(face.glyphs)
    face.glyphs[face.cmap[ord(ch)]].draw(pen)
    x0, y0, x1, y1 = pen.bounds
    size = box * .74 * face.upm / max(x1 - x0, y1 - y0)
    s = size / face.upm
    x = box / 2 - (x0 + x1) / 2 * s
    y = box / 2 + (y0 + y1) / 2 * s
    return face.glyph(ch, size, x, y)[0]


def paths(ds, cls="", style=""):
    attrs = (f' class="{cls}"' if cls else "") + (f' style="{style}"' if style else "")
    return f"<g{attrs}>" + "".join(f'<path d="{d}"/>' for d in ds) + "</g>"


def draw(lang, t, shards, modules, setter, glyph):
    facts = {**RUN, "stages": len(shards), "shards": sum(shards)}
    x = 48
    eyebrow, _ = setter.line(t["eyebrow"].format(**facts), 15, x, 74)
    big, big_end = setter.line(f"{modules:,}", 86, x - 3, 156)
    unit, _ = setter.line(t["unit"], 22 if lang == "zh" else 25, x, 216)
    fact, _ = setter.line(t["facts"].format(**facts), 15, x, 250)

    # the wall: columns bottom-aligned on a shared baseline, one per stage
    x0, x1, base = 500, 912, 236
    pitch = (x1 - x0) / len(shards)
    cw, ch, gap = pitch - 10, 7, 2.2
    cells, labels, delay = [], [], .4
    for s, n in enumerate(shards):
        cx = x0 + s * pitch + (pitch - cw) / 2
        for k in range(n):
            cy = base - (k + 1) * ch - k * gap
            cells.append(f'<rect class="cell" style="animation-delay:{delay + k * .03:.2f}s" '
                         f'x="{cx:.1f}" y="{cy:.1f}" width="{cw:.1f}" height="{ch}" rx="1.6"/>')
        label = str(s + 1)
        lx = cx + cw / 2 - setter.width(label, 13) / 2
        labels += setter.line(label, 13, lx, base + 20)[0]
        delay += .26
    axis_w = setter.width(t["axis"], 12)
    axis, _ = setter.line(t["axis"], 12, (x0 + x1) / 2 - axis_w / 2, base + 46)
    t_seal = delay + .5

    seal_size = 56
    seal_x, seal_y = big_end + 18, 96
    desc = (f"Run {RUN['id']} on commit {RUN['commit']}: {modules:,} Lean modules in "
            f"{len(shards)} stages and {sum(shards)} shards, {RUN['jobs']} jobs, all green. "
            "Each stage is a column of its parallel shards; the selection is sealed with 核.")
    return f'''<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" role="img" aria-labelledby="t d">
  <title id="t">{t["title"]}</title>
  <desc id="d">{desc}</desc>
  <style>{STYLE}  </style>
  <defs>
    <filter id="pen" filterUnits="userSpaceOnUse" x="0" y="0" width="{W}" height="{H}">
      <feTurbulence type="fractalNoise" baseFrequency=".07" numOctaves="2" seed="29" result="t"/>
      <feDisplacementMap in="SourceGraphic" in2="t" scale="1.3" xChannelSelector="R" yChannelSelector="G"/>
    </filter>
    <filter id="inkpad" x="-8%" y="-8%" width="116%" height="116%" color-interpolation-filters="sRGB">
      <feTurbulence type="fractalNoise" baseFrequency=".32" numOctaves="2" seed="21" result="fine"/>
      <feColorMatrix in="fine" type="matrix" values="0 0 0 0 0  0 0 0 0 0  0 0 0 0 0  -7 0 0 0 5" result="pits"/>
      <feTurbulence type="fractalNoise" baseFrequency=".035" numOctaves="3" seed="9" result="broad"/>
      <feColorMatrix in="broad" type="matrix" values="0 0 0 0 0  0 0 0 0 0  0 0 0 0 0  1.2 0 0 0 .3" result="density"/>
      <feComposite in="pits" in2="density" operator="arithmetic" k1="1" result="cover"/>
      <feComposite in="SourceGraphic" in2="cover" operator="in" result="inked"/>
      <feTurbulence type="fractalNoise" baseFrequency=".18" numOctaves="2" seed="4" result="edge"/>
      <feDisplacementMap in="inked" in2="edge" scale="3.2" xChannelSelector="R" yChannelSelector="G"/>
    </filter>
    <filter id="paper" x="0" y="0" width="100%" height="100%">
      <feTurbulence type="fractalNoise" baseFrequency=".8" numOctaves="2" seed="4" result="n"/>
      <feColorMatrix in="n" type="matrix" values="0 0 0 0 .35  0 0 0 0 .28  0 0 0 0 .2  -.5 0 0 0 .3"/>
      <feComposite in2="SourceGraphic" operator="in"/>
    </filter>
    <mask id="carve" maskUnits="userSpaceOnUse" x="-10" y="-10" width="136" height="136">
      <rect x="-10" y="-10" width="136" height="136" fill="#fff"/>
      <path fill="#000" d="{glyph}"/>
      <g fill="#000"><ellipse cx="116" cy="41" rx="2.6" ry="4.2"/><ellipse cx="31" cy="116" rx="3.6" ry="2.2"/></g>
    </mask>
    <radialGradient id="vignette" cx="50%" cy="50%" r="72%">
      <stop offset=".55" style="stop-color:var(--shade);stop-opacity:0"/>
      <stop offset="1" style="stop-color:var(--shade);stop-opacity:var(--shade-a)"/>
    </radialGradient>
  </defs>

  <rect class="paper" width="{W}" height="{H}" rx="14"/>
  <rect width="{W}" height="{H}" rx="14" filter="url(#paper)"/>

  <g class="ink later">
    {paths(eyebrow, style="opacity:.62")}
    {paths(big)}
    {paths(unit, style="opacity:.85")}
    {paths(fact, style="opacity:.62")}
  </g>

  <g filter="url(#pen)">
    {"".join(cells)}
  </g>
  <g class="ink later" style="animation-delay:.4s">
    {paths(labels, style="opacity:.6")}
    {paths(axis, style="opacity:.5")}
  </g>

  <g transform="translate({seal_x:.1f} {seal_y:.1f}) rotate(-4) scale({seal_size / 116:.4f})">
    <g class="stamp" style="animation-delay:{t_seal:.2f}s">
      <g filter="url(#inkpad)"><path class="sealink" mask="url(#carve)" d="{seal_outline()}"/></g>
    </g>
  </g>

  <rect width="{W}" height="{H}" rx="14" fill="url(#vignette)"/>
</svg>
'''


def main():
    shards, modules = selection()
    setter = Setter()
    glyph = seal_glyph(Face("NotoSerifCJKsc-Bold.otf"), "核", 116)
    for lang, name in [("zh", "ci-wall.svg"), ("en", "ci-wall.en.svg")]:
        svg = draw(lang, TEXT[lang], shards, modules, setter, glyph)
        out = Path(__file__).with_name(name)
        out.write_text(svg)
        print(f"{out.name}: {modules:,} modules, {len(shards)} stages, {sum(shards)} shards, {len(svg) // 1024} KB")


if __name__ == "__main__":
    main()
