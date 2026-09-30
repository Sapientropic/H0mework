#!/usr/bin/env python3
"""Draw docs/assets/banner.svg: an unfinished map that grows from one source.

Each region (an atom) appears only against a region that is already there,
across an edge they actually share; the vermilion lineage records which
region it grew from. Nothing is placed out of nowhere, and the map is never
finished: the newest regions stay wet.

Usage: python3 docs/assets/banner.py   (deterministic; rewrites banner.svg)
"""
from __future__ import annotations

import heapq
import math
import random
from pathlib import Path

W, H = 960, 300
SOURCE = (150.0, 150.0)
CARTOUCHE = (668, 172, 928, 278)  # x0, y0, x1, y1
rng = random.Random(20260930)


def in_island(x: float, y: float) -> bool:
    """A continent around the source, kept clear of the cartouche."""
    a = math.atan2(y - 150, x - 330)
    wobble = 1 + .16 * math.sin(3 * a + .7) + .09 * math.sin(7 * a + 2.1) + .05 * math.sin(13 * a)
    inside = ((x - 330) / 315) ** 2 + ((y - 150) / 118) ** 2 < wobble ** 2
    x0, y0, x1, y1 = CARTOUCHE
    return inside and not (x0 - 56 < x < x1 and y0 - 44 < y < y1)


def poisson(r: float, tries: int = 30) -> list[tuple[float, float]]:
    pts = [SOURCE]
    active = [SOURCE]
    while active:
        p = active.pop(rng.randrange(len(active)))
        for _ in range(tries):
            a, d = rng.uniform(0, 2 * math.pi), rng.uniform(r, 2 * r)
            q = (p[0] + d * math.cos(a), p[1] + d * math.sin(a))
            if -40 < q[0] < W + 40 and -40 < q[1] < H + 40 and all(math.dist(q, s) >= r for s in pts):
                pts.append(q)
                active.append(q)
    return pts


def clip(poly, a, b):
    """Keep the half of poly closer to site a than to site b."""
    mx, my = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
    nx, ny = b[0] - a[0], b[1] - a[1]
    side = lambda p: (p[0] - mx) * nx + (p[1] - my) * ny
    out = []
    for i, p in enumerate(poly):
        q = poly[(i + 1) % len(poly)]
        sp, sq = side(p), side(q)
        if sp <= 0:
            out.append(p)
        if sp * sq < 0:
            t = sp / (sp - sq)
            out.append((p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])))
    return out


def cell(i, sites):
    poly = [(-60, -60), (W + 60, -60), (W + 60, H + 60), (-60, H + 60)]
    for j, s in enumerate(sites):
        if j != i and math.dist(s, sites[i]) < 140:
            poly = clip(poly, sites[i], s)
    return poly


def centroid(poly):
    a = cx = cy = 0.0
    for i, p in enumerate(poly):
        q = poly[(i + 1) % len(poly)]
        c = p[0] * q[1] - q[0] * p[1]
        a, cx, cy = a + c, cx + (p[0] + q[0]) * c, cy + (p[1] + q[1]) * c
    return cx / (3 * a), cy / (3 * a)


def inset(poly, c, k=.9):
    return [(c[0] + k * (p[0] - c[0]), c[1] + k * (p[1] - c[1])) for p in poly]


def path(poly):
    return "M" + " L".join(f"{x:.1f} {y:.1f}" for x, y in poly) + "Z"


def main():
    sites = poisson(34)
    keep = [i for i, s in enumerate(sites) if in_island(*s)]
    polys = {i: cell(i, sites) for i in keep}

    def shared(i, j):
        n = sum(1 for p in polys[i] for q in polys[j] if math.dist(p, q) < 1e-3)
        return n >= 2

    near = {i: [j for j in keep if j != i and math.dist(sites[i], sites[j]) < 90 and shared(i, j)]
            for i in keep}

    # Grow from the source: a region joins only through a neighbour already on the map.
    root = 0
    order, parent, seen = [], {root: None}, {root}
    heap = [(0.0, root)]
    while heap:
        _, i = heapq.heappop(heap)
        order.append(i)
        for j in near[i]:
            if j not in seen:
                seen.add(j)
                parent[j] = i
                d = math.dist(sites[j], SOURCE) * rng.uniform(.8, 1.25)
                heapq.heappush(heap, (d, j))

    step, start = .16, .5
    delay = {i: start + step * k for k, i in enumerate(order)}
    cent = {i: centroid(polys[i]) for i in order}
    last = delay[order[-1]]

    # Borders are shared: each segment is inked once, by the region that first reaches it.
    key = lambda a, b: tuple(sorted(((round(a[0], 1), round(a[1], 1)), (round(b[0], 1), round(b[1], 1)))))
    inked = set()
    washes, borders, lineage = [], [], []
    for k, i in enumerate(order):
        d, age = delay[i], k / (len(order) - 1)
        washes.append(f'<path class="wash" style="animation-delay:{d:.2f}s;opacity:{.03 + .34 * age ** 2.5:.3f}" '
                      f'd="{path(polys[i])}"/>')
        poly, segs = polys[i], []
        for n, a in enumerate(poly):
            b = poly[(n + 1) % len(poly)]
            if key(a, b) not in inked and math.dist(a, b) > .3:
                inked.add(key(a, b))
                segs.append(f"M{a[0]:.1f} {a[1]:.1f} L{b[0]:.1f} {b[1]:.1f}")
        if segs:
            borders.append(f'<path class="edge" style="animation-delay:{d:.2f}s" d="{' '.join(segs)}"/>')
        if parent[i] is not None:
            (x0, y0), (x1, y1) = cent[parent[i]], cent[i]
            lineage.append(f'<path class="trace" pathLength="1" style="animation-delay:{d - .08:.2f}s" '
                           f'd="M{x0:.1f} {y0:.1f} L{x1:.1f} {y1:.1f}"/>')

    # A recollection: light walks the lineage from the source to the youngest far region.
    tip = max(order, key=lambda i: math.dist(cent[i], SOURCE))
    walk = []
    while tip is not None:
        walk.append(cent[tip])
        tip = parent[tip]
    walk = "M" + " L".join(f"{x:.1f} {y:.1f}" for x, y in reversed(walk))
    begin = last + 2.5

    x0, y0, x1, y1 = CARTOUCHE
    svg = f'''<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" role="img" aria-labelledby="t d">
  <title id="t">H0mework · 未干的地图</title>
  <desc id="d">An unfinished map grows from a single source. Each region appears only against one already drawn, across an edge they share; a vermilion lineage records where it grew from. The newest regions are still wet.</desc>
  <style>
    :root {{ --paper:#f6f1e6; --ink:#3a342d; --wash:#56789a; --seal:#b3372c; }}
    @media (prefers-color-scheme: dark) {{
      :root {{ --paper:#121416; --ink:#d8d0bf; --wash:#86a7c6; --seal:#d4564a; }}
    }}
    .paper {{ fill:var(--paper); }}
    .wash {{ fill:var(--wash); animation:wet 4s ease-out backwards; }}
    .edge {{ fill:none; stroke:var(--ink); stroke-width:.75; stroke-linejoin:round; stroke-linecap:round; opacity:.5;
             animation:fade 1.2s ease-out backwards; }}
    .trace {{ fill:none; stroke:var(--seal); stroke-width:.85; stroke-linecap:round; opacity:.36;
              stroke-dasharray:1; animation:draw .45s ease-out backwards; }}
    .source {{ fill:var(--seal); transform-box:fill-box; transform-origin:center;
               animation:breathe 5s ease-in-out infinite; }}
    .ring {{ fill:none; stroke:var(--seal); stroke-width:.8; transform-box:fill-box; transform-origin:center;
             opacity:0; animation:ring 5s ease-out infinite; }}
    .spark {{ fill:var(--seal); }}
    .frame {{ fill:var(--paper); stroke:var(--ink); stroke-width:.8; }}
    .frame2 {{ fill:none; stroke:var(--ink); stroke-width:.4; opacity:.6; }}
    .title {{ fill:var(--ink); font:400 40px "Iowan Old Style",Palatino,"Palatino Linotype",Georgia,serif; letter-spacing:.03em; }}
    .zh {{ fill:var(--ink); font:400 15px "Songti SC",STSong,"Noto Serif CJK SC","Source Han Serif SC",serif; letter-spacing:.3em; opacity:.8; }}
    .en {{ fill:var(--ink); font:italic 400 12.5px "Iowan Old Style",Palatino,Georgia,serif; letter-spacing:.06em; opacity:.6; }}
    .seal rect {{ fill:var(--seal); }}
    .seal text {{ fill:var(--paper); font:400 19px "Songti SC",STSong,"Noto Serif CJK SC",serif; }}
    .fade {{ animation:fade 1.8s ease-out backwards; }}
    @keyframes draw {{ from {{ stroke-dashoffset:1; }} }}
    @keyframes wet {{ 0% {{ opacity:0; }} 12% {{ opacity:.55; }} }}
    @keyframes fade {{ from {{ opacity:0; }} }}
    @keyframes breathe {{ 0%,100% {{ transform:scale(1); }} 50% {{ transform:scale(1.3); }} }}
    @keyframes ring {{ 0% {{ transform:scale(.2); opacity:.6; }} 100% {{ transform:scale(1); opacity:0; }} }}
    @media (prefers-reduced-motion: reduce) {{ * {{ animation:none !important; }} .spark {{ display:none; }} }}
  </style>
  <defs>
    <filter id="wet" x="-8%" y="-10%" width="116%" height="120%">
      <feTurbulence type="fractalNoise" baseFrequency=".03" numOctaves="3" seed="7"/>
      <feDisplacementMap in="SourceGraphic" scale="9" result="bled"/>
      <feGaussianBlur in="bled" stdDeviation="2.2"/>
    </filter>
    <filter id="hand" x="-5%" y="-5%" width="110%" height="110%">
      <feTurbulence type="fractalNoise" baseFrequency=".06" numOctaves="2" seed="3"/>
      <feDisplacementMap in="SourceGraphic" scale="1.6"/>
    </filter>
  </defs>

  <rect class="paper" width="{W}" height="{H}" rx="14"/>

  <g filter="url(#wet)">
    {chr(10).join("    " + c for c in washes).strip()}
  </g>
  <g filter="url(#hand)">
    {chr(10).join("    " + c for c in borders).strip()}
  </g>
  <g>
    {chr(10).join("    " + t for t in lineage).strip()}
  </g>

  <circle class="ring" cx="{cent[root][0]:.1f}" cy="{cent[root][1]:.1f}" r="26"/>
  <circle class="source" cx="{cent[root][0]:.1f}" cy="{cent[root][1]:.1f}" r="3.6"/>

  <circle class="spark" r="2" opacity="0">
    <animateMotion dur="6s" begin="{begin:.1f}s;spark.end+9s" id="spark" path="{walk}" calcMode="spline" keyPoints="0;1" keyTimes="0;1" keySplines=".4 0 .5 1"/>
    <animate attributeName="opacity" values="0;.95;.95;0" keyTimes="0;.08;.9;1" dur="6s" begin="{begin:.1f}s;spark.end+9s"/>
  </circle>

  <g class="fade" style="animation-delay:{min(last, 4.5):.1f}s">
    <rect class="frame" x="{x0}" y="{y0}" width="{x1 - x0}" height="{y1 - y0}" rx="2"/>
    <rect class="frame2" x="{x0 + 5}" y="{y0 + 5}" width="{x1 - x0 - 10}" height="{y1 - y0 - 10}" rx="1"/>
    <text class="title" x="{x0 + 24}" y="{y0 + 52}">H0mework</text>
    <g class="seal" transform="translate({x1 - 24} {y0 - 12}) rotate(-4)">
      <rect width="28" height="28" rx="2.5"/>
      <text x="14" y="20.5" text-anchor="middle">源</text>
    </g>
    <text class="zh" x="{x0 + 25}" y="{y0 + 80}">未干的地图</text>
    <text class="en" x="{x0 + 25}" y="{y0 + 96}">The Unfinished Map</text>
  </g>
</svg>
'''
    out = Path(__file__).with_name("banner.svg")
    out.write_text(svg)
    print(f"{out.name}: {len(order)} regions, grown in {last:.1f}s, {len(svg) // 1024} KB")


if __name__ == "__main__":
    main()
