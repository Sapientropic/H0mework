#!/usr/bin/env python3
"""Draw docs/assets/banner.svg: an unfinished map grown from one source.

A territory joins the map only against one already there, across the border
they share, and its colour floods in from that border. A border is inked only
once both of its sides exist; the coast is inked as each shore appears. The
vermilion route records where every territory grew from. Early territories
have dried to ochre, the newest are still wet indigo, and the blank beyond the
frontier has not happened yet.

The Voronoi mesh underneath never shows: every border is wobbled once and
shared by both sides, each territory is washed with pigment pooling at its
edge as on hand-coloured maps, and the waterlines are contours of the land.

Usage: python3 docs/assets/banner.py   (deterministic; rewrites banner.svg)
"""
from __future__ import annotations

import heapq
import math
import random
from pathlib import Path

W, H = 960, 300
SOURCE = (150.0, 152.0)
rng = random.Random(20260930)

# Pigment by age: dried ochre at the source, sage, still-wet indigo at the frontier.
LIGHT = [(192, 160, 106), (142, 162, 128), (66, 100, 148)]
DARK = [(180, 150, 102), (128, 158, 134), (116, 156, 208)]


def pt(p):
    return f"{p[0]:.1f} {p[1]:.1f}"


def mid(a, b):
    return ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2)


def in_land(x, y):
    """The continent the map may grow into, kept clear of the title."""
    a = math.atan2(y - 150, x - 330)
    wobble = 1 + .16 * math.sin(3 * a + .7) + .09 * math.sin(7 * a + 2.1) + .05 * math.sin(13 * a)
    inside = ((x - 330) / 315) ** 2 + ((y - 150) / 106) ** 2 < wobble ** 2
    return inside and not (x > 612 and y > 128)


def spacing(x, y):
    """Territories are broad near the source and finer toward the frontier."""
    t = min(1, max(0, (x - SOURCE[0]) / 480))
    return 44 - 13 * t + 3.5 * math.sin(x * .031 + 1.1) * math.cos(y * .043 - .6)


def poisson(tries=30):
    pts, gap, active = [SOURCE], [spacing(*SOURCE)], [0]
    while active:
        k = active.pop(rng.randrange(len(active)))
        p, r = pts[k], gap[k]
        for _ in range(tries):
            a, d = rng.uniform(0, 2 * math.pi), rng.uniform(r, 2 * r)
            q = (p[0] + d * math.cos(a), p[1] + d * math.sin(a))
            if not (-50 < q[0] < W + 50 and -50 < q[1] < H + 50):
                continue
            rq = spacing(*q)
            if all(math.dist(q, s) >= (rq + g) / 2 for s, g in zip(pts, gap)):
                pts.append(q)
                gap.append(rq)
                active.append(len(pts) - 1)
    return pts


def clip(poly, a, b, j):
    """The half of a labelled polygon nearer site a than site b; the cut edge gets label j."""
    m, n = mid(a, b), (b[0] - a[0], b[1] - a[1])
    side = lambda p: (p[0] - m[0]) * n[0] + (p[1] - m[1]) * n[1]
    out = []
    for k, (p, label) in enumerate(poly):
        q = poly[(k + 1) % len(poly)][0]
        sp, sq = side(p), side(q)
        cut = lambda: (p[0] + sp / (sp - sq) * (q[0] - p[0]), p[1] + sp / (sp - sq) * (q[1] - p[1]))
        if sp <= 0:
            out.append((p, label))
            if sq > 0:
                out.append((cut(), j))
        elif sq <= 0:
            out.append((cut(), label))
    return out


def voronoi_cell(i, sites):
    """Cell of site i as [(vertex, neighbour across the edge to the next vertex)]."""
    poly = [(p, -1) for p in [(-90, -90), (W + 90, -90), (W + 90, H + 90), (-90, H + 90)]]
    for j, s in enumerate(sites):
        if j != i and math.dist(s, sites[i]) < 180:
            poly = clip(poly, sites[i], s, j)
    return poly


class Vertices:
    """Snap the same Voronoi vertex, computed from different cells, to one id."""

    def __init__(self):
        self.pts, self.grid = [], {}

    def id(self, p):
        gx, gy = round(p[0]), round(p[1])
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                for k in self.grid.get((gx + dx, gy + dy), ()):
                    if math.dist(self.pts[k], p) < 1e-3:
                        return k
        self.pts.append(p)
        self.grid.setdefault((gx, gy), []).append(len(self.pts) - 1)
        return len(self.pts) - 1


def wobble(p, q, seed, amp, depth):
    """Midpoint displacement: a hand-drawn border between two mesh vertices."""
    r = random.Random(seed)
    pts = [p, q]
    for _ in range(depth):
        new = [pts[0]]
        for a, b in zip(pts, pts[1:]):
            length = math.dist(a, b)
            off = r.gauss(0, amp * length)
            m = mid(a, b)
            new += [(m[0] + (a[1] - b[1]) / length * off, m[1] + (b[0] - a[0]) / length * off), b]
        pts = new
    return pts


def smooth(pts):
    """Path commands from pts[0] to pts[-1]; read backwards they trace the same curve."""
    if len(pts) == 2:
        return f"L{pt(pts[1])}"
    ms = [mid(a, b) for a, b in zip(pts, pts[1:])]
    return (f"L{pt(ms[0])}" + "".join(f"Q{pt(pts[k])} {pt(ms[k])}" for k in range(1, len(pts) - 1))
            + f"L{pt(pts[-1])}")


def through(points):
    """Catmull-Rom curve through points, as cubic Bézier commands."""
    P = [points[0], *points, points[-1]]
    out = ""
    for k in range(1, len(P) - 2):
        p0, p1, p2, p3 = P[k - 1:k + 3]
        b1 = (p1[0] + (p2[0] - p0[0]) / 6, p1[1] + (p2[1] - p0[1]) / 6)
        b2 = (p2[0] - (p3[0] - p1[0]) / 6, p2[1] - (p3[1] - p1[1]) / 6)
        out += f"C{pt(b1)} {pt(b2)} {pt(p2)}"
    return out


def centroid(poly):
    a = cx = cy = 0.0
    for p, q in zip(poly, poly[1:] + poly[:1]):
        c = p[0] * q[1] - q[0] * p[1]
        a, cx, cy = a + c, cx + (p[0] + q[0]) * c, cy + (p[1] + q[1]) * c
    return cx / (3 * a), cy / (3 * a)


def tint(pal, t):
    lo, hi, u = (pal[0], pal[1], t / .5) if t < .5 else (pal[1], pal[2], (t - .5) / .5)
    return "#" + "".join(f"{round(a + (b - a) * u):02x}" for a, b in zip(lo, hi))


def waterline_table():
    """Alpha transfer turning the blurred land into four shore contours, fading seaward."""
    rings = [(.36, .024, .5), (.22, .018, .36), (.12, .0125, .24), (.055, .008, .13)]
    vals = [max(h * max(0, 1 - abs(k / 400 - lvl) / hw) for lvl, hw, h in rings) for k in range(401)]
    return " ".join(f"{v:.3f}".rstrip("0").rstrip(".") if v else "0" for v in vals)


STYLE = """
    :root { --paper:#f5efe3; --ink:#3a332b; --seal:#b3372c; --wet:#3c679f; --shade:#6b5236; --shade-a:.1; }
    .paper { fill:var(--paper); }
    .flood { fill:var(--c); transform-box:fill-box; transform-origin:center;
             animation:flood 1.5s cubic-bezier(.2,.7,.25,1) backwards, dry 5.5s ease-out backwards; }
    .landcell { fill:var(--ink); animation:fade 1.2s ease-out backwards; }
    .border { fill:none; stroke:var(--ink); stroke-width:1.1; stroke-linecap:round; stroke-dasharray:0 3.4;
              opacity:.45; animation:fade 1.2s ease-out backwards; }
    .coast { fill:none; stroke:var(--ink); stroke-width:1.2; stroke-linecap:round; stroke-linejoin:round;
             opacity:.72; stroke-dasharray:1 2; animation:draw 1.2s ease-in-out backwards; }
    .route { fill:none; stroke:var(--seal); stroke-linecap:round; opacity:.5; stroke-dasharray:1 2;
             animation:draw .6s ease-out backwards; }
    .capital { fill:none; stroke:var(--seal); stroke-width:1.2; }
    .source { fill:var(--seal); }
    .ripple { fill:none; stroke:var(--seal); stroke-width:.8; opacity:0; transform-box:fill-box;
              transform-origin:center; animation:ripple 7s ease-out .4s infinite; }
    .spark { fill:var(--seal); }
    .title { fill:var(--ink); font:400 38px "Iowan Old Style", Palatino, "Palatino Linotype", "Book Antiqua", Georgia, serif;
             letter-spacing:.035em; }
    .rule { stroke:var(--ink); stroke-width:.6; opacity:.5; }
    .zh { fill:var(--ink); font:400 14px "Songti SC", STSong, "Noto Serif CJK SC", "Source Han Serif SC", serif;
          letter-spacing:.42em; opacity:.82; }
    .en { fill:var(--ink); font:italic 400 12px "Iowan Old Style", Palatino, Georgia, serif; letter-spacing:.08em; opacity:.62; }
    .note { fill:var(--ink); font:400 12px "Songti SC", STSong, "Noto Serif CJK SC", serif; letter-spacing:.7em; opacity:.4; }
    .note-en { fill:var(--ink); font:italic 400 10.5px "Iowan Old Style", Palatino, Georgia, serif;
               letter-spacing:.12em; opacity:.36; }
    .seal rect { fill:var(--seal); }
    .seal text { fill:var(--paper); font:400 18px "Songti SC", STSong, "Noto Serif CJK SC", serif; }
    .later { animation:fade 2s ease-out backwards; }
    @keyframes flood { from { transform:scale(0); } }
    @keyframes dry { 0% { fill:var(--wet); opacity:.72; } }
    @keyframes fade { from { opacity:0; } }
    @keyframes draw { from { stroke-dashoffset:1; } }
    @keyframes ripple { 0% { transform:scale(.25); opacity:.5; } 60%, 100% { transform:scale(1); opacity:0; } }
    @media (prefers-color-scheme: dark) {
      :root { --paper:#15171a; --ink:#dcd3c2; --seal:#d4564a; --wet:#8cb4e6; --shade:#000; --shade-a:.45; }
      .flood { fill:var(--cd); }
    }
    @media (prefers-reduced-motion: reduce) { * { animation:none !important; } .spark { display:none; } }
"""


def main():
    sites = poisson()
    land = {i for i, s in enumerate(sites) if in_land(*s)}
    V = Vertices()
    rings = {}
    for i in land:
        ring = []
        for p, label in voronoi_cell(i, sites):
            v = V.id(p)
            if ring and ring[-1][0] == v:  # zero-length edge: the vertex keeps the later edge
                ring[-1] = (v, label)
            else:
                ring.append((v, label))
        if ring[0][0] == ring[-1][0]:
            ring.pop()
        rings[i] = ring
    borders_of = {i: {label: (a, rings[i][(k + 1) % len(rings[i])][0])
                      for k, (a, label) in enumerate(rings[i]) if label >= 0} for i in land}

    def border_len(i, j):
        a, b = borders_of[i][j]
        return math.dist(V.pts[a], V.pts[b])

    # Grow from the source: a territory joins only across a border with one already grown.
    root = 0
    parent, order, seen = {root: None}, [], {root}
    heap = [(0.0, root)]
    while heap:
        _, i = heapq.heappop(heap)
        order.append(i)
        for j in sorted(borders_of[i]):
            if j in land and j not in seen and i in borders_of[j] and border_len(i, j) > 6:
                seen.add(j)
                parent[j] = i
                heapq.heappush(heap, (math.dist(sites[j], SOURCE) * rng.uniform(.82, 1.22), j))
    grown = set(order)

    lines = {}

    def border(a, b, coast):
        """One wobbled line per mesh edge, shared by the territories on both sides."""
        key = (min(a, b), max(a, b))
        if key not in lines:
            p, q = V.pts[key[0]], V.pts[key[1]]
            length = math.dist(p, q)
            seed = key[0] * 7919 + key[1]
            if length < 5:
                lines[key] = [p, q]
            elif coast:
                lines[key] = wobble(p, q, seed, .16, 3 if length > 24 else 2)
            else:
                lines[key] = wobble(p, q, seed, .11, 2)
        return lines[key] if a == key[0] else lines[key][::-1]

    def outline(i):
        ring = rings[i]
        d = f"M{pt(V.pts[ring[0][0]])}"
        for k, (a, label) in enumerate(ring):
            d += smooth(border(a, ring[(k + 1) % len(ring)][0], label not in grown))
        return d + "Z"

    centre = {i: centroid([V.pts[v] for v, _ in rings[i]]) for i in order}
    centre[root] = SOURCE
    glue, depth = {root: SOURCE}, {root: 0}
    for i in order[1:]:
        pts = border(*borders_of[i][parent[i]], False)
        k = (len(pts) - 2) // 2
        glue[i] = mid(pts[k], pts[k + 1])
        depth[i] = depth[parent[i]] + 1

    n = len(order)
    when, age = {}, {}
    for k, i in enumerate(order):
        t = 1.1 + 7.6 * (k / (n - 1)) ** 1.12 + rng.uniform(-.06, .06)
        when[i] = t if parent[i] is None else max(t, when[parent[i]] + .35)
        age[i] = k / (n - 1)

    defs, washes, landcells, routes = [], [], [], []
    for i in order:
        t, a, g = when[i], age[i], glue[i]
        defs.append(f'<path id="c{i}" d="{outline(i)}"/>')
        defs.append(f'<clipPath id="k{i}"><use href="#c{i}"/></clipPath>')
        reach = max(math.dist(g, V.pts[v]) for v, _ in rings[i]) + 8
        washes.append(
            f'<g filter="url(#pigment)"><g clip-path="url(#k{i})"><circle class="flood" '
            f'cx="{g[0]:.1f}" cy="{g[1]:.1f}" r="{reach:.0f}" style="--c:{tint(LIGHT, a)};--cd:{tint(DARK, a)};'
            f'opacity:{.17 + .2 * a ** 1.4:.2f};animation-delay:{t - .15:.2f}s,{t - .15:.2f}s"/></g></g>')
        landcells.append(f'<use href="#c{i}" class="landcell" style="animation-delay:{t:.2f}s"/>')
        if parent[i] is not None:
            p = centre[parent[i]]
            routes.append(f'<path class="route" pathLength="1" style="stroke-width:{.4 + 1.1 * .85 ** depth[i]:.2f};'
                          f'animation-delay:{t - .5:.2f}s" d="M{pt(p)}{through([p, g, centre[i]])}"/>')

    inks, coasts, done = [], [], set()
    for i in order:
        ring = rings[i]
        for k, (a, label) in enumerate(ring):
            b = ring[(k + 1) % len(ring)][0]
            key = (min(a, b), max(a, b))
            if key in done:
                continue
            done.add(key)
            pts = border(a, b, label not in grown)
            d = f"M{pt(pts[0])}{smooth(pts)}"
            if label in grown:  # a border exists once both of its sides do
                inks.append(f'<path class="border" style="animation-delay:{max(when[i], when[label]) + .35:.2f}s" d="{d}"/>')
            else:
                coasts.append(f'<path class="coast" pathLength="1" style="animation-delay:{when[i] + .1:.2f}s" d="{d}"/>')

    # A recollection: light walks the route from the source to a young far territory.
    tip = max(order[int(n * .7):], key=lambda i: math.dist(centre[i], SOURCE))
    chain = []
    while parent[tip] is not None:
        chain.append(tip)
        tip = parent[tip]
    walk = f"M{pt(SOURCE)}" + "".join(through([centre[parent[i]], glue[i], centre[i]]) for i in reversed(chain))
    last = max(when.values())
    begin = last + 3

    join = lambda items: "\n    ".join(items)
    svg = f'''<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" role="img" aria-labelledby="t d">
  <title id="t">H0mework · 未干的地图</title>
  <desc id="d">An unfinished map grows from a single source. Each territory joins only across a border it shares with one already drawn, and its colour floods in from that border; a vermilion route records where it grew from. Old territories have dried to ochre, the newest are still wet, and the sea beyond the frontier has not happened yet.</desc>
  <style>{STYLE}  </style>
  <defs>
    <filter id="pigment" x="-30%" y="-30%" width="160%" height="160%" color-interpolation-filters="sRGB">
      <feTurbulence type="fractalNoise" baseFrequency=".028" numOctaves="3" seed="11" result="n"/>
      <feDisplacementMap in="SourceGraphic" in2="n" scale="7" xChannelSelector="R" yChannelSelector="G" result="d"/>
      <feGaussianBlur in="d" stdDeviation=".9" result="s"/>
      <feGaussianBlur in="d" stdDeviation="4.5" result="w"/>
      <feComposite in="s" in2="w" operator="arithmetic" k2="1.7" k3="-.7" result="rim"/>
      <feTurbulence type="fractalNoise" baseFrequency=".85" numOctaves="1" seed="5" result="g"/>
      <feColorMatrix in="g" type="matrix" values="0 0 0 0 0  0 0 0 0 0  0 0 0 0 0  -.7 0 0 0 1.25" result="grain"/>
      <feComposite in="rim" in2="grain" operator="in"/>
    </filter>
    <filter id="waterlines" x="-6%" y="-20%" width="112%" height="140%" color-interpolation-filters="sRGB">
      <feGaussianBlur in="SourceGraphic" stdDeviation="8"/>
      <feComponentTransfer><feFuncA type="table" tableValues="{waterline_table()}"/></feComponentTransfer>
    </filter>
    <filter id="paper" x="0" y="0" width="100%" height="100%">
      <feTurbulence type="fractalNoise" baseFrequency=".8" numOctaves="2" seed="4" result="n"/>
      <feColorMatrix in="n" type="matrix" values="0 0 0 0 .35  0 0 0 0 .28  0 0 0 0 .2  -.5 0 0 0 .3"/>
      <feComposite in2="SourceGraphic" operator="in"/>
    </filter>
    <radialGradient id="vignette" cx="50%" cy="50%" r="72%">
      <stop offset=".55" style="stop-color:var(--shade);stop-opacity:0"/>
      <stop offset="1" style="stop-color:var(--shade);stop-opacity:var(--shade-a)"/>
    </radialGradient>
    {join(defs)}
  </defs>

  <rect class="paper" width="{W}" height="{H}" rx="14"/>
  <rect width="{W}" height="{H}" rx="14" filter="url(#paper)"/>

  <g filter="url(#waterlines)">
    {join(landcells)}
  </g>
  <g>
    {join(washes)}
  </g>
  <g>
    {join(inks)}
  </g>
  <g>
    {join(coasts)}
  </g>
  <g>
    {join(routes)}
  </g>

  <g class="later" style="animation-delay:.3s">
    <circle class="ripple" cx="{SOURCE[0]}" cy="{SOURCE[1]}" r="30"/>
    <circle class="capital" cx="{SOURCE[0]}" cy="{SOURCE[1]}" r="5.5"/>
    <circle class="source" cx="{SOURCE[0]}" cy="{SOURCE[1]}" r="2.3"/>
  </g>

  <circle class="spark" r="2.1" opacity="0">
    <animateMotion id="walk" dur="6s" begin="{begin:.1f}s;walk.end+10s" path="{walk}" calcMode="spline" keyPoints="0;1" keyTimes="0;1" keySplines=".4 0 .5 1"/>
    <animate attributeName="opacity" values="0;.95;.95;0" keyTimes="0;.08;.9;1" dur="6s" begin="{begin:.1f}s;walk.end+10s"/>
  </circle>

  <g class="later" style="animation-delay:{last + .8:.1f}s">
    <text class="note" x="808" y="84" text-anchor="middle">尚未发生</text>
    <text class="note-en" x="808" y="102" text-anchor="middle">not yet happened</text>
  </g>

  <g class="later" style="animation-delay:{min(last, 6.5):.1f}s">
    <text class="title" x="700" y="216">H0mework</text>
    <line class="rule" x1="701" y1="232" x2="926" y2="232"/>
    <text class="zh" x="701" y="254">未干的地图</text>
    <text class="en" x="701" y="272">The Unfinished Map</text>
    <g class="seal" transform="translate(894 242) rotate(-4)">
      <rect width="28" height="28" rx="2.5"/>
      <text x="14" y="20" text-anchor="middle">源</text>
    </g>
  </g>

  <rect width="{W}" height="{H}" rx="14" fill="url(#vignette)"/>
</svg>
'''
    out = Path(__file__).with_name("banner.svg")
    out.write_text(svg)
    print(f"{out.name}: {n} territories, grown in {last:.1f}s, {len(svg) // 1024} KB")


if __name__ == "__main__":
    main()
