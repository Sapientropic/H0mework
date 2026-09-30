#!/usr/bin/env python3
"""Draw docs/assets/banner.svg: an unfinished map grown from the zero of H0mework.

Read left to right, the banner is a timeline. The name is set first, letter by
letter, leaving a gap; the zero is then painted into it as a vermilion brush
circle, the source. A brush line runs out of the zero, under the name and
across the water, and where it touches land a drop falls and the map begins.

A territory joins the map only against one already there, across the border
they share, and its colour spreads in from that border. A border is inked only
once both of its sides exist; the coast is inked as each shore appears. The
vermilion brush tree records where every territory grew from, broad where much
has grown from it and lifting to a point at the youngest tips. Early
territories have dried to ochre, the newest are still wet indigo. At the far
edge stands an inscription, 尚未发生 (not yet happened), sealed with 源.

The Voronoi mesh underneath never shows: every border is wobbled once and
shared by both sides, the washes bleed softly into each other, and the
waterlines are contours of the land. All lettering is converted to outlines
from SIL OFL fonts, IM Fell English (in TeX Live) and Noto Serif CJK SC, so the
banner looks the same wherever it is shown; the seal glyph is drawn by hand in
a squared Han-seal style.

Usage: python3 docs/assets/banner.py   (deterministic; rewrites banner.svg)
"""
from __future__ import annotations

import heapq
import math
import random
import subprocess
from pathlib import Path

from fontTools.pens.basePen import BasePen
from fontTools.pens.boundsPen import BoundsPen
from fontTools.ttLib import TTFont

W, H = 960, 300
SOURCE = (478.0, 152.0)
rng = random.Random(20260930)

# Pigment by age: dried ochre at the source, sage, still-wet indigo at the frontier.
LIGHT = [(192, 160, 106), (142, 162, 128), (66, 100, 148)]
DARK = [(180, 150, 102), (128, 158, 134), (116, 156, 208)]

# 源 in a squared Han-seal style, glyph box 0..100, drawn as white strokes. The
# water radical is the seal-script 水: a flowing centre line flanked by broken
# strokes. 原 keeps its old sense, a spring (白 over 小) issuing under a cliff (厂).
SEAL_GLYPH = [
    "M19 4C19 18 22 28 19 40C17 52 17 62 19 74C21 84 19 92 19 97",
    "M8 9C5 16 3 24 4 36",
    "M8 50C5 58 3 72 4 90",
    "M30 9C33 16 35 24 34 36",
    "M30 50C33 58 35 72 34 90",
    "M44 6H97",
    "M47 6V60C47 78 45 90 41 97",
    "M74 6V18",
    "M58 18H90V50H58Z",
    "M58 34H90",
    "M74 50C74 64 77 72 74 84C72 90 74 94 74 97",
    "M64 60C60 70 57 80 56 94",
    "M84 60C88 70 91 80 92 94",
]


def pt(p):
    return f"{p[0]:.1f} {p[1]:.1f}"


def mid(a, b):
    return ((a[0] + b[0]) / 2, (a[1] + b[1]) / 2)


# --- lettering ---------------------------------------------------------------

def find_font(name):
    """A font file by name: TeX Live first, then the usual font folders."""
    try:
        hit = subprocess.run(["kpsewhich", name], capture_output=True, text=True).stdout.strip()
        if hit:
            return hit
    except FileNotFoundError:
        pass
    for folder in ["~/Library/Fonts", "/Library/Fonts", "/usr/share/fonts", "/usr/local/share/fonts"]:
        for p in Path(folder).expanduser().rglob(name):
            return str(p)
    raise SystemExit(f"font {name} not found: IM Fell English ships with TeX Live, Noto Serif CJK SC with Noto")


class FlatPen(BasePen):
    """Glyph contours flattened to points about `step` font units apart."""

    def __init__(self, glyphs, step):
        super().__init__(glyphs)
        self.step, self.contours = step, []

    def _moveTo(self, p):
        self.contours.append([p])

    def _lineTo(self, p):
        self.contours[-1].append(p)

    def _curve(self, ctrl, at):
        n = max(2, int(sum(math.dist(a, b) for a, b in zip(ctrl, ctrl[1:])) / self.step))
        self.contours[-1] += [at(k / n) for k in range(1, n + 1)]

    def _curveToOne(self, p1, p2, p3):
        p0 = self._getCurrentPoint()
        self._curve([p0, p1, p2, p3], lambda t: tuple(
            (1 - t) ** 3 * a + 3 * (1 - t) ** 2 * t * b + 3 * (1 - t) * t * t * c + t ** 3 * d
            for a, b, c, d in zip(p0, p1, p2, p3)))

    def _qCurveToOne(self, p1, p2):
        p0 = self._getCurrentPoint()
        self._curve([p0, p1, p2], lambda t: tuple(
            (1 - t) ** 2 * a + 2 * (1 - t) * t * b + t * t * c for a, b, c in zip(p0, p1, p2)))

    def _closePath(self):
        pass

    def _endPath(self):
        pass


def simplify(pts, eps):
    """Ramer-Douglas-Peucker: drop points closer than eps to the line through their neighbours."""
    if len(pts) < 3:
        return pts
    a, b = pts[0], pts[-1]
    ab = math.dist(a, b) or 1e-9
    far, idx = 0.0, 0
    for k in range(1, len(pts) - 1):
        p = pts[k]
        d = abs((b[0] - a[0]) * (a[1] - p[1]) - (a[0] - p[0]) * (b[1] - a[1])) / ab
        if d > far:
            far, idx = d, k
    if far <= eps:
        return [a, b]
    return simplify(pts[:idx + 1], eps)[:-1] + simplify(pts[idx:], eps)


def num(v):
    s = f"{v:.1f}".rstrip("0").rstrip(".")
    return s.replace("0.", ".", 1) if s.startswith(("0.", "-0.")) else s or "0"


def compact(contours):
    """Closed polygons as a short path with relative moves."""
    out, last = [], (0.0, 0.0)
    for c in contours:
        c = [(round(x, 1), round(y, 1)) for x, y in c]
        out.append(f"m{num(c[0][0] - last[0])} {num(c[0][1] - last[1])}")
        steps = []
        for p, q in zip(c, c[1:]):
            dx, dy = q[0] - p[0], q[1] - p[1]
            if dx or dy:
                steps.append(f"{num(dx)} {num(dy)}")
        out.append("l" + " ".join(steps) + "z")
        last = c[0]
    return "".join(out).replace(" -", "-")


class Face:
    def __init__(self, name):
        self.font = TTFont(find_font(name))
        self.glyphs = self.font.getGlyphSet()
        self.cmap = self.font.getBestCmap()
        self.upm = self.font["head"].unitsPerEm

    def glyph(self, ch, size, x, y):
        """Outline of one character with its pen at (x, y), and its advance. Contours
        are flattened and thinned to a tenth of a pixel at this size: the inked edges of
        the Fell types carry far more points than a banner can show."""
        g, s = self.glyphs[self.cmap[ord(ch)]], size / self.upm
        pen = FlatPen(self.glyphs, .3 / s)
        g.draw(pen)
        contours = []
        for c in pen.contours:
            # a closed contour starts and ends on the same point: cut it at the point
            # farthest from the start, so each half has a real chord to simplify against
            far = max(range(len(c)), key=lambda k: math.dist(c[0], c[k]))
            thin = simplify(c[:far + 1], .1 / s)[:-1] + simplify(c[far:] + c[:1], .1 / s)
            contours.append([(x + px * s, y - py * s) for px, py in thin])
        return compact(contours), g.width * s

    def line(self, text, size, x, y, tracking=0.0):
        outs = []
        for ch in text:
            d, adv = self.glyph(ch, size, x, y)
            if d:
                outs.append(d)
            x += adv + tracking
        return outs, x

    def cap_height(self, size):
        pen = BoundsPen(self.glyphs)
        self.glyphs[self.cmap[ord("H")]].draw(pen)
        return pen.bounds[3] * size / self.upm


# --- geometry ----------------------------------------------------------------

def in_land(x, y):
    """The continent the map may grow into, right of the name and left of the inscription."""
    a = math.atan2(y - 150, x - 630)
    wobble = 1 + .16 * math.sin(3 * a + .7) + .09 * math.sin(7 * a + 2.1) + .05 * math.sin(13 * a)
    return ((x - 630) / 205) ** 2 + ((y - 150) / 104) ** 2 < wobble ** 2


def spacing(x, y):
    """Territories are broad near the source and finer toward the frontier."""
    t = min(1, max(0, (x - SOURCE[0]) / 380))
    return 40 - 12 * t + 3 * math.sin(x * .031 + 1.1) * math.cos(y * .043 - .6)


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
    """Midpoint displacement: a hand-drawn line between two fixed points."""
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


def cr_open(P):
    """Catmull-Rom segments from P[1] to P[-2]; the end points only steer the tangents."""
    segs = []
    for k in range(1, len(P) - 2):
        p0, p1, p2, p3 = P[k - 1:k + 3]
        b1 = (p1[0] + (p2[0] - p0[0]) / 6, p1[1] + (p2[1] - p0[1]) / 6)
        b2 = (p2[0] - (p3[0] - p1[0]) / 6, p2[1] - (p3[1] - p1[1]) / 6)
        segs.append((p1, b1, b2, p2))
    return segs


def curve(segs):
    return "".join(f"C{pt(b1)} {pt(b2)} {pt(p2)}" for _, b1, b2, p2 in segs)


def sample(segs, per_segment=8):
    out = []
    for p0, p1, p2, p3 in segs:
        for k in range(per_segment):
            t = k / per_segment
            u = 1 - t
            out.append(tuple(u ** 3 * a + 3 * u * u * t * b + 3 * u * t * t * c + t ** 3 * d
                             for a, b, c, d in zip(p0, p1, p2, p3)))
    out.append(segs[-1][3])
    return out


def offset(pts, k, d):
    """Unit normal of a polyline at point k, scaled by d."""
    a, b = pts[max(0, k - 1)], pts[min(len(pts) - 1, k + 1)]
    dx, dy = b[0] - a[0], b[1] - a[1]
    length = math.hypot(dx, dy) or 1
    return -dy / length * d, dx / length * d


def ribbon(pts, widths):
    """Outline of a brush stroke along pts with the given widths."""
    left, right = [], []
    for k, p in enumerate(pts):
        nx, ny = offset(pts, k, widths[k] / 2)
        left.append((p[0] + nx, p[1] + ny))
        right.append((p[0] - nx, p[1] - ny))
    return "M" + " L".join(pt(p) for p in left + right[::-1]) + "Z"


def polyline(pts):
    return "M" + " L".join(pt(p) for p in pts)


def enso(c, r, seed=5):
    """The zero: a brush circle pressed hard at the start, lifting and running dry at the end."""
    rnd = random.Random(seed)
    ph = rnd.uniform(0, 2 * math.pi)
    n, start, sweep = 120, -2.25, 5.95
    pts, widths = [], []
    for k in range(n + 1):
        t, a = k / n, start + sweep * k / n
        rr = r * (1 + .035 * math.sin(2 * a + ph) + .02 * math.sin(3 * a + 1.3))
        pts.append((c[0] + rr * math.cos(a), c[1] + rr * math.sin(a)))
        widths.append(max(.5, r * .31 * min(1, t / .05) ** .5 * (1 - .82 * max(0, (t - .5) / .5) ** 1.4)))
    # dry brush: hairline gaps where the bristles ran out of ink along the tail
    dry = []
    for f in (-.3, .08, .34):
        tail = [(p[0] + offset(pts, k, f * widths[k])[0], p[1] + offset(pts, k, f * widths[k])[1])
                for k, p in enumerate(pts) if k > .58 * n]
        dry.append(polyline(tail))
    return pts, widths, dry


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


def seal_outline(size=116, corner=7):
    """A square block with slightly uneven sides and softened corners."""
    c = [(0, 0), (size, 0), (size, size), (0, size)]
    d = ""
    for k in range(4):
        a, b, nxt = c[k], c[(k + 1) % 4], c[(k + 2) % 4]
        ux, uy = (b[0] - a[0]) / size, (b[1] - a[1]) / size
        vx, vy = (nxt[0] - b[0]) / size, (nxt[1] - b[1]) / size
        start = (a[0] + ux * corner, a[1] + uy * corner)
        end = (b[0] - ux * corner, b[1] - uy * corner)
        side = wobble(start, end, 400 + k, .004, 3)
        d += (f"M{pt(start)}" if k == 0 else "") + smooth(side)
        d += f"Q{pt(b)} {pt((b[0] + vx * corner, b[1] + vy * corner))}"
    return d + "Z"


def bbox(pts, pad):
    xs, ys = [p[0] for p in pts], [p[1] for p in pts]
    return min(xs) - pad, min(ys) - pad, max(xs) - min(xs) + 2 * pad, max(ys) - min(ys) + 2 * pad


STYLE = """
    :root { --paper:#f5efe3; --ink:#3a332b; --seal:#b3372c; --seal-ink:#b0302a; --wet:#3c679f;
            --shade:#6b5236; --shade-a:.1; }
    .paper { fill:var(--paper); }
    .type { fill:var(--ink); transform-box:fill-box; transform-origin:50% 100%;
            animation:land .55s cubic-bezier(.2,.8,.3,1) backwards; }
    .caption { fill:var(--ink); }
    .vermilion { fill:var(--seal); }
    .reveal { fill:none; stroke:#fff; stroke-linecap:round; stroke-linejoin:round; stroke-dasharray:1 2;
              animation:draw 1s cubic-bezier(.45,.05,.4,1) backwards; }
    .flood { fill:var(--c); transform-box:fill-box; transform-origin:center;
             animation:flood 1.8s cubic-bezier(.2,.7,.25,1) backwards, dry 5.5s ease-out backwards; }
    .landcell { fill:var(--ink); animation:fade 1.2s ease-out backwards; }
    .border { fill:none; stroke:var(--ink); stroke-width:1.1; stroke-linecap:round; stroke-dasharray:0 3.4;
              opacity:.42; animation:fade 1.2s ease-out backwards; }
    .coast { fill:none; stroke:var(--ink); stroke-width:1.2; stroke-linecap:round; stroke-linejoin:round;
             opacity:.72; stroke-dasharray:1 2; animation:draw 1.2s ease-in-out backwards; }
    .brush path { fill:none; stroke:var(--seal); stroke-linecap:round; stroke-linejoin:round;
                  stroke-dasharray:1 2; animation:draw .14s linear backwards; }
    .blot { fill:var(--seal); transform-box:fill-box; transform-origin:center;
            animation:drop .5s cubic-bezier(.3,1.6,.5,1) backwards; }
    .bleed { fill:var(--seal); opacity:.2; animation:fade 1.5s ease-out backwards; }
    .ripple { fill:none; stroke:var(--seal); stroke-width:.9; opacity:0; transform-box:fill-box;
              transform-origin:center; animation:ripple 7s ease-out infinite; }
    .glint { fill:none; stroke:var(--seal); stroke-linecap:round; stroke-dasharray:.03 2; stroke-dashoffset:.03;
             opacity:0; animation:glint 16s ease-in-out infinite; }
    .sealink { fill:var(--seal-ink); }
    .stamp { transform-box:fill-box; transform-origin:center; animation:stamp .45s cubic-bezier(.3,0,.2,1) backwards; }
    .later { animation:fade 2s ease-out backwards; }
    @keyframes land { from { opacity:0; transform:translateY(-7px) scale(1.05); } }
    @keyframes flood { from { transform:scale(0); } }
    @keyframes dry { 0% { fill:var(--wet); opacity:.72; } }
    @keyframes fade { from { opacity:0; } }
    @keyframes draw { from { stroke-dashoffset:1; } }
    @keyframes drop { from { transform:scale(0); } }
    @keyframes ripple { 0% { transform:scale(.3); opacity:.4; } 60%, 100% { transform:scale(1); opacity:0; } }
    @keyframes glint { 0% { stroke-dashoffset:.03; opacity:0; } 4%, 34% { opacity:1; }
                       38%, 100% { stroke-dashoffset:-1; opacity:0; } }
    @keyframes stamp { 0% { transform:scale(1.35); opacity:0; } 70% { transform:scale(.97); opacity:1; } }
    @media (prefers-color-scheme: dark) {
      :root { --paper:#15171a; --ink:#dcd3c2; --seal:#d4564a; --seal-ink:#c9463a; --wet:#8cb4e6;
              --shade:#000; --shade-a:.45; }
      .flood { fill:var(--cd); }
    }
    @media (prefers-reduced-motion: reduce) { * { animation:none !important; } .glint { display:none; } }
"""


def main():
    # --- the name, with a gap where the zero will be painted -----------------
    fell, fell_it = Face("IMFeENrm28P.otf"), Face("IMFeENit28P.otf")
    song, song_light = Face("NotoSerifCJKsc-Regular.otf"), Face("NotoSerifCJKsc-Light.otf")
    size, base, x = 62, 140, 46
    cap = fell.cap_height(size)
    letters = []
    d, adv = fell.glyph("H", size, x, base)
    letters.append(d)
    x += adv
    r0 = cap * .52
    zero = (x + r0 * 1.1, base - cap / 2)
    x = zero[0] + r0 * 1.24
    for ch in "mework":
        d, adv = fell.glyph(ch, size, x, base)
        letters.append(d)
        x += adv
    name_end = x

    t_zero, d_zero = 1.0, .85
    t_swash, d_swash = t_zero + d_zero - .1, 1.05
    t_drop = t_swash + d_swash - .05
    t_grow = t_drop + .15

    ring, ring_w, dry = enso(zero, r0)
    a0 = 1.05
    start = (zero[0] + r0 * math.cos(a0), zero[1] + r0 * math.sin(a0))
    way = [start, (zero[0] + r0 + 24, base + 13), (name_end - 70, base + 19), (name_end + 6, base + 13),
           (SOURCE[0] - 44, SOURCE[1] + 7), SOURCE]
    swash_segs = cr_open([way[0], *way, way[-1]])
    swash = sample(swash_segs, 14)
    m = len(swash) - 1
    swash_w = [.45 + 1.75 * min(1, (k / m) / .22) ** .7 - .45 * max(0, (k / m - .7) / .3) for k in range(m + 1)]

    # --- the map ---------------------------------------------------------------
    sites = poisson()
    land = {i for i, s in enumerate(sites) if in_land(*s)}
    V = Vertices()
    rings = {}
    for i in land:
        cell = []
        for p, label in voronoi_cell(i, sites):
            v = V.id(p)
            if cell and cell[-1][0] == v:  # zero-length edge: the vertex keeps the later edge
                cell[-1] = (v, label)
            else:
                cell.append((v, label))
        if cell[0][0] == cell[-1][0]:
            cell.pop()
        rings[i] = cell
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
        cell = rings[i]
        d = f"M{pt(V.pts[cell[0][0]])}"
        for k, (a, label) in enumerate(cell):
            d += smooth(border(a, cell[(k + 1) % len(cell)][0], label not in grown))
        return d + "Z"

    centre = {i: centroid([V.pts[v] for v, _ in rings[i]]) for i in order}
    centre[root] = SOURCE
    glue, depth = {root: SOURCE}, {root: 0}
    for i in order[1:]:
        pts = border(*borders_of[i][parent[i]], False)
        k = (len(pts) - 2) // 2
        glue[i] = mid(pts[k], pts[k + 1])
        depth[i] = depth[parent[i]] + 1

    # How much has grown out of each territory: the brush is broad where much depends on it.
    grew = {i: 1 for i in order}
    for i in reversed(order[1:]):
        grew[parent[i]] += grew[i]
    heir = {}
    for i in order[1:]:
        if parent[i] not in heir or grew[i] > grew[heir[parent[i]]]:
            heir[parent[i]] = i

    # Where the brush passes through a territory: pulled from its centre toward the
    # borders it enters and leaves by, so a main line bends instead of kinking.
    node = {root: SOURCE}
    for i in order[1:]:
        c, g = centre[i], glue[i]
        if i in heir:
            h = glue[heir[i]]
            node[i] = (.4 * c[0] + .3 * g[0] + .3 * h[0], .4 * c[1] + .3 * g[1] + .3 * h[1])
        else:
            node[i] = c

    def mirror(a, b):
        return (2 * a[0] - b[0], 2 * a[1] - b[1])

    def branch(i):
        """Stroke from the parent through the shared border into i. Its tangent at the
        parent follows the parent's own stroke (the swash, for the source), and at i it
        heads for i's heaviest child, so a main line reads as one brush movement."""
        p, g, c = node[parent[i]], glue[i], node[i]
        before = glue[parent[i]] if parent[i] != root else way[-2]
        after = glue[heir[i]] if i in heir else mirror(c, g)
        return cr_open([before, p, g, c, after])

    n = len(order)
    when, age = {}, {}
    for k, i in enumerate(order):
        t = t_grow + 6.4 * (k / (n - 1)) ** 1.1 + rng.uniform(-.05, .05)
        when[i] = t if parent[i] is None else max(t, when[parent[i]] + .3)
        age[i] = k / (n - 1)
    last = max(when.values())

    defs, washes, landcells, brush = [], [], [], []
    for i in order:
        t, a, g = when[i], age[i], glue[i]
        defs.append(f'<path id="c{i}" d="{outline(i)}"/>')
        defs.append(f'<clipPath id="k{i}"><use href="#c{i}"/></clipPath>')
        reach = max(math.dist(g, V.pts[v]) for v, _ in rings[i]) + 8
        washes.append(
            f'<g clip-path="url(#k{i})"><circle class="flood" cx="{g[0]:.1f}" cy="{g[1]:.1f}" r="{reach:.0f}" '
            f'style="--c:{tint(LIGHT, a)};--cd:{tint(DARK, a)};opacity:{.17 + .2 * a ** 1.4:.2f};'
            f'animation-delay:{t - .15:.2f}s,{t - .15:.2f}s"/></g>')
        landcells.append(f'<use href="#c{i}" class="landcell" style="animation-delay:{t:.2f}s"/>')
        if parent[i] is None:
            continue
        # One brush stroke in four pieces so its width can taper; a tip with
        # nothing grown from it lifts to a point.
        line = sample(branch(i))
        w0 = min(2.2, .5 + .3 * math.sqrt(grew[i]))
        w1 = .25 if grew[i] == 1 else w0 * .9
        pieces, step = 4, (len(line) - 1) // 4
        strokes = []
        for k in range(pieces):
            seg = line[k * step:(k + 1) * step + 1] if k < pieces - 1 else line[k * step:]
            w = w0 + (w1 - w0) * (k + .5) / pieces
            strokes.append(f'<path pathLength="1" style="stroke-width:{w:.2f};animation-delay:{t - .55 + .14 * k:.2f}s" '
                           f'd="{polyline(seg)}"/>')
        brush.append(f'<g style="opacity:{.42 + .2 * min(1, grew[i] / 12):.2f}">' + "".join(strokes) + "</g>")

    inks, coasts, done = [], [], set()
    for i in order:
        cell = rings[i]
        for k, (a, label) in enumerate(cell):
            b = cell[(k + 1) % len(cell)][0]
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

    # A recollection: light runs from the zero along the swash and the main line to a young far territory.
    tip = max(order[int(n * .7):], key=lambda i: math.dist(centre[i], SOURCE))
    chain = []
    while parent[tip] is not None:
        chain.append(tip)
        tip = parent[tip]
    walk = f"M{pt(start)}{curve(swash_segs)}" + "".join(curve(branch(i)) for i in reversed(chain))
    glints = "\n    ".join(
        f'<g style="opacity:{o}"{" filter=\"url(#glow)\"" if w > 2 else ""}><path class="glint" pathLength="1" '
        f'style="stroke-width:{w};animation-delay:{last + 3:.1f}s" d="{walk}"/></g>'
        for w, o in ((8, .16), (4, .3), (1.6, .85)))

    # --- captions, inscription and seal ---------------------------------------
    zh, _ = song.line("未干的地图", 15, 48, 196, tracking=15 * .42)
    en, _ = fell_it.line("The Unfinished Map", 15.5, 48, 218, tracking=.25)
    col_x, col_top, col_step, col_size = 921, 62, 19, 14
    colophon = [song_light.glyph(ch, col_size, col_x - col_size / 2, col_top + k * col_step + col_size * .88)[0]
                for k, ch in enumerate("尚未发生")]
    seal_size = 30
    seal_at = (col_x - seal_size / 2, col_top + 4 * col_step + 10)

    zero_box = bbox(ring, 8)
    swash_box = bbox(swash, 8)
    type_paths = "\n    ".join(
        f'<path class="type" style="animation-delay:{.2 + .09 * k:.2f}s" d="{d}"/>' for k, d in enumerate(letters))
    glyph = "".join(f'<path d="{d}"/>' for d in SEAL_GLYPH)
    join = lambda items: "\n    ".join(items)

    svg = f'''<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" role="img" aria-labelledby="t d">
  <title id="t">H0mework · 未干的地图</title>
  <desc id="d">The name H0mework is set letter by letter; its zero is painted as a vermilion brush circle, the source. A brush line runs from the zero under the name and across the water, and where it touches land an unfinished map begins to grow. Each territory joins only across a border it shares with one already drawn; a vermilion brush tree records where it grew from. Old territories have dried to ochre, the newest are still wet. At the far edge an inscription reads 尚未发生, not yet happened, sealed with 源, source.</desc>
  <style>{STYLE}  </style>
  <defs>
    <filter id="pigment" filterUnits="userSpaceOnUse" x="0" y="0" width="{W}" height="{H}" color-interpolation-filters="sRGB">
      <feTurbulence type="fractalNoise" baseFrequency=".022" numOctaves="3" seed="11" result="n"/>
      <feDisplacementMap in="SourceGraphic" in2="n" scale="14" xChannelSelector="R" yChannelSelector="G" result="d"/>
      <feGaussianBlur in="d" stdDeviation="4.5" result="soft"/>
      <feTurbulence type="fractalNoise" baseFrequency=".8" numOctaves="1" seed="5" result="g"/>
      <feColorMatrix in="g" type="matrix" values="0 0 0 0 0  0 0 0 0 0  0 0 0 0 0  -.5 0 0 0 1.18" result="grain"/>
      <feComposite in="soft" in2="grain" operator="in"/>
    </filter>
    <filter id="waterlines" x="-6%" y="-20%" width="112%" height="140%" color-interpolation-filters="sRGB">
      <feGaussianBlur in="SourceGraphic" stdDeviation="8"/>
      <feComponentTransfer><feFuncA type="table" tableValues="{waterline_table()}"/></feComponentTransfer>
    </filter>
    <filter id="brushed" filterUnits="userSpaceOnUse" x="0" y="0" width="{W}" height="{H}" color-interpolation-filters="sRGB">
      <feTurbulence type="fractalNoise" baseFrequency=".05" numOctaves="2" seed="17" result="t"/>
      <feDisplacementMap in="SourceGraphic" in2="t" scale="2.4" xChannelSelector="R" yChannelSelector="G" result="d"/>
      <feTurbulence type="fractalNoise" baseFrequency=".9" numOctaves="1" seed="23" result="g"/>
      <feColorMatrix in="g" type="matrix" values="0 0 0 0 0  0 0 0 0 0  0 0 0 0 0  -1.3 0 0 0 1.5" result="grain"/>
      <feComposite in="d" in2="grain" operator="in"/>
    </filter>
    <filter id="blot" x="-80%" y="-80%" width="260%" height="260%">
      <feTurbulence type="fractalNoise" baseFrequency=".2" numOctaves="2" seed="31" result="t"/>
      <feDisplacementMap in="SourceGraphic" in2="t" scale="3" xChannelSelector="R" yChannelSelector="G" result="d"/>
      <feGaussianBlur in="d" stdDeviation=".55"/>
    </filter>
    <filter id="glow" x="-10%" y="-20%" width="120%" height="140%">
      <feGaussianBlur stdDeviation="1.8"/>
    </filter>
    <filter id="bleed" x="-80%" y="-80%" width="260%" height="260%">
      <feTurbulence type="fractalNoise" baseFrequency=".12" numOctaves="2" seed="32" result="t"/>
      <feDisplacementMap in="SourceGraphic" in2="t" scale="6" xChannelSelector="R" yChannelSelector="G" result="d"/>
      <feGaussianBlur in="d" stdDeviation="2.4"/>
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
    <mask id="write-zero" maskUnits="userSpaceOnUse" x="{zero_box[0]:.0f}" y="{zero_box[1]:.0f}" width="{zero_box[2]:.0f}" height="{zero_box[3]:.0f}">
      <path class="reveal" pathLength="1" style="stroke-width:{2 * max(ring_w) + 6:.1f};animation-duration:{d_zero}s;animation-delay:{t_zero}s" d="{polyline(ring)}"/>
      <g fill="none" stroke="#000" stroke-width=".7" stroke-linecap="round">{"".join(f'<path d="{p}"/>' for p in dry)}</g>
    </mask>
    <mask id="write-swash" maskUnits="userSpaceOnUse" x="{swash_box[0]:.0f}" y="{swash_box[1]:.0f}" width="{swash_box[2]:.0f}" height="{swash_box[3]:.0f}">
      <path class="reveal" pathLength="1" style="stroke-width:8;animation-duration:{d_swash}s;animation-delay:{t_swash:.2f}s" d="{polyline(swash)}"/>
    </mask>
    <mask id="carve" maskUnits="userSpaceOnUse" x="-10" y="-10" width="136" height="136">
      <rect x="-10" y="-10" width="136" height="136" fill="#fff"/>
      <g transform="translate(8 7.5)" fill="none" stroke="#000" stroke-width="7" stroke-linecap="round" stroke-linejoin="round">{glyph}</g>
      <g fill="#000"><ellipse cx="116" cy="41" rx="2.6" ry="4.2"/><ellipse cx="31" cy="116" rx="3.6" ry="2.2"/><ellipse cx="0" cy="88" rx="1.8" ry="2.8"/></g>
    </mask>
    <clipPath id="land">{"".join(f'<use href="#c{i}"/>' for i in order)}</clipPath>
    <radialGradient id="vignette" cx="50%" cy="50%" r="72%">
      <stop offset=".55" style="stop-color:var(--shade);stop-opacity:0"/>
      <stop offset="1" style="stop-color:var(--shade);stop-opacity:var(--shade-a)"/>
    </radialGradient>
    {join(defs)}
  </defs>

  <rect class="paper" width="{W}" height="{H}" rx="14"/>
  <rect width="{W}" height="{H}" rx="14" filter="url(#paper)"/>

  <g>
    {type_paths}
  </g>

  <g filter="url(#waterlines)">
    {join(landcells)}
  </g>
  <g clip-path="url(#land)"><g filter="url(#pigment)">
    {join(washes)}
  </g></g>
  <g>
    {join(inks)}
  </g>
  <g>
    {join(coasts)}
  </g>
  <g filter="url(#brushed)">
    <path class="vermilion" mask="url(#write-zero)" d="{ribbon(ring, ring_w)}"/>
    <path class="vermilion" mask="url(#write-swash)" style="opacity:.75" d="{ribbon(swash, swash_w)}"/>
    <g class="brush">
    {join(brush)}
    </g>
  </g>

  <circle class="ripple" style="animation-delay:{t_drop:.2f}s" cx="{SOURCE[0]}" cy="{SOURCE[1]}" r="30" filter="url(#blot)"/>
  <circle class="bleed" style="animation-delay:{t_drop:.2f}s" cx="{SOURCE[0] + .6}" cy="{SOURCE[1] - .4}" r="9" filter="url(#bleed)"/>
  <g filter="url(#blot)">
    <g class="blot" style="animation-delay:{t_drop:.2f}s">
      <circle cx="{SOURCE[0]}" cy="{SOURCE[1]}" r="3.7"/>
      <circle cx="{SOURCE[0] + 1.7}" cy="{SOURCE[1] - 1.2}" r="2.6"/>
      <circle cx="{SOURCE[0] - 1.3}" cy="{SOURCE[1] + 1.4}" r="2.2"/>
    </g>
  </g>

  <g>
    {glints}
  </g>

  <g class="later caption" style="animation-delay:{t_swash + .4:.1f}s">
    <g style="opacity:.8">{"".join(f'<path d="{d}"/>' for d in zh)}</g>
    <g style="opacity:.62">{"".join(f'<path d="{d}"/>' for d in en)}</g>
  </g>

  <g class="later caption" style="animation-delay:{last + .4:.1f}s;opacity:.62">
    {"".join(f'<path d="{d}"/>' for d in colophon)}
  </g>
  <g transform="translate({seal_at[0]:.1f} {seal_at[1]:.1f}) rotate(-3) scale({seal_size / 116:.4f})">
    <g class="stamp" style="animation-delay:{last + 1.3:.1f}s">
      <g filter="url(#inkpad)"><path class="sealink" mask="url(#carve)" d="{seal_outline()}"/></g>
    </g>
  </g>

  <rect width="{W}" height="{H}" rx="14" fill="url(#vignette)"/>
</svg>
'''
    out = Path(__file__).with_name("banner.svg")
    out.write_text(svg)
    print(f"{out.name}: {n} territories, name ends at x={name_end:.0f}, land from x="
          f"{min(V.pts[v][0] for i in order for v, _ in rings[i]):.0f}, grown by {last:.1f}s, {len(svg) // 1024} KB")


if __name__ == "__main__":
    main()
