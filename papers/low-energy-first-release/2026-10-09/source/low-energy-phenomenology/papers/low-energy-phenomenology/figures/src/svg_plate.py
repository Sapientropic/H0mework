"""Local editable vector plates, with actual segmented dashes and math outlines."""
from __future__ import annotations
import html, math, os, shutil, signal, subprocess, sys, tempfile, time
from pathlib import Path
import pymupdf as fitz
import matplotlib
from matplotlib.textpath import TextPath
from matplotlib.font_manager import FontProperties
from matplotlib.path import Path as MplPath
sys.path.insert(0, str(Path(__file__).resolve().parents[4] / 'shared/figure-style'))
from house_style import INK, SLATE, MUTE, HAIR, DEEP, VERMILION, GOLD, WASH, SVG_FONT_ZH, SVG_FONT_EN
matplotlib.rcParams['mathtext.fontset'] = 'stix'
W, MIN_SIZE = 1000, 17
CHROME = Path('/Applications/Google Chrome.app/Contents/MacOS/Google Chrome')
CJK = Path.home() / 'Library/Fonts'
PROPS = {('cjk', 'normal'): FontProperties(fname=str(CJK / 'NotoSerifCJKsc-Regular.otf')),
         ('cjk', 'bold'): FontProperties(fname=str(CJK / 'NotoSerifCJKsc-SemiBold.otf')),
         ('lat', 'normal'): FontProperties(family='STIX Two Text'),
         ('lat', 'bold'): FontProperties(family='STIX Two Text', weight='bold')}


def has_cjk(s):
    return any('　' <= c <= '鿿' or '＀' <= c <= '￯' for c in s)


class SVGPlate:
    def __init__(self, title: str, height: int, *, base: Path, source_commit: str,
                 translate=str, font=SVG_FONT_ZH, suffix='', manifest=None,
                 creator='draw_main_figures.py'):
        self.base = base
        self.source_commit = source_commit
        self.translate = translate
        self.font = font
        self.suffix = suffix
        self.manifest = [] if manifest is None else manifest
        self.creator = creator
        self.width, self.height = W, height
        title = self.translate(title)
        self.math_labels = []
        self.items = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{height}" viewBox="0 0 {W} {height}">',
          f'<title>{html.escape(title)}</title>',
          f'<desc>Fixed source {self.source_commit}; reproducible mathematical figure.</desc>',
          f'<rect width="{W}" height="{height}" fill="white"/>']

    def text(self, x, y, text, size=MIN_SIZE, anchor='start', weight='normal', fill=INK):
        text = self.translate(text)
        assert size >= MIN_SIZE, (text, size)
        if "$" in str(text):
            return self.mathtext(x, y, str(text), size, anchor, weight, fill)
        self.items.append(f'<text x="{x}" y="{y}" font-family="{self.font}" font-size="{size}" font-weight="{weight}" text-anchor="{anchor}" fill="{fill}">{html.escape(str(text))}</text>')

    def mathtext(self, x, y, label, size=MIN_SIZE, anchor='start', weight='normal', fill=INK):
        # Keep TeX editable in the script and SVG metadata; draw real typeset glyph outlines.
        prop = PROPS[('cjk' if has_cjk(label) else 'lat', 'bold' if weight in ('bold', '600') else 'normal')]
        glyphs = TextPath((0, 0), label, size=size, prop=prop, usetex=False)
        bounds = glyphs.get_extents()
        left = x - ({'start': bounds.x0, 'middle': (bounds.x0+bounds.x1)/2,
                     'end': bounds.x1}[anchor])
        commands = []
        names = {MplPath.MOVETO: 'M', MplPath.LINETO: 'L',
                 MplPath.CURVE3: 'Q', MplPath.CURVE4: 'C'}
        for vertices, code in glyphs.iter_segments(curves=True, simplify=False):
            if code == MplPath.CLOSEPOLY:
                commands.append('Z')
            elif code in names:
                commands.append(names[code]+' '.join(f'{float(v):.5f}' for v in vertices))
        bbox = [left+bounds.x0, y-bounds.y1, left+bounds.x1, y-bounds.y0]
        if not (0 <= bbox[0] < bbox[2] <= self.width and 0 <= bbox[1] < bbox[3] <= self.height):
            raise ValueError(f'Math label outside canvas: {label}: {bbox}')
        escaped = html.escape(label, quote=True)
        self.items.append(f'<g class="math-label" role="img" aria-label="{escaped}" data-tex="{escaped}">'
            f'<title>{escaped}</title><path transform="translate({left:.5f},{y:.5f}) scale(1,-1)" '
            f'd="{" ".join(commands)}" fill="{fill}"/></g>')
        self.math_labels.append({'tex': label, 'bounds': [round(float(v), 4) for v in bbox]})

    def line(self, x1, y1, x2, y2, stroke=SLATE, width=1.5, dash=None, arrow=False):
        if arrow:  # shaft stops at the head; the head is an actual polygon
            dx, dy = x2-x1, y2-y1; size = math.hypot(dx, dy); dx /= size; dy /= size
            pts = [(x2, y2), (x2-10*dx+4.5*dy, y2-10*dy-4.5*dx), (x2-10*dx-4.5*dy, y2-10*dy+4.5*dx)]
            self.path([(x1, y1), (x2-9*dx, y2-9*dy)], stroke, width, dash)
            self.items.append('<polygon points="'+' '.join(f'{x:.3f},{y:.3f}' for x, y in pts)+f'" fill="{stroke}"/>')
        else:
            self.path([(x1, y1), (x2, y2)], stroke, width, dash)

    def box(self, x, y, w, h, title, lines, fill='white', edge=HAIR, title_fill=INK, lw=1.2):
        self.items.append(f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="6" fill="{fill}" stroke="{edge}" stroke-width="{lw}"/>')
        self.text(x+w/2, y+30, title, 19, 'middle', '600', title_fill)
        for i, t in enumerate(lines):
            self.text(x+w/2, y+60+25*i, t, MIN_SIZE, 'middle')

    def path(self, pts, stroke, width=2.7, dash=None):
        if dash:
            lengths = list(map(float, dash.split())); index = 0; remaining = lengths[0]; commands = []
            for start, end in zip(pts, pts[1:]):
                dx, dy = end[0]-start[0], end[1]-start[1]; distance = math.hypot(dx, dy); used = 0.0
                while used < distance-1e-10:
                    take = min(remaining, distance-used)
                    if index % 2 == 0:
                        x0 = start[0]+dx*used/distance; y0 = start[1]+dy*used/distance
                        x1 = start[0]+dx*(used+take)/distance; y1 = start[1]+dy*(used+take)/distance
                        commands.append(f'M{x0:.3f},{y0:.3f} L{x1:.3f},{y1:.3f}')
                    used += take; remaining -= take
                    if remaining < 1e-9: index = (index+1) % len(lengths); remaining = lengths[index]
            d = ' '.join(commands)
        else: d = 'M'+' L'.join(f'{x:.3f},{y:.3f}' for x, y in pts)
        self.items.append(f'<path d="{d}" fill="none" stroke="{stroke}" stroke-width="{width}" stroke-linecap="round"/>')

    def save(self, stem):
        stem += self.suffix
        svg = self.base/(stem+'.svg')
        svg.write_text('\n'.join(self.items+['</svg>'])+'\n')
        pdf = self.base/(stem+'.pdf')
        with tempfile.TemporaryDirectory(ignore_cleanup_errors=True) as work:
            page = Path(work)/'page.html'
            page.write_text(f'<!doctype html><meta charset="utf-8"><style>@page{{size:{self.width}px {self.height}px;margin:0}}'
                            f'html,body{{margin:0;padding:0}}svg{{display:block}}</style>'+svg.read_text())
            raw = Path(work)/'raw.pdf'
            proc = subprocess.Popen([str(CHROME), '--headless', '--disable-gpu', '--no-first-run', '--no-pdf-header-footer',
                                     f'--user-data-dir={work}/profile', f'--print-to-pdf={raw}', page.as_uri()],
                                    stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, start_new_session=True)
            start = time.monotonic()
            while not (raw.exists() and raw.stat().st_size > 1000) and time.monotonic()-start < 40: time.sleep(.2)
            time.sleep(.5)
            if proc.poll() is None: os.killpg(proc.pid, signal.SIGTERM)
            proc.wait(timeout=10)
            with fitz.open(raw) as doc:
                assert len(doc) == 1, (stem, len(doc))
                doc.set_metadata({'title': stem, 'subject': 'Fixed-source low-energy phenomenology figure', 'creator': self.creator})
                doc.save(pdf, garbage=4, deflate=True, no_new_id=True)
        renderer = shutil.which('pdftoppm') or '/opt/homebrew/bin/pdftoppm'
        subprocess.run([renderer, '-png', '-singlefile', '-scale-to', '1600', str(pdf), str(self.base/stem)], check=True, capture_output=True)
        with fitz.open(pdf) as d:
            self.manifest.append({'stem': stem, 'formats': ['svg', 'pdf', 'png'], 'svg_dimensions': [self.width, self.height],
               'pdf_pages': len(d), 'pdf_text_characters': len(d[0].get_text()), 'rasterizer': 'Poppler pdftoppm',
               'pdf_renderer': 'headless Google Chrome print', 'source_commit': self.source_commit, 'math_labels': self.math_labels,
               'math_renderer': 'Matplotlib '+matplotlib.__version__+' MathText/STIX vector paths'})
