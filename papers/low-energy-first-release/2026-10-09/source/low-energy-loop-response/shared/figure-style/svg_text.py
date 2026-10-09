"""Mixed Chinese / Latin / math text for hand-written SVG figures.

CairoSVG uses only the first family of a font-family list and never falls
back per glyph, while STIX Two Text lacks most math operators. So every text
line is split into runs, each run led by a family that owns its glyphs, and
lines are positioned by measured width (start anchor) instead of relying on
text-anchor over several tspans, which CairoSVG misplaces.

Markup inside a line: {i:..} italic, {sub:..} / {sup:..} scripts, {isub:..} italic subscript, {v:..} run
in the accent colour, {b:..} bold. Tags do not nest; combine by adjacency.
"""
from __future__ import annotations
import ctypes
import math
import ctypes.util
import re
from functools import lru_cache
from html import escape
from pathlib import Path

from house_style import SVG_FONT_ZH, SVG_FONT_EN, SVG_FONT_MATH, VERMILION

SVG_FONT_OPS = 'STIX Two Math, ' + SVG_FONT_MATH
OPS = set('≠→←↔≤≥⇒∄∃∀∘⋅⊗⊕∈∉×')
_CJK = re.compile(r'[　-〿㐀-鿿＀-￯·、]')
_TAG = re.compile(r'\{(i|isub|sub|sup|v|b):(.*?)\}')

_FONT_FILES = {
    'zh': Path.home() / 'Library/Fonts/NotoSerifCJKsc-Regular.otf',
    'en': Path('/System/Library/Fonts/Supplemental/STIXTwoText.ttf'),
    'it': Path('/System/Library/Fonts/Supplemental/STIXTwoText-Italic.ttf'),
    'op': Path('/System/Library/Fonts/Supplemental/STIXTwoMath.otf'),
}


def register_cjk_for_cairo() -> None:
    """Make a user-installed Noto Serif CJK SC visible to Cairo on macOS.

    On this machine CoreText does not list ~/Library/Fonts/NotoSerifCJKsc-*,
    so Cairo's Quartz backend falls back to boxes; register them for this
    process only (no system change)."""
    lib_cf, lib_ct = ctypes.util.find_library('CoreFoundation'), ctypes.util.find_library('CoreText')
    if not (lib_cf and lib_ct):
        return
    cf, ct = ctypes.cdll.LoadLibrary(lib_cf), ctypes.cdll.LoadLibrary(lib_ct)
    cf.CFURLCreateFromFileSystemRepresentation.restype = ctypes.c_void_p
    cf.CFURLCreateFromFileSystemRepresentation.argtypes = [ctypes.c_void_p, ctypes.c_char_p, ctypes.c_long, ctypes.c_bool]
    ct.CTFontManagerRegisterFontsForURL.restype = ctypes.c_bool
    ct.CTFontManagerRegisterFontsForURL.argtypes = [ctypes.c_void_p, ctypes.c_uint32, ctypes.c_void_p]
    for path in sorted((Path.home() / 'Library/Fonts').glob('NotoSerifCJKsc-*.otf')):
        raw = str(path).encode()
        url = cf.CFURLCreateFromFileSystemRepresentation(None, raw, len(raw), False)
        ct.CTFontManagerRegisterFontsForURL(url, 1, None)  # 1 = process scope


@lru_cache(maxsize=None)
def _metrics(key: str):
    from fontTools.ttLib import TTFont
    font = TTFont(str(_FONT_FILES[key]), lazy=True)
    return font.getBestCmap(), font['hmtx'].metrics, font['head'].unitsPerEm


def _width(text: str, key: str, size: float) -> float:
    cmap, hmtx, upm = _metrics(key)
    total = 0
    for ch in text:
        glyph = cmap.get(ord(ch))
        total += hmtx[glyph][0] if glyph in hmtx else upm
    return total * size / upm


def _cls(ch: str) -> str:
    if ch in OPS:
        return 'op'
    return 'zh' if _CJK.match(ch) else 'en'


def _pieces(text: str):
    """Yield (substring, tag) with tag in {'', i, sub, sup, v, b}."""
    pos = 0
    for m in _TAG.finditer(text):
        if m.start() > pos:
            yield text[pos:m.start()], ''
        yield m.group(2), m.group(1)
        pos = m.end()
    if pos < len(text):
        yield text[pos:], ''


def _script(size, min_size):
    return math.ceil(max(size * .7, min_size) * 10) / 10  # round up: the SVG keeps one decimal


def line(x, y, text, size, color, weight=400, anchor='start', accent=VERMILION, min_size=0.0) -> str:
    """One SVG <text> element; x is the anchor point of the whole line.

    Scripts shrink to 70% but never below min_size (the print floor)."""
    runs, width, shift = [], 0.0, 0.0
    for piece, tag in _pieces(str(text)):
        for m in re.finditer(r'(\s+|.)', piece):
            ch = m.group(0)
            cls = 'en' if ch.isspace() else _cls(ch)
            if tag in ('i', 'isub') and cls == 'en':
                cls = 'it'
            if runs and runs[-1][1] == cls and runs[-1][2] == tag:
                runs[-1][0] += ch
            else:
                runs.append([ch, cls, tag])
    out = []
    for chunk, cls, tag in runs:
        s = _script(size, min_size) if tag in ('sub', 'isub', 'sup') else size
        target = {'sub': .28 * size, 'isub': .28 * size, 'sup': -.38 * size}.get(tag, 0.0)
        dy = target - shift
        shift = target
        family = {'zh': SVG_FONT_ZH, 'en': SVG_FONT_EN, 'it': SVG_FONT_EN, 'op': SVG_FONT_OPS}[cls]
        attrs = [f'font-family="{family}"']
        if cls == 'it':
            attrs.append('font-style="italic"')
        if s != size:
            attrs.append(f'font-size="{s:.1f}"')
        if dy:
            attrs.append(f'dy="{dy:.1f}"')
        if tag == 'v':
            attrs.append(f'fill="{accent}"')
        if tag == 'b':
            attrs.append('font-weight="700"')
        out.append(f'<tspan {" ".join(attrs)}>{escape(chunk)}</tspan>')
        width += _width(chunk, 'zh' if cls == 'zh' else cls, s)
    x0 = x - {'start': 0, 'middle': width / 2, 'end': width}[anchor]
    return (f'<text x="{x0:.1f}" y="{y}" font-size="{size}" font-weight="{weight}" '
            f'fill="{color}" xml:space="preserve">{"".join(out)}</text>')


def text_width(text: str, size: float, min_size: float = 0.0) -> float:
    """Measured width of a marked-up line, for layout checks."""
    total = 0.0
    for piece, tag in _pieces(str(text)):
        s = _script(size, min_size) if tag in ('sub', 'isub', 'sup') else size
        for ch in piece:
            cls = _cls(ch)
            if tag in ('i', 'isub') and cls == 'en':
                cls = 'it'
            total += _width(ch, cls, s)
    return total
