"""Shared visual language for every paper's figures (see README.md here).

Type follows the printed paper: Latin Modern for Latin text, Computer Modern
mathtext, Noto Serif CJK SC for Chinese. One warm accent (VERMILION) marks
the object each figure asks the reader to see; everything else stays in ink
and greys so the accent is never ambiguous.
"""
from __future__ import annotations
import subprocess
from pathlib import Path

INK = '#1d2126'; SLATE = '#56606b'; MUTE = '#98a0a9'; HAIR = '#d7dbe0'
DEEP = '#1f4a73'        # primary curves and generated objects
VERMILION = '#c4532d'   # the single accent: what the reader should see
GOLD = '#b88a1e'        # second phase / secondary series
WASH = '#f5f2eb'        # warm paper wash for the few filled regions
DARK = '#18222d'        # the "dark" end of the reading scale
PRINT_SCALE = .72       # canvas shrink for plots; structural plates use .85

# Raw-SVG generators (cairosvg) cannot see TeX's Latin Modern, so they use the
# system STIX Two Text for Latin and math and Noto Serif CJK SC for Chinese.
SVG_FONT_ZH = "Noto Serif CJK SC, STIX Two Text, serif"
SVG_FONT_EN = "STIX Two Text, Noto Serif CJK SC, serif"
SVG_FONT_MATH = "STIX Two Text, STIX Two Math, serif"


def _kpse(name: str) -> Path | None:
    try:
        out = subprocess.run(['kpsewhich', name], capture_output=True, text=True, check=True).stdout.strip()
        return Path(out) if out else None
    except (OSError, subprocess.CalledProcessError):
        return None


def install(salt: str, lang: str = 'zh') -> None:
    # Imported here so raw-SVG generators can take the constants without matplotlib.
    from matplotlib import font_manager
    import matplotlib.pyplot as plt
    # Imported here so raw-SVG generators can take the constants without matplotlib.
    from matplotlib import font_manager
    import matplotlib.pyplot as plt
    families = []
    for name in ['lmroman10-regular.otf', 'lmroman10-italic.otf', 'lmroman10-bold.otf']:
        path = _kpse(name)
        if path and path.exists():
            font_manager.fontManager.addfont(str(path))
    if _kpse('lmroman10-regular.otf'):
        families.append('Latin Modern Roman')
    for path in [Path.home() / 'Library/Fonts/NotoSerifCJKsc-Regular.otf',
                 Path.home() / 'Library/Fonts/NotoSerifCJKsc-SemiBold.otf',
                 Path('/Library/Fonts/NotoSerifCJKsc-Regular.otf')]:
        if path.exists():
            font_manager.fontManager.addfont(str(path))
    families.append('Noto Serif CJK SC')
    if lang == 'zh':
        # mathtext renders the non-math runs of a mixed string with the first
        # family only, so Chinese sets must lead with the CJK face.
        families.reverse()
    plt.rcParams.update({
        'font.family': families, 'font.size': 11, 'mathtext.fontset': 'cm',
        'svg.fonttype': 'none', 'svg.hashsalt': salt, 'axes.unicode_minus': True,
        'axes.spines.top': False, 'axes.spines.right': False,
        'axes.edgecolor': SLATE, 'axes.linewidth': .8, 'axes.labelcolor': INK,
        'xtick.color': SLATE, 'ytick.color': SLATE, 'xtick.major.width': .8,
        'ytick.major.width': .8, 'xtick.major.size': 3.5, 'ytick.major.size': 3.5,
        'legend.frameon': False, 'savefig.facecolor': 'white', 'text.color': INK,
    })
