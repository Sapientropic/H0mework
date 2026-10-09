#!/usr/bin/env python3
"""Build the two reading editions through the shared typography pipeline."""
import argparse
from functools import partial
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'shared/scripts'))
import build_pdf as common

_latin_title = common.latin_title


def subtitle(line):
    # A single-language title is followed by a section, not a second title.
    if line.strip() in {'# Abstract', '## Abstract'}:
        return None
    return _latin_title(line)


common.latin_title = subtitle
common.fit_wide_displays = partial(common.fit_wide_displays, tolerance=0.0)

PAPER = 'papers/low-energy-phenomenology/'
common.RUNHEADS[PAPER + 'manuscript.md'] = (
    'low-energy-phenomenology', 'CourtyCourt · Case 1', '实际电子、Coulomb 返回与 Born 修饰')
common.RUNHEADS[PAPER + 'manuscript-en.md'] = (
    'low-energy-phenomenology', 'CourtyCourt · Case 1', 'Electrons, Coulomb Response and Born Dressing')

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--language', choices=['zh', 'en', 'both'], default='both')
    args = parser.parse_args()
    for language in ['zh', 'en'] if args.language == 'both' else [args.language]:
        name = 'manuscript-en.md' if language == 'en' else 'manuscript.md'
        print(json.dumps(common.build(PAPER + name), ensure_ascii=False))
