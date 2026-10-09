#!/usr/bin/env python3
"""Build both Case 2 editions using the shared publication layout."""
import argparse
import json
import os
import re
import signal
import subprocess
import sys
from pathlib import Path

PAPER = Path(__file__).resolve().parents[1]
ROOT = PAPER.parents[1]
sys.path.insert(0, str(ROOT / 'shared/scripts'))
import build_pdf as shared

ZH = 'papers/low-energy-loop-response/manuscript.md'
EN = 'papers/low-energy-loop-response/manuscript-en.md'
shared.RUNHEADS[EN] = ('low-energy-loop-response', 'CourtyCourt · Case 2',
                       'Ordered Traces and Whole-Ball Curvature')
shared.CONTINUOUS_APPENDICES.add(EN)
# A short English masthead puts the abstract in the shared subtitle scan range.
_latin_title = shared.latin_title
def _subtitle(line):
    if line.strip() in ('# Abstract', '## Abstract'):
        return None
    return _latin_title(line)
shared.latin_title = _subtitle

# The tall new plate keeps the printed label size of the landscape figures.
_compile_tex = shared.compile_tex
def _compile_with_full_return_plate(tex):
    text = tex.read_text()
    text = re.sub(
        r'(\\includegraphics\[width=\\linewidth,height=)0\.62'
        r'(\\textheight,keepaspectratio\]\{[^}]*fig04-full-return(?:-en)?\.pdf\})',
        r'\g<1>0.8\2', text)
    tex.write_text(text)
    return _compile_tex(tex)
shared.compile_tex = _compile_with_full_return_plate

_run = shared.run
def _run_in_paper_cache(command, cwd=None):
    args = [str(item) for item in command]
    if args[0] == shared.CHROME:
        cache = PAPER / 'build/chrome-pdf'
        cache.mkdir(parents=True, exist_ok=True)
        args[1:1] = ['--user-data-dir=' + str(cache), '--no-first-run',
                     '--disable-background-networking']
        target = next((Path(arg.split('=', 1)[1]) for arg in args
                       if arg.startswith('--print-to-pdf=')), None)
        if target is not None:
            target.unlink(missing_ok=True)
            process = subprocess.Popen(args, cwd=cwd, stdout=subprocess.PIPE,
                                       stderr=subprocess.STDOUT, text=True,
                                       start_new_session=True)
            try:
                output, _ = process.communicate(timeout=25)
            except subprocess.TimeoutExpired:
                # Chrome can keep its helpers alive after flushing a valid PDF.
                valid = target.exists() and target.stat().st_size > 1000
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    output, _ = process.communicate(timeout=3)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    output, _ = process.communicate()
                if not valid:
                    raise RuntimeError('Chrome did not finish the figure PDF')
            if not target.exists():
                raise RuntimeError('Chrome did not print the figure PDF')
            subprocess.run(['pdfinfo', str(target)], check=True,
                           stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
            return output
    return _run(args, cwd)
shared.run = _run_in_paper_cache

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lang', choices=('zh', 'en', 'both'), default='both')
    parser.add_argument('--no-toc', action='store_true')
    args = parser.parse_args()
    temp = PAPER / 'build/tmp'
    temp.mkdir(parents=True, exist_ok=True)
    os.environ['TMPDIR'] = str(temp)
    for lang, rel in [('zh', ZH), ('en', EN)]:
        if args.lang in (lang, 'both'):
            print(json.dumps(shared.build(rel, not args.no_toc), ensure_ascii=False))

if __name__ == '__main__':
    main()
