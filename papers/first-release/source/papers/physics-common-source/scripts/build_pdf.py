#!/usr/bin/env python3
"""Build the reading PDF for the common-source Spin×SU(7) manuscript.

Dependencies: Python 3, pandoc, XeLaTeX, xeCJK, Noto Serif/Sans CJK fonts.
Typical use from the package directory:
  python3 scripts/build_pdf.py manuscript.md
No mathematical expressions or theorem statements are edited by this script.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'shared' / 'scripts'))
import byline  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]

# Language profiles: the layout regexes name headings in the manuscript's own
# language. Both manuscripts share one typography; the English profile exists
# because manuscript-en.md keeps the bilingual title and the Chinese abstract.
PROFILES = {
    'zh': {
        'caution': '[注意]',
        'abstract_break': r'^##? Abstract \(English\)$',
        'appendix': r'^# 附录[A-D][^\n]*$',
        'references': r'^# 参考文献$',
        'toc_before': r'^# 1\s+引言[^\n]*$',
        'metadata_lang': 'zh-CN',
        'header': 'article-header.tex',
        'default_output': 'build/physics-common-source.pdf',
    },
    'en': {
        'caution': '[Caution]',
        'abstract_break': r'^##? 摘要$',
        'appendix': r'^# Appendix [A-D][^\n]*$',
        'references': r'^# References$',
        'toc_before': r'^# 1\s+Introduction[^\n]*$',
        'metadata_lang': 'en',
        'header': 'article-header-en.tex',
        'default_output': 'build/physics-common-source-en.pdf',
    },
}

def run(cmd, cwd=None, env=None):
    result = subprocess.run([str(x) for x in cmd], cwd=cwd, env=env,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        print(result.stdout[-16000:])
        raise RuntimeError(f"Command failed ({result.returncode}): {cmd[0]}")
    return result.stdout

def escape(s):
    return re.sub(r'[\\{}#$%&_~^]', lambda m: {
        '\\':r'\textbackslash{}','{':r'\{','}':r'\}', '#':r'\#','$':r'\$',
        '%':r'\%','&':r'\&','_':r'\_', '~':r'\textasciitilde{}','^':r'\textasciicircum{}'
    }[m.group()], s)

def prepare(source: str, toc: bool, profile):
    lines = source.splitlines()
    title_idx = next((i for i,l in enumerate(lines) if l.startswith('# ')),None)
    if title_idx is None:
        title = '共同源生成的 Spin×SU(7) 经典—量子理论'
    else:
        title = lines.pop(title_idx)[2:].strip()
    subtitle = ''
    for i,l in enumerate(lines[:8]):
        if l.startswith('**') and l.endswith('**'):
            subtitle = lines.pop(i)[2:-2]
            break
    body = '\n'.join(lines).lstrip()
    # Headings already separate sections in print. Standalone manuscript rules
    # can otherwise leave a rule-only page immediately before a forced break.
    body = re.sub(r'(?m)^---[ \t]*$', '', body)
    # The caution emoji is a working marker; print uses plain text.
    body = body.replace('[⚠️]',profile['caution'])
    # \tag belongs to the outer display, not the inner aligned block.
    body = re.sub(r'\\tag\{([^}]+)\}\s*\\end\{aligned\}', r'\\end{aligned}\\tag{\1}', body)
    body = re.sub(r'```mermaid\s*\n.*?```\s*', '', body, flags=re.S)
    # Existing numbering is intentional; only heading levels are normalized.
    body = re.sub(r'^(#{2,6}) ',lambda m: m[1][1:]+' ',body,flags=re.M)
    # Keep keywords with their abstract at a readable, compact front-matter size.
    body = re.sub(r'(?ms)^(#{1,2} (?:摘要|Abstract(?: \(English\))?))\n(.*?)(?=^#{1,2} |\Z)',
                  lambda m: m[1]+'\n\n```{=latex}\n\\begingroup\\small\\setstretch{1.16}\n```\n'+m[2]
                  +'\n```{=latex}\n\\endgroup\n```\n\n',body)
    # Keep each language's abstract continuous; this avoids opening the second
    # abstract with just a few lines at the foot of the title page.
    body = re.sub('(?m)'+profile['abstract_break'],
                  lambda m: '```{=latex}\n\\clearpage\n```\n\n'+m[0], body, count=1)
    # Appendices start on fresh pages.
    body = re.sub('(?m)'+profile['appendix'],
                  lambda m: '```{=latex}\n\\clearpage\n```\n\n'+m[0], body)
    # Reference entries remain intact, in the conventional smaller reference
    # font. The explicit group keeps the body typography unchanged.
    if re.search('(?m)'+profile['references'],body):
        body = re.sub('(?m)'+profile['references'],
             lambda m: '```{=latex}\n\\Needspace{0.55\\textheight}\n```\n\n'+m[0]
             +'\n\n```{=latex}\n\\begingroup\\footnotesize\\setstretch{1.13}\n```',body,count=1)
        body += '\n\n```{=latex}\n\\endgroup\n```\n'
    if toc:
        body = re.sub('(?m)'+profile['toc_before'],
            lambda m: '```{=latex}\n\\clearpage\n{\\small\\tableofcontents}\n\\clearpage\n```\n\n'+m[0],body,count=1)
    return title,subtitle,body

def compile_tex(tex: Path, destination: Path, env=None):
    logs = []
    # Start each build from clean auxiliary files; the three passes then create
    # a consistent table of contents and PDF bookmark set for this source.
    for suffix in ('.aux','.toc','.out'):
        tex.with_suffix(suffix).unlink(missing_ok=True)
    for _ in range(3):
        logs.append(run(['xelatex','-interaction=nonstopmode','-halt-on-error',
                         '-file-line-error',tex.name],cwd=tex.parent,env=env))
    produced = tex.with_suffix('.pdf')
    if not produced.exists(): raise RuntimeError('XeLaTeX did not produce a PDF')
    destination.parent.mkdir(parents=True,exist_ok=True)
    shutil.copy2(produced,destination)
    log = tex.with_suffix('.log').read_text(errors='replace')
    warnings = [x for x in log.splitlines() if 'Overfull' in x or 'Missing character' in x]
    return warnings

def build_manuscript(source: Path, output: Path, temp: Path, profile, toc=True):
    lines = source.read_text().splitlines()
    author,details = byline.pop(lines)
    title,subtitle,body = prepare('\n'.join(lines)+'\n',toc,profile)
    normalized = temp / 'manuscript-layout.md'
    normalized.write_text(body)
    subtitle_header = temp / 'subtitle.tex'
    subtitle_header.write_text('\\papersubtitle{'+escape(subtitle)+'}\n'+byline.tex(author,details,escape))
    font_dir = next((d for d in (Path.home()/'Library/Fonts',Path('/Library/Fonts'))
                     if (d/'NotoSerifCJKsc-Regular.otf').exists()),None)
    if font_dir is None:
        raise RuntimeError('Noto Serif/Sans CJK SC fonts not found in Library/Fonts')
    fonts_header = temp / 'fonts-dir.tex'
    fonts_header.write_text('\\newcommand{\\CJKFontDir}{'+str(font_dir)+'}\n')
    tex = temp / 'manuscript.tex'
    run(['pandoc',normalized,'-f','markdown+tex_math_dollars+raw_tex-smart','-t','latex',
         '--standalone','--top-level-division=section',
         '--resource-path',str(source.parent)+':'+str(ROOT),
         '--lua-filter',ROOT/'styles/article-filter.lua',
         '--include-in-header',fonts_header,
         '--include-in-header',ROOT/'styles'/profile['header'],
         '--include-in-header',subtitle_header,
         '--metadata','title='+title,'--metadata','lang='+profile['metadata_lang'],
         '-V','documentclass=article','-V','fontsize=11pt',
         '-V','microtypeoptions=protrusion=false,nopatch=footnote',
         '-V','colorlinks=true','-o',tex],cwd=source.parent)
    # Pandoc emits resource paths relative to the manuscript, while XeLaTeX is
    # run in a clean build directory. Make paths absolute without altering art.
    ts = tex.read_text()
    def absolute_graphic(m):
        p = Path(m[2]); p = p if p.is_absolute() else source.parent/p
        return m[1]+'{'+str(p.resolve())+'}'
    ts = re.sub(r'(\\includegraphics(?:\[[^\]]*\])?)\{([^}]+)\}',absolute_graphic,ts)
    tex.write_text(ts)
    warnings = compile_tex(tex,output)
    return {'path':str(output),'layout_warnings':warnings,'tex':str(tex)}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('manuscript',nargs='?',type=Path,default=ROOT/'manuscript.md')
    ap.add_argument('--lang',choices=sorted(PROFILES),
                    help='Layout language profile; default is inferred from a -en manuscript name')
    ap.add_argument('--output',type=Path)
    ap.add_argument('--no-toc',action='store_true')
    ap.add_argument('--work-dir',type=Path)
    args=ap.parse_args()
    lang=args.lang or ('en' if args.manuscript.name.endswith('-en.md') else 'zh')
    profile=PROFILES[lang]
    supplement=args.manuscript.name.startswith('supplement')
    if args.output:
        output=args.output
    elif supplement:
        output=ROOT/'build'/f'physics-common-source-{args.manuscript.stem}.pdf'
    else:
        output=ROOT/profile['default_output']
    if args.work_dir:
        temp=args.work_dir.resolve()
    else:
        work_name='pdf-work-supplement' if supplement else 'pdf-work'
        temp=ROOT/'build'/(work_name+('-en' if lang=='en' else ''))
    temp.mkdir(parents=True,exist_ok=True)
    report=[dict(lang=lang,**build_manuscript(args.manuscript.resolve(),output.resolve(),temp,profile,not args.no_toc and not supplement))]
    (temp/'build-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2))
    print(json.dumps(report,ensure_ascii=False,indent=2))

if __name__=='__main__': main()
