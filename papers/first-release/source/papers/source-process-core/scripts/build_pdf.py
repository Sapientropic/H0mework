#!/usr/bin/env python3
"""Build the reading PDF, and (optionally) an annotated vector figure atlas.

Dependencies: Python 3, pandoc, XeLaTeX, xeCJK, Noto Serif/Sans CJK fonts.
Typical use from the package directory:
  python3 scripts/build_pdf.py manuscript.md --atlas
  python3 scripts/build_pdf.py manuscript-en.md --atlas
The layout language profile is inferred from a -en manuscript name (or set
explicitly with --lang). No mathematical expressions or theorem statements
are edited by this script.
"""
from __future__ import annotations
import argparse
import json
import os
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
        'abstract_break': r'^##? Abstract \(English\)$',
        'appendix': r'^# 附录\s*E[^\n]*$',
        'references': r'^# 参考文献$',
        'toc_before': r'^# 1\s+引言[^\n]*$',
        'metadata_lang': 'zh-CN',
        'header': 'article-header.tex',
        'default_output': 'build/source-process-core.pdf',
        'atlas_output': 'build/source-process-core-figures.pdf',
        'atlas_manifest': 'figures/manifest.json',
        'atlas_pdftitle': '状态不是历史，源才是：论文图集',
        'atlas_pdfsubject': '五幅主图及两幅补图',
        'atlas_label': lambda fid: fid.replace('figure', '图 ').replace('supp', '补图 S'),
        'atlas_sep': '　',
    },
    'en': {
        'abstract_break': r'^##? 摘要$',
        'appendix': r'^# Appendix\s*E[^\n]*$',
        'references': r'^# References$',
        'toc_before': r'^# 1\s+Introduction[^\n]*$',
        'metadata_lang': 'en',
        'header': 'article-header-en.tex',
        'default_output': 'build/source-process-core-en.pdf',
        'atlas_output': 'build/source-process-core-figures-en.pdf',
        'atlas_manifest': 'figures/manifest-en.json',
        'atlas_pdftitle': 'The State Is Not the History: Figure Atlas',
        'atlas_pdfsubject': 'Five main figures and two supplementary figures',
        'atlas_label': lambda fid: fid.replace('figure', 'Figure ').replace('supp', 'Figure S'),
        'atlas_sep': '. ',
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
        title = '状态不是历史，源才是：过程同一性、责任承接与最小修订'
    else:
        title = lines.pop(title_idx)[2:].strip()
    subtitle = ''
    for i,l in enumerate(lines[:8]):
        # The bilingual subtitle is a fully bold line near the top, whichever
        # language it is in.
        if l.startswith('**') and l.endswith('**') and len(l) > 4:
            subtitle = lines.pop(i)[2:-2]
            break
    body = '\n'.join(lines).lstrip()
    # The printed section hierarchy replaces standalone manuscript rules.
    body = re.sub(r'(?m)^---[ \t]*$', '', body)
    # The original dossier prints figure titles as section headings. In the
    # reading edition figures do not receive a chapter hierarchy of their own.
    body = re.sub(r'^## (图\s*\d[^\n]+)$',r'**\1**',body,flags=re.M)
    body = re.sub(r'^可编辑源：[^\n]+\n?', '', body, flags=re.M)
    # Preserve every item while giving the original run-on Appendix C a break.
    body = re.sub(r'(?<=。)\*\*(C\.[2-9])',r'\n\n**\1',body)
    body = re.sub(r'```mermaid\s*\n.*?```\s*', '', body, flags=re.S)
    # Existing numbering is intentional; only heading levels are normalized.
    body = re.sub(r'^(#{2,6}) ',lambda m: m[1][1:]+' ',body,flags=re.M)
    # Keep each language's abstract continuous; this avoids opening the second
    # abstract with just a few lines at the foot of the title page.
    body = re.sub('(?m)'+profile['abstract_break'],
                  lambda m: '```{=latex}\n\\clearpage\n```\n\n'+m[0], body, count=1)
    body = re.sub('(?m)'+profile['appendix'],
                  lambda m: '```{=latex}\n\\clearpage\n```\n\n'+m[0], body, count=1)
    # Reference entries remain intact, in the conventional smaller reference
    # font. The explicit group keeps the body typography unchanged.
    if re.search('(?m)'+profile['references'],body):
        body = re.sub('(?m)'+profile['references'],
             lambda m: '```{=latex}\n\\noindent\\begin{minipage}{\\linewidth}\n```\n\n'+m[0]
             +'\n\n```{=latex}\n\\begingroup\\footnotesize\\setstretch{1.13}\n```',body,count=1)
        body += '\n\n```{=latex}\n\\endgroup\\end{minipage}\\par\n```\n'
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

def font_header(temp: Path) -> Path:
    font_dir = next((d for d in (Path.home()/'Library/Fonts',Path('/Library/Fonts'))
                     if (d/'NotoSerifCJKsc-Regular.otf').exists()),None)
    if font_dir is None:
        raise RuntimeError('Noto Serif/Sans CJK SC fonts not found in Library/Fonts')
    header = temp/'fonts-dir.tex'
    header.write_text('\\newcommand{\\CJKFontDir}{'+str(font_dir)+'}\n')
    return header

def build_manuscript(source: Path, output: Path, temp: Path, profile, toc=True):
    lines = source.read_text().splitlines()
    author,details = byline.pop(lines)
    title,subtitle,body = prepare('\n'.join(lines)+'\n',toc,profile)
    normalized = temp / 'manuscript-layout.md'
    normalized.write_text(body)
    subtitle_header = temp / 'subtitle.tex'
    subtitle_header.write_text('\\papersubtitle{'+escape(subtitle)+'}\n'+byline.tex(author,details,escape))
    fonts = font_header(temp)
    tex = temp / 'manuscript.tex'
    run(['pandoc',normalized,'-f','markdown+tex_math_dollars+raw_tex-smart','-t','latex',
         '--standalone','--top-level-division=section',
         '--resource-path',str(source.parent)+':'+str(ROOT),
         '--lua-filter',ROOT/'styles/article-filter.lua',
         '--include-in-header',fonts,
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

def build_atlas(manifest: Path, output: Path, temp: Path, profile, lang: str):
    fonts = font_header(temp)
    data = json.loads(manifest.read_text())
    figures = data if isinstance(data,list) else data['figures']
    caption_path = manifest.parent/'paper-captions.json'
    captions = json.loads(caption_path.read_text()) if caption_path.exists() else {}
    body = []
    for fig in figures:
        path = (manifest.parent/fig['pdf']).resolve()
        label = profile['atlas_label'](fig['id'])
        title = label+profile['atlas_sep']+fig.get('title',fig.get('id',''))
        cap_entry = captions.get(fig['id'],{})
        cap = cap_entry.get(lang,'') if isinstance(cap_entry,dict) else cap_entry
        if not cap:
            cap = fig.get('caption','')
        body.append(r'\section*{'+escape(title)+'}')
        body.append(r'\addcontentsline{toc}{section}{'+escape(title)+'}')
        body.append(r'\vspace{0.8em}\begin{center}')
        body.append(r'\includegraphics[width=\linewidth,height=0.72\textheight,keepaspectratio]{'+str(path)+'}')
        body.append(r'\end{center}\vspace{0.5em}')
        if cap:
            # Use Pandoc's math parser for captions supplied as Markdown.
            cap_tex = subprocess.run(
                ['pandoc','-f','markdown+tex_math_dollars-smart','-t','latex'],input=cap,text=True,capture_output=True,check=True).stdout
            body.append(r'{\small '+cap_tex+'}\n')
        body.append(r'\clearpage')
    tex = temp/'figures-atlas.tex'
    tex.write_text(r'''\documentclass[11pt,a4paper]{article}
\usepackage{fontspec}
\usepackage{amsmath,amssymb}
\usepackage{unicode-math}
\usepackage{graphicx,longtable,booktabs,array}
\usepackage[colorlinks=true]{hyperref}
\PassOptionsToPackage{protrusion=false,nopatch=footnote}{microtype}
\input{'''+str(fonts)+r'''}
\input{'''+str(ROOT/'styles'/profile['header'])+r'''}
\geometry{left=15mm,right=15mm,top=18mm,bottom=20mm}
\hypersetup{pdftitle={'''+profile['atlas_pdftitle']+r'''},pdfsubject={'''+profile['atlas_pdfsubject']+r'''}}
\begin{document}
'''+ '\n'.join(body)+r'\end{document}')
    warnings=compile_tex(tex,output)
    return {'path':str(output),'layout_warnings':warnings,'tex':str(tex)}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('manuscript',nargs='?',type=Path,default=ROOT/'manuscript.md')
    ap.add_argument('--lang',choices=sorted(PROFILES),
                    help='Layout language profile; default is inferred from a -en manuscript name')
    ap.add_argument('--output',type=Path)
    ap.add_argument('--atlas',action='store_true')
    ap.add_argument('--atlas-only',action='store_true')
    ap.add_argument('--no-toc',action='store_true')
    ap.add_argument('--work-dir',type=Path)
    args=ap.parse_args()
    lang=args.lang or ('en' if args.manuscript.name.endswith('-en.md') else 'zh')
    profile=PROFILES[lang]
    if args.manuscript.name.startswith('supplement'):
        default_output = f'build/source-process-core-supplement{"-en" if lang == "en" else ""}.pdf'
        args.no_toc = True
    else:
        default_output = profile['default_output']
    output=args.output or ROOT/default_output
    temp=args.work_dir.resolve() if args.work_dir else ROOT/'build'/('pdf-work-en' if lang=='en' else 'pdf-work')
    temp.mkdir(parents=True,exist_ok=True)
    report=[]
    if not args.atlas_only:
        report.append(dict(lang=lang,**build_manuscript(args.manuscript.resolve(),output.resolve(),temp,profile,not args.no_toc)))
    if args.atlas or args.atlas_only:
        report.append(dict(lang=lang,**build_atlas(ROOT/profile['atlas_manifest'],ROOT/profile['atlas_output'],temp,profile,lang)))
    (temp/'build-report.json').write_text(json.dumps(report,ensure_ascii=False,indent=2))
    print(json.dumps(report,ensure_ascii=False,indent=2))

if __name__=='__main__': main()
