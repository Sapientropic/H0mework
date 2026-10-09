#!/usr/bin/env python3
"""Build the preprint reading PDF of a drafted manuscript with the shared layout.

Usage (from the publish root):
  python3 shared/scripts/build_pdf.py papers/<paper>/manuscript.md
  python3 shared/scripts/build_pdf.py --all

The output goes to <manuscript dir>/build/<paper>.pdf (or <paper>-en.pdf for a
-en manuscript); intermediates stay in <manuscript dir>/build/pdf-work[-en]/.
Typography follows papers/physics-common-source/styles; running heads come from
RUNHEADS below. Links into the local workspace print as plain text (see
shared/styles/article-filter.lua). No mathematical expression or statement is
edited. Requires Python 3, pandoc 3, XeLaTeX with xeCJK, Google Chrome (SVG
figures), and Noto Serif/Sans CJK SC in ~/Library/Fonts or /Library/Fonts.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
from pathlib import Path

import byline

PUBLISH = Path(__file__).resolve().parents[2]
STYLES = PUBLISH / "shared" / "styles"

# manuscript -> (paper id, left head, right head). source-process-core and
# physics-common-source keep their own scripts/build_pdf.py (figure atlases).
RUNHEADS = {
    "papers/low-energy-phenomenology/manuscript.md": ("low-energy-phenomenology", "共同源低能展开", "传播谱、物质交换与量子响应"),
    "papers/low-energy-loop-response/manuscript.md": ("low-energy-loop-response", "CourtyCourt · Case 2", "有序闭迹与整球响应曲率"),
    "papers/constrained-local-quantum/manuscript.md": ("constrained-local-quantum", "CourtyCourt · Case 5A", "原作用约束与共同量子 Hamiltonian"),
    "papers/native-flow/review-20260922-65001/manuscript.md": ("native-flow", "同源流", "有限宏修订、完整应力与晚时全阶演化"),
    "papers/whole-ledger-accounting/manuscript.md": ("whole-ledger-accounting", "整账法", "账平了，债还在"),
    "papers/observation-dynamics/manuscript.md": ("observation-dynamics", "自主观察", "未来来收压缩账单"),
}
PROFILES = {
    "zh": {"caution": "[注意]", "lang": "zh-CN", "header": "article-header.tex"},
    "en": {"caution": "[Caution]", "lang": "en", "header": "article-header-en.tex"},
}
APPENDIX = r"^# +(附录|Appendix)\b[^\n]*$"
REFERENCES = r"^# +(参考文献|References)\s*$"
FIRST_SECTION = r"^# +1(?:[\s.．　]|$)[^\n]*$"
# Short technical appendices continue after closing explanations, avoiding a
# few-line carry-over page immediately followed by another forced page break.
CONTINUOUS_APPENDICES = {"papers/low-energy-loop-response/manuscript.md"}


def run(cmd, cwd=None):
    result = subprocess.run([str(x) for x in cmd], cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        print(result.stdout[-16000:])
        raise RuntimeError(f"Command failed ({result.returncode}): {cmd[0]}")
    return result.stdout


def escape(s):
    return re.sub(r"[\\{}#$%&_~^]", lambda m: {
        "\\": r"\textbackslash{}", "{": r"\{", "}": r"\}", "#": r"\#", "$": r"\$",
        "%": r"\%", "&": r"\&", "_": r"\_", "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}"}[m.group()], s)


def latin_title(line: str) -> str | None:
    """English title line under the Chinese title: '# X', '## X', '**X**' or '*X*'."""
    m = re.fullmatch(r"(?:#{1,2} +(.+)|\*\*(.+)\*\*|\*(.+)\*)", line.strip())
    if not m:
        return None
    text = next(g for g in m.groups() if g)
    if not re.match(r"[A-Za-z]", text) or text.upper() == text or "COURTYCOURT" in text.upper():
        return None  # series tags such as COURTYCOURT stay in the body
    return text


def number_citations(body: str) -> str:
    """Turn pandoc-style [@Key, locator] citations into numbered ones.

    The reference list is written by hand with entries opening "[Key] ...";
    keys are numbered in list order and the labels become [n]. Locators and
    entry text stay verbatim; an unknown key is left visible."""
    if "[@" not in body:
        return body
    refs = re.search("(?m)" + REFERENCES, body)
    if refs is None:
        return body
    keys = re.findall(r"(?m)^\[([A-Za-z][A-Za-z0-9]+)\]\s", body[refs.end():])
    number = {k: str(i) for i, k in enumerate(keys, 1)}

    def cite(m):
        parts = []
        for item in m[1].split(";"):
            key, _, loc = item.strip().lstrip("@").partition(",")
            if key.strip() not in number:
                return m[0]
            parts.append(number[key.strip()] + ("," + loc if loc else ""))
        return "[" + "; ".join(parts) + "]"
    body = re.sub(r"\[(@[^\]]+)\]", cite, body)
    refs = re.search("(?m)" + REFERENCES, body)
    tail = re.sub(r"(?m)^\[([A-Za-z][A-Za-z0-9]+)\](?=\s)",
                  lambda m: "[" + number[m[1]] + "]" if m[1] in number else m[0],
                  body[refs.end():])
    return body[:refs.end()] + tail


def prepare(source: str, toc: bool, profile) -> tuple[str, str, str]:
    lines = source.splitlines()
    title_idx = next(i for i, l in enumerate(lines) if l.startswith("# "))
    title = lines.pop(title_idx)[2:].strip()
    subtitle = ""
    for i, line in enumerate(lines[title_idx:title_idx + 8], start=title_idx):
        found = latin_title(line)
        if found and found != title:
            subtitle = found
            lines.pop(i)
            break
    body = "\n".join(lines).lstrip()
    # Section headings supply the printed separation; a manuscript rule may
    # otherwise be stranded immediately before a forced page break.
    body = re.sub(r"(?m)^---[ \t]*$", "", body)
    body = body.replace("[⚠️]", profile["caution"])
    # \tag belongs to the outer display, not an inner aligned/split block.
    body = re.sub(r"\\tag\{([^}]+)\}\s*\\end\{(aligned|split)\}", r"\\end{\2}\\tag{\1}", body)
    # {\rm name, ...} would also switch the trailing symbols to the text font.
    body = re.sub(r"\{\\rm\s+([A-Za-z]+)", r"{\\mathrm{\1}", body)
    # unicode-math needs braces around a font command used as a bare script.
    body = re.sub(r"([_^])\\(mathbb|mathcal|mathrm|mathfrak|mathsf|mathbf|boldsymbol)\s*([A-Za-z0-9])",
                  r"\1{\\\2 \3}", body)
    body = re.sub(r"```mermaid\s*\n.*?```\s*", "", body, flags=re.S)
    body = re.sub(r"<!--.*?-->\n?", "", body, flags=re.S)
    # An anchor line glued to a heading would swallow the heading into a paragraph.
    body = re.sub(r"(?m)^(<a id=[^\n]*</a>)[ \t]*\n(#)", r"\1\n\n\2", body)
    body = re.sub(r"^(#{2,6}) ", lambda m: m[1][1:] + " ", body, flags=re.M)
    body = number_citations(body)
    # Each abstract and its keywords form one block. Short bilingual abstracts
    # can share the title page; a longer second abstract moves whole.
    body = re.sub(r"(?ms)^(#{1,2} (?:摘要|Abstract(?: \(English\))?))\n(.*?)(?=^#{1,2} |\Z)",
                  lambda m: "```{=latex}\n\\noindent\\begin{minipage}{\\linewidth}\n```\n\n"+m[1]
                  +"\n\n```{=latex}\n\\begingroup\\small\\setstretch{1.16}\n```\n"+m[2]
                  +"\n```{=latex}\n\\endgroup\\end{minipage}\\par\n```\n\n",body)
    appendix_started = False
    def appendix_start(match):
        nonlocal appendix_started
        new_page = not profile.get("continuous_appendices") or not appendix_started
        appendix_started = True
        return ("```{=latex}\n\\clearpage\n```\n\n" if new_page else "") + match[0]
    body = re.sub("(?m)" + APPENDIX, appendix_start, body)
    if re.search("(?m)" + REFERENCES, body):
        body = re.sub("(?m)" + REFERENCES,
                      lambda m: "```{=latex}\n\\noindent\\begin{minipage}{\\linewidth}\n```\n\n"+m[0]
                      + "\n\n```{=latex}\n\\begingroup\\footnotesize\\setstretch{1.13}"
                      "\\setlength{\\parindent}{0pt}\\setlength{\\parskip}{0.45em}\n```",
                      body, count=1)
        body += "\n\n```{=latex}\n\\endgroup\\end{minipage}\\par\n```\n"
    if toc:
        body = re.sub("(?m)" + FIRST_SECTION,
                      lambda m: "```{=latex}\n\\clearpage\n{\\small\\tableofcontents}\n\\clearpage\n```\n\n" + m[0],
                      body, count=1)
    return title, subtitle, body


CHROME = "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"


def svg_to_pdf(svg: Path, pdf: Path):
    """Print one SVG to a vector PDF page of its own size with headless Chrome.

    Chrome's font fallback matches what the authors reviewed in the HTML
    previews; cairosvg dropped sub/superscript and math glyphs to boxes."""
    head = svg.read_text(errors="replace")[:4000]
    box = re.search(r'viewBox="\s*[-\d.]+[\s,]+[-\d.]+[\s,]+([\d.]+)[\s,]+([\d.]+)', head)
    if box is None:
        raise RuntimeError(f"SVG without viewBox: {svg}")
    w, h = box.group(1), box.group(2)
    page = pdf.with_suffix(".html")
    page.write_text("<!doctype html><html><head><style>"
                    f"@page{{size:{w}px {h}px;margin:0}}html,body{{margin:0;padding:0}}"
                    f"img{{display:block;width:{w}px;height:{h}px}}</style></head>"
                    f'<body><img src="{svg.as_uri()}"></body></html>')
    run([CHROME, "--headless=new", "--disable-gpu", "--no-pdf-header-footer",
         "--allow-file-access-from-files", f"--print-to-pdf={pdf}", page.as_uri()])
    if not pdf.exists():
        raise RuntimeError(f"Chrome did not print {svg}")


def vector_figures(body: str, base: Path, temp: Path) -> str:
    """Point SVG figures at vector PDFs: a sibling .pdf if the paper ships one,
    otherwise a headless-Chrome print inside the build directory."""
    out_dir = temp / "figures"

    def swap(m):
        path = m[2]
        if not path.endswith(".svg") or re.match(r"https?://", path):
            return m[0]
        svg = (base / path).resolve()
        sibling = svg.with_suffix(".pdf")
        if sibling.exists():
            return m[1] + "(" + str(sibling) + m[3] + ")"
        out_dir.mkdir(parents=True, exist_ok=True)
        pdf = out_dir / (svg.stem + ".pdf")
        if not pdf.exists() or pdf.stat().st_mtime < svg.stat().st_mtime:
            svg_to_pdf(svg, pdf)
        return m[1] + "(" + str(pdf) + m[3] + ")"
    return re.sub(r"(!\[[^\]]*\])\(([^)\s]+)((?:\s+\"[^\"]*\")?)\)", swap, body)


def compile_tex(tex: Path):
    for suffix in (".aux", ".toc", ".out"):
        tex.with_suffix(suffix).unlink(missing_ok=True)
    for _ in range(3):
        run(["xelatex", "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", tex.name],
            cwd=tex.parent)


def fit_wide_displays(tex: Path, tolerance: float = 3.0) -> int:
    """Scale display equations that overran the text width in the last run.

    Only the rendered size changes: the display body is wrapped whole in a
    width-limited box, and a \\tag stays outside the box so numbering is kept."""
    log = tex.with_suffix(".log").read_text(errors="replace")
    ends = {int(m[2]) for m in re.finditer(r"Overfull \\hbox \(([\d.]+)pt too wide\) detected at line (\d+)", log)
            if float(m[1]) > tolerance}
    if not ends:
        return 0
    lines = tex.read_text().split("\n")
    fitted = 0
    for end in sorted(ends, reverse=True):
        i = end - 1
        if i >= len(lines) or not lines[i].rstrip().endswith("\\]"):
            continue
        start = i
        while start >= 0 and "\\[" not in lines[start]:
            start -= 1
        if start < 0:
            continue
        block = "\n".join(lines[start:i + 1])
        head, _, rest = block.partition("\\[")
        body, _, tail = rest.rpartition("\\]")
        tag = re.search(r"\\tag\{[^}]*\}\s*$", body)
        label = ""
        if tag:
            label, body = tag.group(0).strip(), body[:tag.start()]
        # Leave room for the equation number so it stays on the same line.
        width = "0.9\\linewidth" if label else "\\linewidth"
        wrapped = (head + "\\[\\adjustbox{max width=" + width + "}{$\\displaystyle " + body.strip()
                   + "$}" + label + "\\]" + tail)
        lines[start:i + 1] = wrapped.split("\n")
        fitted += 1
    tex.write_text("\n".join(lines))
    return fitted


def build(rel: str, toc: bool = True) -> dict:
    source = (PUBLISH / rel).resolve()
    paper, left, right = RUNHEADS[rel]
    lang = "en" if source.name.endswith("-en.md") else "zh"
    profile = dict(PROFILES[lang], continuous_appendices=rel in CONTINUOUS_APPENDICES)
    build_dir = source.parent / "build"
    temp = build_dir / ("pdf-work-en" if lang == "en" else "pdf-work")
    temp.mkdir(parents=True, exist_ok=True)
    output = build_dir / (paper + ("-en" if lang == "en" else "") + ".pdf")

    lines = source.read_text().splitlines()
    author, details = byline.pop(lines)
    title, subtitle, body = prepare("\n".join(lines) + "\n", toc, profile)
    body = vector_figures(body, source.parent, temp)
    normalized = temp / "manuscript-layout.md"
    normalized.write_text(body)
    font_dir = next((d for d in (Path.home() / "Library/Fonts", Path("/Library/Fonts"))
                     if (d / "NotoSerifCJKsc-Regular.otf").exists()), None)
    if font_dir is None:
        raise RuntimeError("Noto Serif/Sans CJK SC fonts not found in Library/Fonts")
    params = temp / "paper-params.tex"
    params.write_text("\\newcommand{\\CJKFontDir}{" + str(font_dir) + "}\n"
                      "\\newcommand{\\PaperRunHeadLeft}{" + left + "}\n"
                      "\\newcommand{\\PaperRunHeadRight}{" + right + "}\n")
    subtitle_tex = temp / "subtitle.tex"
    subtitle_tex.write_text("\\papersubtitle{" + escape(subtitle) + "}\n"
                            + byline.tex(author, details, escape))
    tex = temp / "manuscript.tex"
    run(["pandoc", normalized, "-f", "markdown+tex_math_dollars+tex_math_single_backslash+raw_tex-smart", "-t", "latex",
         "--standalone", "--top-level-division=section",
         "--resource-path", str(source.parent),
         "--lua-filter", STYLES / "article-filter.lua",
         "--include-in-header", params,
         "--include-in-header", STYLES / profile["header"],
         "--include-in-header", subtitle_tex,
         "--metadata", "title=" + title, "--metadata", "lang=" + profile["lang"],
         "-V", "documentclass=article", "-V", "fontsize=11pt",
         "-V", "microtypeoptions=protrusion=false,nopatch=footnote",
         "-V", "colorlinks=true", "-o", tex], cwd=source.parent)
    ts = tex.read_text()

    def absolute_graphic(m):
        p = Path(m[2])
        p = p if p.is_absolute() else source.parent / p
        return m[1] + "{" + str(p.resolve()) + "}"
    tex.write_text(re.sub(r"(\\includegraphics(?:\[[^\]]*\])?)\{([^}]+)\}", absolute_graphic, ts))
    compile_tex(tex)
    fitted = fit_wide_displays(tex)
    if fitted:
        compile_tex(tex)
    shutil.copy2(tex.with_suffix(".pdf"), output)
    log = tex.with_suffix(".log").read_text(errors="replace")
    missing = sorted({l.strip() for l in log.splitlines() if "Missing character" in l})
    overfull = sum(1 for l in log.splitlines() if l.startswith("Overfull"))
    report = {"manuscript": rel, "pdf": str(output.relative_to(PUBLISH)), "subtitle": subtitle,
              "fitted_displays": fitted,
              "missing_characters": missing, "overfull_boxes": overfull}
    (temp / "build-report.json").write_text(json.dumps(report, ensure_ascii=False, indent=2))
    return report


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("manuscripts", nargs="*")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--no-toc", action="store_true")
    args = ap.parse_args()
    targets = list(RUNHEADS) if args.all else args.manuscripts
    reports = []
    for rel in targets:
        try:
            reports.append(build(rel, not args.no_toc))
        except Exception as error:  # report every paper, keep building the rest
            reports.append({"manuscript": rel, "error": str(error)})
        print(json.dumps(reports[-1], ensure_ascii=False))
    if any("error" in r for r in reports):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
