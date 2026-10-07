#!/usr/bin/env python3
"""Build an English-only arXiv source package for a paper with its own builder.

Usage: arxiv_package.py <paper directory>   (source-process-core, physics-common-source)

The paper's manuscript-en.md stays the content source. The package drops the
Chinese title, the Chinese abstract and the Chinese form of the author name,
then reuses the paper's own layout code (prepare(), Lua filter, English header)
so the arXiv PDF matches the English reading edition. arXiv compiles XeLaTeX
with TeX Live 2025 and resolves fonts by file name only, so the header keeps the
Latin Modern OTF files shipped with TeX Live and drops xeCJK and Noto CJK.

Output in <paper>/build/arxiv/: the unpacked source tree, <paper>-arxiv.tar.gz
and <paper>-arxiv.pdf, which is compiled from an extracted copy of the tarball
so that nothing outside the package is used.
"""
from __future__ import annotations

import importlib.util
import json
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path

import byline

PUBLISH = Path(__file__).resolve().parents[2]
CJK = re.compile(r"[　-〿㐀-鿿＀-￯]")
CJK_HEADER = re.compile(r"^.*(xeCJK|CJKFontDir|setCJK|xeCJKsetup).*\n", re.M)
README = {"spec_version": 1, "process": {"compiler": "xelatex"},
          "sources": [{"filename": "main.tex", "usage": "toplevel"}],
          "texlive_version": 2025}


def load_builder(paper: Path):
    spec = importlib.util.spec_from_file_location("paper_builder", paper / "scripts/build_pdf.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def english_only(text: str) -> str:
    lines = text.splitlines()
    title = next(i for i, l in enumerate(lines) if l.startswith("# "))
    # The Chinese title is the fully bold CJK line right under the English one.
    for i in range(title + 1, title + 6):
        if CJK.search(lines[i]) and lines[i].startswith("**") and lines[i].endswith("**"):
            del lines[i]
            break
    text = "\n".join(lines) + "\n"
    # The Chinese abstract runs from its heading to the next heading.
    text = re.sub(r"(?ms)^#{1,3} 摘要\n.*?(?=^#{1,3} )", "", text, count=1)
    # "Jian Gao (高健)" -> "Jian Gao".
    text = re.sub(r"(\*\*Authors?:[^*\n]*?)\s*\([^)\n]*[㐀-鿿][^)\n]*\)", r"\1", text)
    left = [(n, l[:80]) for n, l in enumerate(text.splitlines(), 1) if CJK.search(l)]
    if left:
        raise SystemExit("Chinese text left in the English package:\n"
                         + "\n".join(f"  line {n}: {l}" for n, l in left))
    return text


def run(cmd, cwd):
    result = subprocess.run([str(c) for c in cmd], cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        print(result.stdout[-8000:])
        raise SystemExit(f"failed: {cmd[0]}")
    return result.stdout


def figure_fonts(pdf: Path) -> list[str]:
    """Problems with one figure PDF: a font not embedded, or Chinese text.

    An embedded CJK font by itself is fine (e.g. circled digits in an English
    figure); arXiv never needs the font file."""
    bad = []
    for row in run(["pdffonts", pdf], pdf.parent).splitlines()[2:]:
        cols = row.split()
        if cols[-5] != "yes":
            bad.append(f"{pdf.name}: font {cols[0]} not embedded")
    if CJK.search(run(["pdftotext", pdf, "-"], pdf.parent)):
        bad.append(f"{pdf.name}: Chinese text in figure")
    return bad


def build(paper: Path) -> dict:
    mod = load_builder(paper)
    profile = mod.PROFILES["en"]
    out = paper / "build/arxiv"
    src = out / "src"
    shutil.rmtree(out, ignore_errors=True)
    (src / "figures").mkdir(parents=True)
    work = out / "work"
    work.mkdir()

    lines = english_only((paper / "manuscript-en.md").read_text()).splitlines()
    author, details = byline.pop(lines)
    title, subtitle, body = mod.prepare("\n".join(lines) + "\n", True, profile)
    if subtitle:
        raise SystemExit(f"unexpected subtitle picked up: {subtitle!r}")

    supplement = paper / "supplement-en.md"
    if supplement.is_file():
        supp_lines = english_only(supplement.read_text()).splitlines()
        byline.pop(supp_lines)
        _supp_title, _supp_subtitle, supp_body = mod.prepare(
            "\n".join(supp_lines) + "\n", False, profile)
        body += ("\n\n```{=latex}\n\\clearpage\n```\n\n"
                 "# Supplementary material: complete proofs\n\n" + supp_body)

    (work / "manuscript-layout.md").write_text(body)

    header = CJK_HEADER.sub("", (paper / "styles" / profile["header"]).read_text())
    header = header.replace("xeCJK stays because the manuscript keeps the bilingual\n"
                            "% title and the Chinese abstract.",
                            "arXiv edition: English only, fonts from TeX Live by file name.")
    header += "\n" + byline.tex(author, details, mod.escape)
    (work / "header.tex").write_text(header)

    tex = src / "main.tex"
    run(["pandoc", work / "manuscript-layout.md",
         "-f", "markdown+tex_math_dollars+raw_tex-smart", "-t", "latex",
         "--standalone", "--top-level-division=section",
         "--resource-path", f"{paper}:{paper}",
         "--lua-filter", paper / "styles/article-filter.lua",
         "--include-in-header", work / "header.tex",
         "--metadata", "title=" + title, "--metadata", "lang=en",
         "-V", "documentclass=article", "-V", "fontsize=11pt",
         "-V", "microtypeoptions=protrusion=false,nopatch=footnote",
         "-V", "colorlinks=true", "-o", tex], paper)

    problems, copied = [], []

    def local_graphic(m):
        path = Path(m[2])
        path = path if path.is_absolute() else paper / path
        target = src / "figures" / path.name
        if not target.exists():
            shutil.copy2(path, target)
            copied.append(path.name)
            if path.suffix == ".pdf":
                problems.extend(figure_fonts(target))
        return m[1] + "{figures/" + path.name + "}"

    text = re.sub(r"(\\includegraphics(?:\[[^\]]*\])?)\{([^}]+)\}", local_graphic, tex.read_text())
    if "/Users/" in text or CJK.search(text):
        problems.append("main.tex still has an absolute path or Chinese text")
    tex.write_text(text)
    (src / "00README.json").write_text(json.dumps(README, indent=2) + "\n")

    name = paper.name + "-arxiv"
    tarball = out / (name + ".tar.gz")
    with tarfile.open(tarball, "w:gz") as tar:
        for f in sorted(src.rglob("*")):
            if f.is_file():
                tar.add(f, arcname=str(f.relative_to(src)))

    # Compile from an extracted copy of the tarball: only packaged files count.
    with tempfile.TemporaryDirectory() as tmp:
        with tarfile.open(tarball) as tar:
            tar.extractall(tmp, filter="data")
        for _ in range(3):
            run(["xelatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"], tmp)
        log = (Path(tmp) / "main.log").read_text(errors="replace")
        shutil.copy2(Path(tmp) / "main.pdf", out / (name + ".pdf"))
        shutil.copy2(Path(tmp) / "main.log", work / "main.log")
    missing = sorted(set(re.findall(r"Missing character: There is no (.+?) in font", log)))
    overfull = len(re.findall(r"^Overfull", log, re.M))
    undefined = len(re.findall(r"undefined", log))
    fonts = run(["pdffonts", out / (name + ".pdf")], out).splitlines()[2:]
    not_embedded = [r.split()[0] for r in fonts if r.split()[-5] != "yes"]
    pages = re.search(r"Pages:\s+(\d+)", run(["pdfinfo", out / (name + ".pdf")], out))[1]
    report = {"paper": paper.name, "tarball": str(tarball.relative_to(PUBLISH)),
              "tarball_bytes": tarball.stat().st_size, "files": len(copied) + 2,
              "figures": copied, "pages": int(pages), "compiler": "xelatex",
              "local_tex": run(["xelatex", "--version"], out).splitlines()[0],
              "missing_characters": missing, "overfull_boxes": overfull,
              "undefined_warnings": undefined, "fonts_not_embedded": not_embedded,
              "problems": problems}
    (out / "package-report.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
    return report


if __name__ == "__main__":
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    print(json.dumps(build(Path(sys.argv[1]).resolve()), ensure_ascii=False, indent=2))
