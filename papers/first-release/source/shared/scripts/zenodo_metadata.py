#!/usr/bin/env python3
"""Write Zenodo upload metadata for the eight drafted papers.

Usage: zenodo_metadata.py [--only DIR[,DIR...]]

Each paper gets <paper dir>/zenodo-metadata.md with the web-form fields in the
order Zenodo's upload page asks for them. Titles, abstracts and keywords are
read from the manuscripts, so rerunning after an edit keeps them in step; the
PDFs listed are the current reading editions under each paper's build/.
"""
from __future__ import annotations

import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CODE = "https://github.com/Sapientropic/H0mework"
TAG = "papers-2026-09"
CREATOR = ("Gao, Jian", "0009-0009-5002-1655", "Independent Researcher")

# directory, zh manuscript, en manuscript (None: Chinese text with an English
# abstract), reading PDFs to upload (first one is the primary file)
PAPERS = [
    ("source-process-core", "manuscript.md", "manuscript-en.md",
     ["build/source-process-core-en.pdf", "build/source-process-core.pdf",
      "build/source-process-core-supplement-en.pdf", "build/source-process-core-supplement.pdf"]),
    ("physics-common-source", "manuscript.md", "manuscript-en.md",
     ["build/physics-common-source-en.pdf", "build/physics-common-source.pdf",
      "build/physics-common-source-supplement-en.pdf", "build/physics-common-source-supplement.pdf"]),
    ("low-energy-phenomenology", "manuscript.md", None, ["build/low-energy-phenomenology.pdf"]),
    ("low-energy-loop-response", "manuscript.md", None, ["build/low-energy-loop-response.pdf"]),
    ("constrained-local-quantum", "manuscript.md", None, ["build/constrained-local-quantum.pdf"]),
    ("native-flow/review-20260922-65001", "manuscript.md", None, ["build/native-flow.pdf"]),
    ("whole-ledger-accounting", "manuscript.md", None, ["build/whole-ledger-accounting.pdf"]),
    ("observation-dynamics", "manuscript.md", None, ["build/observation-dynamics.pdf"]),
]


def section(text: str, heading: str) -> str:
    m = re.search(r"(?ms)^#{1,3} " + heading + r"[^\n]*\n(.*?)(?=^#{1,3} |\Z)", text)
    if not m:
        raise SystemExit(f"no {heading} section")
    return m[1]


def split_keywords(block: str) -> tuple[str, list[str]]:
    m = re.search(r"(?m)^\*\*(?:关键词|Keywords)\s*[:：]?\*\*\s*[:：]?\s*(.+)$", block)
    body = block[:m.start()] if m else block
    words = [w.strip(" 。.") for w in re.split(r"[；;]", m[1])] if m else []
    paras = [re.sub(r"\s+", " ", p).strip() for p in re.split(r"\n\s*\n", body)]
    return "\n\n".join(p.replace("**", "") for p in paras if p), [w for w in words if w]


def english_title(text: str) -> str:
    for line in text.splitlines()[1:8]:
        m = re.fullmatch(r"(?:#{1,2} +(.+)|\*\*(.+)\*\*|\*(.+)\*)", line.strip())
        if m:
            t = next(g for g in m.groups() if g)
            if re.match(r"[A-Za-z]", t) and "COURTYCOURT" not in t.upper():
                return t
    raise SystemExit("no English title")


def pages(pdf: Path) -> int:
    info = subprocess.run(["pdfinfo", pdf], capture_output=True, text=True).stdout
    return int(re.search(r"Pages:\s+(\d+)", info)[1])


def write(paper: str, zh_name: str, en_name: str | None, pdfs: list[str]) -> Path:
    base = ROOT / "papers" / paper
    zh = (base / zh_name).read_text()
    title_zh = zh.splitlines()[0][2:].strip()
    title_en = english_title(zh)
    series = "CourtyCourt · The Theory Takes the Stand" if "COURTYCOURT" in zh[:600].upper() else ""
    abstract_zh, kw_zh = split_keywords(section(zh, "摘要"))
    if en_name:
        abstract_en, kw_en = split_keywords(section((base / en_name).read_text(), "Abstract"))
        languages = "English (eng), Chinese (zho) — English and Chinese editions"
    else:
        abstract_en, kw_en = split_keywords(section(zh, "Abstract"))
        languages = "Chinese (zho) — full text in Chinese with an English abstract"
    files = []
    for rel in pdfs:
        pdf = base / rel
        files.append(f"- `{pdf.relative_to(ROOT)}`（{pages(pdf)} 页）")
    out = base / "zenodo-metadata.md"
    binding = re.search(r"H0mework 固定提交 `([0-9a-f]{40})`", zh)
    code_relation = (f"{CODE}/tree/{binding[1]}（commit `{binding[1]}`）"
                     if binding else f"{CODE}（tag `{TAG}`）")
    out.write_text(f"""# Zenodo 上传元数据

由 `python3 shared/scripts/zenodo_metadata.py` 从正文生成；改稿后重新生成。字段按 Zenodo 上传页的顺序排列，逐项复制。Zenodo 记录发布后不能删除，只能发新版本。

## Files（上传）

{chr(10).join(files)}

## Resource type

Publication → Preprint

## Title

{title_en}

## Additional titles

- Translated title（Chinese）：{title_zh}

## Publication date

上传当天（Zenodo 默认值）。

## Creators

- Person：{CREATOR[0]}
- ORCID：{CREATOR[1]}
- Affiliation：{CREATOR[2]}
- Role：（留空；独著）

## Description

{abstract_en}

## Additional descriptions

- Type：Abstract；Language：Chinese

{abstract_zh}

## Licenses

Creative Commons Attribution 4.0 International（CC BY 4.0）。代码仓另为 Apache-2.0。

## Keywords and subjects

{"; ".join(kw_en)}

## Languages

{languages}

## Version

v1

## Related works

- Relation：Is supplemented by；Identifier：{code_relation}；Scheme：URL；Resource type：Software

## Notes（可选）

{("Part of the series " + series + ". ") if series else ""}Formal proofs, exact programs and frozen receipts are in the code repository above; the paper's "Code and data availability" section gives the entry modules and reproduction commands.
""")
    return out


if __name__ == "__main__":
    import sys
    only = set()
    argv = sys.argv[1:]
    i = 0
    while i < len(argv):
        if argv[i] == "--only":
            i += 1
            only.update(d for d in argv[i].split(",") if d)
        i += 1
    for spec in PAPERS:
        if only and spec[0] not in only:
            continue
        print("wrote", write(*spec).relative_to(ROOT))
