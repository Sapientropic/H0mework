"""Author byline shared by the PDF builders.

A manuscript states its byline right under the title as two Markdown lines:

    **作者：高健（Jian Gao）**\\
    独立研究者 · innersummer@hotmail.com · ORCID 0009-0009-5002-1655

(English drafts use "**Author: ...**"). The Markdown lines stay the single
source; builders pop them from the body and typeset them on the title page via
the style's \\paperbyline{name}{details}.
"""
from __future__ import annotations

import re
from typing import Callable

LINE = re.compile(r"\*\*(?:作者|Authors?)\s*[：:]\s*(.+?)\*\*\\?")
EMAIL = re.compile(r"[\w.+-]+@[\w-]+(?:\.[\w-]+)+")
ORCID = re.compile(r"ORCID\s+(\d{4}-\d{4}-\d{4}-\d{3}[\dX])")


def pop(lines: list[str], window: int = 16) -> tuple[str, str]:
    """Remove the byline (name line plus details line) from the top of lines."""
    for i, line in enumerate(lines[:window]):
        m = LINE.fullmatch(line.strip())
        if m:
            details = ""
            if i + 1 < len(lines) and lines[i + 1].strip():
                details = lines.pop(i + 1).strip()
            lines.pop(i)
            return m[1].strip(), details
    return "", ""


def tex(name: str, details: str, escape: Callable[[str], str]) -> str:
    """\\paperbyline command with the e-mail and ORCID iD as live links."""
    if not name:
        return ""
    out, pos = [], 0
    spans = sorted([(m.start(), m.end(), "mail", m[0]) for m in EMAIL.finditer(details)]
                   + [(m.start(), m.end(), "orcid", m[1]) for m in ORCID.finditer(details)])
    for start, end, kind, value in spans:
        out.append(escape(details[pos:start]))
        if kind == "mail":
            out.append(r"\href{mailto:" + value + "}{" + escape(value) + "}")
        else:
            out.append(r"\href{https://orcid.org/" + value + "}{ORCID " + value + "}")
        pos = end
    out.append(escape(details[pos:]))
    # xeCJK treats "·" as CJK punctuation and swallows the spaces around it.
    body = "".join(out).replace(" · ", r"\hspace{0.55em}\textperiodcentered\hspace{0.55em}")
    return r"\paperbyline{" + escape(name) + "}{" + body + "}\n"
