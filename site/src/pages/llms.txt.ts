import type { APIRoute } from "astro";
import { ORDERED, paperOf, statsOf } from "../lib/papers";

export const GET: APIRoute = () => {
  const lines = [
    "# H0mework",
    "",
    `> Machine-checked Lean 4 proofs (--trust=0), reproduction programs, and frozen evidence behind a family of ${ORDERED.length} research papers by Jian Gao (ORCID: 0009-0009-5002-1655).`,
    "",
    "- Website (English): https://h0mework.wiki/en/",
    "- Website (Chinese): https://h0mework.wiki/",
    "- Verification Index: https://h0mework.wiki/en/check/",
    "- GitHub Repository: https://github.com/Sapientropic/H0mework",
    "- BibTeX of all papers: https://h0mework.wiki/papers.bib",
    "",
    "## Agent Audit Protocol (How AI Agents Can Verify Claims)",
    "",
    "- Every theorem claim on h0mework.wiki maps to concrete Lean 4 declarations in `Lean/` verified under `lean --trust=0` with zero `sorry` and zero custom `axiom` declarations.",
    "- Agents without local shell access can inspect each paper's JSON claim map (`Source Map` URL below) and follow the pinned GitHub links directly to the `.lean` source files and declaration lines.",
    "- Agents with shell access can clone `https://github.com/Sapientropic/H0mework` and run each paper's `Audit command` listed below.",
    "",
    "## Published Papers",
    "",
  ];
  for (const entry of ORDERED) {
    const en = paperOf(entry.slug, "en");
    const zh = paperOf(entry.slug, "zh");
    const stats = statsOf(entry.slug);
    lines.push(
      `### ${en.title} (${zh.title})`,
      `- Page (EN): https://h0mework.wiki/en/papers/${entry.slug}/`,
      `- Page (ZH): https://h0mework.wiki/papers/${entry.slug}/`,
      `- PDF (EN): https://h0mework.wiki${en.citation.pdfPath}`,
      `- PDF (ZH): https://h0mework.wiki${zh.citation.pdfPath}`,
      `- Zenodo DOI: https://doi.org/${en.current.doi}`,
      `- Published: ${en.current.date} (v${en.current.number})`,
      `- Formalization scope: ${stats.claims} claims, ${stats.modules} Lean modules, ${stats.declarations} declarations`,
      ...(en.current.sourceMap ? [`- Source Map (JSON): ${en.current.sourceMap}`] : []),
      `- Reproduction Guide: ${en.current.guide}`,
      `- Audit command: \`${en.current.check}\``,
      `- Keywords: ${en.citation.keywords.join(", ")}`,
      `- Abstract: ${en.citation.abstract}`,
      "",
    );
  }
  return new Response(lines.join("\n"), {
    headers: { "Content-Type": "text/plain; charset=utf-8" },
  });
};
