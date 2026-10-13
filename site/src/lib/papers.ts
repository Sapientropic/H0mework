// Build-time view of a paper: titles and abstract from its latest manuscript, editions, files and
// claim statistics. Every fact shown on the site is read from the repository, never retyped.
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { unified } from "unified";
import remarkParse from "remark-parse";
import remarkMath from "remark-math";
import remarkRehype from "remark-rehype";
import rehypeKatex from "rehype-katex";
import rehypeStringify from "rehype-stringify";
import katex from "katex";
import { PAPERS, RELEASES, entryOf, manuscriptOf, once, repoLink, type Lang } from "./registry";
import { claimsOf } from "./claims";

export { PAPERS, type Lang };

const markdown = unified().use(remarkParse).use(remarkMath).use(remarkRehype).use(rehypeKatex, { throwOnError: false }).use(rehypeStringify);
// Some manuscripts write math as \( \) and \[ \]; remark-math reads only dollars.
const dollars = (text: string) => text.replace(/\\\[([\s\S]+?)\\\]/g, (_, m) => `$$${m}$$`).replace(/\\\(([\s\S]+?)\\\)/g, (_, m) => `$${m}$`);
export const renderMarkdown = (text: string) => String(markdown.processSync(dollars(text)));
const plain = (text: string) => text.replace(/\$+([^$]*)\$+/g, "$1").replace(/\\[()[\]]/g, "").replace(/[*_`]/g, "").replace(/\s+/g, " ").trim();
export const renderInline = (text: string) => renderMarkdown(text).replace(/^<p>|<\/p>\s*$/g, "");

// Claim texts are plain text with `code` and $math$ only: "*" there is multiplication, not emphasis.
const escape = (text: string) => text.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
function claimInline(text: string) {
  return text
    .split(/(\$\$[\s\S]+?\$\$|\$[^$\n]+?\$|`[^`]+`)/)
    .map((part, index) => {
      if (index % 2 === 0) return escape(part);
      if (part.startsWith("`")) return `<code>${escape(part.slice(1, -1))}</code>`;
      const display = part.startsWith("$$");
      return katex.renderToString(part.slice(display ? 2 : 1, display ? -2 : -1), { displayMode: display, throwOnError: false });
    })
    .join("");
}
export const renderClaim = (text: string) => text.split(/\n\s*\n/).map((paragraph) => `<p>${claimInline(paragraph.trim())}</p>`).join("");
export const renderClaimTitle = claimInline;

// Titles are "main：subtitle"; the two parts are shown at two levels.
function splitTitle(title: string) {
  const at = title.search(/：|: /);
  return at < 0 ? { main: title, sub: "" } : { main: title.slice(0, at), sub: title.slice(at).replace(/^(：|: )/, "") };
}
const titleOf = (manuscript: string) => manuscript.split("\n", 1)[0].replace(/^#\s+/, "").trim();

function abstractOf(manuscript: string, lang: Lang) {
  const lines = manuscript.split("\n");
  const start = lines.findIndex((line) => line.trim() === (lang === "zh" ? "## 摘要" : "## Abstract"));
  const end = lines.findIndex((line, index) => index > start && /^(##|---)/.test(line));
  return lines
    .slice(start + 1, end)
    .join("\n")
    .trim()
    .split(/\n\s*\n/)
    .filter((paragraph) => !/^\*\*(关键词|Keywords)/.test(paragraph));
}

export function paperOf(slug: string, lang: Lang) {
  const entry = entryOf(slug);
  const editions = entry.editions.map((edition, index) => {
    const release = RELEASES[edition.release];
    const files = release.files(slug, lang);
    return {
      number: index + 1,
      date: release.date,
      doi: edition.doi,
      doiLink: `https://doi.org/${edition.doi}`,
      pdf: repoLink(files.pdf),
      supplement: files.supplement && repoLink(files.supplement),
      arxiv: files.arxiv && repoLink(files.arxiv),
      check: release.check,
      guide: repoLink(release.guide),
    };
  });
  const latest = entry.editions.at(-1)!.release;
  const manuscript = manuscriptOf(latest, slug, lang);
  const title = titleOf(manuscript);
  const abstract = abstractOf(manuscript, lang);
  return {
    ...entry,
    title,
    ...splitTitle(title),
    other: titleOf(manuscriptOf(latest, slug, lang === "zh" ? "en" : "zh")),
    editions,
    current: editions.at(-1)!,
    abstractLead: renderMarkdown(abstract[0]),
    // Plain first sentences of the abstract for the page description.
    summary: plain(abstract[0]).match(/^.{40,160}?(。|[.!?](?=\s|$))/)?.[0] ?? plain(abstract[0]).slice(0, 160),
    abstractRest: renderMarkdown(abstract.slice(1).join("\n\n")),
  };
}

// Chapter headings of the latest manuscript, keyed "6" or "A", for dividers in the claim list.
export function chaptersOf(slug: string, lang: Lang) {
  return once(`chapters:${slug}:${lang}`, () => {
    const chapters = new Map<string, string>();
    for (const line of manuscriptOf(entryOf(slug).editions.at(-1)!.release, slug, lang).split("\n")) {
      const heading = line.match(/^##\s+(?:(\d+)|(?:附录|Appendix)\s*([A-Z]))[\s　.:：]+(.+)$/);
      if (heading) chapters.set(heading[1] ?? heading[2], renderInline(heading[3].trim()));
    }
    return chapters;
  });
}

export function statsOf(slug: string) {
  const rows = claimsOf(slug, "zh");
  const leans = rows.flatMap((row) => row.lean);
  return {
    claims: new Set(rows.flatMap((row) => row.ids)).size,
    modules: new Set(leans.map((lean) => lean.module)).size,
    declarations: new Set(leans.flatMap((lean) => lean.declarations.map((decl) => decl.qualified))).size,
  };
}

// The static first frame of a figure, for thumbnails.
export function figureSvgOf(name: string) {
  const fragment = JSON.parse(readFileSync(resolve(process.cwd(), "src/generated", `${name}.json`), "utf8"));
  return String(fragment.html.zh.match(/<svg[\s\S]*?<\/svg>/)?.[0] ?? "");
}
