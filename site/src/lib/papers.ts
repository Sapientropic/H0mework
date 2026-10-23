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
import { PAPERS, RELEASES, THEMES, entryOf, manuscriptOf, once, repoLink, type Lang, type ThemeId } from "./registry";
import { claimsOf } from "./claims";

export { PAPERS, THEMES, type Lang };

// Index order: by theme, then as registered. The paper index and the pager both follow it.
export const ORDERED = THEMES.flatMap((theme) => PAPERS.filter((paper) => paper.theme === theme.id));
export const themeOf = (id: ThemeId) => THEMES.find((theme) => theme.id === id)!;
// View-transition names: a paper's title and figure keep their place across pages.
export const vtTitle = (slug: string) => `vt-t-${slug}`;
export const vtFigure = (slug: string) => `vt-f-${slug}`;

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
// A statement quoted from a manuscript: formulas are typeset first, so a display written on one line
// with its text or inside a list item stays a display, and Markdown never reads inside a formula.
export function renderPaperText(text: string) {
  const formulas: string[] = [];
  const keep = (tex: string, displayMode: boolean) => `KATEX${formulas.push(katex.renderToString(tex.trim(), { displayMode, throwOnError: false })) - 1}X`;
  const masked = text
    .replace(/\$\$([\s\S]+?)\$\$|\\\[([\s\S]+?)\\\]/g, (_, a, b) => keep(a ?? b, true))
    // Inline math may wrap across lines, never across paragraphs.
    .replace(/\$((?:[^$\n]|\n(?!\s*\n))+?)\$|\\\(([\s\S]+?)\\\)/g, (_, a, b) => keep(a ?? b, false));
  return String(markdown.processSync(masked)).replace(/KATEX(\d+)X/g, (_, i) => formulas[+i]);
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
    // Keywords stay in the PDF; a bare section anchor is markup, not a paragraph.
    .filter((paragraph) => !/^\*\*(关键词|Keywords)/.test(paragraph) && paragraph.replace(/<[^>]+>/g, "").trim());
}

// Sentences of a markdown paragraph, cut after 。！？ or an English full stop before a capital; math is
// masked first so a stop inside a formula never cuts, and common abbreviations do not end a sentence.
function sentencesOf(paragraph: string, lang: Lang) {
  const math: string[] = [];
  const text = dollars(paragraph).replace(/\$\$[\s\S]+?\$\$|\$[^$\n]+?\$/g, (m) => `\u0000${math.push(m) - 1}\u0000`);
  const stop = lang === "zh" ? /[。！？][”」』）]*/g : /[.!?][”’")\]]*(?=\s+[A-Z“‘"(\u0000])/g;
  const cuts: number[] = [];
  for (const m of text.matchAll(stop)) {
    if (lang === "en" && /\b(e\.g|i\.e|cf|vs|etc|al|Fig|Eq|Sec|No)$/.test(text.slice(0, m.index))) continue;
    cuts.push(m.index + m[0].length);
  }
  return [0, ...cuts]
    .map((at, i) => text.slice(at, cuts[i] ?? text.length).trim())
    .filter(Boolean)
    .map((sentence) => sentence.replace(/\u0000(\d+)\u0000/g, (_, i) => math[+i]));
}

// Contiguous pieces of near-equal length: the fewest pieces of about `target` each, cut where the longest is shortest.
function balanced(sentences: string[], target: number) {
  const k = Math.max(1, Math.min(sentences.length, Math.round(sentences.reduce((sum, s) => sum + s.length, 0) / target)));
  const prefix = sentences.reduce((acc, s) => [...acc, acc.at(-1)! + s.length], [0]);
  const n = sentences.length;
  // best[j][i]: the smallest possible longest piece when the first i sentences form j pieces.
  const best = Array.from({ length: k + 1 }, () => Array(n + 1).fill(Infinity));
  const from = Array.from({ length: k + 1 }, () => Array(n + 1).fill(0));
  best[0][0] = 0;
  for (let j = 1; j <= k; j++)
    for (let i = j; i <= n; i++)
      for (let h = j - 1; h < i; h++) {
        const worst = Math.max(best[j - 1][h], prefix[i] - prefix[h]);
        if (worst < best[j][i]) [best[j][i], from[j][i]] = [worst, h];
      }
  const pieces: string[][] = [];
  for (let j = k, i = n; j > 0; i = from[j][i], j--) pieces.unshift(sentences.slice(from[j][i], i));
  return pieces;
}

// The abstract set for a screen, word for word: a short first sentence as the lead, each enumerated step
// (第一，/First,) as its own paragraph, and long paragraphs cut at sentence ends into balanced pieces.
// A long abstract shows its opening and folds the rest. Lengths are in characters, so English runs about
// three times the Chinese figures for the same text.
const LAYOUT = { zh: { lead: 80, piece: 210, fold: 420, shown: 150 }, en: { lead: 240, piece: 680, fold: 1400, shown: 500 } };
function abstractLayout(paragraphs: string[], lang: Lang) {
  const { lead: short, piece, fold, shown } = LAYOUT[lang];
  const step = lang === "zh" ? /^(第[一二三四五六七八九十]|其[一二三四五])(?=[，、])/ : /^(First|Second|Third|Fourth|Fifth)(?=,)/;
  const sentences = paragraphs.map((paragraph) => sentencesOf(paragraph, lang));
  const lead = sentences[0][0].length <= short ? sentences[0].shift()! : "";
  const join = (part: string[]) => part.join(lang === "zh" ? "" : " ");
  const blocks: { text: string; step: boolean }[] = [];
  const prose = (run: string[]) => run.length && blocks.push(...balanced(run, piece).map((part) => ({ text: join(part), step: false })));
  for (const paragraph of sentences) {
    const starts = paragraph.flatMap((sentence, i) => (step.test(sentence) ? [i] : []));
    if (starts.length < 2) {
      prose(paragraph);
      continue;
    }
    // A step runs to the next one; the last takes as many sentences as the first, and the rest is prose again.
    const end = starts.at(-1)! + starts[1] - starts[0];
    prose(paragraph.slice(0, starts[0]));
    starts.forEach((at, k) => {
      const item = paragraph.slice(at, starts[k + 1] ?? end);
      blocks.push({ text: join([item[0].replace(step, "**$1**"), ...item.slice(1)]), step: true });
    });
    prose(paragraph.slice(end));
  }
  const html = blocks.map((block) => renderMarkdown(block.text).replace(/^<p>/, block.step ? '<p class="step">' : "<p>"));
  const total = blocks.reduce((sum, block) => sum + block.text.length, 0);
  let cut = blocks.length;
  if (total > fold) for (let i = 0, seen = 0; i < blocks.length; i++) if ((seen += blocks[i].text.length) >= shown) { cut = i + 1; break; }
  return { lead: lead && renderInline(lead), shown: html.slice(0, cut), folded: html.slice(cut) };
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
  const other = titleOf(manuscriptOf(latest, slug, lang === "zh" ? "en" : "zh"));
  return {
    ...entry,
    title,
    ...splitTitle(title),
    // The other language's title, less a main title both languages share.
    other: splitTitle(other).main === splitTitle(title).main ? splitTitle(other).sub : other,
    editions,
    current: editions.at(-1)!,
    abstract: abstractLayout(abstract, lang),
    // Plain first sentences of the abstract for the page description.
    summary: plain(abstract[0]).match(/^.{40,160}?(。|[.!?](?=\s|$))/)?.[0] ?? plain(abstract[0]).slice(0, 160),
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

const latestOf = (slug: string, lang: Lang) => manuscriptOf(entryOf(slug).editions.at(-1)!.release, slug, lang);
const mainOf = (slug: string, lang: Lang) => splitTitle(titleOf(latestOf(slug, lang))).main;

// The sibling papers a paper's reference list cites, matched by any edition's DOI or by main title:
// a same-series manuscript is cited by title before it has a DOI. Both languages are read.
export function citesOf(slug: string) {
  return once(`cites:${slug}`, () => {
    const refs = (["zh", "en"] as const)
      .map((lang) => {
        const text = latestOf(slug, lang);
        const at = text.search(/^##\s+(References|参考文献)\s*$/m);
        return at < 0 ? "" : text.slice(at);
      })
      .join("\n");
    const doiIn = (doi: string) => new RegExp(`${doi.replace(/\./g, "\\.")}(?!\\d)`).test(refs);
    return PAPERS.filter((other) => other.slug !== slug && (other.editions.some((edition) => doiIn(edition.doi)) || (["zh", "en"] as const).some((lang) => refs.includes(mainOf(other.slug, lang))))).map((other) => other.slug);
  });
}
export const citedByOf = (slug: string) => PAPERS.filter((other) => citesOf(other.slug).includes(slug)).map((other) => other.slug);

// The static first frame of a figure.
export const figureSvgOf = (name: string) =>
  once(`svg:${name}`, () => {
    const fragment = JSON.parse(readFileSync(resolve(process.cwd(), "src/generated", `${name}.json`), "utf8"));
    return String(fragment.html.zh.match(/<svg[\s\S]*?<\/svg>/)?.[0] ?? "");
  });

// Thumbnails are that frame as a standalone light-theme SVG file (src/pages/thumbs), so a list loads one
// cached image per paper instead of inlining every drawing into its HTML.
export function thumbOf(name: string) {
  const [, width, height] = figureSvgOf(name).match(/viewBox="0 0 ([\d.]+) ([\d.]+)"/) ?? [];
  return { src: `/thumbs/${name}.svg`, width: Number(width), height: Number(height) };
}
// An SVG file is parsed as XML, so a bare HTML boolean attribute (data-on) needs a value.
const xmlAttributes = (svg: string) => svg.replace(/<[a-zA-Z][^>]*>/g, (tag) => tag.replace(/("[^"]*")|\s([a-zA-Z_:][-\w:.]*)(?=\s|\/?>)/g, (match, quoted, name) => quoted ?? ` ${name}=""`));
export function thumbSvgOf(name: string, css: string) {
  const { width, height } = thumbOf(name);
  return xmlAttributes(figureSvgOf(name)).replace(/^<svg([^>]*)>/, (_, attrs: string) => {
    const kept = attrs.replace(/\s(role|aria-label)="[^"]*"/g, "").replace(/class="/, 'class="iso ');
    return `<svg${kept} data-theme="light" width="${width}" height="${height}"><style><![CDATA[${css}]]></style>`;
  });
}
