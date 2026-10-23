// The paper's own words for a claim: the numbered results its registered location cites, read from
// the manuscript of the release that registered it, in the page language. A reader sees the theorem
// as the paper states it; the map's acceptance wording stays a secondary layer. A location that names
// a passage rather than a result ("§8.2 / 两次执行的独立差账") is served by the reading layer, which
// gives the opening words of that paragraph.
import { manuscriptOf, once, type Lang, type ReleaseId } from "./registry";

type Result = { kind: string; number: string; name: string; body: string; section: string };
// `label` heads the quotation: a result's kind and number, or a passage's section.
export type Excerpt = { label: string; name: string; body: string; parts: string | null };

// "**定理 6.2（名）。** 正文" / "**Theorem 6.2 (Name).** Text": a kind word, a dotted number, then the name in brackets.
const HEAD = /^\*\*([^*\d（(]{1,24}?)\s*((?:[A-Z]\.)?\d+(?:\.\d+)*[a-z]?)\s*([（(][\s\S]*?)\*\*\s*[。．.:：]?\s*/;
const NOT_RESULT = /^(图|表|Figure|Table)$/;
const ANCHOR = /^<a id="[^"]*"><\/a>\s*/gm;

const isDisplay = (p: string) => /^(\$\$|\\\[)/.test(p);
// Items of a statement: numbered or bulleted lines, and bold bracketed part labels ("**（一般恒等式）**").
const isList = (p: string) => /^(\d+[.)]\s|[-*+]\s|\([0-9ivx]+\)|（[0-9一二三四五六七八九十ivx]+）|\*\*[（(])/.test(p);
// A statement ends where its proof, the next result, a heading, a figure or a table begins.
const ENDS = /^(\*{0,2}(证明|Proof|构造|Construction)|\*\*(?![（(])|#|!\[|\||---|<|\[\^)/;

// Manuscript cross-references point at anchors this page does not have; their text stays, the links go.
const clean = (text: string) =>
  text
    .replace(ANCHOR, "")
    .replace(/\[\^[^\]]+\]/g, "")
    .replace(/\[\[(\d+)\]\]\(#[^)]*\)/g, "[$1]")
    .replace(/\[([^\]]+)\]\(#[^)]*\)/g, "$1")
    .trim();

function nameOf(rest: string) {
  const name = rest.trim().replace(/[。．.:：]+$/, "");
  const open = name[0];
  const close = open === "（" ? "）" : ")";
  return name.endsWith(close) ? name.slice(1, -1).trim() : name;
}

// A statement's paragraphs after its first: a head standing alone opens a statement that runs to its
// proof; an inline statement continues only into its own displays, lists and the lines a colon or a
// display introduces.
function continuation(paragraphs: string[], at: number, inline: boolean, body: string[]) {
  for (let next = at + 1; next < paragraphs.length && body.length < 14; next++) {
    const p = paragraphs[next].trim();
    if (ENDS.test(p)) break;
    const prev = body.at(-1)?.trim() ?? "";
    if (inline && !(isDisplay(p) || isList(p) || isDisplay(prev) || /[：:]$/.test(prev))) break;
    body.push(paragraphs[next]);
  }
  return body;
}

// A manuscript as paragraphs, each with the subsection it sits in, and its numbered results by number.
function indexOf(release: ReleaseId, slug: string, lang: Lang) {
  return once(`results:${release}:${slug}:${lang}`, () => {
    const paragraphs = manuscriptOf(release, slug, lang)
      .split(/\n\s*\n/)
      .flatMap((block) => block.replace(ANCHOR, "").split(/\n(?=#)/))
      // Indentation is kept: it is what holds a display or a paragraph inside its list item.
      .map((p) => p.replace(/^\n+|\s+$/g, ""))
      .filter((p) => p.trim());
    const sections: string[] = [];
    const results = new Map<string, Result>();
    let section = "";
    paragraphs.forEach((raw, at) => {
      const paragraph = raw.trim();
      const heading = paragraph.match(/^#{2,4}\s+(?:附录\s*|Appendix\s+)?((?:[A-Z]|\d+)(?:\.\d+)*)[\s　.:：]/);
      if (heading) section = heading[1];
      sections.push(section);
      const head = !heading && paragraph.match(HEAD);
      if (!head || NOT_RESULT.test(head[1].trim()) || results.has(head[2])) return;
      const first = paragraph.slice(head[0].length).trim();
      const body = continuation(paragraphs, at, Boolean(first), first ? [first] : []);
      results.set(head[2], { kind: head[1].trim(), number: head[2], name: clean(nameOf(head[3])), body: clean(body.join("\n\n")), section });
    });
    return { paragraphs, sections, results };
  });
}

const sectionLabel = (section: string, lang: Lang) => (/^[A-Z]/.test(section) ? `${lang === "zh" ? "附录" : "Appendix"} ${section}` : `§${section}`);

// The paragraph a reading entry names by its opening words, with what its colon or display introduces.
function passageOf(release: ReleaseId, slug: string, lang: Lang, opening: string): Excerpt | null {
  const { paragraphs, sections } = indexOf(release, slug, lang);
  const found = paragraphs.flatMap((p, at) => (p.trim().startsWith(opening) ? [at] : []));
  if (found.length !== 1) {
    console.warn(`[reading-${lang}] ${slug}: ${found.length} paragraphs open with “${opening}”`);
    return null;
  }
  const at = found[0];
  const body = continuation(paragraphs, at, true, [paragraphs[at].trim()]);
  return { label: sectionLabel(sections[at], lang), name: "", body: clean(body.join("\n\n")), parts: null };
}

// --- the location's references ---------------------------------------------------------------

const KIND = "主定理|定理|命题|引理|推论|定义|例|构造|反例|实例|具名复用|注记|注|直接反证|反证";
const NUM = "(?:[A-Z]|\\d+)\\.\\d+[a-z]?";
const PARTS = "(?:\\(\\d+\\))+(?:–\\(\\d+\\))?";
const ITEM = `${NUM}(?:\\s*[–-]\\s*${NUM})?(?:${PARTS})?`;
const CITED = new RegExp(`(?:${KIND})\\s*(${ITEM}(?:\\s*[、,，]\\s*${ITEM})*)`, "g");

// "6.7–6.10" → 6.7, 6.8, 6.9, 6.10.
function expand(from: string, to: string) {
  const [a, b] = [from, to].map((n) => n.match(/^(.*\.)(\d+)$/));
  if (!a || !b || a[1] !== b[1]) return [from, to];
  return Array.from({ length: Math.max(0, +b[2] - +a[2]) + 1 }, (_, i) => `${a[1]}${+a[2] + i}`);
}

function citedResults(location: string) {
  const cited: { number: string; parts: string | null }[] = [];
  for (const [, list] of location.matchAll(CITED))
    for (const item of list.split(/\s*[、,，]\s*/)) {
      const [, from, to, parts] = item.match(new RegExp(`^(${NUM})(?:\\s*[–-]\\s*(${NUM}))?(${PARTS})?$`))!;
      for (const number of to ? expand(from, to) : [from]) cited.push({ number, parts: parts ?? null });
    }
  return cited;
}

// A location made only of sections ("§3.1–3.2；B.1", "§6；附录 C–E") names no result; the results
// standing in those sections are its nearest written statements. A section qualified by words
// ("§9.2 NIST 名义重放段") points at a passage, not at the section's results, and yields none.
function citedSections(location: string) {
  const parts = location.split(/[；;]\s*/).map((part) => part.trim()).filter(Boolean);
  const pure = /^(?:§\s*\d+(?:\.\d+)?(?:\s*[–-]\s*§?\s*\d+(?:\.\d+)?)?|(?:附录\s*)?[A-Z](?:\.\d+)?(?:\s*[–-]\s*(?:[A-Z]\.)?\d+|\s*[–-]\s*[A-Z])?|图\s*\d+)$/;
  if (!parts.every((part) => part.split(/\s*[、,]\s*/).every((piece) => pure.test(piece)))) return [];
  const sections: [string, string][] = [];
  for (const part of parts.flatMap((part) => part.split(/\s*[、,]\s*/))) {
    if (/^图/.test(part)) continue;
    const m = part.replace(/^附录\s*|§\s*/g, "").match(/^([A-Z]|\d+)(?:\.(\d+))?(?:\s*[–-]\s*§?\s*(?:([A-Z]|\d+)\.)?(\d+|[A-Z]))?$/);
    if (!m) continue;
    const [, head, sub, toHead, to] = m;
    if (to && !sub) sections.push([head, to]); // "C–E", "§6–§11": whole chapters
    else if (to) sections.push([`${head}.${sub}`, `${toHead ?? head}.${to}`]);
    else sections.push([sub ? `${head}.${sub}` : head, sub ? `${head}.${sub}` : head]);
  }
  return sections;
}

// A section lies in a range when its leading parts, as deep as each bound, fall between the bounds:
// "3.10" follows "3.9", and "D.4" lies in "C–E". Chapters and appendices never mix.
const parts = (section: string) => section.split(".").map((part) => (/^\d+$/.test(part) ? +part : part.charCodeAt(0)));
function compare(section: number[], bound: number[]) {
  for (let i = 0; i < bound.length; i++) if ((section[i] ?? 0) !== bound[i]) return (section[i] ?? 0) - bound[i];
  return 0;
}
function within(section: string, [from, to]: [string, string]) {
  if (/^[A-Z]/.test(section) !== /^[A-Z]/.test(from)) return false;
  return compare(parts(section), parts(from)) >= 0 && compare(parts(section), parts(to)) <= 0;
}

// The section fallback shows at most this many results, and no remarks: a remark comments on a result, it states none.
const SECTION_LIMIT = 4;
const REMARK = /^(注|注记|Remark|Note)$/;

const quoted = (result: Result, parts: string | null): Excerpt => ({ label: `${result.kind} ${result.number}`, name: result.name, body: result.body, parts });

// `more` comes from the reading layer: results to cite beyond the location's, and passages by their
// opening words. Either makes the quotation the paper's own words, so no section fallback is drawn.
export function excerptsOf(release: ReleaseId, slug: string, lang: Lang, location: string | null, more: { cite?: string[]; passages?: string[] } = {}) {
  const { results } = indexOf(release, slug, lang);
  const cited = [...(location ? citedResults(location) : []), ...(more.cite ?? []).map((number) => ({ number, parts: null }))];
  const passages = (more.passages ?? []).flatMap((opening) => passageOf(release, slug, lang, opening) ?? []);
  if (cited.length > 0 || passages.length > 0) {
    const seen = new Set<string>();
    const named = cited.flatMap(({ number, parts }) => {
      const result = results.get(number);
      if (!result || seen.has(number)) return [];
      seen.add(number);
      return [quoted(result, parts)];
    });
    return { cited: true, results: [...named, ...passages] };
  }
  if (!location) return { cited: true, results: [] as Excerpt[] };
  const sections = citedSections(location);
  const inSections = [...results.values()].filter((result) => !REMARK.test(result.kind) && result.section && sections.some((range) => within(result.section, range)));
  return { cited: false, results: inSections.slice(0, SECTION_LIMIT).map((result) => quoted(result, null)) };
}
