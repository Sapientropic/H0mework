// Build-time view of the repository: papers, abstracts and the claim → Lean map.
// Every fact shown on the site is read from these files, never retyped.
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { unified } from "unified";
import remarkParse from "remark-parse";
import remarkMath from "remark-math";
import remarkRehype from "remark-rehype";
import rehypeKatex from "rehype-katex";
import rehypeStringify from "rehype-stringify";

export type Lang = "zh" | "en";

const ROOT = resolve(process.cwd(), "..");
const REPO = "https://github.com/Sapientropic/H0mework/blob/main";
const read = (path: string) => readFileSync(resolve(ROOT, path), "utf8");
export const repoLink = (path: string, line?: number) => `${REPO}/${path}${line ? `#L${line}` : ""}`;

// DOIs are registered in the root README; slugs and figures belong to the site.
export const PAPERS = [
  { slug: "source-process-core", doi: "10.5281/zenodo.23210084", figure: { name: "source-tape", claim: "core.C23" } },
  { slug: "physics-common-source", doi: "10.5281/zenodo.23210292", figure: { name: "pairing-balance", claim: "phys.P4" } },
] as const;
export type Slug = (typeof PAPERS)[number]["slug"];

const markdown = unified().use(remarkParse).use(remarkMath).use(remarkRehype).use(rehypeKatex, { throwOnError: false }).use(rehypeStringify);
export const renderMarkdown = (text: string) => String(markdown.processSync(text));

const manuscriptPath = (slug: string, lang: Lang) =>
  `papers/first-release/source/papers/${slug}/manuscript${lang === "en" ? "-en" : ""}.md`;

// Both papers are titled "main: subtitle"; the two parts are shown at two levels.
function splitTitle(title: string) {
  const at = title.search(/：|: /);
  return at < 0 ? { main: title, sub: "" } : { main: title.slice(0, at), sub: title.slice(at).replace(/^(：|: )/, "") };
}

export function paperOf(slug: string, lang: Lang) {
  const meta = PAPERS.find((paper) => paper.slug === slug);
  if (!meta) throw new Error(`unknown paper ${slug}`);
  const lines = read(manuscriptPath(slug, lang)).split("\n");
  const title = lines[0].replace(/^#\s+/, "");
  const other = (lines.find((line) => /^\*\*[^*]+\*\*$/.test(line)) ?? "").replace(/\*\*/g, "");
  const start = lines.findIndex((line) => line === (lang === "zh" ? "## 摘要" : "## Abstract"));
  const end = lines.findIndex((line, index) => index > start && /^(##|---)/.test(line));
  const paragraphs = lines.slice(start + 1, end).join("\n").trim().split(/\n\s*\n/);
  const pdf = (suffix: string) => repoLink(`papers/first-release/pdf/${slug}${suffix}.pdf`);
  return {
    ...meta,
    title,
    ...splitTitle(title),
    other,
    date: JSON.parse(read("papers/first-release/manifest.json")).date as string,
    abstractLead: renderMarkdown(paragraphs[0]),
    abstractRest: renderMarkdown(paragraphs.slice(1).join("\n\n")),
    links: {
      doi: `https://doi.org/${meta.doi}`,
      pdf: pdf(lang === "en" ? "-en" : ""),
      supplement: pdf(lang === "en" ? "-supplement-en" : "-supplement"),
      arxiv: repoLink(`papers/first-release/arxiv/${slug}-arxiv.pdf`),
    },
  };
}

type Declaration = { name: string; qualified_name: string; kind: string; line: number };
type Producer = {
  kind: string;
  public?: { path: string; module?: string };
  verification?: { kernel?: string; identity?: string };
  declarations?: Declaration[];
};
type Claim = {
  id: string;
  paper: string;
  title: string;
  statement: string;
  status: string;
  text_location: { selection: Record<Lang, string> };
  producers: Producer[];
};

let mapCache: { claims: Claim[] } | null = null;
const claimMap = () => (mapCache ??= JSON.parse(read("docs/first-release-map.json")));

// English claims are translated from the registered Chinese ones. Each entry carries a
// fingerprint of the Chinese it was translated from; a changed claim falls back to Chinese.
type English = Record<string, { title: string; statement: string; zh: string }>;
let englishCache: English | null = null;
const fingerprint = (claim: Claim) => createHash("sha256").update(`${claim.title}\n${claim.statement}`).digest("hex").slice(0, 16);
function textOf(claim: Claim, lang: Lang) {
  if (lang === "zh") return { title: claim.title, statement: claim.statement };
  const entry = (englishCache ??= JSON.parse(readFileSync(resolve(process.cwd(), "src/data/claims-en.json"), "utf8")))[claim.id];
  if (entry?.zh === fingerprint(claim)) return { title: entry.title, statement: entry.statement };
  console.warn(`[claims-en] ${claim.id}: English text missing or stale; showing the registered Chinese`);
  return { title: claim.title, statement: claim.statement };
}

// "H0mework.Realization.Operations.Tree.Fold.Source" → "Tree.Fold.Source": the tail names the
// mathematical object; the full name stays in the link title.
const shortModule = (module: string) => module.split(".").slice(-3).join(".");

// Reading order: by the first section the claim cites; appendices come after the main text.
function orderOf(location: string): number[] {
  const appendix = location.match(/附录\s*([A-Z])(?:\.(\d+))?/);
  if (appendix && location.indexOf(appendix[0]) === location.search(/[§附构定命例]/)) return [100 + appendix[1].charCodeAt(0), Number(appendix[2] ?? 0)];
  const numbers = location.match(/(\d+)(?:\.(\d+))?/);
  return numbers ? [Number(numbers[1]), Number(numbers[2] ?? 0)] : [999, 0];
}
const byReading = (a: Claim, b: Claim) => {
  const [x, y] = [orderOf(a.text_location.selection.zh), orderOf(b.text_location.selection.zh)];
  return x[0] - y[0] || x[1] - y[1];
};

export function claimsOf(slug: string, lang: Lang) {
  return claimMap()
    .claims.filter((claim) => claim.paper === slug)
    .sort(byReading)
    .map((claim) => {
      const lean = claim.producers.filter((producer) => producer.kind === "lean" && producer.public?.module);
      return {
        id: claim.id,
        ...textOf(claim, lang),
        status: claim.status,
        location: claim.text_location.selection[lang],
        // The row shows only the leading reference ("§3.4", "§8.1–§8.3", "Theorem 6.2"); the body shows the rest.
        section: claim.text_location.selection[lang].match(/^(§[^\s；;,，]+|[^\s\d；;,，、]*\s?[\d.A-Z]+[\d.–()]*)/)?.[1] ?? claim.text_location.selection[lang],
        kernelPassed: lean.every((producer) => producer.verification?.kernel === "passed"),
        declarationCount: lean.reduce((sum, producer) => sum + (producer.declarations?.length ?? 0), 0),
        lean: lean.map((producer) => ({
          module: producer.public!.module!,
          short: shortModule(producer.public!.module!),
          link: repoLink(producer.public!.path, producer.declarations?.[0]?.line),
          declarations: (producer.declarations ?? []).map((decl) => ({ name: decl.name, link: repoLink(producer.public!.path, decl.line) })),
        })),
        artifacts: claim.producers
          .filter((producer) => producer.kind !== "lean" && producer.public)
          .map((producer) => ({ path: producer.public!.path, name: producer.public!.path.split("/").pop()!, link: repoLink(producer.public!.path) })),
      };
    });
}

export function statsOf(slug: string) {
  const claims = claimsOf(slug, "zh");
  const modules = new Set(claims.flatMap((claim) => claim.lean.map((lean) => lean.module)));
  return {
    claims: claims.length,
    verified: claims.filter((claim) => claim.status === "verified").length,
    modules: modules.size,
    declarations: claims.reduce((sum, claim) => sum + claim.declarationCount, 0),
    kernel: claims.every((claim) => claim.kernelPassed),
    artifacts: claims.reduce((sum, claim) => sum + claim.artifacts.length, 0),
  };
}

// The static first frame of a figure, for thumbnails.
export function figureSvgOf(name: string) {
  const fragment = JSON.parse(readFileSync(resolve(process.cwd(), "src/generated", `${name}.json`), "utf8"));
  return String(fragment.html.zh.match(/<svg[\s\S]*?<\/svg>/)?.[0] ?? "");
}
