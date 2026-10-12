// Build-time view of the repository: papers, abstracts and the claim → Lean map.
// Every fact shown on the site is read from these files, never retyped.
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
  { slug: "physics-common-source", doi: "10.5281/zenodo.23210292", figure: null },
] as const;
export type Slug = (typeof PAPERS)[number]["slug"];

const markdown = unified().use(remarkParse).use(remarkMath).use(remarkRehype).use(rehypeKatex, { throwOnError: false }).use(rehypeStringify);
export const renderMarkdown = (text: string) => String(markdown.processSync(text));

const manuscriptPath = (slug: string, lang: Lang) =>
  `papers/first-release/source/papers/${slug}/manuscript${lang === "en" ? "-en" : ""}.md`;

export function paperOf(slug: string, lang: Lang) {
  const meta = PAPERS.find((paper) => paper.slug === slug);
  if (!meta) throw new Error(`unknown paper ${slug}`);
  const lines = read(manuscriptPath(slug, lang)).split("\n");
  const title = lines[0].replace(/^#\s+/, "");
  const other = (lines.find((line) => /^\*\*[^*]+\*\*$/.test(line)) ?? "").replace(/\*\*/g, "");
  const start = lines.findIndex((line) => line === (lang === "zh" ? "## 摘要" : "## Abstract"));
  const end = lines.findIndex((line, index) => index > start && /^(##|---)/.test(line));
  const abstract = lines.slice(start + 1, end).join("\n").trim();
  const pdf = (suffix: string) => repoLink(`papers/first-release/pdf/${slug}${suffix}.pdf`);
  return {
    ...meta,
    title,
    other,
    abstractHtml: renderMarkdown(abstract),
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
  public?: { path: string; module: string };
  verification?: { kernel?: string; identity?: string };
  declarations?: Declaration[];
};
type Claim = {
  id: string;
  paper: string;
  title: string;
  statement: string;
  quantifiers_premises: string;
  status: string;
  classification: string;
  text_location: { selection: Record<Lang, string> };
  producers: Producer[];
};

let mapCache: { claims: Claim[] } | null = null;
const claimMap = () => (mapCache ??= JSON.parse(read("docs/first-release-map.json")));

export function claimsOf(slug: string, lang: Lang) {
  return claimMap()
    .claims.filter((claim) => claim.paper === slug)
    .map((claim) => ({
      id: claim.id,
      title: claim.title,
      statement: claim.statement,
      premises: claim.quantifiers_premises,
      status: claim.status,
      classification: claim.classification,
      location: claim.text_location.selection[lang],
      lean: claim.producers
        .filter((producer) => producer.kind === "lean" && producer.public)
        .map((producer) => ({
          module: producer.public!.module,
          path: producer.public!.path,
          kernel: producer.verification?.kernel ?? "",
          declarations: (producer.declarations ?? []).map((decl) => ({
            name: decl.name,
            kind: decl.kind,
            link: repoLink(producer.public!.path, decl.line),
          })),
        })),
    }));
}
