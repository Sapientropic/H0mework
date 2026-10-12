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
  { slug: "physics-common-source", doi: "10.5281/zenodo.23210292", figure: { name: "pairing-balance", claim: "phys.P4" } },
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
  const paragraphs = lines.slice(start + 1, end).join("\n").trim().split(/\n\s*\n/);
  const pdf = (suffix: string) => repoLink(`papers/first-release/pdf/${slug}${suffix}.pdf`);
  return {
    ...meta,
    title,
    other,
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
  quantifiers_premises: string;
  status: string;
  text_location: { selection: Record<Lang, string> };
  producers: Producer[];
};

let mapCache: { claims: Claim[] } | null = null;
const claimMap = () => (mapCache ??= JSON.parse(read("docs/first-release-map.json")));

// "H0mework.Realization.Operations.Tree.Fold.Source" → "Tree.Fold.Source": the tail names the
// mathematical object; the full name stays in the link title.
const shortModule = (module: string) => module.split(".").slice(-3).join(".");

export function claimsOf(slug: string, lang: Lang) {
  return claimMap()
    .claims.filter((claim) => claim.paper === slug)
    .map((claim) => {
      const lean = claim.producers.filter((producer) => producer.kind === "lean" && producer.public?.module);
      return {
        id: claim.id,
        title: claim.title,
        statement: claim.statement,
        premises: claim.quantifiers_premises,
        status: claim.status,
        location: claim.text_location.selection[lang],
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
