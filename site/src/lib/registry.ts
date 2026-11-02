// What the site publishes: each paper, its editions, and where each release keeps its files.
// A new paper is one PAPERS entry; a new release with a new map schema also needs an adapter in claims.ts.
import { execFileSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";

export type Lang = "zh" | "en";

export const ROOT = resolve(process.cwd(), "..");
export const read = (path: string) => readFileSync(resolve(ROOT, path), "utf8");
export const readJson = <T = any>(path: string): T => JSON.parse(read(path));
const REPO = "https://github.com/Sapientropic/H0mework/blob";
export const repoLink = (path: string, line?: number, commit = "main") => `${REPO}/${commit}/${path}${line ? `#L${line}` : ""}`;

const suffix = (lang: Lang) => (lang === "en" ? "-en" : "");
const unzip = (zip: string, member: string) => execFileSync("unzip", ["-p", resolve(ROOT, zip), member], { encoding: "utf8", maxBuffer: 1 << 26 });

export type ReleaseId = "first-release" | "second-edition" | "low-energy" | "whole-ledger" | "one-bit" | "generated-society" | "economic-constitution";
type Release = {
  label: Record<Lang, string>;
  date: string;
  map: string;
  // The release selection: a JSON file, or a member of an archive.
  selection?: { path: string; member?: string };
  manuscript: (slug: string, lang: Lang) => string;
  supplement?: (slug: string, lang: Lang) => string;
  files: (slug: string, lang: Lang) => { pdf: string; supplement?: string; arxiv?: string };
  check: string;
  guide: string;
  sourceCommit?: string;
  acceptance?: Record<Lang, string>;
  claimsNote?: Record<Lang, string>;
};

const FIRST = "papers/first-release";
const SECOND = "papers/second-edition/2026-10-11";
const LOW = "papers/low-energy-first-release/2026-10-11";
const LEDGER = "papers/whole-ledger-one-bit/2026-10-17";
// The 2026-10-17 papers ship their manuscripts and selections inside the editable archive uploaded to Zenodo.
const ledgerArchive = (slug: string) => `${LEDGER}/editable/${slug}-v1-editable.zip`;
const SOCIETY = "papers/society-economic/2026-11-03";
const SOCIETY_SOURCE = "2d6fbc96e33b7c4c3cfd91104fda74e3caeda045";
const societyArchive = (slug: string) => `${SOCIETY}/editable/${slug}-v1-editable.zip`;
const societyPaper = (slug: string) => {
  const paper = readJson(`${SOCIETY}/manifest.json`).papers.find((paper: any) => paper.paper === slug);
  if (!paper?.doi || !/^10\.\d{4,9}\/\S+$/.test(paper.doi) || paper.source_commit !== SOCIETY_SOURCE)
    throw new Error(`release manifest has no fixed proof source and DOI for ${slug}`);
  return paper;
};
export const publishedPaperJson = (slug: string, path: string) =>
  once(`published:${slug}:${path}`, () => JSON.parse(unzip(societyArchive(slug), `papers/${slug}/${path}`)));
const localAcceptance = {
  zh: "固定回执中的完整本地构建、trust 与完整类型验收通过；该回执不含新选集的远端 CI 通过记录。",
  en: "The fixed receipts record a passed complete local build, trust, and complete-type acceptance. They contain no remote CI pass for the new selection.",
};

export const RELEASES: Record<ReleaseId, Release> = {
  "first-release": {
    label: { zh: "首发", en: "First release" },
    date: readJson(`${FIRST}/manifest.json`).date,
    map: "docs/first-release-map.json",
    manuscript: (slug, lang) => read(`${FIRST}/source/papers/${slug}/manuscript${suffix(lang)}.md`),
    files: (slug, lang) => ({
      pdf: `${FIRST}/pdf/${slug}${suffix(lang)}.pdf`,
      supplement: `${FIRST}/pdf/${slug}-supplement${suffix(lang)}.pdf`,
      arxiv: `${FIRST}/arxiv/${slug}-arxiv.pdf`,
    }),
    check: "make check-first-release-entry",
    guide: "docs/first-release-reproduction.md",
  },
  // Later releases ship the manuscripts only inside their editable archives.
  "second-edition": {
    label: { zh: "第 2 版", en: "Second editions" },
    date: readJson(`${SECOND}/manifest.json`).snapshot_date,
    map: "docs/second-edition-map.json",
    selection: { path: `${SECOND}/handoff/second-edition-selection.json` },
    manuscript: (slug, lang) => unzip(`${SECOND}/editable/${slug}-v2-editable.zip`, `papers/${slug}/manuscript${suffix(lang)}.md`),
    files: (slug, lang) => ({
      pdf: `${SECOND}/pdf/${slug}${suffix(lang)}.pdf`,
      supplement: `${SECOND}/pdf/${slug}-supplement${suffix(lang)}.pdf`,
      arxiv: `${SECOND}/arxiv/${slug}-arxiv.pdf`,
    }),
    check: "python3 tools/edition_release.py --edition second verify-map",
    guide: "docs/edition-reproduction.md",
  },
  "low-energy": {
    label: { zh: "低能系列", en: "Low-energy series" },
    date: readJson(`${LOW}/manifest.json`).snapshot_date,
    map: "docs/low-energy-release-map.json",
    manuscript: (slug, lang) => unzip(`${LOW}/editable/${slug}-editable.zip`, `papers/${slug}/manuscript${suffix(lang)}.md`),
    files: (slug, lang) => ({ pdf: `${LOW}/pdf/${slug}${suffix(lang)}.pdf` }),
    check: "python3 tools/edition_release.py --edition low-energy verify-map",
    guide: "docs/edition-reproduction.md",
  },
  "whole-ledger": {
    label: { zh: "整账法", en: "Whole ledger" },
    date: readJson(`${LEDGER}/manifest.json`).date,
    map: "docs/whole-ledger-map.json",
    selection: { path: ledgerArchive("whole-ledger-accounting"), member: "papers/whole-ledger-accounting/release-selection.json" },
    manuscript: (slug, lang) => unzip(ledgerArchive(slug), `papers/${slug}/manuscript${suffix(lang)}.md`),
    files: (slug, lang) => ({ pdf: `${LEDGER}/pdf/${slug}${suffix(lang)}.pdf`, supplement: `${LEDGER}/pdf/${slug}-supplement${suffix(lang)}.pdf` }),
    check: "make check-whole-ledger-entry",
    guide: "docs/whole-ledger-reproduction.md",
  },
  "one-bit": {
    label: { zh: "一比特", en: "One bit" },
    date: readJson(`${LEDGER}/manifest.json`).date,
    map: "docs/one-bit-map.json",
    selection: { path: ledgerArchive("one-bit"), member: "papers/one-bit/release-selection.json" },
    manuscript: (slug, lang) => unzip(ledgerArchive(slug), `papers/${slug}/manuscript${suffix(lang)}.md`),
    files: (slug, lang) => ({ pdf: `${LEDGER}/pdf/${slug}${suffix(lang)}.pdf` }),
    check: "make check-one-bit-entry",
    guide: "docs/one-bit-reproduction.md",
  },
  "generated-society": {
    label: { zh: "典范社会总定理", en: "Canonical society" },
    date: "2026-11-03",
    map: "docs/generated-society-map.json",
    selection: { path: societyArchive("generated-society"), member: "papers/generated-society/release-selection.json" },
    manuscript: (slug, lang) => unzip(societyArchive(slug), `papers/${slug}/manuscript${suffix(lang)}.md`),
    supplement: (slug, lang) => unzip(societyArchive(slug), `papers/${slug}/supplement${suffix(lang)}.md`),
    files: (slug, lang) => ({ pdf: `${SOCIETY}/pdf/${slug}${suffix(lang)}.pdf`, supplement: `${SOCIETY}/pdf/${slug}-supplement${suffix(lang)}.pdf` }),
    check: "python3 tools/generated_society.py entry --require-ready --output .local/generated-society-entry",
    guide: "docs/generated-society-reproduction.md",
    sourceCommit: SOCIETY_SOURCE,
    acceptance: localAcceptance,
    claimsNote: {
      zh: "G0–G27 与 G2a 按实际来源映射列示。展开可读论文原文、生产声明、直接消费者及原认证；G10–G12 保持引用接口。",
      en: "G0–G27 and G2a follow the actual source map. Open a row for the paper's wording, producers, direct consumers, and original evidence. G10–G12 remain cited interfaces.",
    },
  },
  "economic-constitution": {
    label: { zh: "可能性的经济宪法", en: "Economic constitution" },
    date: "2026-11-03",
    map: "docs/economic-constitution-map.json",
    selection: { path: societyArchive("economic-constitution"), member: "papers/economic-constitution/release-selection.json" },
    manuscript: (slug, lang) => unzip(societyArchive(slug), `papers/${slug}/manuscript${suffix(lang)}.md`),
    supplement: (slug, lang) => unzip(societyArchive(slug), `papers/${slug}/supplement${suffix(lang)}.md`),
    files: (slug, lang) => ({ pdf: `${SOCIETY}/pdf/${slug}${suffix(lang)}.pdf`, supplement: `${SOCIETY}/pdf/${slug}-supplement${suffix(lang)}.pdf` }),
    check: "python3 tools/economic_constitution.py entry --require-ready --output .local/economic-constitution-entry",
    guide: "docs/economic-constitution-reproduction.md",
    sourceCommit: SOCIETY_SOURCE,
    acceptance: localAcceptance,
    claimsNote: {
      zh: "八项制度原则与八项采用的形式结果分别列示。原则由规范论证承担；Lean 模块证明其明确采用的形式支撑。每条可展开原文、实际声明、直接消费者及原证据。",
      en: "Eight institutional principles and eight adopted formal results are listed separately. The principles have normative arguments; Lean checks their explicitly adopted formal support. Each row opens the original text, actual declarations, direct consumers, and evidence.",
    },
  },
};

type Edition = { release: ReleaseId; doi: string };
export type ThemeId = "preface" | "core" | "computation" | "physics" | "low-energy" | "math" | "chemistry" | "metrology" | "life" | "mind";
// Home groups the index by these themes, in this order; a paper's theme lives on its PAPERS entry.
export const THEMES: { id: ThemeId; label: Record<Lang, string> }[] = [
  // The preface opens the series; the home forest draws it as the root, not as a branch.
  { id: "preface", label: { zh: "总序", en: "Preface" } },
  { id: "core", label: { zh: "核心方法", en: "Core methods" } },
  { id: "computation", label: { zh: "计算与博弈", en: "Computation & games" } },
  { id: "physics", label: { zh: "物理", en: "Physics" } },
  { id: "low-energy", label: { zh: "低能系列", en: "Low-energy series" } },
  { id: "math", label: { zh: "数学", en: "Mathematics" } },
  { id: "chemistry", label: { zh: "化学与材料", en: "Chemistry & materials" } },
  { id: "metrology", label: { zh: "计量与仪器", en: "Metrology & instruments" } },
  { id: "life", label: { zh: "生命与神经", en: "Life & neuroscience" } },
  { id: "mind", label: { zh: "心智与社会", en: "Mind & society" } },
];
// Papers in preparation, by theme, drawn as hollow nodes in the home forest. Counts only: a title is
// published with its paper. `soon` of them are written and await release. A released paper moves to
// PAPERS and leaves this count. A series can grow, so the page shows these counts as lower bounds.
export const UPCOMING: Partial<Record<ThemeId, { count: number; soon?: number }>> = {
  core: { count: 2 },
  computation: { count: 2 },
  physics: { count: 1 },
  "low-energy": { count: 5 },
  math: { count: 6 },
  chemistry: { count: 4 },
  metrology: { count: 3 },
  life: { count: 3 },
  mind: { count: 1 },
};
export type PaperEntry = {
  slug: string;
  theme: ThemeId;
  editions: Edition[];
  series?: Record<Lang, string>;
  figure?: { name: string; claim: string };
};

// Version DOIs as registered on Zenodo; editions oldest first.
export const PAPERS: PaperEntry[] = [
  {
    slug: "one-bit",
    theme: "preface",
    editions: [{ release: "one-bit", doi: "10.5281/zenodo.23437456" }],
    figure: { name: "ghost-register", claim: "ob.OB2" },
  },
  {
    slug: "source-process-core",
    theme: "core",
    editions: [
      { release: "first-release", doi: "10.5281/zenodo.23210084" },
      { release: "second-edition", doi: "10.5281/zenodo.23297175" },
    ],
    figure: { name: "source-tape", claim: "core.C23" },
  },
  {
    slug: "whole-ledger-accounting",
    theme: "core",
    editions: [{ release: "whole-ledger", doi: "10.5281/zenodo.23437454" }],
    figure: { name: "whole-ledger-tower", claim: "wla.WA10" },
  },
  {
    slug: "physics-common-source",
    theme: "physics",
    editions: [
      { release: "first-release", doi: "10.5281/zenodo.23210292" },
      { release: "second-edition", doi: "10.5281/zenodo.23297179" },
    ],
    figure: { name: "pairing-balance", claim: "phys.P4" },
  },
  {
    slug: "low-energy-phenomenology",
    theme: "low-energy",
    editions: [{ release: "low-energy", doi: "10.5281/zenodo.23299174" }],
    series: { zh: "低能系列 1", en: "Low-energy series 1" },
    figure: { name: "current-witness", claim: "low1.L17" },
  },
  {
    slug: "low-energy-loop-response",
    theme: "low-energy",
    editions: [{ release: "low-energy", doi: "10.5281/zenodo.23299177" }],
    series: { zh: "低能系列 2", en: "Low-energy series 2" },
    figure: { name: "curvature-dome", claim: "low2.Q4" },
  },
  {
    slug: "generated-society",
    theme: "mind",
    editions: [{ release: "generated-society", doi: societyPaper("generated-society").doi }],
  },
  {
    slug: "economic-constitution",
    theme: "mind",
    editions: [{ release: "economic-constitution", doi: societyPaper("economic-constitution").doi }],
  },
];

export const entryOf = (slug: string) => {
  const entry = PAPERS.find((paper) => paper.slug === slug);
  if (!entry) throw new Error(`unknown paper ${slug}`);
  return entry;
};

const cache = new Map<string, unknown>();
export const once = <T>(key: string, make: () => T): T => {
  if (!cache.has(key)) cache.set(key, make());
  return cache.get(key) as T;
};
export const manuscriptOf = (release: ReleaseId, slug: string, lang: Lang) =>
  once(`manuscript:${release}:${slug}:${lang}`, () => RELEASES[release].manuscript(slug, lang));
export const supplementOf = (release: ReleaseId, slug: string, lang: Lang) =>
  once(`supplement:${release}:${slug}:${lang}`, () => RELEASES[release].supplement?.(slug, lang) ?? "");
export const mapOf = (release: ReleaseId) => once(`map:${release}`, () => readJson(RELEASES[release].map));
export const selectionOf = (release: ReleaseId) =>
  once(`selection:${release}`, () => {
    const { path, member } = RELEASES[release].selection!;
    return JSON.parse(member ? unzip(path, member) : read(path));
  });
