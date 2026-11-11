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

export type ReleaseId = "first-release" | "second-edition" | "low-energy" | "whole-ledger" | "whole-ledger-v2" | "source-process-core-v3" | "one-bit" | "one-bit-v2" | "generated-society" | "economic-constitution" | "generated-society-v2" | "economic-constitution-v2" | "capital-formation" | "enforceable-peace" | "physics-third-edition";
type Release = {
  label: Record<Lang, string>;
  date: string;
  map: string;
  // The release selection: a JSON file, or a member of an archive.
  selection?: { path: string; member?: string };
  manuscript: (slug: string, lang: Lang) => string;
  supplement?: (slug: string, lang: Lang) => string;
  bibliography?: (slug: string) => string;
  files: (slug: string, lang: Lang) => { pdf: string; supplement?: string; arxiv?: string };
  check: string;
  guide: string;
  sourceCommit?: string;
  documentationCommit?: string;
  acceptance?: Record<Lang, string>;
  claimsNote?: Record<Lang, string>;
  // A prose revision quotes its current text once while retaining both editions' downloads.
  replacesClaimsFrom?: ReleaseId;
};

const FIRST = "papers/first-release";
const SECOND = "papers/second-edition/2026-10-11";
const THIRD = "papers/third-edition/2026-11-10";
const physicsArchive = `${THIRD}/editable/physics-common-source-v3-editable.zip`;
const physicsThird = readJson(`${THIRD}/manifest.json`).papers.find((paper: any) => paper.paper === "physics-common-source");
if (!physicsThird?.is_published || !/^10\.5281\/zenodo\.\d+$/.test(physicsThird.doi) || !/^[0-9a-f]{40}$/.test(physicsThird.source_commit))
  throw new Error("physics third edition has no published DOI and fixed proof source");
const LOW = "papers/low-energy-first-release/2026-10-11";
const LEDGER = "papers/whole-ledger-one-bit/2026-10-17";
// The 2026-10-17 papers ship their manuscripts and selections inside the editable archive uploaded to Zenodo.
const ledgerArchive = (slug: string) => `${LEDGER}/editable/${slug}-v1-editable.zip`;
const PROCESS_LEDGER = "papers/process-core-whole-ledger/2026-11-12";
const processLedgerManifest = readJson(`${PROCESS_LEDGER}/manifest.json`);
function processLedgerPaper(slug: string, version: string) {
  const paper = processLedgerManifest.papers.find((row: any) => row.paper === slug);
  if (!paper?.is_published || paper.version !== version || !/^10\.5281\/zenodo\.\d+$/.test(paper.doi)
    || !/^[0-9a-f]{40}$/.test(paper.source_commit) || paper.source_commit !== processLedgerManifest.source_commit)
    throw new Error(`Missing published ${version} DOI or proof binding for ${slug}`);
  return paper;
}
const coreThird = processLedgerPaper("source-process-core", "v3");
const ledgerSecond = processLedgerPaper("whole-ledger-accounting", "v2");
function processLedgerRelease(slug: string, version: string, paper: any, binding: string) {
  const archive = `${PROCESS_LEDGER}/editable/${slug}-${version}-editable.zip`;
  const member = `papers/${slug}`;
  return {
    date: paper.publication_date,
    selection: { path: archive, member: `${member}/${binding}` },
    manuscript: (_slug: string, lang: Lang) => unzip(archive, `${member}/manuscript${suffix(lang)}.md`),
    supplement: (_slug: string, lang: Lang) => unzip(archive, `${member}/supplement${suffix(lang)}.md`),
    bibliography: () => unzip(archive, `${member}/references-${version}.bib`),
    files: (_slug: string, lang: Lang) => ({
      pdf: `${PROCESS_LEDGER}/pdf/${slug}${suffix(lang)}.pdf`,
      supplement: `${PROCESS_LEDGER}/pdf/${slug}-supplement${suffix(lang)}.pdf`,
    }),
    sourceCommit: paper.source_commit,
  };
}
const ONE_BIT_V2 = "papers/one-bit/2026-11-11-v2";
const oneBitArchive = `${ONE_BIT_V2}/editable/one-bit-v2-editable.zip`;
const oneBitSecond = readJson(`${ONE_BIT_V2}/manifest.json`).papers.find((paper: any) => paper.paper === "one-bit");
if (!oneBitSecond?.is_published || oneBitSecond.version !== "v2"
    || !/^10\.5281\/zenodo\.\d+$/.test(oneBitSecond.doi) || !/^[0-9a-f]{40}$/.test(oneBitSecond.source_commit))
  throw new Error("One Bit second edition has no published DOI and fixed proof source");
const SOCIETY = "papers/society-economic/2026-11-03";
const SOCIETY_V2 = "papers/society-economic/2026-11-03-v2";
const SOCIETY_SOURCE = "2d6fbc96e33b7c4c3cfd91104fda74e3caeda045";
const CAPITAL = "papers/capital-formation/2026-11-04";
const capitalArchive = `${CAPITAL}/editable/capital-formation-v1-editable.zip`;
const PEACE = "papers/enforceable-peace/2026-11-10";
const peaceArchive = `${PEACE}/editable/enforceable-peace-editable.zip`;
const peaceMember = "enforceable-peace-source/papers/enforceable-peace";
const PEACE_SOURCE = "2678896740481f6eb6fc248c38d86549a6b6911d";
export const peaceBinding = () =>
  once("enforceable-peace:binding", () => JSON.parse(unzip(peaceArchive, `${peaceMember}/public-source-binding.json`)));
const peacePaper = () => {
  const paper = readJson(`${PEACE}/manifest.json`).papers.find((paper: any) => paper.paper === "enforceable-peace");
  if (!paper?.is_published || !/^10\.5281\/zenodo\.\d+$/.test(paper.doi) || paper.source_commit !== PEACE_SOURCE)
    throw new Error("peace release manifest has no published DOI and fixed proof source");
  return paper;
};
const capitalPaper = () => {
  const paper = readJson(`${CAPITAL}/manifest.json`).papers.find((paper: any) => paper.paper === "capital-formation");
  if (!paper?.doi || !/^10\.\d{4,9}\/\S+$/.test(paper.doi) || paper.source_commit !== SOCIETY_SOURCE)
    throw new Error("capital release manifest has no fixed proof source and DOI");
  return paper;
};
const societyArchive = (slug: string, version = "v1") => `${version === "v2" ? SOCIETY_V2 : SOCIETY}/editable/${slug}-${version}-editable.zip`;
const societyPaper = (slug: string, version = "v1") => {
  const paper = readJson(`${version === "v2" ? SOCIETY_V2 : SOCIETY}/manifest.json`).papers.find((paper: any) => paper.paper === slug);
  if (!paper?.doi || !/^10\.\d{4,9}\/\S+$/.test(paper.doi) || paper.source_commit !== SOCIETY_SOURCE)
    throw new Error(`release manifest has no fixed proof source and DOI for ${slug}`);
  return paper;
};
export const publishedPaperJson = (release: ReleaseId, slug: string, path: string) =>
  once(`published:${release}:${slug}:${path}`, () => JSON.parse(unzip(RELEASES[release].selection!.path, `papers/${slug}/${path}`)));

const BASE_RELEASES: Record<Exclude<ReleaseId, "generated-society-v2" | "economic-constitution-v2">, Release> = {
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
  "physics-third-edition": {
    label: { zh: "物理旗舰第三版", en: "Physics flagship, third edition" },
    date: physicsThird.publication_date,
    map: "docs/physics-third-edition-map.json",
    selection: { path: "checks/physics-third-edition-selection.json" },
    manuscript: (slug, lang) => unzip(physicsArchive, `papers/${slug}/manuscript${suffix(lang)}.md`),
    supplement: (slug, lang) => unzip(physicsArchive, `papers/${slug}/supplement${suffix(lang)}.md`),
    files: (slug, lang) => ({ pdf: `${THIRD}/pdf/${slug}${suffix(lang)}.pdf`, supplement: `${THIRD}/pdf/${slug}-supplement${suffix(lang)}.pdf` }),
    check: "python3 tools/physics_third_edition.py entry",
    guide: "docs/physics-third-edition-reproduction.md",
    sourceCommit: physicsThird.source_commit,
    acceptance: {
      zh: "P45–P47 的新增证明通过构建、信任闭包和完整声明类型验收。",
      en: "The additions for P45–P47 passed the build, dependency trust audit, and complete declaration type checks.",
    },
    claimsNote: {
      zh: "展开第三版新增结果，查看正文命题、Lean 声明、直接消费者和原回执。前两版登记的证明列在下方。",
      en: "Open the third-edition additions to see the results, Lean declarations, direct consumers and original receipts. Earlier proofs follow below.",
    },
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
  "whole-ledger-v2": {
    ...processLedgerRelease("whole-ledger-accounting", "v2", ledgerSecond, "release-selection-v2.json"),
    label: { zh: "整账法第二版", en: "Whole ledger, second edition" },
    map: "docs/whole-ledger-v2-map.json",
    check: "python3 tools/whole_ledger_v2.py entry",
    guide: "docs/whole-ledger-v2-reproduction.md",
    replacesClaimsFrom: "whole-ledger",
    acceptance: {
      zh: "WA4 的容量核及 WA41–WA45 通过本地构建、公理依赖和完整声明类型核验。",
      en: "The WA4 capacity kernel and WA41–WA45 passed the local build, dependency trust audit, and complete declaration type checks.",
    },
  },
  "source-process-core-v3": {
    ...processLedgerRelease("source-process-core", "v3", coreThird, "public-source-binding.json"),
    label: { zh: "过程核心第三版", en: "Process core, third edition" },
    map: "docs/source-process-core-v3-map.json",
    check: "python3 tools/source_process_core_v3.py entry",
    guide: "docs/source-process-core-v3-reproduction.md",
    acceptance: {
      zh: "C47–C48 通过本地构建、公理依赖和完整声明类型核验。其余新增主张沿用整账法的验收。",
      en: "C47–C48 passed the local build, dependency trust audit, and complete declaration type checks. The other new claims reuse the whole-ledger acceptance.",
    },
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
  "one-bit-v2": {
    label: { zh: "一比特第二版", en: "One Bit, second edition" },
    date: oneBitSecond.publication_date,
    map: "docs/one-bit-v2-map.json",
    selection: { path: oneBitArchive, member: "papers/one-bit/release-selection-v2.json" },
    manuscript: (slug, lang) => unzip(oneBitArchive, `papers/${slug}/manuscript${suffix(lang)}.md`),
    bibliography: (slug) => unzip(oneBitArchive, `papers/${slug}/references-v2.bib`),
    files: (slug, lang) => ({ pdf: `${ONE_BIT_V2}/pdf/${slug}${suffix(lang)}.pdf` }),
    check: "python3 tools/one_bit_v2.py entry",
    guide: "docs/one-bit-v2-reproduction.md",
    sourceCommit: oneBitSecond.source_commit,
    replacesClaimsFrom: "one-bit",
    acceptance: {
      zh: "OB2、OB12 和 OB13 的新增材料通过本地构建、公理依赖和完整声明类型核验。",
      en: "The additions for OB2, OB12, and OB13 passed the local build, dependency trust audit, and complete declaration type checks.",
    },
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
    claimsNote: {
      zh: "八项制度原则与八项采用的形式结果分别列示。原则由规范论证承担；Lean 模块证明其明确采用的形式支撑。每条可展开原文、实际声明、直接消费者及原证据。",
      en: "Eight institutional principles and eight adopted formal results are listed separately. The principles have normative arguments; Lean checks their explicitly adopted formal support. Each row opens the original text, actual declarations, direct consumers, and evidence.",
    },
  },
  "capital-formation": {
    label: { zh: "资本主义的结构总定理", en: "The structural theorem of capitalism" },
    date: capitalPaper().publication_date,
    map: "docs/capital-formation-map.json",
    selection: { path: capitalArchive, member: "papers/capital-formation/records/source-selection.json" },
    manuscript: (slug, lang) => unzip(capitalArchive, `papers/${slug}/manuscript${suffix(lang)}.md`),
    supplement: (slug, lang) => unzip(capitalArchive, `papers/${slug}/supplement${suffix(lang)}.md`),
    files: (slug, lang) => ({ pdf: `${CAPITAL}/pdf/${slug}${suffix(lang)}.pdf`, supplement: `${CAPITAL}/pdf/${slug}-supplement${suffix(lang)}.pdf` }),
    check: "python3 tools/capital_formation.py entry --require-ready --output .local/capital-formation-entry",
    guide: "docs/capital-formation-reproduction.md",
    sourceCommit: SOCIETY_SOURCE,
    documentationCommit: "main",
    claimsNote: {
      zh: "按论文顺序列出18项结果。展开可读定理原文、证明声明、直接消费者与来源材料。",
      en: "The paper's eighteen results appear in reading order. Open a row for its original statement, proof declarations, direct consumers, and source materials.",
    },
  },
  "enforceable-peace": {
    label: { zh: "战争与和平的源生终局定理", en: "War and Peace" },
    date: peacePaper().publication_date,
    map: "docs/enforceable-peace-map.json",
    manuscript: (_slug, lang) => unzip(peaceArchive, `${peaceMember}/manuscript${suffix(lang)}.md`),
    supplement: (_slug, lang) => ["technical-appendix", "appendix-execution"]
      .map((part) => unzip(peaceArchive, `${peaceMember}/${part}${suffix(lang)}.md`)).join("\n\n"),
    bibliography: () => unzip(peaceArchive, `${peaceMember}/references.bib`),
    files: (slug, lang) => ({ pdf: `${PEACE}/pdf/${slug}${suffix(lang)}.pdf`, supplement: `${PEACE}/pdf/${slug}-supplement${suffix(lang)}.pdf` }),
    check: "python3 tools/enforceable_peace.py entry",
    guide: "docs/enforceable-peace-reproduction.md",
    sourceCommit: peacePaper().source_commit,
    acceptance: {
      zh: "PE1–PE33 的六个证明包通过内核验收。原认证账本离线复演至钟 28。",
      en: "All six proof packages for PE1–PE33 passed kernel checks. The original certified journal replays offline through clock 28.",
    },
    claimsNote: {
      zh: "按论文位置查阅 PE1–PE33 的证明、直接消费者和原回执。四机执行的日期、账头与角色签认以原回执为准。",
      en: "Explore the proofs, direct consumers, and original receipts for PE1–PE33. The four-host receipts record the execution dates, ledger heads, and role signatures.",
    },
  },
};

function societyRevision(slug: "generated-society" | "economic-constitution"): Release {
  return {
    ...BASE_RELEASES[slug],
    label: { zh: `${BASE_RELEASES[slug].label.zh} · 第 2 版`, en: `${BASE_RELEASES[slug].label.en} · v2` },
    date: societyPaper(slug, "v2").publication_date,
    selection: { path: societyArchive(slug, "v2"), member: `papers/${slug}/release-selection.json` },
    manuscript: (paper, lang) => unzip(societyArchive(paper, "v2"), `papers/${paper}/manuscript${suffix(lang)}.md`),
    supplement: (paper, lang) => unzip(societyArchive(paper, "v2"), `papers/${paper}/supplement${suffix(lang)}.md`),
    files: (paper, lang) => ({ pdf: `${SOCIETY_V2}/pdf/${paper}${suffix(lang)}.pdf`, supplement: `${SOCIETY_V2}/pdf/${paper}-supplement${suffix(lang)}.pdf` }),
    replacesClaimsFrom: slug,
  };
}

export const RELEASES: Record<ReleaseId, Release> = {
  ...BASE_RELEASES,
  "generated-society-v2": societyRevision("generated-society"),
  "economic-constitution-v2": societyRevision("economic-constitution"),
};

type Edition = { release: ReleaseId; doi: string };
export type ThemeId = "preface" | "core" | "computation" | "physics" | "low-energy" | "math" | "chemistry" | "energy" | "metrology" | "life" | "mind" | "society";
export const PAPER_PLAN = readJson<{
  asOf: string;
  source: string;
  registeredPapers: number;
  resultTriggeredSlots: number;
  themes: { id: ThemeId; label: Record<Lang, string>; registered: number; reserved?: number; soon?: number }[];
}>("site/src/data/paper-plan.json");
// Home groups the index by these themes, in this order; a paper's theme lives on its PAPERS entry.
export const THEMES = PAPER_PLAN.themes.map(({ id, label }) => ({ id, label }));
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
    editions: [
      { release: "one-bit", doi: "10.5281/zenodo.23437456" },
      { release: "one-bit-v2", doi: oneBitSecond.doi },
    ],
    figure: { name: "ghost-register", claim: "ob.OB2" },
  },
  {
    slug: "source-process-core",
    theme: "core",
    editions: [
      { release: "first-release", doi: "10.5281/zenodo.23210084" },
      { release: "second-edition", doi: "10.5281/zenodo.23297175" },
      { release: "source-process-core-v3", doi: coreThird.doi },
    ],
    figure: { name: "source-tape", claim: "core.C23" },
  },
  {
    slug: "whole-ledger-accounting",
    theme: "core",
    editions: [
      { release: "whole-ledger", doi: "10.5281/zenodo.23437454" },
      { release: "whole-ledger-v2", doi: ledgerSecond.doi },
    ],
    figure: { name: "whole-ledger-tower", claim: "wla.WA10" },
  },
  {
    slug: "physics-common-source",
    theme: "physics",
    editions: [
      { release: "first-release", doi: "10.5281/zenodo.23210292" },
      { release: "second-edition", doi: "10.5281/zenodo.23297179" },
      { release: "physics-third-edition", doi: physicsThird.doi },
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
    theme: "society",
    editions: [
      { release: "generated-society", doi: societyPaper("generated-society").doi },
      { release: "generated-society-v2", doi: societyPaper("generated-society", "v2").doi },
    ],
    figure: { name: "exit-run", claim: "G4" },
  },
  {
    slug: "economic-constitution",
    theme: "society",
    editions: [
      { release: "economic-constitution", doi: societyPaper("economic-constitution").doi },
      { release: "economic-constitution-v2", doi: societyPaper("economic-constitution", "v2").doi },
    ],
    figure: { name: "clepsydra", claim: "R4" },
  },
  {
    slug: "capital-formation",
    theme: "society",
    editions: [{ release: "capital-formation", doi: capitalPaper().doi }],
    figure: { name: "replay-bakery", claim: "R8" },
  },
  {
    slug: "enforceable-peace",
    theme: "society",
    editions: [{ release: "enforceable-peace", doi: peacePaper().doi }],
    figure: { name: "quan-heng", claim: "PE2" },
  },
];

// The inventory counts registered papers, including published ones. A release automatically leaves
// the preparation count. Reserved result-dependent slots have no brief and remain separate.
export const UPCOMING: Partial<Record<ThemeId, { count: number; reserved: number; soon?: number }>> = Object.fromEntries(
  PAPER_PLAN.themes.map((theme) => [theme.id, {
    count: theme.registered - PAPERS.filter((paper) => paper.theme === theme.id).length,
    reserved: theme.reserved ?? 0,
    soon: theme.soon,
  }]),
);

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
export const bibliographyOf = (release: ReleaseId, slug: string) =>
  once(`bibliography:${release}:${slug}`, () => RELEASES[release].bibliography?.(slug) ?? "");
export const mapOf = (release: ReleaseId) => once(`map:${release}`, () => readJson(RELEASES[release].map));
export const selectionOf = (release: ReleaseId) =>
  once(`selection:${release}`, () => {
    const { path, member } = RELEASES[release].selection!;
    return JSON.parse(member ? unzip(path, member) : read(path));
  });
