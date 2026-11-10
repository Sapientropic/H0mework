// Rebuild the bilingual README navigation and CI figure from the paper registry and fixed run record.
// Run from site/: bun run readme
import { execFileSync, spawnSync } from "node:child_process";
import { readFileSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";
import { PAPERS, RELEASES, ROOT, THEMES } from "../src/lib/registry";
import { paperOf } from "../src/lib/papers";

const run = JSON.parse(readFileSync(resolve(ROOT, "docs/assets/ci-run.json"), "utf8"));
const runUrl = `https://github.com/Sapientropic/H0mework/actions/runs/${run.id}`;
const acceptedLayout = execFileSync("git", ["show", `${run.commit}:tools/ci_layout.tsv`], { cwd: ROOT, encoding: "utf8", maxBuffer: 1 << 26 });
const currentLayout = readFileSync(resolve(ROOT, "tools/ci_layout.tsv"), "utf8");
const metrics = (layout) => {
  const parts = layout.trimEnd().split("\n").map((line) => line.split("\t")[0]);
  return {
    modules: parts.length.toLocaleString("en-US"),
    stageCount: new Set(parts.map((part) => part.split("-")[0])).size,
    shardCount: new Set(parts).size,
  };
};
const { modules, stageCount, shardCount } = metrics(acceptedLayout);
const current = currentLayout === acceptedLayout ? null : metrics(currentLayout);

const COPY = {
  zh: {
    file: "README.md",
    base: "",
    all: "在网站上浏览全部论文，读摘要并逐条展开证明 →",
    latest: "最新",
    count: (n) => `${n} 篇`,
    map: "映射",
    reproduce: "复现",
    badge: `<a href="#论文"><img alt="Zenodo 论文 ${PAPERS.length} 篇" src="https://img.shields.io/badge/Zenodo-${PAPERS.length}%20%E7%AF%87%E8%AE%BA%E6%96%87-3c679f?style=flat-square"></a>`,
    alt: `Lean 完整选集：${modules} 个模块，${stageCount} 个阶段、${shardCount} 个分片，全部通过`,
    image: "docs/assets/ci-wall.svg",
    status: `**${modules} 个 Lean 模块通过完整内核验收。** [验收运行](${runUrl}) 使用 ${stageCount} 个阶段、${shardCount} 个分片，全包 \`--trust=0\`，提交 \`${run.commit.slice(0, 8)}\`。` +
      (current ? `当前构建覆盖 ${current.modules} 个模块、${current.shardCount} 个分片。` : ""),
  },
  en: {
    file: "README.en.md",
    base: "/en",
    all: "Browse all papers on the site, with abstracts and claim-level proofs →",
    latest: "Latest",
    count: (n) => `${n} ${n === 1 ? "paper" : "papers"}`,
    map: "Map",
    reproduce: "Reproduce",
    badge: `<a href="#papers"><img alt="${PAPERS.length} papers on Zenodo" src="https://img.shields.io/badge/Zenodo-${PAPERS.length}%20papers-3c679f?style=flat-square"></a>`,
    alt: `Lean full selection: ${modules} modules across ${stageCount} stages and ${shardCount} shards, all checked`,
    image: "docs/assets/ci-wall.en.svg",
    status: `**${modules} Lean modules passed the complete kernel check.** [The accepted run](${runUrl}) used ${stageCount} stages and ${shardCount} shards with \`--trust=0\` throughout at \`${run.commit.slice(0, 8)}\`.` +
      (current ? ` The current build covers ${current.modules} modules across ${current.shardCount} shards.` : ""),
  },
};

function replaceBlock(source, name, body) {
  const begin = `<!-- BEGIN ${name} -->`, end = `<!-- END ${name} -->`;
  const a = source.indexOf(begin), b = source.indexOf(end);
  if (a < 0 || b < a) throw new Error(`README block ${name} is missing`);
  return source.slice(0, a) + `${begin}\n${body}\n${end}` + source.slice(b + end.length);
}

function papers(lang) {
  const t = COPY[lang];
  const entries = PAPERS.map((entry, order) => {
    const paper = paperOf(entry.slug, lang);
    const edition = entry.editions.at(-1);
    return { entry, paper, edition, release: RELEASES[edition.release], order };
  });
  const latest = [...entries].sort((a, b) => b.paper.current.date.localeCompare(a.paper.current.date) || b.order - a.order).slice(0, 2);
  const out = [
    `**[${t.all}](https://h0mework.wiki${t.base}/papers/)**`,
    "",
    `${t.latest}${lang === "zh" ? "：" : ": "}${latest.map(({ paper }) => `[${paper.main}](https://h0mework.wiki${t.base}/papers/${paper.slug}/)`).join(" · ")}`,
    "",
  ];
  for (const theme of THEMES) {
    const rows = entries.filter(({ entry }) => entry.theme === theme.id);
    if (!rows.length) continue;
    out.push("<details>", `<summary><strong>${theme.label[lang]}</strong> · ${t.count(rows.length)}</summary>`, "");
    for (const { paper, release } of rows) {
      out.push(`- [${paper.main}](https://h0mework.wiki${t.base}/papers/${paper.slug}/) · [v${paper.editions.length}](${paper.current.doiLink}) · [${t.map}](${release.map}) · [${t.reproduce}](${release.guide})`);
    }
    out.push("", "</details>", "");
  }
  return out.join("\n").trim();
}

for (const lang of ["zh", "en"]) {
  const t = COPY[lang];
  const path = resolve(ROOT, t.file);
  let source = readFileSync(path, "utf8");
  source = replaceBlock(source, "CI STATUS", `<a href="${runUrl}"><img src="${t.image}" alt="${t.alt}" width="100%"></a>\n\n- ${t.status}`);
  source = replaceBlock(source, "PAPERS", papers(lang));
  const badge = /^  <a href="#(?:论文|papers)"><img alt="[^"]*" src="https:\/\/img\.shields\.io\/badge\/Zenodo-[^"]*"><\/a>$/m;
  if (!badge.test(source)) throw new Error(`${t.file}: Zenodo badge not found`);
  source = source.replace(badge, `  ${t.badge}`);
  writeFileSync(path, source);
}

const figure = spawnSync(process.env.PYTHON ?? "python3.12", ["docs/assets/ci_wall.py"], { cwd: ROOT, stdio: "inherit" });
if (figure.status !== 0) throw new Error("CI figure generation failed");
console.log(`README.md + README.en.md: ${PAPERS.length} papers; CI ${modules} modules, ${stageCount} stages, ${shardCount} shards, run ${run.id}`);
