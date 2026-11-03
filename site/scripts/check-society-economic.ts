// Check the two accepted proof-map adapters against their actual release files and paper wording.
import assert from "node:assert/strict";
import { existsSync, readFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { resolve } from "node:path";
import { claimsOf, fingerprint, leanPaths, sourcesOf, translationsOf } from "../src/lib/claims";
import { PAPERS, RELEASES, ROOT, entryOf, mapOf, manuscriptOf, readJson, supplementOf } from "../src/lib/registry";
import { paperOf, statsOf } from "../src/lib/papers";

const commit = "2d6fbc96e33b7c4c3cfd91104fda74e3caeda045";
assert.equal(PAPERS.length, 9);
for (const slug of ["generated-society", "economic-constitution"] as const) {
  const entry = entryOf(slug), current = entry.editions.at(-1)!;
  const release = RELEASES[current.release], map = mapOf(current.release);
  assert.equal(entry.editions.length, 2);
  assert.equal(current.release, `${slug}-v2`);
  assert.equal(release.replacesClaimsFrom, slug);
  const manifests = ["2026-11-03", "2026-11-03-v2"].map((date) => ({
    root: `papers/society-economic/${date}`,
    paper: readJson(`papers/society-economic/${date}/manifest.json`).papers.find((paper: any) => paper.paper === slug),
  }));
  manifests.forEach(({ root, paper }, index) => {
    assert.equal(paper.version, `v${index + 1}`);
    assert.equal(paper.doi, entry.editions[index].doi);
    assert.equal(paper.is_published, true);
    assert.equal(paper.files.length, 5);
    for (const file of paper.files) {
      const raw = readFileSync(resolve(ROOT, root, file.path));
      assert.equal(raw.length, file.bytes);
      assert.equal(createHash("sha256").update(raw).digest("hex"), file.sha256);
    }
  });
  for (const file of manifests[0].paper.files.filter((file: any) => file.key.includes("-supplement")))
    assert.equal(manifests[1].paper.files.find((next: any) => next.key === file.key)?.sha256, file.sha256);
  assert.equal(release.sourceCommit, commit);
  assert.equal(release.date, "2026-11-03");
  assert.equal(map.acceptance.status, "passed");
  assert.equal(statsOf(slug).declarations, slug === "generated-society" ? 1010 : 3313);
  assert.equal(release.check.includes("entry --require-ready"), true);
  for (const lang of ["zh", "en"] as const) {
    const rows = claimsOf(slug, lang), paper = paperOf(slug, lang);
    assert.equal(rows.length, slug === "generated-society" ? 29 : 16);
    assert.equal(new Set(rows.map((row) => row.key)).size, rows.length);
    assert.equal(rows.every((row) => row.edition === 2), true);
    assert.equal(paper.current.number, 2);
    assert.equal(paper.current.doi, current.doi);
    assert.equal(paper.current.pdf.includes("/2026-11-03-v2/"), true);
    const currentText = manuscriptOf(current.release, slug, lang) + "\n\n" + supplementOf(current.release, slug, lang);
    assert.equal(paper.current.guide.includes(`/blob/${commit}/`), true);
    assert.equal(Boolean(paper.current.acceptance), false);
    assert.equal(Boolean(paper.abstract.shown.length), true);
    for (const file of Object.values(release.files(slug, lang))) assert.equal(existsSync(resolve(ROOT, file)), true, file);
    for (const row of rows) {
      for (const excerpt of row.excerpts) assert.ok(currentText.includes(excerpt.body), `${slug}/${row.key}: excerpt absent from v2`);
      assert.ok(row.lean.length, `${slug}/${row.key}: no accepted support`);
      for (const module of row.lean) assert.ok(module.link.includes(`/blob/${commit}/`));
      if (row.category === "principle") {
        assert.equal(row.proved, false);
        assert.equal(row.excerpts.length, 1);
        assert.ok(row.excerpts[0].body.includes(lang === "zh" ? "原则" : "Principle"));
      } else assert.equal(row.proved, true);
      if (row.key.startsWith("ecn.R")) {
        assert.equal(row.excerpts.length, 1);
        assert.equal(row.excerpts[0].label, `${lang === "zh" ? "结果" : "Result"} ${row.ids[0].slice(1)}`);
        assert.ok(row.excerpts[0].body.length > 40);
      }
    }
    if (slug === "economic-constitution") {
      assert.equal(rows.filter((row) => row.category === "principle").length, 8);
      assert.equal(rows.filter((row) => row.category === "formal").length, 8);
      if (lang === "en") assert.equal(paper.main, "An Economic Constitution of Possibility");
    } else {
      assert.deepEqual(rows.filter((row) => row.category === "interface").map((row) => row.ids[0]).sort(), ["G10", "G11", "G12"]);
      assert.ok(rows.find((row) => row.key === "soc.G2")?.excerpts[0]?.label.endsWith("4.3"));
      assert.ok(rows.find((row) => row.key === "soc.G18")?.excerpts[0]?.label.endsWith("6.4"));
      assert.ok(rows.find((row) => row.key === "soc.G6")?.location?.includes("§3.6"));
      assert.equal(rows.some((row) => /(?:结果|Result)\s*3\.6/.test(row.location ?? "")), false);
    }
  }
  for (const source of sourcesOf(slug)) assert.equal(translationsOf("en")[source.key]?.from, fingerprint(source.text), source.key);
  console.log(`${slug}: published files, accepted owners, fixed source links, bilingual text and claim classifications passed`);
}
assert.ok(leanPaths(["generated-society", "economic-constitution"]).length > 0);
