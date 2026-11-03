// Check the two accepted proof-map adapters against their actual release files and paper wording.
import assert from "node:assert/strict";
import { existsSync } from "node:fs";
import { resolve } from "node:path";
import { claimsOf, fingerprint, leanPaths, sourcesOf, translationsOf } from "../src/lib/claims";
import { PAPERS, RELEASES, ROOT, UPCOMING, mapOf } from "../src/lib/registry";
import { paperOf, statsOf } from "../src/lib/papers";

const commit = "2d6fbc96e33b7c4c3cfd91104fda74e3caeda045";
assert.equal(PAPERS.length, 8);
assert.equal(UPCOMING.mind?.count, 1);
for (const slug of ["generated-society", "economic-constitution"] as const) {
  const release = RELEASES[slug], map = mapOf(slug);
  assert.equal(release.sourceCommit, commit);
  assert.equal(release.date, "2026-11-03");
  assert.equal(map.acceptance.status, "passed");
  assert.equal(statsOf(slug).declarations, slug === "generated-society" ? 1010 : 3313);
  assert.equal(release.check.includes("entry --require-ready"), true);
  for (const lang of ["zh", "en"] as const) {
    const rows = claimsOf(slug, lang), paper = paperOf(slug, lang);
    assert.equal(rows.length, slug === "generated-society" ? 29 : 16);
    assert.equal(paper.current.guide.includes(`/blob/${commit}/`), true);
    assert.equal(Boolean(paper.current.acceptance), false);
    assert.equal(Boolean(paper.abstract.shown.length), true);
    for (const file of Object.values(release.files(slug, lang))) assert.equal(existsSync(resolve(ROOT, file)), true, file);
    for (const row of rows) {
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
    }
  }
  for (const source of sourcesOf(slug)) assert.equal(translationsOf("en")[source.key]?.from, fingerprint(source.text), source.key);
  console.log(`${slug}: published files, accepted owners, fixed source links, bilingual text and claim classifications passed`);
}
assert.ok(leanPaths(["generated-society", "economic-constitution"]).length > 0);
