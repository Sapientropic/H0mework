import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { claimsOf, leanPaths } from "../src/lib/claims";
import { paperOf } from "../src/lib/papers";
import { ROOT, mapOf, publishedPaperJson, readJson } from "../src/lib/registry";

const slug = "economic-constitution", edition = "economic-constitution-v3";
const folder = "papers/economic-constitution/2026-11-13-v3";
const [published] = readJson(folder + "/manifest.json").papers;
const previous = readJson("papers/society-economic/2026-11-03-v2/manifest.json").papers
  .find((paper: any) => paper.paper === slug);
const map = mapOf(edition);
assert.equal(published.previous_doi, previous.doi);
assert.deepEqual(published.proof_commits, map.proof_snapshots);
assert.equal(published.files.length, 5);
assert.equal(map.acceptance.status, "passed");
for (const file of published.files) {
  const bytes = readFileSync(resolve(ROOT, folder, file.path));
  assert.equal(bytes.length, file.bytes);
  assert.equal(createHash("sha256").update(bytes).digest("hex"), file.sha256);
}
const binding = publishedPaperJson(edition, slug, "records/v3-source-binding.json");
assert.deepEqual(binding.results, map.results);
const sourcePaths = new Set(leanPaths([slug]));
for (const lang of ["zh", "en"] as const) {
  const paper = paperOf(slug, lang);
  const rows = claimsOf(slug, lang);
  assert.equal(paper.current.number, 3);
  assert.equal(paper.current.doi, published.doi);
  assert.equal(rows.length, 26);
  assert.ok(rows.every((row) => row.edition === 3));
  assert.equal(new Set(rows.map((row) => row.key)).size, rows.length);
  const principles = rows.filter((row) => row.category === "principle");
  assert.equal(principles.length, 8);
  assert.ok(principles.every((row) => !row.proved && row.excerpts.length === 1));
  for (const result of map.results) {
    const { label } = result.titles[lang];
    const row = rows.find((item) => item.category === "formal" && item.label === label);
    assert.ok(row?.proved, label);
    assert.equal(row.excerpts[0]?.label, label);
    assert.ok(row.excerpts[0].body.length > 40);
    for (const claim of map.claims.filter((claim: any) => result.proof_claims.includes(claim.id))) {
      for (const entry of [...claim.producers, ...claim.direct_consumers]) {
        assert.ok(sourcePaths.has(entry.public.path));
        const owner = row.lean.find((item) => item.module === entry.public.module);
        const commit = map.proof_snapshots[map.source_snapshots[entry.public.path]];
        assert.ok(owner?.link.includes("/blob/" + commit + "/"));
        const lines = readFileSync(resolve(ROOT, entry.public.path), "utf8").split("\n");
        for (const decl of entry.declarations) {
          const linked = owner.declarations.find((item) => item.qualified === decl.qualified_name);
          assert.ok(linked?.link.endsWith("#L" + decl.public_line));
          assert.ok(lines[decl.public_line - 1].includes(linked.name));
        }
      }
    }
  }
  assert.ok(rows.some((row) => row.key === "ecn.R4" && row.label.endsWith("4.2")));
}
console.log("economic-constitution v3: publication, bilingual results, principles, and fixed source links passed");
