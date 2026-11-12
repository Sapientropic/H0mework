import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { claimsOf, leanPaths } from "../src/lib/claims";
import { excerptsOf } from "../src/lib/excerpts";
import { paperOf } from "../src/lib/papers";
import { ROOT, mapOf, publishedPaperJson, readJson } from "../src/lib/registry";

const slug = "generated-society", edition = "generated-society-v3";
const folder = "papers/generated-society/2026-11-12-v3";
const manifest = readJson(folder + "/manifest.json");
const [release] = manifest.papers;
const previous = readJson("papers/society-economic/2026-11-03-v2/manifest.json").papers
  .find((paper: any) => paper.paper === slug);
const map = mapOf(edition);
assert.equal(release.paper, slug);
assert.equal(release.previous_doi, previous.doi);
assert.equal(release.files.length, 5);
assert.equal(map.acceptance.status, "passed");
assert.equal(map.proof_snapshots.main, release.source_commit);
for (const file of release.files) {
  const raw = readFileSync(resolve(ROOT, folder, file.path));
  assert.equal(raw.length, file.bytes);
  assert.equal(createHash("sha256").update(raw).digest("hex"), file.sha256);
}

const binding = publishedPaperJson(edition, slug, "records/m7-source-binding-v3.json");
const sourcePaths = leanPaths([slug]);
assert.equal(binding.total_v3_modules_verified, 24);
for (const lang of ["zh", "en"] as const) {
  const paper = paperOf(slug, lang), rows = claimsOf(slug, lang);
  assert.equal(paper.current.doi, release.doi);
  assert.equal(paper.current.number, 3);
  assert.ok(paper.sub.length > 10);
  assert.equal(rows.length, 32);
  assert.ok(rows.every((row) => row.edition === 3));
  assert.deepEqual(rows.filter((row) => row.category === "interface").map((row) => row.ids[0]).sort(),
    ["G10", "G11", "G12"]);
  const opening = excerptsOf(edition, slug, lang, "定理 1.1").results[0];
  assert.equal(opening.label, lang === "zh" ? "定理 1.1" : "Theorem 1.1");
  for (const claim of map.claims) {
    const crossDomain = claim.id === "cross-domain-actors";
    const row = rows.find((candidate) => candidate.ids[0] === (crossDomain ? "G0" : claim.id));
    assert.ok(row?.proved);
    if (!crossDomain) {
      assert.equal(row.excerpts[0]?.label, claim.location[lang]);
      assert.ok(row.excerpts[0]?.body.length > 60);
    }
    const commit = crossDomain ? map.proof_snapshots.cross_domain : map.proof_snapshots.main;
    for (const entry of [...claim.producers, ...claim.direct_consumers]) {
      assert.ok(sourcePaths.includes(entry.public.path));
      const module = row.lean.find((item) => item.module === entry.public.module);
      assert.ok(module?.link.includes("/blob/" + commit + "/"));
      const lines = readFileSync(resolve(ROOT, entry.public.path), "utf8").split("\n");
      for (const decl of entry.declarations) {
        const linked = module.declarations.find((item) => item.qualified === decl.qualified_name);
        assert.ok(linked?.link.endsWith("#L" + decl.public_line));
        assert.ok(lines[decl.public_line - 1].includes(linked.name));
      }
    }
  }
}
console.log("generated-society v3: published files, bilingual results, and fixed producer and consumer links passed");
