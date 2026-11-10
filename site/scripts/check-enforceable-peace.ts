import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { claimsOf, leanPaths } from "../src/lib/claims";
import { citesOf, paperOf } from "../src/lib/papers";
import { ROOT, peaceBinding, readJson } from "../src/lib/registry";

const slug = "enforceable-peace";
const release = "papers/enforceable-peace/2026-11-10";
const manifest = readJson(`${release}/manifest.json`).papers.find((paper: any) => paper.paper === slug);
const binding = peaceBinding();
assert.equal(binding.public_commit, manifest.source_commit);
assert.deepEqual(citesOf(slug), ["whole-ledger-accounting", "generated-society", "economic-constitution", "capital-formation"]);
assert.equal(manifest.files.length, 5);
for (const file of manifest.files) {
  const raw = readFileSync(resolve(ROOT, release, file.path));
  assert.equal(raw.length, file.bytes, file.path);
  assert.equal(createHash("sha256").update(raw).digest("hex"), file.sha256, file.path);
}

const checkedPaths = new Set(leanPaths([slug]));
for (const source of binding.appendix_support) assert.ok(checkedPaths.has(source.path), source.path);
for (const lang of ["zh", "en"] as const) {
  const paper = paperOf(slug, lang);
  assert.equal(paper.current.doi, manifest.doi);
  assert.ok(paper.current.sourceMap?.endsWith(`/${manifest.source_commit}/docs/enforceable-peace-map.json`));
  assert.ok(paper.current.guide.endsWith(`/${manifest.source_commit}/docs/enforceable-peace-reproduction.md`));
  const rows = claimsOf(slug, lang);
  assert.equal(rows.length, 33);
  for (let i = 1; i <= 33; i++) {
    const row = rows.find((claim) => claim.key === `peace.PE${i}`);
    assert.ok(row?.proved && row.declarationCount > 0 && row.title, `missing ${lang} PE${i}`);
    assert.ok(row.excerpts.length || row.statement, `missing paper text for ${lang} PE${i}`);
    assert.ok(row.lean.every((module) => module.link.includes(`/${manifest.source_commit}/`)));
    if (lang === "en") assert.ok(row.translated, `untranslated PE${i}`);
  }
  const late = rows.find((row) => row.key === "peace.PE33")!;
  assert.ok(late.artifacts.some((file) => file.name === "handoff-resolution-acceptance.json"));
}
console.log("Peace release: five fixed files, two languages, 33 proof rows and the original execution receipt.");
