// Check the new paper against its actual eighteen results and reused proof-source identities.
import assert from "node:assert/strict";
import { readFileSync, existsSync } from "node:fs";
import { createHash } from "node:crypto";
import { execFileSync } from "node:child_process";
import { resolve } from "node:path";
import { claimsOf, sourcesOf, fingerprint, translationsOf } from "../src/lib/claims";
import { paperOf, statsOf, citesOf } from "../src/lib/papers";
import { ROOT, RELEASES, mapOf, manuscriptOf, publishedPaperJson, readJson } from "../src/lib/registry";

const slug = "capital-formation", fixed = "2d6fbc96e33b7c4c3cfd91104fda74e3caeda045";
const map = mapOf(slug);
const sha = (raw: Buffer) => createHash("sha256").update(raw).digest("hex");
const manifest = readJson("papers/capital-formation/2026-11-04/manifest.json");
const release = manifest.papers.find((paper: any) => paper.paper === slug);
assert.equal(manifest.published, true);
assert.equal(release.is_published, true);
assert.equal(release.is_draft, false);
assert.equal(release.files.length, 5);
for (const file of release.files) {
  const raw = readFileSync(resolve(ROOT, "papers/capital-formation/2026-11-04", file.path));
  assert.equal(raw.length, file.bytes);
  assert.equal(sha(raw), file.sha256);
}
const unzip = (member: string) => execFileSync("unzip", ["-p", resolve(ROOT, map.inputs.archive), member], { maxBuffer: 1 << 26 });
assert.equal(sha(unzip(map.inputs.binding_member)), map.inputs.binding_sha256);
assert.equal(sha(unzip(map.inputs.selection_member)), map.inputs.selection_sha256);
for (const [member, digest] of Object.entries(map.inputs.manuscripts)) assert.equal(sha(unzip(member)), digest);
const binding = publishedPaperJson(slug, slug, "records/public-source-binding.json");
for (const entry of binding.entries) {
  if (entry.public) assert.equal(sha(readFileSync(resolve(ROOT, entry.public.path))), entry.public.target_sha256);
  if (entry.preserved_source) assert.equal(sha(readFileSync(resolve(ROOT, "papers/capital-formation/2026-11-04", entry.preserved_source.path))), entry.source_sha256);
}
for (const consumer of Object.values(map.public_consumers) as any[])
  assert.equal(sha(readFileSync(resolve(ROOT, consumer.public.path))), consumer.public.sha256);
assert.equal(map.schema, "capital-formation/claim-map@1");
assert.equal(map.summary.accepted_public_modules, 100);
assert.equal(map.summary.additional_public_direct_consumer_owners, 63);
assert.equal(map.summary.existing_complete_type_observations_in_selected_modules, 160);
assert.equal(map.summary.auxiliary_reading_files, 5);
assert.equal(map.acceptance.new_Lean_execution, false);
assert.deepEqual(statsOf(slug), { claims: 18, modules: 163, declarations: 160 });
for (const lang of ["zh", "en"] as const) {
  const paper = paperOf(slug, lang), rows = claimsOf(slug, lang);
  const text = manuscriptOf(slug, slug, lang);
  assert.equal(rows.length, 18);
  assert.equal(new Set(rows.map((row) => row.key)).size, 18);
  assert.ok(paper.sub.length > 10);
  assert.ok(paper.current.guide.includes("/blob/main/docs/capital-formation-reproduction.md"));
  assert.ok(paper.current.sourceMap?.includes("/blob/main/docs/capital-formation-map.json"));
  assert.equal(paper.current.sourceCommit, fixed);
  assert.ok(paper.abstract.shown.length > 0);
  for (const [index, row] of rows.entries()) {
    assert.equal(row.ids[0], `R${index + 1}`);
    assert.equal(row.proved, true);
    assert.equal(row.excerpts.length, 1);
    assert.equal(row.excerpts[0].label, `${index === 9 ? (lang === "zh" ? "命题" : "Proposition") : (lang === "zh" ? "定理" : "Theorem")} ${index + 1}`);
    assert.ok(row.excerpts[0].body.length > 35);
    assert.ok(text.includes(row.excerpts[0].body), `${lang}/${row.key}: statement absent from actual manuscript`);
    for (const module of row.lean) {
      assert.ok(module.link.includes(`/blob/${fixed}/Lean/`));
      assert.ok(existsSync(resolve(ROOT, "Lean", module.module.replaceAll(".", "/") + ".lean")));
      for (const declaration of module.declarations) {
        assert.ok(declaration.line && declaration.link.endsWith(`#L${declaration.line}`));
        const path = new URL(declaration.link).pathname.split(`/blob/${fixed}/`)[1];
        assert.ok(readFileSync(resolve(ROOT, path), "utf8").split("\n")[declaration.line! - 1].includes(declaration.name));
      }
    }
    for (const artifact of row.artifacts) {
      assert.ok(artifact.link.includes("/blob/main/papers/capital-formation/2026-11-04/source-excerpts/"));
      assert.ok(existsSync(resolve(ROOT, artifact.path)));
    }
  }
  for (const file of Object.values(RELEASES[slug].files(slug, lang))) assert.ok(existsSync(resolve(ROOT, file)));
}
for (const source of sourcesOf(slug))
  assert.equal(translationsOf("en")[source.key]?.from, fingerprint(source.text), source.key);
assert.deepEqual(citesOf(slug).sort(), ["economic-constitution", "generated-society"]);
assert.equal(paperOf(slug, "zh").current.doi, release.doi);
console.log("capital-formation: all eighteen bilingual statements, theorem/proposition distinction, 163 exact owners, 160 observed declaration links, five source resources, current documentation and fixed proof links passed");
