// Check both publication records and the current edition's fixed proof links.
import assert from "node:assert/strict";
import { readFileSync, existsSync } from "node:fs";
import { createHash } from "node:crypto";
import { execFileSync } from "node:child_process";
import { resolve } from "node:path";
import { claimsOf } from "../src/lib/claims";
import { paperOf, statsOf, citesOf } from "../src/lib/papers";
import { ROOT, RELEASES, mapOf, manuscriptOf, publishedPaperJson, readJson } from "../src/lib/registry";

const slug = "capital-formation", edition = "capital-formation-v2";
const firstFolder = "papers/capital-formation/2026-11-04", folder = "papers/capital-formation/2026-11-12-v2";
const first = mapOf(slug), current = mapOf(edition), risk = current.risk_compensation;
const sha = (raw: Buffer) => createHash("sha256").update(raw).digest("hex");

function checkRelease(directory: string) {
  const manifest = readJson(`${directory}/manifest.json`);
  const release = manifest.papers.find((paper: any) => paper.paper === slug);
  assert.equal(manifest.published, true);
  assert.equal(release.is_published, true);
  assert.equal(release.is_draft, false);
  assert.equal(release.files.length, 5);
  for (const file of release.files) {
    const raw = readFileSync(resolve(ROOT, directory, file.path));
    assert.equal(raw.length, file.bytes);
    assert.equal(sha(raw), file.sha256);
  }
  return release;
}

const previous = checkRelease(firstFolder), release = checkRelease(folder);
assert.equal(release.previous_doi, previous.doi);
assert.equal(release.source_commit, risk.proof_commit);
assert.equal(current.inherited.proof_commit, first.proof_commit);
assert.equal(sha(readFileSync(resolve(ROOT, current.inherited.map))), current.inherited.map_sha256);
assert.equal(first.schema, "capital-formation/claim-map@1");
assert.equal(current.schema, "capital-formation/claim-map@2");
assert.equal(first.summary.public_support_owners, 163);
assert.equal(first.summary.existing_complete_type_observations_in_selected_modules, 160);
assert.equal(first.summary.auxiliary_reading_files, 5);
assert.equal(first.acceptance.new_Lean_execution, false);
assert.equal(risk.summary.complete_types, 17);
assert.equal(risk.summary.pricing_modules, 55);
assert.equal(RELEASES[edition].replacesClaimsFrom, slug);

for (const { inputs } of [first, current]) {
  const unzip = (member: string) => execFileSync("unzip", ["-p", resolve(ROOT, inputs.archive), member], { maxBuffer: 1 << 26 });
  assert.equal(sha(unzip(inputs.binding_member)), first.inputs.binding_sha256);
  assert.equal(sha(unzip(inputs.selection_member)), first.inputs.selection_sha256);
  for (const [member, digest] of Object.entries(inputs.manuscripts)) assert.equal(sha(unzip(member)), digest);
  if (inputs.risk_binding_member) assert.equal(sha(unzip(inputs.risk_binding_member)), inputs.risk_binding_sha256);
}
const binding = publishedPaperJson(slug, slug, "records/public-source-binding.json");
for (const entry of binding.entries) {
  if (entry.public) assert.equal(sha(readFileSync(resolve(ROOT, entry.public.path))), entry.public.target_sha256);
  if (entry.preserved_source) assert.equal(sha(readFileSync(resolve(ROOT, firstFolder, entry.preserved_source.path))), entry.source_sha256);
}
const riskEntries = [...risk.claim.producers, ...risk.claim.direct_consumers];
const riskModules = new Set(riskEntries.map((entry) => entry.public.module));
for (const entry of [...Object.values(first.public_consumers) as any[], ...riskEntries])
  assert.equal(sha(readFileSync(resolve(ROOT, entry.public.path))), entry.public.sha256);
assert.deepEqual(statsOf(slug), { claims: 19, modules: 172, declarations: 177 });
for (const lang of ["zh", "en"] as const) {
  const paper = paperOf(slug, lang), rows = claimsOf(slug, lang);
  const text = manuscriptOf(edition, slug, lang);
  assert.equal(rows.length, 19);
  assert.equal(new Set(rows.map((row) => row.key)).size, 19);
  assert.ok(paper.sub.length > 10);
  assert.ok(paper.current.guide.includes("/blob/main/docs/capital-formation-v2-reproduction.md"));
  assert.ok(paper.current.sourceMap?.includes("/blob/main/docs/capital-formation-v2-map.json"));
  assert.equal(paper.current.sourceCommit, risk.proof_commit);
  assert.equal(paper.current.doi, release.doi);
  assert.ok(paper.abstract.shown.length > 0);
  for (const [index, row] of rows.entries()) {
    const number = index + 1, result = current.claims[index];
    const label = number === 10 ? (lang === "zh" ? "命题" : "Proposition") : (lang === "zh" ? "定理" : "Theorem");
    assert.equal(row.ids[0], `R${number}`);
    assert.equal(result.inherited_result, number === 12 ? null : `R${number - Number(number > 12)}`);
    assert.equal(row.title.replaceAll(" ", ""), result.title[lang].replaceAll(" ", ""));
    assert.equal(row.proved, true);
    assert.equal(row.excerpts.length, 1);
    assert.equal(row.excerpts[0].label, `${label} ${number}`);
    assert.ok(row.excerpts[0].body.length > 35 && text.includes(row.excerpts[0].body));
    assert.equal(row.lean.filter((module) => riskModules.has(module.module)).length, result.risk_claim ? riskModules.size : 0);
    for (const module of row.lean) {
      const commit = riskModules.has(module.module) ? risk.proof_commit : first.proof_commit;
      assert.ok(module.link.includes(`/blob/${commit}/Lean/`));
      assert.ok(existsSync(resolve(ROOT, "Lean", module.module.replaceAll(".", "/") + ".lean")));
      for (const declaration of module.declarations) {
        assert.ok(declaration.line && declaration.link.endsWith(`#L${declaration.line}`));
        const path = new URL(declaration.link).pathname.split(`/blob/${commit}/`)[1];
        assert.ok(readFileSync(resolve(ROOT, path), "utf8").split("\n")[declaration.line! - 1].includes(declaration.name));
      }
    }
    for (const artifact of row.artifacts) {
      assert.ok(artifact.link.includes(`/blob/main/${firstFolder}/source-excerpts/`));
      assert.ok(existsSync(resolve(ROOT, artifact.path)));
    }
  }
  for (const file of Object.values(RELEASES[edition].files(slug, lang))) assert.ok(existsSync(resolve(ROOT, file)));
}
assert.deepEqual(citesOf(slug).sort(), ["economic-constitution", "generated-society", "whole-ledger-accounting"]);
console.log("capital-formation: both publications, nineteen bilingual results, CF17 direct consumers, and both proof snapshots passed");
