import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { claimsOf } from "../src/lib/claims";
import { paperOf } from "../src/lib/papers";
import { ROOT, readJson } from "../src/lib/registry";

const release = "papers/process-core-whole-ledger/2026-11-12";
const manifest = readJson(`${release}/manifest.json`);
assert.equal(manifest.papers.length, 2);
for (const record of manifest.papers) {
  assert.equal(record.files.length, 5);
  assert.equal(record.source_commit, manifest.source_commit);
  for (const file of record.files) {
    const raw = readFileSync(resolve(ROOT, file.public_path));
    assert.equal(raw.length, file.bytes, file.public_path);
    assert.equal(createHash("sha256").update(raw).digest("hex"), file.sha256, file.public_path);
  }
}

for (const lang of ["zh", "en"] as const) {
  const core = paperOf("source-process-core", lang);
  const ledger = paperOf("whole-ledger-accounting", lang);
  const coreRows = claimsOf(core.slug, lang);
  const ledgerRows = claimsOf(ledger.slug, lang);
  for (const paper of [core, ledger]) {
    const record = manifest.papers.find((row: any) => row.paper === paper.slug);
    assert.equal(paper.current.doi, record.doi);
    assert.ok(paper.current.sourceMap?.includes(`/${record.source_commit}/`));
  }
  assert.equal(ledgerRows.length, 45);
  if (lang === "en") assert.equal(ledger.citation.title,
    "Provenance-Preserving Conservation Calculus and Non-Free Continuity: Whole-Event Ledgers, Observer Safety, and Well-Founded Settlement");
  for (let number = 1; number <= 45; number++) {
    const rows = ledgerRows.filter((row) => row.key === `wla.WA${number}`);
    assert.equal(rows.length, 1);
    assert.ok(rows[0].proved && rows[0].declarationCount > 0);
  }
  for (let number = 46; number <= 54; number++) {
    const rows = coreRows.filter((row) => row.key === `core.C${number}`);
    assert.equal(rows.length, 1);
    assert.ok(rows[0].proved && rows[0].declarationCount > 0);
  }
  const capacity = ledgerRows.find((row) => row.key === "wla.WA4")!;
  assert.ok(capacity.lean.some((module) => module.module.endsWith(".ResponsibilityCapacityKernel")));
  for (const [c, wa] of [[53, 44], [54, 45]]) {
    const coreModules = coreRows.find((row) => row.key === `core.C${c}`)!.lean;
    const ledgerModules = ledgerRows.find((row) => row.key === `wla.WA${wa}`)!.lean;
    assert.deepEqual(coreModules.map((module) => module.link), ledgerModules.map((module) => module.link));
  }
}
console.log("Process core and whole ledger: ten fixed files, bilingual latest editions and exact shared proof links.");
