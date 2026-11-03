// Compare the planning inventory with actual published entries; a reserved slot is not a draft.
import assert from "node:assert/strict";
import { PAPER_PLAN, PAPERS, THEMES, UPCOMING } from "../src/lib/registry";

const ids = new Set(THEMES.map((theme) => theme.id));
assert.equal(ids.size, THEMES.length, "Repeated theme");
assert.equal(new Set(PAPERS.map((paper) => paper.slug)).size, PAPERS.length, "Repeated published paper");
for (const paper of PAPERS) assert.ok(ids.has(paper.theme), `${paper.slug}: unknown theme`);
for (const theme of PAPER_PLAN.themes) {
  assert.ok(theme.label.zh.trim() && theme.label.en.trim(), `${theme.id}: missing label`);
  for (const n of [theme.registered, theme.reserved ?? 0, theme.soon ?? 0]) assert.ok(Number.isInteger(n) && n >= 0);
  const remaining = UPCOMING[theme.id]!;
  assert.ok(remaining.count >= 0, `${theme.id}: more published papers than planned`);
  assert.ok((remaining.soon ?? 0) <= remaining.count, `${theme.id}: ready count exceeds preparation count`);
}
assert.equal(PAPER_PLAN.themes.reduce((n, theme) => n + theme.registered, 0), PAPER_PLAN.registeredPapers);
assert.equal(PAPER_PLAN.themes.reduce((n, theme) => n + (theme.reserved ?? 0), 0), PAPER_PLAN.resultTriggeredSlots);
const preparing = Object.values(UPCOMING).reduce((n, theme) => n + theme!.count, 0);
assert.equal(PAPERS.length + preparing, PAPER_PLAN.registeredPapers);
assert.equal(PAPERS.filter((paper) => paper.theme === "preface").length, 1);
assert.equal(UPCOMING.preface?.count, 0, "The forest root must be the published preface");
assert.equal(UPCOMING.preface?.reserved, 0);
console.log(`Paper plan: ${PAPER_PLAN.registeredPapers} registered, ${PAPERS.length} published, ${preparing} in preparation, ${PAPER_PLAN.resultTriggeredSlots} separate result-dependent slot`);
