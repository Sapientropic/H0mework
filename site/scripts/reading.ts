// Maintains src/data/reading-<lang>.json, the reader wording of claim rows (claims.ts, "reading layer").
//
//   bun scripts/reading.ts --lang zh                      entries written from an earlier registered text
//   bun scripts/reading.ts --lang zh --merge <file.json>  add or replace entries {key: {title?, statement?, cite?, passages?}},
//                                                         fingerprinted against the registered text
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";
import { fingerprint, sourcesOf } from "../src/lib/claims";
import { PAPERS, type Lang } from "../src/lib/registry";

type Entry = { title?: string; statement?: string; cite?: string[]; passages?: string[] };
const arg = (name: string) => process.argv[process.argv.indexOf(name) + 1];
const lang = (process.argv.includes("--lang") ? arg("--lang") : "zh") as Lang;
const path = resolve(process.cwd(), `src/data/reading-${lang}.json`);
const reading: Record<string, Entry & { from: string }> = existsSync(path) ? JSON.parse(readFileSync(path, "utf8")) : {};
const sources = PAPERS.flatMap((paper) => sourcesOf(paper.slug));

if (process.argv.includes("--merge")) {
  const additions: Record<string, Entry> = JSON.parse(readFileSync(arg("--merge"), "utf8"));
  for (const [key, entry] of Object.entries(additions)) {
    const source = sources.find((candidate) => candidate.key === key);
    if (!source) throw new Error(`${key}: no such row`);
    if (entry.statement && !source.text.statement) throw new Error(`${key}: a restatement needs a registered statement`);
    reading[key] = { ...entry, from: fingerprint(source.text) };
  }
}
// Rewritten in reading order; entries for rows that no longer exist are dropped.
const kept = Object.fromEntries(sources.filter((source) => reading[source.key]).map((source) => [source.key, reading[source.key]]));
writeFileSync(path, JSON.stringify(kept, null, 1) + "\n");
const stale = sources.filter((source) => kept[source.key] && kept[source.key].from !== fingerprint(source.text));
for (const source of stale) console.log(JSON.stringify({ key: source.key, ...source.text }));
console.log(`${lang}: ${Object.keys(kept).length} entries, ${stale.length} stale`);
