// Maintains src/data/claims-en.json, the English layer over the registered Chinese claims.
//
//   bun scripts/claims-en.ts                       list rows whose English is missing or stale, with their Chinese
//   bun scripts/claims-en.ts --merge <file.json>   add translations {key: {title?, statement?}}, fingerprinted
//                                                  against the Chinese they were translated from
import { readFileSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";
import { fingerprint, sourcesOf } from "../src/lib/claims";
import { PAPERS } from "../src/lib/registry";

const path = resolve(process.cwd(), "src/data/claims-en.json");
const english: Record<string, { title?: string; statement?: string; zh: string }> = JSON.parse(readFileSync(path, "utf8"));
const sources = new Map(PAPERS.flatMap((paper) => sourcesOf(paper.slug)).map((source) => [source.key, source]));

const merge = process.argv.indexOf("--merge");
if (merge > 0) {
  const additions: Record<string, { title?: string; statement?: string }> = JSON.parse(readFileSync(process.argv[merge + 1], "utf8"));
  for (const [key, text] of Object.entries(additions)) {
    const source = sources.get(key);
    if (!source) throw new Error(`${key}: no registered claim row`);
    for (const field of ["title", "statement"] as const)
      if (Boolean(text[field]) !== Boolean(source.text[field])) throw new Error(`${key}: ${field} does not match the registered Chinese`);
    english[key] = { ...text, zh: fingerprint(source.text) };
  }
  const ordered = Object.fromEntries([...sources.keys()].filter((key) => english[key]).map((key) => [key, english[key]]));
  writeFileSync(path, JSON.stringify(ordered, null, 1) + "\n");
  console.log(`merged ${Object.keys(additions).length}; ${Object.keys(ordered).length} rows translated`);
} else {
  const stale = [...sources.values()].filter((source) => english[source.key]?.zh !== fingerprint(source.text));
  for (const source of stale) console.log(JSON.stringify({ key: source.key, ...source.text }));
  console.log(`${stale.length} of ${sources.size} rows need English`);
}
