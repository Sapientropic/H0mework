// Maintains src/data/claims-<lang>.json, the translations of claims registered in the other language.
//
//   bun scripts/translations.ts --lang zh                      rows needing a translation, with their registered text
//   bun scripts/translations.ts --lang zh --merge <file.json>  add translations {key: {title?, statement?}},
//                                                              fingerprinted against the registered text
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { resolve } from "node:path";
import { fingerprint, needsTranslation, sourcesOf } from "../src/lib/claims";
import { PAPERS, type Lang } from "../src/lib/registry";

const arg = (name: string) => process.argv[process.argv.indexOf(name) + 1];
const lang = (process.argv.includes("--lang") ? arg("--lang") : "en") as Lang;
const path = resolve(process.cwd(), `src/data/claims-${lang}.json`);
const translations: Record<string, { title?: string; statement?: string; from: string }> = existsSync(path) ? JSON.parse(readFileSync(path, "utf8")) : {};
const sources = PAPERS.flatMap((paper) => sourcesOf(paper.slug)).filter((source) => needsTranslation(source, lang));

if (process.argv.includes("--merge")) {
  const additions: Record<string, { title?: string; statement?: string }> = JSON.parse(readFileSync(arg("--merge"), "utf8"));
  for (const [key, text] of Object.entries(additions)) {
    const source = sources.find((candidate) => candidate.key === key);
    if (!source) throw new Error(`${key}: no registered row needs a ${lang} translation`);
    for (const field of ["title", "statement"] as const)
      if (Boolean(text[field]) !== Boolean(source.text[field])) throw new Error(`${key}: ${field} does not match the registered text`);
    translations[key] = { ...text, from: fingerprint(source.text) };
  }
}
// Rewritten in reading order; entries no row needs any more are dropped.
const kept = Object.fromEntries(sources.filter((source) => translations[source.key]).map((source) => [source.key, translations[source.key]]));
writeFileSync(path, JSON.stringify(kept, null, 1) + "\n");
const stale = sources.filter((source) => kept[source.key]?.from !== fingerprint(source.text));
for (const source of stale) console.log(JSON.stringify({ key: source.key, ...source.text }));
console.log(`${lang}: ${sources.length - stale.length} of ${sources.length} rows translated`);
