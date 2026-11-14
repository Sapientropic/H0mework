// The anatomy figures built by figures/<name>/build.mjs --fragment, and each one's page script.
import { createHash } from "node:crypto";
import type { Lang } from "./papers";

export type FigureFragment = { html: Record<Lang, string>; css: string; script: string };
const fragments = import.meta.glob<FigureFragment>("../generated/*.json", { eager: true, import: "default" });

export function figureOf(name: string): FigureFragment {
  const figure = fragments[`../generated/${name}.json`];
  if (!figure) throw new Error(`figure ${name} not built: run bun run figures`);
  return figure;
}

// Whitespace and syntax only: identifiers stay, so a stack trace still reads against the source.
const minified = (source: string): string => {
  const bun = (globalThis as { Bun?: { Transpiler: new (options: object) => { transformSync(code: string): string } } }).Bun;
  return bun ? new bun.Transpiler({ loader: "js", target: "browser", minifyWhitespace: true, minifySyntax: true }).transformSync(source) : source;
};

const scripts = new Map<string, { code: string; version: string }>();
// `version` is the hash of the code, for the script URL: a rebuilt figure is fetched anew, an unchanged one stays cached.
export function figureScriptOf(name: string) {
  let script = scripts.get(name);
  if (!script) {
    const code = minified(figureOf(name).script);
    script = { code, version: createHash("sha256").update(code).digest("hex").slice(0, 12) };
    scripts.set(name, script);
  }
  return script;
}
