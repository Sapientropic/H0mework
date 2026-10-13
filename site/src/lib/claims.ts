// Claim rows for a paper, read from every release map that registers it.
// The maps differ in schema; each adapter below turns one schema into the same Source shape.
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { RELEASES, entryOf, manuscriptOf, mapOf, once, read, readJson, repoLink, type Lang, type ReleaseId } from "./registry";

type Declaration = { name?: string; qualified_name: string; line?: number };
type Producer = {
  kind: string;
  public?: { path: string; module?: string };
  declarations?: Declaration[];
};
type Text = { title: string | null; statement: string | null };
export type Source = { key: string; ids: string[]; edition: number; text: Text; location: Record<Lang, string | null>; producers: Producer[] };

// Every mapped Lean producer passed its kernel check before release. A map's "pending" marks only
// the later re-acceptance of the public package in CI, so the site does not show it as a status.
const leanOf = (producers: Producer[]) => producers.filter((producer) => producer.kind === "lean" && producer.public?.module);

// --- adapters ---------------------------------------------------------------------------------

function firstRelease(slug: string, edition: number): Source[] {
  return mapOf("first-release")
    .claims.filter((claim: any) => claim.paper === slug)
    .map((claim: any) => ({
      key: claim.id,
      ids: [claim.id],
      edition,
      text: { title: claim.title, statement: claim.statement },
      location: claim.text_location.selection,
      producers: claim.producers,
    }));
}

// The low-energy map records the written location in three shapes; zh locations are written in English.
function lowEnergyLocation(claim: any, lang: Lang): string | null {
  const proof = claim.written_proof;
  if (!proof) return null;
  const own = proof[lang];
  const raw = typeof own === "object" && own ? own.location ?? own.sections?.join("; ") : proof.sections?.map((s: string) => (/^\d/.test(s) ? `§${s}` : s)).join("; ");
  if (!raw) return null;
  return lang === "zh" ? raw.replace(/Appendix\s*/g, "附录 ").replace(/Figure\s*/g, "图 ").replace(/;\s*/g, "；") : raw;
}

function lowEnergy(slug: string, edition: number): Source[] {
  return mapOf("low-energy")
    .claims.filter((claim: any) => claim.paper === slug)
    .map((claim: any) => ({
      key: claim.id,
      ids: [claim.id],
      edition,
      text: { title: claim.title ?? null, statement: claim.statement ?? null },
      location: { zh: lowEnergyLocation(claim, "zh"), en: lowEnergyLocation(claim, "en") },
      producers: claim.producers,
    }));
}

// The second-edition map registers its claims per intake package: several claims share one
// package text, so the site shows one row per package, titled and located by the release selection.
const KINDS: Record<Lang, RegExp> = { zh: /定理|命题|引理|推论|例|定义|构造/, en: /Theorem|Proposition|Lemma|Corollary|Example|Definition|Construction/ };
function kindOf(manuscript: string, result: string, lang: Lang) {
  const id = result.replace(/\./g, "\\.");
  const pattern = lang === "zh" ? new RegExp(`\\*\\*(${KINDS.zh.source})\\s*${id}(?![\\w.])`) : new RegExp(`\\*\\*(${KINDS.en.source})\\s+${id}(?![\\w.])`);
  return manuscript.match(pattern)?.[1] ?? (lang === "zh" ? "结果" : "Result");
}

function resultsAt(intake: any, slug: string, lang: Lang) {
  const manuscript = manuscriptOf("second-edition", slug, lang);
  const sections = new Map<string, string[]>();
  for (const at of intake.actual_text.filter((entry: any) => entry.language === lang)) {
    const results = sections.get(at.section) ?? [];
    if (at.result && !results.includes(at.result)) results.push(at.result);
    sections.set(at.section, results);
  }
  const numeric = (s: string) => s.split(".").map((part) => parseFloat(part));
  const sorted = [...sections].sort(([a], [b]) => numeric(a)[0] - numeric(b)[0] || (numeric(a)[1] ?? 0) - (numeric(b)[1] ?? 0));
  return sorted
    .map(([section, results]) => {
      const named = results.sort((a, b) => parseFloat(a.split(".")[1]) - parseFloat(b.split(".")[1])).map((result) => ({ kind: kindOf(manuscript, result, lang), result }));
      const list = named.map(({ kind, result }, index) => {
        const repeat = index > 0 && named[index - 1].kind === kind;
        return lang === "zh" ? `${repeat ? "" : kind}${result}` : repeat ? result : kind + (named[index + 1]?.kind === kind ? "s" : "") + " " + result;
      });
      return `§${section}${list.length ? " " + list.join(lang === "zh" ? "、" : ", ") : ""}`;
    })
    .join(lang === "zh" ? "；" : "; ");
}

function secondEdition(slug: string, edition: number): Source[] {
  const claims = mapOf("second-edition").claims.filter((claim: any) => claim.paper === slug);
  const selection = once("selection:second", () => readJson(RELEASES["second-edition"].selection!));
  return selection.intake
    .filter((intake: any) => intake.paper === slug)
    .map((intake: any) => {
      const members = claims.filter((claim: any) => (claim.intake_ids ?? [claim.intake_id]).includes(intake.id));
      return {
        key: intake.id,
        ids: members.map((claim: any) => claim.id),
        edition,
        text: { title: intake.title, statement: null },
        location: { zh: resultsAt(intake, slug, "zh"), en: resultsAt(intake, slug, "en") },
        producers: members.flatMap((claim: any) => claim.producers),
      };
    });
}

const ADAPTERS: Record<ReleaseId, (slug: string, edition: number) => Source[]> = {
  "first-release": firstRelease,
  "second-edition": secondEdition,
  "low-energy": lowEnergy,
};

// --- translations -----------------------------------------------------------------------------

// A row shows its registered text when that text is in the page language, and otherwise a
// translation from src/data/claims-<lang>.json. Each translation carries a fingerprint of the
// registered text it was made from; a changed claim falls back to the registered text and warns.
type Translations = Record<string, { title?: string; statement?: string; from: string }>;
export const fingerprint = (text: Text) => createHash("sha256").update(`${text.title ?? ""}\n${text.statement ?? ""}`).digest("hex").slice(0, 16);
export const translationsOf = (lang: Lang) =>
  once<Translations>(`claims-${lang}`, () => JSON.parse(readFileSync(resolve(process.cwd(), `src/data/claims-${lang}.json`), "utf8")));
const isChinese = (text: Text) => /[\u4e00-\u9fff]/.test(`${text.title ?? ""}${text.statement ?? ""}`);
export const needsTranslation = (source: Source, lang: Lang) => (lang === "zh") !== isChinese(source.text);

function textOf(source: Source, lang: Lang): Text & { translated: boolean } {
  if (!needsTranslation(source, lang)) return { ...source.text, translated: false };
  const entry = translationsOf(lang)[source.key];
  if (entry?.from === fingerprint(source.text)) return { title: entry.title ?? null, statement: entry.statement ?? null, translated: true };
  console.warn(`[claims-${lang}] ${source.key}: translation missing or stale; showing the registered text`);
  return { ...source.text, translated: false };
}

// A claim without a registered title is listed by the first sentence of its statement.
const firstSentence = (text: string) => text.match(/^.+?(。|\.(?=\s|$))/)?.[0] ?? text;

// --- rows -------------------------------------------------------------------------------------

// "H0mework.Realization.Operations.Tree.Fold.Source" → "Tree.Fold.Source": the tail names the
// mathematical object; the full name stays in the link title.
const shortModule = (module: string) => module.split(".").slice(-3).join(".");

// Maps from later releases list declarations without lines; find the definition in the public file.
const DEFINES = "(?:theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)";
function lineOf(path: string, qualified: string) {
  const lines = once(`lines:${path}`, () => read(path).split("\n"));
  const name = qualified.split(".").pop()!.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const pattern = new RegExp(`^\\s*(?:@\\[[^\\]]*\\]\\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\\s+)*${DEFINES}\\s+(?:[\\w'.]*\\.)?${name}(?![\\w'])`);
  const index = lines.findIndex((line) => pattern.test(line));
  return index < 0 ? undefined : index + 1;
}

function modulesOf(producers: Producer[]) {
  const modules = new Map<string, { path: string; declarations: Map<string, Declaration> }>();
  for (const producer of leanOf(producers)) {
    const entry = modules.get(producer.public!.module!) ?? { path: producer.public!.path, declarations: new Map() };
    for (const decl of producer.declarations ?? []) entry.declarations.set(decl.qualified_name, decl);
    modules.set(producer.public!.module!, entry);
  }
  return [...modules].map(([module, { path, declarations }]) => {
    const decls = [...declarations.values()].map((decl) => {
      const line = decl.line ?? lineOf(path, decl.qualified_name);
      return { name: decl.name ?? decl.qualified_name.split(".").pop()!, qualified: decl.qualified_name, line, link: repoLink(path, line) };
    });
    return { module, short: shortModule(module), link: repoLink(path, decls[0]?.line), declarations: decls };
  });
}

// Reading order from the first reference: chapters by number, appendices after the main text.
function orderOf(location: string | null): number[] {
  const head = location?.split(/[；;]/)[0] ?? "";
  const appendix = head.match(/(?:附录|Appendix)\s*([A-Z])(?:\.(\d+))?/) ?? head.match(/^([A-Z])\.(\d+)/);
  if (appendix) return [100 + appendix[1].charCodeAt(0) - 65, Number(appendix[2] ?? 0)];
  const numbers = head.match(/(\d+)(?:\.(\d+))?/);
  return numbers ? [Number(numbers[1]), Number(numbers[2] ?? 0)] : [999, 0];
}
export const chapterOf = (order: number[]) => (order[0] >= 999 ? null : order[0] >= 100 ? String.fromCharCode(65 + order[0] - 100) : String(order[0]));

const idNumber = (id: string) => Number(id.match(/\d+$/)?.[0] ?? 0);

// "core.C35", "core.C36", "core.C37", "core.C42" → "C35–C37 · C42"
export function labelOf(ids: string[]): string {
  const parts = [...ids].sort((a, b) => idNumber(a) - idNumber(b)).map((id) => id.split(".").pop()!).map((tail) => ({ tail, prefix: tail.replace(/\d+$/, ""), n: Number(tail.match(/\d+$/)?.[0]) }));
  const runs: string[] = [];
  for (let i = 0; i < parts.length; ) {
    let j = i;
    while (j + 1 < parts.length && parts[j + 1].prefix === parts[i].prefix && parts[j + 1].n === parts[j].n + 1) j++;
    runs.push(j > i ? `${parts[i].tail}–${parts[j].tail}` : parts[i].tail);
    i = j + 1;
  }
  return runs.join(" · ");
}

export type ClaimRow = ReturnType<typeof rowOf>;
function rowOf(source: Source, lang: Lang) {
  const text = textOf(source, lang);
  const title = text.title ?? firstSentence(text.statement ?? source.key);
  const statement = text.statement && text.statement !== title ? text.statement : null;
  const location = source.location[lang];
  const lean = modulesOf(source.producers);
  const order = orderOf(source.location.zh ?? source.location.en);
  return {
    key: source.key,
    ids: source.ids,
    label: labelOf(source.ids),
    edition: source.edition,
    title,
    statement,
    translated: text.translated,
    location,
    // The row shows only the leading reference ("§3.4", "§8.1–§8.3", "Theorem 6.2"); the body shows the rest.
    section: location?.match(/^(§[^\s；;,，]+|[^\s\d；;,，、]*\s?[\d.A-Z]+[\d.–()]*)/)?.[1] ?? location,
    order,
    chapter: chapterOf(order),
    proved: lean.length > 0,
    declarationCount: lean.reduce((sum, module) => sum + module.declarations.length, 0),
    lean,
    artifacts: source.producers
      .filter((producer) => producer.kind !== "lean" && producer.public)
      .map((producer) => ({ path: producer.public!.path, name: producer.public!.path.split("/").pop()!, link: repoLink(producer.public!.path) })),
  };
}

export function claimsOf(slug: string, lang: Lang) {
  return once(`claims:${slug}:${lang}`, () =>
    entryOf(slug)
      .editions.flatMap((edition, index) => ADAPTERS[edition.release](slug, index + 1))
      .map((source) => rowOf(source, lang))
      .sort((a, b) => a.order[0] - b.order[0] || a.order[1] - b.order[1] || idNumber(a.ids[0] ?? "") - idNumber(b.ids[0] ?? "")),
  );
}

// Sources keyed for the translation layers, used by scripts/translations.ts.
export const sourcesOf = (slug: string) => entryOf(slug).editions.flatMap((edition, index) => ADAPTERS[edition.release](slug, index + 1));
