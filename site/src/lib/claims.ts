// Claim rows for a paper, read from every release map that registers it.
// The maps differ in schema; each adapter below turns one schema into the same Source shape.
import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { resolve } from "node:path";
import { RELEASES, entryOf, manuscriptOf, mapOf, once, peaceBinding, publishedPaperJson, read, repoLink, selectionOf, type Lang, type ReleaseId } from "./registry";
import { excerptsOf } from "./excerpts";

type Declaration = { name?: string; qualified_name: string; line?: number };
type Producer = {
  kind: string;
  public?: { path: string; module?: string; commit?: string };
  declarations?: Declaration[];
};
type Text = { title: string | null; statement: string | null };
export type Source = { key: string; ids: string[]; edition: number; text: Text; localizedText?: Partial<Record<Lang, Text>>; location: Record<Lang, string | null>; producers: Producer[]; category?: "principle" | "interface" | "formal"; citations?: string[]; passages?: Partial<Record<Lang, string[]>>; readingOrder?: number };

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
  return lang === "zh" ? raw.replace(/Appendi(?:x|ces)\s*/g, "附录 ").replace(/Figure\s*/g, "图 ").replace(/;\s*/g, "；") : raw;
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
  const selection = selectionOf("second-edition");
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

// Locations are registered in Chinese; the English page names the same results in English and keeps
// only the section of a reference that is a description rather than a result.
const TERMS: [RegExp, string][] = [
  [/主定理/g, "Main theorem "], [/定理/g, "Theorem "], [/命题/g, "Proposition "], [/引理/g, "Lemma "], [/推论/g, "Corollary "],
  [/定义/g, "Definition "], [/反例/g, "Counterexample "], [/反证/g, "Refutation "], [/实例/g, "Example "], [/图/g, "Figure "],
  [/具名复用/g, "Named reuse "], [/补充|補充/g, "Supplement "], [/附录/g, "Appendix "], [/及/g, " and "], [/、/g, ", "], [/；/g, "; "],
];
function englishLocation(zh: string) {
  const parts = zh.split(/\s*\/\s*/).map((part) => {
    let text = part;
    for (const [pattern, word] of TERMS) text = text.replace(pattern, word);
    text = text.replace(/\s+/g, " ").replace(/\s+([,;])/g, "$1").trim();
    return /[\u4e00-\u9fff]/.test(text) ? text.match(/^§[\d.,–§ ]*\d/)?.[0] ?? null : text;
  });
  return parts.filter(Boolean).join(" / ") || null;
}

function wholeLedger(slug: string, edition: number, release: ReleaseId): Source[] {
  const selection = selectionOf(release);
  const inherited = new Map<string, any>(mapOf("whole-ledger").claims
    .filter((claim: any) => claim.paper === slug).map((claim: any) => [claim.id, claim]));
  const additions = release === "whole-ledger-v2" ? mapOf(release) : null;
  if (additions && (additions.acceptance?.status !== "passed"
    || selection.h0_binding.new_paper_acceptance_commit !== RELEASES[release].sourceCommit))
    throw new Error("Whole-ledger second edition does not match its accepted proof selection");
  const added = new Map<string, any>((additions?.claims ?? []).map((claim: any) => [claim.id, claim]));
  return selection.claims.map((location: any) => {
    const prior = inherited.get(location.id);
    const current = added.get(location.id);
    const claim = prior ?? current;
    if (!claim) throw new Error(`Whole-ledger result has no proof map entry: ${location.id}`);
    const zh = location.body?.location ?? null;
    const citations = additions ? location.written.zh.flatMap((anchor: string) => {
      const match = anchor.match(/^manuscript\.md#(?:thm|prop|def|cor|lem|ex)-(\d+(?:-\d+)*)$/);
      return match && match[1] !== "1-1" ? [match[1].replace(/-/g, ".")] : [];
    }) : [];
    return {
      key: `wla.${claim.id}`,
      ids: [`wla.${claim.id}`],
      edition,
      text: { title: claim.title.replace(/^WA\d+\s*/, ""), statement: claim.statement_scope ?? null },
      location: { zh, en: zh && englishLocation(zh) },
      citations,
      producers: [...acceptedEntries(prior?.producers ?? []), ...(current ? proofEntries(current) : [])],
    };
  });
}

// One-bit rows come from the published selection: its titles, its manuscript anchors, and each
// claim's verified H0 bindings, the public modules of the claims it reuses and of its own control.
const ANCHORS: Record<string, Record<Lang, string>> = {
  thm: { zh: "定理", en: "Theorem" }, def: { zh: "定义", en: "Definition" }, prop: { zh: "命题", en: "Proposition" },
  cor: { zh: "推论", en: "Corollary" }, lem: { zh: "引理", en: "Lemma" }, ex: { zh: "例", en: "Example" },
};
function anchorLabel(anchor: string, lang: Lang) {
  const [kind, ...rest] = anchor.split("#").pop()!.split("-");
  if (kind === "sec") return `§${rest.join(".")}`;
  if (kind === "appendix") return `${lang === "zh" ? "附录" : "Appendix"} ${rest[0].toUpperCase()}`;
  return ANCHORS[kind] ? `${ANCHORS[kind][lang]} ${rest.map((part) => part.toUpperCase()).join(".")}` : anchor;
}
function oneBit(_slug: string, edition: number, release: ReleaseId): Source[] {
  const selection = selectionOf(release);
  const additions = release === "one-bit-v2" ? mapOf(release) : null;
  if (additions && (additions.acceptance?.status !== "passed"
      || selection.h0_binding.one_bit_v2.commit !== RELEASES[release].sourceCommit))
    throw new Error("One Bit second edition does not match its accepted proof selection");
  return selection.claims.map((claim: any) => ({
    key: `ob.${claim.id}`,
    ids: [`ob.${claim.id}`],
    edition,
    text: { title: claim.title, statement: null },
    location: {
      zh: claim.written.zh.map((anchor: string) => anchorLabel(anchor, "zh")).join("；"),
      en: claim.written.en.map((anchor: string) => anchorLabel(anchor, "en")).join("; "),
    },
    producers: [
      ...claim.h0.filter((binding: any) => binding.identity === "verified").map((binding: any) => {
        const path = binding.target_path ?? `Lean/${binding.target_module.replace(/\./g, "/")}.lean`;
        const source = claim.sources.find((entry: any) => entry.path === binding.source_path);
        const declarations = binding.declarations ?? source?.declarations ?? [];
        return { kind: "lean", public: { path, module: binding.target_module }, declarations: declarations.map((name: string) => ({ qualified_name: name })) };
      }),
      ...(additions?.claims.find((entry: any) => entry.id === claim.id)?.resources ?? []),
    ],
  }));
}

// These accepted maps already select exact owners, including aliases and provider revisions.
// Do not resolve their entries again by a matching path or a single-file digest.
const acceptedEntries = (entries: any[]): Producer[] => entries.map((entry) => ({
  kind: entry.declarations?.length ? "lean" : "artifact",
  public: entry.public,
  declarations: entry.declarations?.map((decl: any) => ({ qualified_name: decl.public_name ?? decl.qualified_name })),
}));
const proofEntries = (claim: any) => acceptedEntries([...claim.producers, ...claim.direct_consumers, ...claim.resources]);

function sourceProcessCoreV3(_slug: string, edition: number, release: ReleaseId): Source[] {
  const map = mapOf(release);
  const binding = selectionOf(release);
  if (map.acceptance?.status !== "passed" || binding.public_commit !== RELEASES[release].sourceCommit)
    throw new Error("Process core third edition does not match its accepted proof selection");
  const selected: Source[] = map.claims.map((claim: any) => ({
    key: `core.${claim.id}`, ids: [`core.${claim.id}`], edition,
    text: { title: claim.titles.zh, statement: claim.statements.zh },
    localizedText: { en: { title: claim.titles.en, statement: claim.statements.en } },
    location: claim.location,
    producers: proofEntries(claim),
  }));
  for (const row of map.shared_claims) {
    const shared = mapOf(row.release);
    const claim = shared.claims.find((entry: any) => entry.id === row.claim_id);
    if (RELEASES[row.release as ReleaseId].map !== row.map || shared.acceptance?.status !== "passed" || !claim)
      throw new Error(`Process core result has no accepted shared proof: ${row.id}`);
    selected.push({
      key: `core.${row.id}`, ids: [`core.${row.id}`], edition,
      text: { title: claim.title, statement: claim.statement_scope ?? null },
      location: row.location,
      producers: proofEntries(claim),
    });
  }
  return selected;
}
function societyIds(text: string): string[] {
  return [...text.matchAll(/G(\d+)(a)?(?:[–-]G(\d+))?/g)].flatMap((match) =>
    match[3] ? Array.from({ length: +match[3] - +match[1] + 1 }, (_, i) => `G${+match[1] + i}`) : [`G${match[1]}${match[2] ?? ""}`]);
}
function generatedSociety(slug: string, edition: number, release: ReleaseId): Source[] {
  const third = release === "generated-society-v3" ? mapOf(release) : null;
  const correspondence = publishedPaperJson(release, slug,
    third ? "records/theorem-correspondence-v3.json" : "records/theorem-correspondence.json").rows;
  const inherited = third ? mapOf("generated-society") : mapOf(release);
  const rows: Source[] = inherited.claims.map((claim: any) => {
    const all = correspondence.filter((row: any) => societyIds(row.claims).includes(claim.id)
      || (claim.cited_interface_contracts?.length && row.claims === "PT15 independent"));
    const specific = all.filter((row: any) => row.main !== "1.1");
    // Lead with the result devoted to this claim, before a broader assembly that also cites it.
    const references = (specific.length ? specific : all).sort((a: any, b: any) =>
      (new Set(societyIds(a.claims)).size || 999) - (new Set(societyIds(b.claims)).size || 999));
    const locations = (lang: Lang) => [...new Set(references.map((row: any) => {
      if (!row.main) return `${lang === "zh" ? "附录" : "Appendix"} ${row.supplement}`;
      const text = manuscriptOf(release, slug, lang);
      const kind = kindOf(text, row.main, lang);
      // Some correspondence rows point to a section, without a numbered result there.
      if (kind === (lang === "zh" ? "结果" : "Result")
        && new RegExp(`^#{2,4}\\s+${row.main.replace(/\./g, "\\.")}\\s`, "m").test(text)) return `§${row.main}`;
      return `${kind} ${row.main}`;
    }))].join(lang === "zh" ? "；" : "; ") || null;
    return {
      key: `soc.${claim.id}`, ids: [claim.id], edition,
      text: { title: claim.title, statement: claim.statement_scope === claim.title ? null : claim.statement_scope },
      location: { zh: locations("zh"), en: locations("en") },
      category: claim.interface_only ? "interface" : "formal",
      producers: acceptedEntries([...claim.producers, ...claim.direct_consumers, ...claim.resources]),
    };
  });
  if (!third) return rows;
  if (third.acceptance?.status !== "passed"
      || third.proof_snapshots.main !== RELEASES[release].sourceCommit)
    throw new Error("Canonical Society third edition does not match the accepted proof selection");
  for (const claim of third.claims) {
    const crossDomain = claim.id === "cross-domain-actors";
    const commit = crossDomain ? third.proof_snapshots.cross_domain : third.proof_snapshots.main;
    const entries: Producer[] = [...claim.producers, ...claim.direct_consumers].map((entry: any) => ({
      kind: "lean",
      public: { ...entry.public, commit },
      declarations: entry.declarations.map((decl: any) => ({ qualified_name: decl.qualified_name, line: decl.public_line })),
    }));
    if (crossDomain) {
      // The four-domain certificate gives a second source for the subject-generation claim.
      rows.find((row) => row.ids.includes("G0"))!.producers.push(...entries);
    } else {
      rows.push({
        key: `soc.${claim.id}`, ids: [claim.id], edition, category: "formal",
        text: { title: claim.titles.zh, statement: null },
        localizedText: { en: { title: claim.titles.en, statement: null } },
        location: claim.location,
        producers: entries,
      });
    }
  }
  return rows;
}

const PRINCIPLES = { zh: ["一", "二", "三", "四", "五", "六", "七", "八"], en: ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight"] };
function principleAt(slug: string, ordinal: number, lang: Lang, release: ReleaseId) {
  const text = manuscriptOf(release, slug, lang);
  const openings = lang === "zh" ? [`**原则${PRINCIPLES.zh[ordinal - 1]}`]
    : [`**Principle ${PRINCIPLES.en[ordinal - 1]}`, `**Principle ${ordinal}`];
  const matches = text.split(/\n\s*\n/).flatMap((paragraph) => openings
    .filter((opening) => paragraph.startsWith(opening) && /[:：. (]/.test(paragraph.slice(opening.length, opening.length + 1)))
    .map((opening) => ({ paragraph, opening })));
  if (matches.length !== 1) throw new Error(`paper must have exactly one principle ${ordinal}: ${lang}`);
  const { paragraph, opening } = matches[0];
  const readingOrder = text.indexOf(paragraph);
  const before = text.slice(0, readingOrder);
  const section = [...before.matchAll(/^#{2,4}\s+(\d+(?:\.\d+)*)\s/gm)].at(-1)?.[1];
  return { opening, location: section ? `§${section}` : null, readingOrder };
}
function formalResultAt(slug: string, ordinal: string, lang: Lang, release: ReleaseId) {
  const text = manuscriptOf(release, slug, lang);
  const pattern = new RegExp(`^\\*\\*${lang === "zh" ? "结果" : "Result "}\\s*${ordinal}(?!\\d)`, "m");
  const readingOrder = text.search(pattern);
  if (readingOrder < 0) throw new Error(`paper has no formal result ${ordinal}: ${lang}`);
  const section = [...text.slice(0, readingOrder).matchAll(/^#{2,4}\s+(\d+(?:\.\d+)*)\s/gm)].at(-1)?.[1];
  return { location: `${section ? `§${section} ` : ""}${lang === "zh" ? "结果" : "Result"} ${ordinal}`, readingOrder };
}
function economicConstitution(slug: string, edition: number, release: ReleaseId): Source[] {
  const map = mapOf(release);
  const principles: Source[] = map.claims.map((claim: any, index: number) => {
    if (claim.claim_kind !== "normative_argument_with_exact_formal_support" || !claim.formal_support_only)
      throw new Error(`economic principle classification changed: ${claim.id}`);
    const zh = principleAt(slug, index + 1, "zh", release), en = principleAt(slug, index + 1, "en", release);
    return {
      key: `ecn.${claim.id}`, ids: [claim.id], edition, category: "principle", readingOrder: zh.readingOrder,
      text: { title: claim.title, statement: claim.statement_scope },
      location: { zh: zh.location, en: en.location }, passages: { zh: [zh.opening], en: [en.opening] },
      producers: acceptedEntries([...claim.producers, ...claim.direct_consumers, ...claim.resources]),
    };
  });
  const entries = map.claims.flatMap((claim: any) => [...claim.producers, ...claim.direct_consumers]);
  const results: Source[] = map.paper_formal_results.map((result: any) => {
    const bindings = map.paper_interface_registry.bindings.filter((binding: any) => result.source_keys.includes(binding.source_key));
    const selected = entries.flatMap((entry: any) => {
      const names = new Set(bindings.filter((binding: any) => binding.source_commit === entry.source_commit && binding.source_path === entry.source_path)
        .flatMap((binding: any) => binding.declarations.map((decl: any) => decl.qualified_name)));
      const declarations = entry.declarations.filter((decl: any) => names.has(decl.qualified_name));
      return declarations.length ? [{ ...entry, declarations }] : [];
    });
    if (!selected.length) throw new Error(`formal result has no accepted declarations: ${result.id}`);
    const zh = formalResultAt(slug, result.id.slice(1), "zh", release), en = formalResultAt(slug, result.id.slice(1), "en", release);
    return {
      key: `ecn.${result.id}`, ids: [result.id], edition, category: "formal", readingOrder: zh.readingOrder,
      text: { title: result.paper_label, statement: result.statement },
      location: { zh: zh.location, en: en.location },
      producers: acceptedEntries(selected),
    };
  });
  return [...principles, ...results];
}

function capitalFormation(slug: string, edition: number, release: ReleaseId): Source[] {
  const map = mapOf(release);
  const prior = release === "capital-formation-v2" ? mapOf("capital-formation") : map;
  const risk = map.risk_compensation;
  if (risk && risk.proof_commit !== RELEASES[release].sourceCommit)
    throw new Error("Capital formation second edition does not match its accepted risk proof");
  const binding = publishedPaperJson(release, slug, "records/public-source-binding.json");
  const byId = new Map<string, any>(binding.entries.map((entry: any) => [entry.id, entry]));
  return map.claims.map((claim: any) => {
    const selected = claim.source_ids.map((id: string) => {
      const entry = byId.get(id);
      if (!entry) throw new Error(`capital result has no registered source ${id}`);
      return entry;
    });
    const producers: Producer[] = selected.flatMap((entry: any) => {
      if (!entry.public) return [];
      const locations = new Map<string, number>(entry.previous_claim_map_declarations.map((declaration: any) => [declaration.qualified_name, declaration.source_line]));
      return [{
        kind: "lean", public: { ...entry.public, commit: prior.proof_commit },
        declarations: entry.type_observations.map((observation: any) => ({
          qualified_name: observation.qualified_name, line: locations.get(observation.qualified_name),
        })),
      }];
    });
    const consumers = new Set<string>(selected.flatMap((entry: any) => entry.consumers ?? [])
      .flatMap((consumer: any) => consumer.public_module ? [consumer.public_module] : []));
    for (const module of consumers) {
      const consumer = prior.public_consumers[module];
      if (!consumer) throw new Error(`capital consumer has no accepted owner ${module}`);
      producers.push({ kind: "lean", public: { ...consumer.public, commit: prior.proof_commit }, declarations: [] });
    }
    for (const entry of selected.filter((entry: any) => entry.preserved_source))
      producers.push({ kind: "artifact", public: { path: `papers/capital-formation/2026-11-04/${entry.preserved_source.path}`, commit: "main" } });
    if (claim.risk_claim) {
      if (!risk || risk.claim.id !== claim.risk_claim) throw new Error("Capital result has no accepted risk proof");
      for (const entry of [...risk.claim.producers, ...risk.claim.direct_consumers]) {
        producers.push({
          kind: "lean", public: { ...entry.public, commit: risk.proof_commit },
          declarations: entry.declarations.map((declaration: any) => ({
            qualified_name: declaration.qualified_name, line: declaration.public_line,
          })),
        });
      }
    }
    return {
      key: `cap.${claim.id}`, ids: [claim.id], edition, category: "formal",
      text: { title: claim.title.zh, statement: null },
      localizedText: { en: { title: claim.title.en, statement: null } },
      location: claim.written,
      producers,
    };
  });
}

// PE numbers identify source claims. Result numbers follow the bilingual reading editions.
const PE_LOCATIONS: [string, string[]][] = [
  ["§2.2", ["4", "5"]], ["§2.2", ["4"]], ["§2.1", ["2", "3"]],
  ["§3.1", ["6"]], ["§3.2", ["7", "8"]], ["§4.1", ["9", "10", "13"]],
  ["§4.2", ["11"]], ["§7", ["21"]], ["§6.3", ["18", "19"]],
  ["§5.2", ["15"]], ["§5.2", ["15"]], ["§5.2", ["15"]],
  ["§5.1", ["14"]], ["§5.3", []], ["§6.3", ["18"]],
  ["§4.2", ["10", "11"]], ["§4.3", ["12"]], ["§4.3", ["12"]],
  ["§5.1", ["13", "14"]], ["§6.4", ["20"]], ["§6.3", ["19"]],
  ["§3.2", ["8"]], ["§6.1", ["16"]], ["§6.2", ["17"]],
  ["§6.4", ["20"]], ["§10.1", []], ["I.6", []],
  ["§8.2", []], ["I.6", []], ["§8.1", ["22", "23"]],
  ["§9.1", ["24", "25"]], ["§9.4", ["26"]], ["I.6", []],
];

function enforceablePeace(slug: string, edition: number, release: ReleaseId): Source[] {
  const map = mapOf(release);
  const binding = peaceBinding();
  if (map.acceptance.status !== "passed" || binding.public_commit !== RELEASES[release].sourceCommit)
    throw new Error("peace claims have no fixed accepted proof source");
  return map.claims.filter((claim: any) => claim.paper === slug).map((claim: any) => {
    const [section, citations] = PE_LOCATIONS[Number(claim.id.slice(2)) - 1];
    const appendix = section.startsWith("I.");
    const supports = binding.appendix_support.filter((entry: any) => entry.claim === claim.id)
      .map((entry: any) => ({
        kind: "lean", public: { path: entry.path, module: entry.module },
        declarations: entry.declarations,
      }));
    return {
      key: `peace.${claim.id}`, ids: [claim.id], edition, category: "formal",
      text: { title: claim.title, statement: claim.statement },
      location: appendix ? { zh: `附录 ${section}`, en: `Appendix ${section}` } : { zh: section, en: section },
      citations,
      producers: [...claim.producers, ...claim.direct_consumers, ...supports, ...claim.resources],
    };
  });
}

function physicsThirdEdition(slug: string, edition: number, release: ReleaseId): Source[] {
  const map = mapOf(release);
  if (map.acceptance.status !== "passed")
    throw new Error("physics third edition has no accepted proof selection");
  return map.claims.filter((claim: any) => claim.paper === slug).map((claim: any) => ({
    key: claim.id, ids: [claim.id], edition, category: "formal",
    text: { title: claim.title, statement: claim.statement },
    location: { zh: claim.location, en: claim.location },
    citations: claim.paper_results,
    producers: [...claim.producers, ...claim.direct_consumers, ...claim.resources],
  }));
}

const ADAPTERS: Record<ReleaseId, (slug: string, edition: number, release: ReleaseId) => Source[]> = {
  "first-release": firstRelease,
  "second-edition": secondEdition,
  "low-energy": lowEnergy,
  "whole-ledger": wholeLedger,
  "whole-ledger-v2": wholeLedger,
  "source-process-core-v3": sourceProcessCoreV3,
  "one-bit": oneBit,
  "one-bit-v2": oneBit,
  "generated-society": generatedSociety,
  "economic-constitution": economicConstitution,
  "generated-society-v2": generatedSociety,
  "generated-society-v3": generatedSociety,
  "economic-constitution-v2": economicConstitution,
  "capital-formation": capitalFormation,
  "capital-formation-v2": capitalFormation,
  "enforceable-peace": enforceablePeace,
  "physics-third-edition": physicsThirdEdition,
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
export const needsTranslation = (source: Source, lang: Lang) =>
  !source.localizedText?.[lang] && (lang === "zh") !== isChinese(source.text);

function textOf(source: Source, lang: Lang): Text & { translated: boolean } {
  const localized = source.localizedText?.[lang];
  if (localized) return { ...localized, translated: false };
  if (!needsTranslation(source, lang)) return { ...source.text, translated: false };
  const entry = translationsOf(lang)[source.key];
  if (entry?.from === fingerprint(source.text)) return { title: entry.title ?? null, statement: entry.statement ?? null, translated: true };
  console.warn(`[claims-${lang}] ${source.key}: translation missing or stale; showing the registered text`);
  return { ...source.text, translated: false };
}

// A claim without a registered title is listed by the first sentence of its statement.
const firstSentence = (text: string) => text.match(/^.+?(。|\.(?=\s|$))/)?.[0] ?? text;

// --- reading layer ----------------------------------------------------------------------------

// The maps are bound by their acceptance receipts, and their wording is written for the machine
// check. src/data/reading-<lang>.json gives a row reader wording instead: a title, a restatement of a
// registered statement the paper does not state as one result, and where to quote the paper (results
// by number, passages by their opening words). Each entry fingerprints the registered text it was
// written from; a changed claim drops the entry and warns. The registered text stays under the row.
type Reading = { title?: string; statement?: string; cite?: string[]; passages?: string[]; from: string };
export const readingOf = (lang: Lang) =>
  once<Record<string, Reading>>(`reading-${lang}`, () => JSON.parse(readFileSync(resolve(process.cwd(), `src/data/reading-${lang}.json`), "utf8")));
function readingFor(source: Source, lang: Lang) {
  const entry = readingOf(lang)[source.key];
  if (!entry || entry.from === fingerprint(source.text)) return entry ?? null;
  console.warn(`[reading-${lang}] ${source.key}: written from an earlier registered text; showing the registered wording`);
  return null;
}

// Chinese next to Latin letters, digits, Greek or inline code and math takes a space, as the
// manuscripts set it ("完整 typed 库存"); formulas and code are left as they are.
function spaced(text: string) {
  const kept: string[] = [];
  const masked = text.replace(/\$[^$]+\$|`[^`]+`/g, (m) => `\u0001${kept.push(m) - 1}\u0002`);
  const latin = "A-Za-z0-9\u0370-\u03ff\u2070-\u209f%\u0001\u0002";
  return masked
    .replace(new RegExp(`([\u4e00-\u9fff])([${latin}])`, "g"), "$1 $2")
    .replace(new RegExp(`([${latin}])([\u4e00-\u9fff])`, "g"), "$1 $2")
    .replace(/\u0001(\d+)\u0002/g, (_, i) => kept[+i]);
}

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

function modulesOf(producers: Producer[], commit?: string) {
  const modules = new Map<string, { path: string; commit?: string; declarations: Map<string, Declaration> }>();
  for (const producer of leanOf(producers)) {
    const owner = producer.public!;
    const entry = modules.get(owner.module!) ?? { path: owner.path, commit: owner.commit ?? commit, declarations: new Map() };
    for (const decl of producer.declarations ?? []) entry.declarations.set(decl.qualified_name, decl);
    modules.set(producer.public!.module!, entry);
  }
  return [...modules].map(([module, { path, commit, declarations }]) => {
    const decls = [...declarations.values()].map((decl) => {
      const line = decl.line ?? lineOf(path, decl.qualified_name);
      return { name: decl.name ?? decl.qualified_name.split(".").pop()!, qualified: decl.qualified_name, line, link: repoLink(path, line, commit) };
    });
    return { module, short: shortModule(module), link: repoLink(path, decls[0]?.line, commit), declarations: decls };
  });
}

// Reading order from the first reference: chapters by number, appendices after the main text.
function orderOf(location: string | null): number[] {
  const head = location?.split(/[；;]/)[0] ?? "";
  const appendix = head.match(/(?:附录|Appendix)\s*([A-Z])(?:\.(\d+))?/) ?? head.match(/(?:^|\s)([A-Z])\.(\d+)/);
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
function rowOf(source: Source, release: ReleaseId, slug: string, lang: Lang) {
  const text = textOf(source, lang);
  const reading = readingFor(source, lang);
  const derived = text.title ?? firstSentence(text.statement ?? source.key);
  // A title taken from the statement's first sentence is not repeated under it.
  const rest = text.statement && !text.title && !reading?.title ? text.statement.slice(derived.length).trim() : text.statement;
  const statement = rest && rest !== derived ? rest : null;
  const location = source.location[lang];
  // Results are found by number, so the registered location (Chinese where both exist) names them for either page.
  const paper = excerptsOf(release, slug, lang, source.location.zh ?? source.location.en,
    { ...reading, cite: [...(reading?.cite ?? []), ...(source.citations ?? [])],
      passages: [...(reading?.passages ?? []), ...(source.passages?.[lang] ?? [])] });
  const commit = RELEASES[release].sourceCommit;
  const lean = modulesOf(source.producers, commit);
  const order = orderOf(source.location.zh ?? source.location.en);
  const artifacts = source.producers
    .filter((producer) => producer.kind !== "lean" && producer.public)
    .map((producer) => ({ path: producer.public!.path, name: producer.public!.path.split("/").pop()!, link: repoLink(producer.public!.path, undefined, producer.public!.commit ?? commit) }));
  return {
    key: source.key,
    category: source.category,
    ids: source.ids,
    label: labelOf(source.ids),
    edition: source.edition,
    readingOrder: source.readingOrder,
    title: spaced(reading?.title ?? derived),
    // The registered wording (or its translation): the statement, and the title a reading title replaced.
    statement,
    registeredTitle: reading?.title && text.title ? text.title : null,
    // A restatement for readers where the paper gives no single result or passage to quote.
    restated: reading?.statement ?? null,
    translated: text.translated,
    // The paper's own statements of the results the location cites; `cited` is false when they were
    // found by the sections the location names rather than by result numbers.
    excerpts: paper.results,
    excerptsCited: paper.cited,
    location,
    // The row shows only the leading reference ("§3.4", "§8.1–§8.3", "Theorem 6.2"); the body shows the rest.
    section: location?.match(/^(§[\dA-Z.]+(?:[–-]§?[\dA-Z.]+)?|[^\s\d；;,，、]*\s?[\d.A-Z]+[\d.–()]*)/)?.[1] ?? location,
    order,
    chapter: chapterOf(order),
    proved: source.category !== "principle" && lean.length > 0,
    declarationCount: lean.reduce((sum, module) => sum + module.declarations.length, 0),
    lean,
    artifacts: source.category ? [...new Map(artifacts.map((artifact) => [artifact.path, artifact])).values()] : artifacts,
  };
}

function claimEditions(slug: string) {
  const editions = entryOf(slug).editions;
  const replaced = new Set(editions.map((edition) => RELEASES[edition.release].replacesClaimsFrom));
  return editions.map((edition, index) => ({ ...edition, number: index + 1 }))
    .filter((edition) => !replaced.has(edition.release));
}

export function claimsOf(slug: string, lang: Lang) {
  return once(`claims:${slug}:${lang}`, () =>
    claimEditions(slug)
      .flatMap((edition) => ADAPTERS[edition.release](slug, edition.number, edition.release).map((source) => rowOf(source, edition.release, slug, lang)))
      .sort((a, b) => a.order[0] - b.order[0] || a.order[1] - b.order[1]
        || (a.readingOrder ?? Number.MAX_SAFE_INTEGER) - (b.readingOrder ?? Number.MAX_SAFE_INTEGER)
        || idNumber(a.ids[0] ?? "") - idNumber(b.ids[0] ?? "")),
  );
}

// Sources keyed for the translation layers, used by scripts/translations.ts.
export const sourcesOf = (slug: string) => claimEditions(slug).flatMap((edition) => ADAPTERS[edition.release](slug, edition.number, edition.release));

// Every public Lean file the pages read, for the site workflow's sparse checkout (scripts/lean-paths.ts).
export const leanPaths = (slugs: string[]) => [...new Set(slugs.flatMap(sourcesOf).flatMap((source) => leanOf(source.producers).map((producer) => producer.public!.path)))].sort();
