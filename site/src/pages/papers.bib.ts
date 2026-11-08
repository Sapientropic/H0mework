import type { APIRoute } from "astro";
import { ORDERED, paperOf } from "../lib/papers";

export const GET: APIRoute = () => {
  const entries = ORDERED.map((entry) => {
    const en = paperOf(entry.slug, "en");
    const year = en.current.date.slice(0, 4);
    const key = `gao${year}_${entry.slug.replaceAll("-", "_")}`;
    return [
      `@misc{${key},`,
      `  author       = {Gao, Jian},`,
      `  title        = {{${en.title}}},`,
      `  year         = {${year}},`,
      `  date         = {${en.current.date}},`,
      `  version      = {v${en.current.number}},`,
      `  publisher    = {Zenodo},`,
      `  doi          = {${en.current.doi}},`,
      `  url          = {https://h0mework.wiki/en/papers/${entry.slug}/},`,
      `  note         = {Machine-checked Lean 4 proofs and interactive claim map at https://h0mework.wiki/en/papers/${entry.slug}/}`,
      `}`,
    ].join("\n");
  });
  return new Response(entries.join("\n\n") + "\n", {
    headers: { "Content-Type": "application/x-bibtex; charset=utf-8" },
  });
};
