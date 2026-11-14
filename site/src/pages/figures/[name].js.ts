import type { APIRoute } from "astro";
import { PAPERS } from "../../lib/registry";
import { figureScriptOf } from "../../lib/figures";

// A figure's page script as its own cacheable file, instead of 80–170 KB inline in every paper page.
export const getStaticPaths = () => PAPERS.flatMap((paper) => (paper.figure ? [{ params: { name: paper.figure.name } }] : []));

export const GET: APIRoute = ({ params }) => new Response(figureScriptOf(params.name!).code, { headers: { "Content-Type": "text/javascript; charset=utf-8" } });
