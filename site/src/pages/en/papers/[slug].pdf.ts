import type { APIRoute } from "astro";
import { PAPERS, paperPdfOf } from "../../../lib/papers";

export const getStaticPaths = () => PAPERS.map((paper) => ({ params: { slug: paper.slug } }));

export const GET: APIRoute = ({ params }) =>
  new Response(paperPdfOf(params.slug!, "en"), { headers: { "Content-Type": "application/pdf" } });
