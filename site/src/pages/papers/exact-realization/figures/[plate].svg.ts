import type { APIRoute } from "astro";
import { exactArchive, unzip } from "../../../../lib/registry";

export const getStaticPaths = () =>
  ["fig2-torsion-picard", "fig3-sparse-hankel", "fig4-hilbert-cayley"].flatMap((file) =>
    ["", "-en"].map((suffix) => ({ params: { plate: file + suffix } })));

export const GET: APIRoute = ({ params }) =>
  new Response(unzip(exactArchive, `papers/exact-realization/figures/web/${params.plate}.svg`), {
    headers: { "Content-Type": "image/svg+xml" },
  });
