import type { APIRoute } from "astro";
import isoCss from "../../../figures/kit/iso.css?raw";
import { PAPERS, thumbSvgOf } from "../../lib/papers";

export const getStaticPaths = () => PAPERS.flatMap((paper) => (paper.figure ? [{ params: { name: paper.figure.name } }] : []));

export const GET: APIRoute = ({ params }) => new Response(thumbSvgOf(params.name!, isoCss), { headers: { "Content-Type": "image/svg+xml" } });
