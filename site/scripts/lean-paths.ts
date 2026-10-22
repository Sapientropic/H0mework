// Prints the public Lean files the site reads, one per line with a leading "/", for
// `git sparse-checkout add --stdin` in the site workflow. Needs only papers/, docs/ and
// tools/export-map.json: the claim adapters resolve paths without opening any Lean file.
import { leanPaths } from "../src/lib/claims";
import { PAPERS } from "../src/lib/registry";

console.log(leanPaths(PAPERS.map((paper) => paper.slug)).map((path) => `/${path}`).join("\n"));
