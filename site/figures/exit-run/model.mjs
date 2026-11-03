// Truth model for the exit sand table: Theorem 5.1, Propositions 5.2–5.3 and Theorem 1.3 of "The
// Canonical Society Theorem" (G3, G4, G23, G13). Every reading the figure shows is computed here.

// The original carrier's future codes. Idle cannot act; the old employment has no continuation in the
// target ("work" is not among its candidates); "leave" is the one survivor (Appendix E.7.2).
export const CODES = ["idle", "work", "leave"];
// The two installed domains and the service queue: three pending items, two capacity units, and the
// maintenance runs slots 0 (tenure) and 1 (health). The single-service source runs slot 0 only.
export const DOMAINS = ["tenure", "health"];
export const QUEUE = 3;
export const CAPACITY = 2;

// A source: the payment's association with the action, the action's path to its service, capture of
// the continuation by a controller, and whether the health service actually occurred.
export const SOURCES = {
  whole: { link: true, path: true, captured: false, health: true }, // x_d: the complete source
  link: { link: false, path: true, captured: false, health: true }, // z_p: payment association missing
  path: { link: true, path: false, captured: false, health: true }, // z_r: path association missing
  capture: { link: true, path: true, captured: true, health: true }, // z_c: full capture
  single: { link: true, path: true, captured: false, health: false }, // y_d: the single-service source
};
// Each failing source keeps its failure kind; the complete and single-service sources have none.
export const kindOf = (name) => (name === "link" || name === "path" || name === "capture" ? name : null);

export const servedOf = (source) => (source.health ? [0, 1] : [0]);

// The feasible edges E(c, j) = R(c) ∧ ¬I(c) ∧ ¬H(c) ∧ P(c) ∧ T(c, j), on one action and one served slot.
export function edgesOf(source) {
  const R = (c) => c === "leave";
  const I = (c) => c === "idle";
  const H = (c) => source.captured && c === "leave";
  const Pay = (c) => source.link && c === "leave";
  const T = (c, j) => source.path && c === "leave" && servedOf(source).includes(j);
  return CODES.flatMap((c) => servedOf(source).filter((j) => R(c) && !I(c) && !H(c) && Pay(c) && T(c, j)).map((j) => [c, j]));
}

// Exit capacity K: the maximum matching of the finite bipartite graph of feasible edges.
export function capacityOf(source) {
  const edges = edgesOf(source);
  const owner = new Map();
  const tryAction = (c, seen) => {
    for (const [a, j] of edges) {
      if (a !== c || seen.has(j)) continue;
      seen.add(j);
      if (!owner.has(j) || tryAction(owner.get(j), seen)) { owner.set(j, c); return true; }
    }
    return false;
  };
  return CODES.filter((c) => tryAction(c, new Set())).length;
}

// The domains the bearer actually reaches (a feasible edge to that domain's served slot), and the complete
// capability bundle: every installed domain reached.
export const reachedOf = (source) => DOMAINS.filter((_, j) => edgesOf(source).some(([, slot]) => slot === j));
export const bundleOf = (source) => reachedOf(source).length === DOMAINS.length;

// The repair language: each operation sets one relation back and keeps the payment, the bearer, the exit
// interest and the served services. A repair is effective when it restores a positive capacity.
export const REPAIRS = { relink: "link", restorePath: "path", uncapture: "capture" };
export function repaired(source, op) {
  if (op === "relink") return { ...source, link: true };
  if (op === "restorePath") return { ...source, path: true };
  if (op === "uncapture") return { ...source, captured: false };
  throw new Error(`no repair ${op}`);
}
export const effective = (source, op) => capacityOf(repaired(source, op)) > 0;

// The paid frontier H_i = [γ_0, …, γ_i]: every completed exit appends one new occurrence with its own
// identity (its index), so the frontier's image grows strictly while the capacity reading stays 1.
export const appended = (frontier) => [...frontier, { occurrence: frontier.length }];
