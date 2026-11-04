// Truth model for the replay bakery: Theorems 2, 3 and 8 of "The Structural Theorem of Capitalism" on one
// small production law. The oven is the production port p and 丙 its controller c; 甲 and 乙 are the
// affected, whose life maintenance is one loaf each. The order tape w is the given action sequence.

export const CONTROLLER = "丙";
export const MEMBERS = ["甲", "乙"];
export const PEOPLE = ["甲", "乙", "丙"];
// Who signs each request on the tape, and whose basket its loaf is for.
export const W = [
  { by: "丙", to: "丙" }, { by: "甲", to: "甲" }, { by: "丙", to: "甲" },
  { by: "丙", to: "乙" }, { by: "乙", to: "乙" }, { by: "丙", to: "丙" },
];
export const S0 = { dough: 6, bread: { 甲: 0, 乙: 0, 丙: 0 } };

// A law fixes two admissions at the oven: the controller's, a(s, p, c), and the affected's, a(s, p, i).
// The public interpretation opens the port to everyone and drops the controller's consent.
export const lawOf = (controller, affected) => ({ controller, affected, public: false });
export const PUBLIC = { controller: 1, affected: 1, public: true };
export const access = (L, who) => (who === CONTROLLER ? L.controller : L.affected);
// Private_L(p, i): the controller is admitted and i is not (eq. 2); NoAsymmetry(L) excludes it for every i (eq. 3).
export const privateGap = (L, who) => access(L, CONTROLLER) === 1 && access(L, who) === 0;
export const noAsymmetry = (L) => PEOPLE.every((who) => !privateGap(L, who));

// One request. A bake is valid when its signer is admitted at the oven and there is dough; a refused bake
// changes nothing. A presentation, the replay's entry for a refused position, has no effect either.
export function stepOf(L, s, request) {
  if (request.op === "present") return { state: s, item: { by: request.by, to: request.to, op: "present", done: false } };
  const done = access(L, request.by) === 1 && s.dough >= 1;
  const state = done ? { dough: s.dough - 1, bread: { ...s.bread, [request.to]: s.bread[request.to] + 1 } } : s;
  return { state, item: { by: request.by, to: request.to, op: "bake", done } };
}
// The execution of w from s: every state from s to next(s, w), and one entry per position.
export function run(L, s, w) {
  const states = [s], items = [];
  for (const request of w) {
    const next = stepOf(L, states[states.length - 1], request);
    states.push(next.state);
    items.push(next.item);
  }
  return { state: states[states.length - 1], states, items };
}
// ρ_{L,s}(w), generated entry by entry from the given execution: an accepted bake keeps its signer, its use and
// its effect, with no consent condition; a refused one becomes a presentation by the same signer for the same use.
export const replayOf = (L, s, w) => run(L, s, w).items.map(({ by, to, done }) => ({ by, to, op: done ? "bake" : "present" }));
// ι_L: the correspondence of the given execution's entries with the replay's.
export const iota = (item) => (item.done ? item : { by: item.by, to: item.to, op: "present", done: false });
export const needsPaid = (state) => MEMBERS.every((member) => state.bread[member] >= 1);

// The capital core C = (A, R, D) of an execution, or null. A: a member's loaf delivered through the oven while
// the controller is admitted there and the member is not. R: a loaf routed back to the controller. D: at a
// reached state the controller can make a valid request at the port and keeps the private advantage.
export function capitalCore(L, s, w) {
  const { states, items } = run(L, s, w);
  const A = items.find((item) => item.done && MEMBERS.includes(item.to) && privateGap(L, item.to));
  const R = items.find((item) => item.done && item.to === CONTROLLER);
  const D = access(L, CONTROLLER) === 1 && states.some((state) => state.dough >= 1) && MEMBERS.some((member) => privateGap(L, member));
  return A && R && D ? { A, R } : null;
}
