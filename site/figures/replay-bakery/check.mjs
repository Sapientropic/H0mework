// Checks the replay bakery's model against Theorems 2, 3 and 8 on the figure's tape and on random runs.
import { CONTROLLER, PEOPLE, PUBLIC, S0, W, capitalCore, iota, lawOf, needsPaid, noAsymmetry, replayOf, run } from "./model.mjs";

let failures = 0;
const expect = (ok, message) => { if (!ok) { failures++; console.error("FAIL", message); } };
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const CELLS = [[1, 0], [1, 1], [0, 0], [0, 1]];

// Theorem 3 on the figure's family: the same stock, needs and tape; C exists exactly when the controller is
// admitted and the affected are not.
for (const [c, i] of CELLS) {
  const L = lawOf(c, i);
  expect(Boolean(capitalCore(L, S0, W)) === (c === 1 && i === 0), `Theorem 3 at (${c}, ${i})`);
  // Theorem 2: NoCapital ⇔ NoAsymmetry, here with the family's tape as the witness for the converse.
  expect(noAsymmetry(L) === !capitalCore(L, S0, W), `Theorem 2 at (${c}, ${i})`);
}

// Theorem 8 on random laws, stocks and tapes: same length, same complete post-state, the entries mapped one
// by one, needs paid on one side exactly when on the other, and no capital core in the public execution.
let seed = 11;
const random = () => ((seed = (seed * 1103515245 + 12345) % 2147483648) / 2147483648);
const pick = (list) => list[Math.floor(random() * list.length)];
for (let n = 0; n < 2000; n++) {
  const L = lawOf(pick([0, 1]), pick([0, 1]));
  const s = { dough: Math.floor(random() * 8), bread: { 甲: Math.floor(random() * 2), 乙: 0, 丙: Math.floor(random() * 3) } };
  const w = Array.from({ length: Math.floor(random() * 11) }, () => ({ by: pick(PEOPLE), to: pick(PEOPLE) }));
  const given = run(L, s, w);
  const rho = replayOf(L, s, w);
  const replay = run(PUBLIC, s, rho);
  expect(rho.length === w.length, "|ρ(w)| = |w|");
  expect(same(replay.state, given.state), "next_pub(s, ρ(w)) = next_L(s, w)");
  expect(same(replay.items, given.items.map(iota)), "items_pub = map(ι, items_L)");
  expect(needsPaid(replay.state) === needsPaid(given.state), "AllNeedsPaid ⇔");
  expect(!capitalCore(PUBLIC, s, rho), "the public execution has no capital core");
  expect(rho.every((entry) => entry.op === "present" || PUBLIC.controller === 1), "every replayed request is admitted");
  if (noAsymmetry(L)) expect(!capitalCore(L, s, w), "no asymmetry, no capital core");
}

// Why refused positions must become presentations: opening the port and rerunning w itself bakes the loaves
// that the given execution refused, so its post-state is not the given one.
const given = run(lawOf(1, 0), S0, W);
expect(!same(run(PUBLIC, S0, W).state, given.state), "the raw tape under the open port differs");
expect(same(given.state, { dough: 2, bread: { 甲: 1, 乙: 1, 丙: 2 } }) && needsPaid(given.state), "the figure's private run");
expect(!needsPaid(run(lawOf(0, 0), S0, W).state) && noAsymmetry(lawOf(0, 0)), "closing every key removes the gap and delivers nothing");
expect(W.filter((entry) => entry.by !== CONTROLLER).length === 2, "two of the tape's requests are the affected's own");

if (failures) process.exit(1);
console.log(`model check passed: C exactly at (1, 0) on the figure's tape; 2000 random runs replay with the same length, post-state, entries and needs`);
