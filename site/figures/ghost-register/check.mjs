// Checks the figure's model against Lemma 2.2 and Proposition 2.3 on the states the figure can reach.
import { admit, auth, finite, initial, next, occ, raw, same, stateAt } from "./model.mjs";

let failures = 0;
const expect = (ok, message) => {
  if (!ok) {
    failures++;
    console.error("FAIL", message);
  }
};

const RUN = 400;
const states = Array.from({ length: RUN }, (_, i) => stateAt(i + 1));
const w1 = finite(initial());
const w2 = finite(next(initial()));
expect(same(states[0], w1) && same(states[1], w2), "the run starts at the initial visit and steps by next");

// (1) A real difference has an identity.
expect(!same(w1, w2) && !same(occ(w1), occ(w2)), "w₁ ≠ w₂ and occ(w₁) ≠ occ(w₂)");
// (2) The ghost bit has none: the raw pairs differ, their admitted parts agree everywhere.
for (const w of states) {
  const g0 = raw(w, false);
  const g1 = raw(w, true);
  expect(!same(g0, g1), "g₀ ≠ g₁ as raw data");
  expect(same(admit(g0), admit(g1)), "g₀.1 = g₁.1");
  expect(same(occ(admit(g0)), occ(admit(g1))), "occ(g₀.1) = occ(g₁.1)");
  expect(same(auth(admit(g0)), auth(admit(g1))), "auth(g₀.1) = auth(g₁.1)");
}
// (3) The producer takes a visit only.
expect(finite.length === 1, "the legal-state constructor has no Boolean parameter");
// Lemma 2.2 on the whole run: equal occurrences only for equal states.
const keys = states.map((w) => JSON.stringify(occ(w)));
expect(new Set(keys).size === RUN, "occ is injective on the run");
states.forEach((w, i) => expect(same(auth(w), states[i + 1] ?? auth(w)), `auth(w${i + 1}) is the next state`));

if (failures) process.exit(1);
console.log(`model check passed: ${RUN} states, ghost pairs agree on state, occurrence and evolution`);
