// Checks the water terrace's model against Results 4, 5 and 7 and the separation of the four claims.
import { LEGS, Q, TERM, cleared, draw, issue, jurisdiction, open, opens, pay, receivedFor, remainingFor, renew, seatOf, transfer } from "./model.mjs";

let failures = 0;
const expect = (ok, message) => { if (!ok) { failures++; console.error("FAIL", message); } };

// Result 4: over every random run of payments, transfers and waits, remaining + received = Q, and the
// whole receipt of the one origin never exceeds Q.
let seed = 7;
const random = () => ((seed = (seed * 1103515245 + 12345) % 2147483648) / 2147483648);
for (let run = 0; run < 300; run++) {
  let { account } = issue({ slots: [] }, "well", "甲", Q);
  const holders = ["甲", "丙", "丁"];
  for (let step = 0; step < 30; step++) {
    const before = remainingFor(account, "well");
    const roll = random();
    if (roll < 0.5) {
      const result = pay(account, "well", 1 + Math.floor(random() * 2));
      expect(remainingFor(result.account, "well") + result.paid === before, "eq. 2: remaining + paid = before");
      account = result.account;
    } else if (roll < 0.8) {
      account = transfer(account, "well", holders[Math.floor(random() * 3)]);
      expect(remainingFor(account, "well") === before, "a transfer pays nothing");
    } else {
      const again = issue(account, "well", "丙", Q);
      expect(again.refused && again.account === account, "the same origin is not issued twice");
    }
    expect(remainingFor(account, "well") + receivedFor(account, "well") === Q, "telescoping: remaining + received = Q");
    expect(receivedFor(account, "well") <= Q, "eq. 3: the whole receipt is at most Q");
  }
}

// Result 5: the mill's two legs; one performed leaves the other open.
expect(cleared(LEGS) && !cleared(["pay"]) && open(["pay"]).join() === "grind" && open(["grind"]).join() === "pay", "complete clearing and one-sided openness");

// Result 7: the term expires on every later clock, the original occupant included; the log keeps its history.
const seat = seatOf("乙", 0);
for (let clock = 0; clock <= 3 * TERM; clock++) expect(jurisdiction(seat, "乙", clock) === (clock <= TERM), `jurisdiction at ${clock}`);
const next = renew([{ kind: "duty", at: 0 }], "戊", TERM + 1);
expect(next.log.length === 2 && next.log[0].kind === "duty" && jurisdiction(next.seat, "戊", TERM + 2) && !jurisdiction(next.seat, "乙", TERM + 2), "a new seat is its own occurrence; duties stay in the log");

// The claims do not upgrade: a contribution tally never opens the gate, whoever holds it.
for (let clock = 0; clock <= TERM; clock++) expect(!opens({ kind: "tally", holder: "乙" }, seat, clock) && opens({ kind: "seat", holder: "乙" }, seat, clock), "a tally is not a key");
expect(draw({ draws: 3 }).draws === 4, "the spring serves without a token");

if (failures) process.exit(1);
console.log(`model check passed: 300 runs of 30 steps keep remaining + received = Q = ${Q}; clearing; term ${TERM} expires for the original occupant; a tally opens no gate`);
