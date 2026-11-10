// Checks the figure's model against Proposition 4 and the three-party ledger of §1 (PE1–PE2).
import { ADVANTAGE, DESTROYED, FULL, PAYERS, PEACE, SHIFTED, STAR, STEPS, WAR, capOf, deltaOf, fraction, halves, stateOf } from "./model.mjs";

let failures = 0;
const same = (a, b, message) => {
  if (JSON.stringify(a) !== JSON.stringify(b)) {
    failures++;
    console.error("FAIL", message, a, b);
  }
};
const sum = (list) => list.reduce((a, b) => a + b, 0);

same(sum(PEACE), 21, "peace total 21");
same(sum(WAR), sum(PEACE) - DESTROYED, "war total 19");
same(WAR[0] - PEACE[0], ADVANTAGE, "m = +4");
same(ADVANTAGE, -DESTROYED + SHIFTED, "+4 = −2 + 6");
same([deltaOf(0), deltaOf(2 / 3) < 1e-12 && deltaOf(2 / 3) > -1e-12, deltaOf(1)], [4, true, -2], "Δ(0) = 4, Δ(2/3) = 0, Δ(1) = −2");
same(fraction(STAR), "2/3", "λ* = m / T = 2/3");
same(0 < ADVANTAGE && ADVANTAGE < SHIFTED, true, "0 < m < T: full reattachment flips (eq. 6)");
same(stateOf(STEPS, FULL).stock2.map((h) => h / 2), [2, 7, 10], "full reattachment leaves (2, 7, 10)");
for (const avail of PAYERS) for (let step = 0; step <= STEPS; step++) {
  const s = stateOf(step, avail);
  same(sum(s.stock2), 2 * sum(WAR), `total stays 19 at λ=${fraction(step)}`);
  same(s.delta2, s.stock2[0] - 2 * PEACE[0], `Δ is the initiator's stock above peace at λ=${fraction(step)}`);
  same(s.delta2 / 2, deltaOf(step / STEPS), `Δ = m − λT at λ=${fraction(step)}`);
  // λ ∈ Λpeace exactly when the rate is payable and leaves no positive incentive.
  same(s.interval !== null && step >= s.interval[0] && step <= s.interval[1], step <= s.cap && s.delta2 <= 0, `Λpeace membership at λ=${fraction(step)}, avail ${avail}`);
  same(s.interval === null, s.shortfall > 0, `empty exactly on a strict shortfall, avail ${avail}`);
}
same([capOf(5), capOf(3)].map((c) => fraction(c)), ["5/6", "1/2"], "λcap = 5/6 and 1/2");
same(stateOf(0, 3).shortfall, 1, "judgment-proof: λ*·full = 4 > avail = 3");
same([halves(11), halves(-4), halves(1), halves(0)], ["5½", "−2", "½", "0"], "halves format");

if (failures) process.exit(1);
console.log("model check passed: Δ = 4 − 6λ, λ* = 2/3, Λ = [2/3, 5/6] or ∅, totals 21 / 19 / 19");
