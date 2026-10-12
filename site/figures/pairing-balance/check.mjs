// Checks the figure's model against Theorems 6.2–6.3, Example 6.6 and Example 1.1.
import { N, balance, currentObservable, gauges, k, omega, rawCurrent, read } from "./model.mjs";

let failures = 0;
const near = (a, b, message, tol = 1e-12) => {
  if (!(Math.abs(a - b) <= tol)) {
    failures++;
    console.error("FAIL", message, a, b);
  }
};

near(omega ** 2, 972 / 3125, "ω² = 972/3125");
near(4 * N * k * 0.5, (12 * Math.sqrt(15)) / 25, "J = 4Nk·½ = 12√15/25");
for (let step = 0; step <= 64; step++) {
  const u = step / 16;
  const { theta, accepted, omitted } = gauges(u);
  near(read(theta, [...Array(8)].map((_, i) => [...Array(8)].map((__, j) => [i === j ? 1 : 0, 0])))[0], 1, `⟨v,v⟩ = 1 at u=${u}`);
  near(accepted, 0.5, `accepted current ½ at u=${u}`);
  near(omitted, Math.cos(2 * theta) / 2, `omitted current cos2θ/2 at u=${u}`);
  near(balance(u, true).gap, 0, `with S the balance is level at u=${u}`);
  near(balance(u, false).gap, 4 * N * k * (0.5 - Math.cos(2 * theta) / 2), `without S the gap is 4Nk·sin²θ at u=${u}`);
  for (let d = 0; d < 3; d++) for (let h = 0; h < 3; h++) {
    const value = read(theta, currentObservable(d + 1, h));
    near(value[0], d === h ? 0.5 : 0, `⟨v,O_${d + 1}(τ_${h})v⟩ = ½δ at u=${u}`);
  }
}
near(gauges(0).omitted, gauges(0).accepted, "initial agreement");
near(gauges(1).accepted - gauges(1).omitted, 1, "dark moment separates by 1");
near(read(Math.PI / 4, rawCurrent(1, 0))[0], 0, "θ = π/4: omitted reads 0");
near(balance(1, false).gap, 2 * balance(1, false).classical, "dark moment: the pans differ by 2J");

if (failures) process.exit(1);
console.log(`model check passed: ω² = 972/3125, J = ${(4 * N * k * 0.5).toFixed(4)}, ½δ on 3×3 at 65 times, dark gap 1`);
