// Checks the figure's model against Theorem 6.2 (R49), Example 1.1(d) and Example 6.2.
import { ADDRESSES, EXAMPLE, K, LOADINGS, det, hankelOf, momentsOf, polyText, stateOf } from "./model.mjs";

let failures = 0;
const same = (a, b, message) => {
  if (JSON.stringify(a) !== JSON.stringify(b)) {
    failures++;
    console.error("FAIL", message, a, b);
  }
};

// Example 1.1(d): moments (0, 2, 0, 2, 0, 2), determinants 0, −4, 0, order 2, P = t² − 1, weights (−1, 1).
const example = stateOf(EXAMPLE);
same(example.moments, [0, 2, 0, 2, 0, 2], "Example 1.1(d) moments");
same(example.dets, [0, -4, 0], "Example 1.1(d) leading determinants");
same(example.r, 2, "largest nonsingular block locks r = 2");
same(polyText(example.poly), "t² − 1", "P(t) = t² − 1");
same(example.support.map((i) => ADDRESSES[i]), [-1, 1], "roots on A are {−1, 1}");
same(example.recovered, [-1, 1, 0], "Vandermonde recovers the weights");

// Theorem 6.2 on every loading of A with weights in {−1, 0, 1}.
const patterns = new Map();
for (const weights of LOADINGS) {
  const s = stateOf(weights);
  const live = weights.map((a, i) => i).filter((i) => weights[i] !== 0);
  same(s.r, live.length, `r = |S| for ${weights}`);
  same(s.support, live, `roots of P on A are S for ${weights}`);
  same(s.recovered, weights, `weights recovered for ${weights}`);
  // (2): det H_r ≠ 0 and det H_w = 0 for w > r.
  same([1, 2, 3].map((w) => (w === s.r ? s.dets[w - 1] !== 0 : w > s.r ? s.dets[w - 1] === 0 : true)), [true, true, true], `block pattern for ${weights}`);
  // (1): H_w = V_w diag(a) V_wᵀ entrywise.
  for (const w of [1, 2, 3]) {
    const H = hankelOf(s.moments, w);
    const gram = H.map((row, p) => row.map((_, q) => live.reduce((sum, i) => sum + ADDRESSES[i] ** p * weights[i] * ADDRESSES[i] ** q, 0)));
    same(H, gram, `Gram factorisation H_${w} for ${weights}`);
  }
  const key = s.dets.map((d) => (d ? "■" : "□")).join("");
  patterns.set(key, [...(patterns.get(key) ?? []), weights]);
}
same(LOADINGS.length, 3 ** K, "27 loadings");

// Example 6.2 over F_7: A = {1, 2, 4}, weights (3, 4, 0): determinants 0, 5, 0 mod 7.
const mod = (n) => ((n % 7) + 7) % 7;
const f7 = Array.from({ length: 6 }, (_, j) => mod(3 * 1 ** j + 4 * 2 ** j));
same(f7, [0, 4, 5, 0, 4, 5], "Example 6.2 moments mod 7");
same([1, 2, 3].map((w) => mod(det(hankelOf(f7, w)))), [0, 5, 0], "Example 6.2 determinants mod 7");

if (failures) process.exit(1);
console.log(`model check passed: 27 loadings recover exactly; Example 1.1(d) M = ${example.moments.join(",")}, det H = ${example.dets.join(",")}, r = 2`);
if (process.argv.includes("--patterns")) for (const [key, list] of patterns) console.log(key, list.map((w) => `(${w})`).join(" "));
