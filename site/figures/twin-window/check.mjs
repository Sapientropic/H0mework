// Checks the twin-window model against Example 3.2, Theorems 3.3–3.4 and the collision of §3.3 (O8).
import { A_SCALE, COLUMNS, FRAMES, HIDDEN, PROBES, TWIN, SIGNAL, clockAt, decode, embed, responseOf, splitOf, windowOf } from "./model.mjs";

let failures = 0;
const same = (a, b, message) => {
  if (JSON.stringify(a) !== JSON.stringify(b)) {
    failures++;
    console.error("FAIL", message, a, b);
  }
};

same(PROBES, [1, 3], "probes read spatial indices 1 and 3");
same(embed([0, 0, 1, 0]), SIGNAL, "ι(e_2) = (e_2, 1, 3)");
// Example 3.2 and §1: (7, 13) → (9, 18) → (11, 21).
same(windowOf(SIGNAL), [[7, 13], [9, 18], [11, 21]], "unit signal frames");
// §3.3: the hidden state reads (0, 0), (0, 0), then (5, 8).
same(windowOf(HIDDEN), [[0, 0], [0, 0], [5, 8]], "hidden state frames");
// The twin reads what the unit reads for a frames and splits at frame a + 1.
same(TWIN, { h: [-3, -1, -4, -1], m: 2, c: 3 }, "twin state");
same(windowOf(TWIN), [[7, 13], [9, 18], [16, 29]], "twin frames");
same(splitOf(SIGNAL, TWIN), A_SCALE, "split at the third frame (index a)");
same([clockAt(SIGNAL, 2), clockAt(TWIN, 2)], [5, 7], "clocks advance by the mass: 3,4,5 and 3,5,7");
// Theorem 3.3: the a + 1 frames decode mass, clock and the first na spatial coordinates.
same(decode(windowOf(SIGNAL)), { h: [0, 0, 1, 0], m: 1, c: 3 }, "decode the unit signal");
same(decode(windowOf(TWIN)), { h: [-3, -1, -4, -1], m: 2, c: 3 }, "decode the twin");
same(decode(windowOf(HIDDEN)), { h: [-3, -1, -5, -1], m: 1, c: 0 }, "decode the hidden state");
const distant = { h: [...SIGNAL.h, 4, -7], m: SIGNAL.m, c: SIGNAL.c };
same(windowOf(distant, 12), windowOf(SIGNAL, 12), "spatial coordinates beyond the probes give the same future");
same(decode(windowOf(distant)), SIGNAL, "decoder recovers exactly the observable state");
// Decoding is exact on every state with |h_k|, m, c ≤ 2 (spatial support inside the first na cells).
const range = [-2, -1, 0, 1, 2];
let decoded = 0;
for (const h0 of range) for (const h1 of range) for (const h2 of range) for (const h3 of range) for (const m of range) for (const c of range) {
  const v = { h: [h0, h1, h2, h3], m, c };
  same(decode(windowOf(v)), v, `decode ${JSON.stringify(v)}`);
  decoded++;
}
// Theorem 3.4: an injective map from the observable space ℂ^{na+2} into ℓ + 1 frames of ℂ^n needs
// na + 2 ≤ (ℓ + 1)n, so ℓ + 1 ≥ a + 1.
const need = COLUMNS * A_SCALE + 2;
same([1, 2, 3].map((frames) => need <= frames * COLUMNS), [false, false, true], "dimension count: 6 > 2, 6 > 4, 6 ≤ 6");
same(FRAMES, 3, "a + 1 = 3 frames");
// Eq. (3.6): the physical Gram matrix and the coefficients of the single-frame observation.
const g = (j) => [A_SCALE * (j + 1) - 1, 1, A_SCALE * (j + 1)];
const gram = [0, 1].map((j) => [0, 1].map((l) => (j === l ? 1 : 0) + 1 + g(j)[2] * g(l)[2]));
same(gram, [[6, 9], [9, 18]], "Γ = [[6, 9], [9, 18]]");
const det = gram[0][0] * gram[1][1] - gram[0][1] * gram[1][0], r = responseOf(SIGNAL, 0);
same([(gram[1][1] * r[0] - gram[0][1] * r[1]) * 9 / det, (gram[0][0] * r[1] - gram[1][0] * r[0]) * 9 / det], [3, 5], "x = Γ⁻¹ r = (1/3, 5/9)");

if (failures) process.exit(1);
console.log(`model check passed: unit (7,13)(9,18)(11,21), twin (7,13)(9,18)(16,29), split at frame 3; ${decoded} states decode exactly`);
