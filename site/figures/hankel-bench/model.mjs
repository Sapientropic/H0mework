// Truth model for the hankel-bench figure: Theorem 6.2 (R49) of "Faithful Representations and Exact
// Inversion from Quotients, Moments, and Streams" (papers/exact-realization) over K = ℚ, with the
// candidate set A = {−1, 1, 2} of Example 1.1(d) and k = |A| = 3. Every number is exact: integers for
// the moments and determinants, reduced fractions for the recurrence and the recovered weights.

export const ADDRESSES = [-1, 1, 2]; // τ on the candidate set, in rail order
export const K = ADDRESSES.length; // the sparsity bound k; 2k moments are read
export const WEIGHTS = [-1, 0, 1]; // what a station can hold: an ink weight, nothing, a marble weight
// Example 1.1(d): a = 1 at τ = 1 and −1 at τ = −1, nothing at τ = 2.
export const EXAMPLE = [-1, 1, 0];

// --- exact fractions -------------------------------------------------------------------------
const gcd = (a, b) => (b ? gcd(b, a % b) : Math.abs(a));
export const frac = (n, d = 1) => {
  if (d < 0) [n, d] = [-n, -d];
  const g = gcd(n, d) || 1;
  return [n / g, d / g];
};
const add = ([a, b], [c, d]) => frac(a * d + c * b, b * d);
const sub = ([a, b], [c, d]) => frac(a * d - c * b, b * d);
const mul = ([a, b], [c, d]) => frac(a * c, b * d);
const div = ([a, b], [c, d]) => frac(a * d, b * c);
const isZero = ([a]) => a === 0;
export const value = ([n, d]) => n / d;

// M_j = Σ a_i τ_i^j for j = 0 … 2k − 1 (eq. 6.3).
export const momentsOf = (weights) =>
  Array.from({ length: 2 * K }, (_, j) => weights.reduce((sum, a, i) => sum + a * ADDRESSES[i] ** j, 0));

// (H_w)_{p,q} = M_{p+q} for 0 ≤ p, q < w.
export const hankelOf = (moments, w) => Array.from({ length: w }, (_, p) => Array.from({ length: w }, (_, q) => moments[p + q]));

// Exact determinant by fraction elimination; det H_0 = 1.
export function det(matrix) {
  const a = matrix.map((row) => row.map((x) => frac(x)));
  let result = frac(1);
  for (let c = 0; c < a.length; c++) {
    const pivot = a.findIndex((row, r) => r >= c && !isZero(row[c]));
    if (pivot < 0) return 0;
    if (pivot !== c) { [a[c], a[pivot]] = [a[pivot], a[c]]; result = mul(result, frac(-1)); }
    result = mul(result, a[c][c]);
    for (let r = c + 1; r < a.length; r++) {
      const f = div(a[r][c], a[c][c]);
      a[r] = a[r].map((x, j) => sub(x, mul(f, a[c][j])));
    }
  }
  return value(result);
}

// Solve A x = b exactly (A nonsingular).
function solve(A, b) {
  const n = A.length, m = A.map((row, i) => [...row.map((x) => frac(x)), frac(b[i])]);
  for (let c = 0; c < n; c++) {
    const pivot = m.findIndex((row, r) => r >= c && !isZero(row[c]));
    [m[c], m[pivot]] = [m[pivot], m[c]];
    for (let r = 0; r < n; r++) if (r !== c) {
      const f = div(m[r][c], m[c][c]);
      m[r] = m[r].map((x, j) => sub(x, mul(f, m[c][j])));
    }
  }
  return m.map((row, i) => div(row[n], row[i]));
}

// The polynomial P(t) = t^r + Σ c_j t^j (eq. 6.6), as fractions lowest degree first.
export const evalPoly = (coefficients, t) => coefficients.reduce((sum, c, j) => sum + value(c) * t ** j, 0);
const exactAt = (coefficients, t) => coefficients.reduce((sum, c, j) => add(sum, mul(c, frac(t ** j))), frac(0));

export function stateOf(weights) {
  const moments = momentsOf(weights);
  const dets = ADDRESSES.map((_, i) => det(hankelOf(moments, i + 1)));
  // eq. (6.5): the order is the largest nonsingular leading block, w ≤ k.
  const r = [1, ...dets].reduce((best, d, w) => (d !== 0 ? w : best), 0);
  const c = r ? solve(hankelOf(moments, r), moments.slice(r, 2 * r).map((m) => -m)) : [];
  const poly = [...c, frac(1)];
  const support = ADDRESSES.map((t, i) => i).filter((i) => isZero(exactAt(poly, ADDRESSES[i])));
  // V_r a|_S = (M_0, …, M_{r−1}): the Vandermonde system on the recovered support.
  const found = solve(Array.from({ length: r }, (_, p) => support.map((i) => ADDRESSES[i] ** p)), moments.slice(0, r));
  const recovered = ADDRESSES.map((_, i) => { const at = support.indexOf(i); return at < 0 ? 0 : value(found[at]); });
  return { weights, moments, dets, r, poly, support, recovered };
}

// Every loading of the three stations, for the check and the tour.
export const LOADINGS = WEIGHTS.flatMap((a) => WEIGHTS.flatMap((b) => WEIGHTS.map((c) => [a, b, c])));

// Text: signed integers with a true minus, and P(t) as the bench prints it.
export const signed = (n) => (n < 0 ? "−" + -n : String(n));
const SUP = { 2: "²", 3: "³" };
export function polyText(poly) {
  const terms = [];
  for (let j = poly.length - 1; j >= 0; j--) {
    const [n, d] = poly[j];
    if (!n) continue;
    const size = Math.abs(n) === d && j ? "" : (d === 1 ? String(Math.abs(n)) : Math.abs(n) + "/" + d);
    const body = size + (j ? "t" + (SUP[j] ?? "") : "");
    terms.push((terms.length ? (n < 0 ? " − " : " + ") : n < 0 ? "−" : "") + body);
  }
  return terms.join("") || "0";
}
