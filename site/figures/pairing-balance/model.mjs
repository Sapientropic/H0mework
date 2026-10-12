// Truth model for the pairing-balance figure: Theorem 6.2, Theorem 6.3(1) and Example 6.6 of
// "We Found No Magic in This Mighty Universe" (papers/first-release, physics-common-source).
// Matrices follow the Lean definitions: rawCurrent d g = i·γ^d ⊗ τ_g (CheckControls.lean),
// currentObservable = S · rawCurrent (R(A) = SPAE, DualResponse.lean), read = Re⟨v, M v⟩.

// Complex numbers as [re, im].
const c = (re, im = 0) => [re, im];
const add = (a, b) => [a[0] + b[0], a[1] + b[1]];
const mul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
const conj = (a) => [a[0], -a[1]];
const expi = (t) => [Math.cos(t), Math.sin(t)];
const I = c(0, 1);

// Source constants (Appendix A.4).
export const k = Math.SQRT2;
export const a = (3 * k) / 5;
export const N = Math.sqrt(54 / 125);
export const omega = (3 * N * (k - a)) / 2;
export const darkTime = Math.PI / (2 * omega);

const zero2 = [[c(0), c(0)], [c(0), c(0)]];
const pauli = [
  [[c(0), c(1)], [c(1), c(0)]],
  [[c(0), c(0, -1)], [c(0, 1), c(0)]],
  [[c(1), c(0)], [c(0), c(-1)]],
];
const block = (tl, tr, bl, br) => [0, 1, 2, 3].map((r) => [0, 1, 2, 3].map((col) => {
  const m = r < 2 ? (col < 2 ? tl : tr) : col < 2 ? bl : br;
  return m[r % 2][col % 2];
}));
const id2 = [[c(1), c(0)], [c(0), c(1)]];
const neg = (m) => m.map((row) => row.map((x) => [-x[0], -x[1]]));
// Appendix A.2: γ⁰ = [[0, I], [−I, 0]], γⁱ = [[0, σᵢ], [σᵢ, 0]].
export const gamma = [block(zero2, id2, neg(id2), zero2), ...pauli.map((s) => block(zero2, s, s, zero2))];
// Appendix A.1: τ_g = (i/2) σ_{g+1}.
export const tau = pauli.map((s) => s.map((row) => row.map((x) => mul(c(0, 0.5), x))));

const kron = (A, B) => {
  const out = [];
  for (let i = 0; i < A.length; i++) for (let p = 0; p < B.length; p++) {
    const row = [];
    for (let j = 0; j < A.length; j++) for (let q = 0; q < B.length; q++) row.push(mul(A[i][j], B[p][q]));
    out.push(row);
  }
  return out;
};
const matmul = (A, B) => A.map((row) => B[0].map((_, j) => row.reduce((s, x, m) => add(s, mul(x, B[m][j])), c(0))));
const apply = (M, v) => M.map((row) => row.reduce((s, x, j) => add(s, mul(x, v[j])), c(0)));
const inner = (u, v) => u.reduce((s, x, i) => add(s, mul(conj(x), v[i])), c(0));

// S swaps the upper and lower Dirac components (0↔2, 1↔3), colour unchanged.
const swap4 = [0, 1, 2, 3].map((r) => [0, 1, 2, 3].map((col) => c((r + 2) % 4 === col ? 1 : 0)));
export const S = kron(swap4, id2);

export const rawCurrent = (direction, generator) => kron(gamma[direction], tau[generator]).map((row) => row.map((x) => mul(I, x)));
export const currentObservable = (direction, generator) => matmul(S, rawCurrent(direction, generator));

// Definition 6.1: v = ½(0, e^{iθ}; −e^{iθ}, 0; 0, e^{−iθ}; −e^{−iθ}, 0), indices (spin, colour).
export function state(theta) {
  const up = expi(theta), low = expi(-theta);
  return [c(0), up, [-up[0], -up[1]], c(0), c(0), low, [-low[0], -low[1]], c(0)].map((x) => mul(c(0.5), x));
}
export const read = (theta, M) => inner(state(theta), apply(M, state(theta)));

// Dimensionless time u = t / t*, so θ = ωt = uπ/2 (§7.3).
export const thetaOf = (u) => (u * Math.PI) / 2;

// The two readings of Example 6.6 (direction 1, generator τ₀): with the dual's exchange S
// (the accepted response) and without it (the bare compression).
export function gauges(u) {
  const theta = thetaOf(u);
  return {
    theta,
    accepted: read(theta, currentObservable(1, 0))[0],
    omitted: read(theta, rawCurrent(1, 0))[0],
  };
}

// The classical side of Example 1.1(b): J = 4Nk·⟨τ,τ⟩ with ⟨τ_g, τ_h⟩ = ½δ.
export const classicalCurrent = 4 * N * k * 0.5;

// The balance: the classical pan holds J; the quantum pan holds 4Nk times the chosen reading.
// With S the two are equal at every time; without it they part, by 4Nk = 2J at the dark moment.
export function balance(u, withS) {
  const g = gauges(u);
  const quantum = 4 * N * k * (withS ? g.accepted : g.omitted);
  return { theta: g.theta, classical: classicalCurrent, quantum, gap: classicalCurrent - quantum };
}
