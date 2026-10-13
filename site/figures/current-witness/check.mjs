// Checks the figure's model against §1 of the paper: the 12-dimensional objects (1.2)–(1.4),
// the window evolution (1.6)–(1.8), and the three testimonies (1.9)–(1.12), by matrix computation.
import { AMPLITUDES, bloch, deltaU, derivative, finite, kernel, kubo, leg, omega, readB, readT, s, testimony } from "./model.mjs";

let failures = 0, checks = 0;
const near = (a, b, message, tol = 1e-9) => {
  checks++;
  if (!(Math.abs(a - b) <= tol)) {
    failures++;
    if (failures < 20) console.error("FAIL", message, a, b);
  }
};

// Complex numbers [re, im] and dense matrices.
const C = (re, im = 0) => [re, im];
const add = (a, b) => [a[0] + b[0], a[1] + b[1]];
const mul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
const conj = (a) => [a[0], -a[1]];
const scale = (k, a) => [k * a[0], k * a[1]];
const zeros = (n, m = n) => [...Array(n)].map(() => [...Array(m)].map(() => C(0)));
const eye = (n) => zeros(n).map((row, i) => row.map((_, j) => C(i === j ? 1 : 0)));
const real = (rows) => rows.map((row) => row.map((x) => C(x)));
const matmul = (A, B) => A.map((row) => B[0].map((_, j) => row.reduce((acc, x, k) => add(acc, mul(x, B[k][j])), C(0))));
const apply = (A, v) => A.map((row) => row.reduce((acc, x, j) => add(acc, mul(x, v[j])), C(0)));
const madd = (A, B, k = 1) => A.map((row, i) => row.map((x, j) => add(x, scale(k, B[i][j]))));
const mscale = (k, A) => A.map((row) => row.map((x) => mul(k, x)));
const dagger = (A) => A[0].map((_, j) => A.map((row) => conj(row[j])));
const inner = (u, v) => u.reduce((acc, x, i) => add(acc, mul(conj(x), v[i])), C(0));
const kron = (A, B) => {
  const out = [];
  for (let i = 0; i < A.length; i++) for (let p = 0; p < B.length; p++) {
    const row = [];
    for (let j = 0; j < A[0].length; j++) for (let q = 0; q < B[0].length; q++) row.push(mul(A[i][j], B[p][q]));
    out.push(row);
  }
  return out;
};
// exp(A) by scaling and squaring with a 24-term Taylor series.
function expm(A) {
  const norm = Math.max(...A.map((row) => row.reduce((acc, x) => acc + Math.hypot(...x), 0)));
  const k = Math.max(0, Math.ceil(Math.log2(norm + 1)) + 2);
  const B = mscale(C(2 ** -k), A);
  let term = eye(A.length), sum = eye(A.length);
  for (let n = 1; n <= 24; n++) {
    term = mscale(C(1 / n), matmul(term, B));
    sum = madd(sum, term);
  }
  for (let i = 0; i < k; i++) sum = matmul(sum, sum);
  return sum;
}
const re = (z) => z[0];

// (1.1)
near(omega ** 2, 972 / 3125, "ω² = 972/3125", 1e-15);
near(omega, (18 * Math.sqrt(15)) / 125, "ω = 18√15/125", 1e-15);

// (1.2)–(1.3) on H₁₂ = C⁴ ⊗ C³, spin first, colour second.
const w = [0, 1, 0, -1, 0, 0, 0, 1, 0, -1, 0, 0].map((x) => C(x / 2));
const Q = kron(real([[-1, 0, 0, 0], [0, -1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]), eye(3));
const rho01 = real([[0, 1, 0], [-1, 0, 0], [0, 0, 0]]);
const T = mscale(C(0, -1), kron(eye(4), rho01));
const B = mscale(C(-s), matmul(Q, T));
const isHermitian = (A) => A.every((row, i) => row.every((x, j) => Math.hypot(x[0] - A[j][i][0], x[1] + A[j][i][1]) < 1e-15));
near(+isHermitian(T), 1, "T Hermitian");
near(+isHermitian(B), 1, "B Hermitian");
const r = apply(T, w), q = apply(Q, r), p = apply(Q, w);
const F = [w, r, q, p];
F.forEach((u, i) => F.forEach((v, j) => {
  const z = inner(u, v);
  near(z[0], i === j ? 1 : 0, `F orthonormal (${i},${j})`, 1e-15);
  near(z[1], 0, `F orthonormal im (${i},${j})`, 1e-15);
}));
// (1.4): F†TF and the window matrices.
const window = (A) => F.map((u) => F.map((v) => inner(u, apply(A, v))));
const T4 = real([[0, 1, 0, 0], [1, 0, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]]);
window(T).forEach((row, i) => row.forEach((z, j) => { near(z[0], T4[i][j][0], `F†TF (${i},${j})`, 1e-15); near(z[1], 0, `F†TF im`, 1e-15); }));
const Q4 = window(Q);
const B4 = window(B);
// T and B keep the window: their images of each column lie in span F.
for (const A of [T, B, Q]) for (const u of F) {
  const image = apply(A, u);
  const back = F.reduce((acc, v) => acc.map((x, i) => add(x, mul(inner(v, image), v[i]))), image.map(() => C(0)));
  near(Math.max(...image.map((x, i) => Math.hypot(x[0] - back[i][0], x[1] - back[i][1]))), 0, "window invariant", 1e-14);
}
const H0 = real([[0, 0, 0, 0], [0, 0, 2 * omega, 0], [0, 2 * omega, 0, 0], [0, 0, 0, 0]]);
const W0 = [C(1), C(0), C(0), C(0)];

// The finite evolution in the window, U_ε(t) = exp(−it(h₀ + εT)).
const U = (eps, t) => expm(mscale(C(0, -t), madd(H0, T4, eps)));
const current = (A, eps, t) => { const u = apply(U(eps, t), W0); return re(inner(u, apply(A, u))); };

const XS = [...Array(33)].map((_, i) => (i * 2 * Math.PI) / 32);
for (const a of [1, ...AMPLITUDES, 3, 0.03]) for (const x of XS) {
  const eps = a * omega, t = x / omega;
  const J = current(B4, eps, t);
  // (1.8) and its normalisation (8.14).
  near(J, ((s * eps * omega) / (omega ** 2 + eps ** 2)) * (1 - Math.cos(2 * t * Math.sqrt(omega ** 2 + eps ** 2))), `(1.8) a=${a} x=${x}`);
  near((omega * J) / (s * eps), finite(a, x), `(8.14) a=${a} x=${x}`);
  near(readB(a, x), J, `blocks read with B a=${a} x=${x}`);
  // Read with the force T the two blocks cancel at every amplitude.
  near(current(T4, eps, t), 0, `T reads zero a=${a} x=${x}`);
  near(readT(a, x), 0, `block T reading a=${a} x=${x}`);
  // The blocks of (1.5) on (w ± p)/√2, (r ± q)/√2, rescaled to a unit state, against (1.7).
  const u = apply(U(eps, t), W0);
  for (const block of [1, -1]) {
    const b0 = add(u[0], scale(block, u[3])), b1 = add(u[1], scale(block, u[2]));
    const z = mul(conj(b0), b1);
    const S = bloch(a, x, block);
    near(2 * z[0], S[0], `Bloch σx block ${block} a=${a} x=${x}`);
    near(2 * z[1], S[1], `Bloch σy block ${block} a=${a} x=${x}`);
    near(b0[0] ** 2 + b0[1] ** 2 - b1[0] ** 2 - b1[1] ** 2, S[2], `Bloch σz block ${block} a=${a} x=${x}`);
  }
}

// (1.9)–(1.11): the derivative at ε = 0, the state derivative δu and its two legs.
const h = 1e-5;
for (const x of XS) {
  const t = x / omega;
  const slope = (current(B4, h, t) - current(B4, -h, t)) / (2 * h);
  near(slope, (s / omega) * derivative(x), `(1.9) x=${x}`, 1e-7);
  const du = apply(madd(U(h, t), U(-h, t), -1), W0).map((z) => scale(1 / (2 * h), z));
  const expect = deltaU(x);
  near(du[0][0], 0, `δu has no w part x=${x}`, 1e-7);
  near(Math.hypot(...du[3]), 0, `δu has no p part x=${x}`, 1e-7);
  near(du[1][0], expect.r[0], `δu r re x=${x}`, 1e-7);
  near(du[1][1], expect.r[1], `δu r im x=${x}`, 1e-7);
  near(du[2][0], expect.q[0], `δu q re x=${x}`, 1e-7);
  near(du[2][1], expect.q[1], `δu q im x=${x}`, 1e-7);
  const bra = inner(du, apply(B4, W0)), ket = inner(W0, apply(B4, du));
  near(re(bra) + re(ket), (s / omega) * derivative(x), `(1.11) both legs x=${x}`, 1e-7);
  near((omega / s) * re(bra), leg(x), `one leg is half x=${x}`, 1e-7);
  near((omega / s) * re(ket), leg(x), `other leg is half x=${x}`, 1e-7);
  near(re(inner(du, apply(T4, W0))) + re(inner(W0, apply(T4, du))), 0, `legs read with T vanish x=${x}`, 1e-7);
  // (1.12): the Kubo commutator integral, Simpson's rule over τ ∈ [0, t].
  const U0 = (tau) => expm(mscale(C(0, -tau), H0));
  const BH = matmul(dagger(U0(t)), matmul(B4, U0(t)));
  const integrand = (tau) => {
    const TH = matmul(dagger(U0(tau)), matmul(T4, U0(tau)));
    const comm = madd(matmul(TH, BH), matmul(BH, TH), -1);
    return re(mul(C(0, 1), inner(W0, apply(comm, W0))));
  };
  const n = 256;
  let sum = 0;
  for (let i = 0; i <= n; i++) {
    const tau = (t * i) / n;
    const value = integrand(tau);
    near(value, 2 * s * Math.sin(2 * omega * (t - tau)), `Kubo kernel x=${x} τ=${tau}`, 1e-9);
    near((omega / s) * value / omega, kernel(x - omega * tau), `normalised kernel x=${x}`, 1e-9);
    sum += value * (i === 0 || i === n ? 1 : i % 2 ? 4 : 2);
  }
  near((sum * t) / (3 * n), (s / omega) * derivative(x), `(1.12) x=${x}`, 1e-6);
  near(kubo(x), derivative(x), `kubo pen x=${x}`, 0);
  const honest = testimony("honest", 1 / 8, x), half = testimony("oneLeg", 1 / 8, x), lie = testimony("readT", 1 / 8, x);
  near(honest.legs, derivative(x), "honest legs");
  near(half.legs, derivative(x) / 2, "one leg halves");
  near(lie.finite, 0, "reading T is flat");
}
// Finite → derivative: (8.14) tends to 1 − cos 2x, with the bound of (8.8) shrinking like ε.
const gap = (a) => Math.max(...XS.map((x) => Math.abs(finite(a, x) - derivative(x))));
near(+(gap(1 / 8) < gap(1 / 4) && gap(1 / 4) < gap(1 / 2) && gap(1 / 2) < gap(1)), 1, "finite traces converge");

if (failures) {
  console.error(`${failures} of ${checks} checks failed`);
  process.exit(1);
}
console.log(`model check passed: ${checks} checks; ω = ${omega.toFixed(6)}, finite gaps ${[1, 1 / 2, 1 / 4, 1 / 8].map((a) => gap(a).toFixed(3)).join(" ")}`);
