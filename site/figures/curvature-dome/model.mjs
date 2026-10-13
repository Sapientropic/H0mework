// Truth model for the curvature-dome figure: Theorem 1.2 and §§7–11 of "Two Minuses, One Plus,
// and a Bare Trace Under Oath" (papers/low-energy-first-release, low-energy-loop-response).
// The complete five-term response, read along a unit direction n of the external momentum d = sn,
// is R(0) + a(n)|s| + s²·nᵀKn + o(s²) (1.3). K is the response curvature tensor. Every value
// here is in units of 10⁻²⁰ of the original action, the unit of the paper's table.

// (1.2): the two-ball window's radius.
export const B = (Math.SQRT2 * 5234375) / 294988800512;

// (10.7): the leading raw tensor of the two propagation legs, exactly diagonal.
export const KG0 = [-1.3031969814, 2.1922740186, -1.690596719];
// (10.7)'s integers: the three central values are √30(Aℓ_R + b_i g)/D_* up to one common factor.
export const B_INT = [
  -2320339522879271170011217524973217861256927053064666079052657705109338n,
  3921375100572892251186223581547532771093087034683851044524183837417062n,
  -3012102837963769108469432161130193495577865811561102038217309537582938n,
];
// §10.3: all-direction bound on ‖K_G − K_G0‖ for raw (a spectral bound, so it covers every n).
export const G_REM = 0.02070266;
// (7.20): the raw Hessian of the two quantum source legs, every unit n; half of it enters K.
export const S_N = [-0.0625928534, -0.0534484924];
export const HALF_S = [S_N[0] / 2, S_N[1] / 2];
// (9.12): the reader contact's quadratic coefficient, ‖K_C‖.
export const K_C = 3.686515414428545e-6;
// §11.1: quantum legs plus contact, every unit n (outward-rounded).
export const QC = [-0.0313001133, -0.0267205597];

// §1.2 table and (1.5): diagonal intervals and mixed-entry bounds; (11.3)–(11.4): Gershgorin rows.
export const TABLE = {
  raw: [[-1.3552, -1.309214], [2.140271, 2.186257], [-1.7426, -1.696614]],
  mean: [[-0.06012, -0.055272], [-0.001635, 0.003212], [-0.043357, -0.038509]],
  conn: [[-1.297332, -1.251692], [2.139655, 2.185295], [-1.701494, -1.655854]],
};
export const MIXED = { raw: 0.02299243, mean: 0.002423430, conn: 0.02281948 };
export const GERSHGORIN = {
  raw: [[-1.401185, -1.263229], [2.094286, 2.232242], [-1.788585, -1.650629]],
  conn: [[-1.342971, -1.206052], [2.094015, 2.230935], [-1.747134, -1.610214]],
};

// What is on the stand: all five terms, or the two quantum source legs alone.
export const MODES = ["five", "quantum"];

// The three groups of terms along n: the propagation legs' central value nᵀK_G0n, the quantum
// legs (no directional data beyond their interval, so their midpoint), the contact (≤ 4·10⁻²⁶).
export const quadratic = (n) => n[0] * n[0] * KG0[0] + n[1] * n[1] * KG0[1] + n[2] * n[2] * KG0[2];
export function terms(mode, n) {
  const q = (HALF_S[0] + HALF_S[1]) / 2;
  return mode === "five" ? { G: quadratic(n), Q: q, C: 0 } : { G: 0, Q: q, C: 0 };
}

// The strict enclosure of nᵀKn for a unit n (11.1): K = K_G + ½S_N + K_C.
export function enclosure(mode, n) {
  if (mode === "quantum") return [...HALF_S];
  const q = quadratic(n);
  return [q - G_REM + QC[0], q + G_REM + QC[1]];
}
// +1 when the whole enclosure is positive, −1 when it is negative, 0 when it straddles zero.
export function verdict(mode, n) {
  const [lo, hi] = enclosure(mode, n);
  return lo > 0 ? 1 : hi < 0 ? -1 : 0;
}

// The dome's stamps: rings every 10° of elevation above the e1–e3 plane, about 36 per great
// circle, and the zenith. n = (cos el cos az, sin el, cos el sin az), so e2 is the zenith. The
// horizon ring has stamps on ±e1 and ±e3; the rings above sit half a step round.
export const directionOf = (el, az) => [Math.cos(el) * Math.cos(az), Math.sin(el), Math.cos(el) * Math.sin(az)];
export function stamps() {
  const out = [];
  for (let j = 0; j < 9; j++) {
    const el = (j * 10 * Math.PI) / 180;
    const count = Math.round(36 * Math.cos(el));
    for (let i = 0; i < count; i++) {
      const az = ((i + (j ? 0.5 : 0)) / count) * 2 * Math.PI;
      out.push({ ring: j, el, az, n: directionOf(el, az) });
    }
  }
  out.push({ ring: 9, el: Math.PI / 2, az: 0, n: [0, 1, 0] });
  return out;
}

// (8.1): the two-ball intersection, as a fraction of one ball, at centre separation u = |s|/B.
// The |s| term is the window's cusp: the volume falls linearly from the first step.
export const lens = (u) => 1 - 0.75 * u + (u * u * u) / 16;
