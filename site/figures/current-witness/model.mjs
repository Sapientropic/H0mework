// Truth model for the current-witness figure: §1 and Theorems 8.1–8.2 of
// "The Current Takes the Stand" (papers/low-energy-first-release, low-energy-phenomenology).
// The opening current testifies three times: as a finite evolution divided by ε, as the
// two-leg derivative of the state, and as a Kubo commutator integral (eqs. 1.8–1.12, 8.14).
// Time is x = ωt; every reading is normalised as in (8.14), ωJ/(sε), so the true
// derivative reads 1 − cos 2x.

export const s = Math.SQRT2;
export const N = Math.sqrt(54 / 125);
export const alpha0 = (3 * Math.SQRT2) / 5;
export const omega = ((3 * N) / 2) * (s - alpha0); // (1.1): 18√15/125

export const derivative = (x) => 1 - Math.cos(2 * x);

// Witness 1, (1.8)/(8.14): the finite current divided by ε, at ε = aω.
export const finite = (a, x) => (1 - Math.cos(2 * x * Math.sqrt(1 + a * a))) / (1 + a * a);

// The two 2×2 blocks of (1.5)–(1.6) in units of ω: h±/ω = ±I + aσx ∓ σz, each started at (1, 0).
// Returns the Bloch vector (⟨σx⟩, ⟨σy⟩, ⟨σz⟩) of the block's state at time x, from (1.7).
export function bloch(a, x, block) {
  const r = Math.sqrt(1 + a * a);
  const c = Math.cos(r * x), sn = Math.sin(r * x) / r;
  // (aσx ∓ σz)(1,0) = (∓1, a), so up to the global phase e^{∓ix}, U(1,0) = (c ± i·sn, −i·a·sn).
  const u0 = [c, block * sn], u1 = [0, -a * sn];
  const cross = [u0[0] * u1[0] + u0[1] * u1[1], u0[0] * u1[1] - u0[1] * u1[0]]; // conj(u0)·u1
  return [2 * cross[0], 2 * cross[1], u0[0] ** 2 + u0[1] ** 2 - (u1[0] ** 2 + u1[1] ** 2)];
}

// The window's current B± = ∓sσx and force T± = σx, each block carrying half the unit state.
// Read with B the blocks add; read with T they cancel (§1.2).
export const readB = (a, x) => (s / 2) * (-bloch(a, x, 1)[0] + bloch(a, x, -1)[0]);
export const readT = (a, x) => 0.5 * (bloch(a, x, 1)[0] + bloch(a, x, -1)[0]);

// Witness 2, (1.10)–(1.11): δu(t) = −i sin2x/(2ω) r + (cos2x − 1)/(2ω) q. Each leg of the
// current, δu†Bw and w†Bδu, reads (s/2ω)(1 − cos 2x); normalised, each leg is half the derivative.
export const deltaU = (x) => ({ r: [0, -Math.sin(2 * x) / (2 * omega)], q: [(Math.cos(2 * x) - 1) / (2 * omega), 0] });
export const leg = (x) => derivative(x) / 2;

// Witness 3, (1.12): the Kubo kernel Re i⟨w,[T_H(τ),B_H(t)]w⟩ = 2s·sin 2ω(t−τ), integrated over
// τ ∈ [0, t]; with σ = t − τ the running integral is ∫₀ˣ 2 sin 2σ dσ in the normalised units.
export const kernel = (sigma) => 2 * Math.sin(2 * sigma);
export const kubo = (x) => derivative(x);

// What the three pens write, for each way of testifying.
export const MODES = ["honest", "oneLeg", "readT"];
export function testimony(mode, a, x) {
  return {
    finite: mode === "readT" ? 0 : finite(a, x),
    legs: mode === "oneLeg" ? leg(x) : 2 * leg(x),
    kubo: kubo(x),
  };
}

// The control amplitudes the figure steps through, as ε/ω (the paper's Figure 3 uses 1, 1/2, 1/4).
export const AMPLITUDES = [1 / 2, 1 / 4, 1 / 8];
