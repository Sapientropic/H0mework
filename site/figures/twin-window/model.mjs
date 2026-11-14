// Truth model for the twin-window figure: §3 of "Autonomous Observation Dynamics, Minimal All-Future
// Realizations, and Provenance Information Loss" (papers/observation-dynamics), claim O8: the fixed
// full-column observer at copy scale a = n = 2 (Definition 3.1, eqs. 3.3–3.9, Theorems 3.3–3.4).
// A state is (h, m, c): spatial coefficients, an independent mass and an independent clock. Every
// number here is an integer.

export const A_SCALE = 2; // the copy scale a
export const COLUMNS = 2; // n probes per frame
export const FRAMES = A_SCALE + 1; // the shortest window, a + 1 frames
// Probe j reads spatial index i_j = a(j + 1) − 1 (eq. 3.4): positions 1 and 3.
export const PROBES = Array.from({ length: COLUMNS }, (_, j) => A_SCALE * (j + 1) - 1);
export const CELLS = 6; // spatial cells drawn on each conveyor

// Example 1.1 and Example 3.2: the unit source word at position 2, ι(e_2) = (e_2, 1, 3).
export const SIGNAL = { h: [0, 0, 1, 0], m: 1, c: 3 };
// The explicit collision of §3.3: two zero frames, then (5, 8).
export const HIDDEN = { h: [-3, -1, -5, -1], m: 1, c: 0 };
// The twin: the unit signal plus the hidden state. Linear, so it reads exactly what SIGNAL reads for a frames.
export const TWIN = { h: SIGNAL.h.map((x, k) => x + HIDDEN.h[k]), m: SIGNAL.m + HIDDEN.m, c: SIGNAL.c + HIDDEN.c };

// ι(w) = (w, Σ w_k, Σ (k + 1) w_k) (eq. 3.2) for a finitely supported word.
export const embed = (w) => ({ h: [...w], m: w.reduce((s, x) => s + x, 0), c: w.reduce((s, x, k) => s + (k + 1) * x, 0) });

// A^t(h, m, c) = (S^t h, m, c + t m) (eq. 3.3).
export const cellAt = (v, k, t) => (k - t >= 0 && k - t < v.h.length ? v.h[k - t] : 0);
export const clockAt = (v, t) => v.c + t * v.m;
// r_j(t) = 1[t ≤ i_j] h_{i_j − t} + m + a(j + 1)(c + t m) (eq. 3.7).
export const responseOf = (v, t) => PROBES.map((i, j) => cellAt(v, i, t) + v.m + A_SCALE * (j + 1) * clockAt(v, t));
export const windowOf = (v, frames = FRAMES) => Array.from({ length: frames }, (_, t) => responseOf(v, t));

// Theorem 3.3: closed-form decoding from the a + 1 frames (eqs. 3.8–3.9).
export function decode(frames) {
  const a = A_SCALE, r = (j, t) => frames[t][j];
  const m = (r(1, a) - r(0, 0) - r(0, a)) / (a * a - 1);
  const c = (r(0, a) - m) / a - a * m;
  const h = Array.from({ length: COLUMNS * a }, (_, k) => {
    const j = Math.floor(k / a), t = a * (j + 1) - 1 - k;
    return r(j, t) - m - a * (j + 1) * (c + t * m);
  });
  return { h, m, c };
}

// The first frame t at which two states' windows differ, or −1.
export const splitOf = (u, v, frames = FRAMES + 2) => windowOf(u, frames).findIndex((row, t) => row.join() !== windowOf(v, frames)[t].join());
