// Truth model for the quan-heng figure: Proposition 4 (eqs. 5–8) and the three-party ledger of §1 of
// "War and Peace: A Source-Generated Terminal Theorem" (papers/enforceable-peace, claims PE1–PE2).
// Everything is exact: the rate λ is counted in twelfths, stock and Δ in halves.

export const STEPS = 12; // λ = step / 12
export const ADVANTAGE = 4; // m: the initiator's net advantage over peace
export const SHIFTED = 6; // T: liability shifted onto another ledger
export const DESTROYED = 2;
export const PEACE = [4, 7, 10];
export const WAR = [8, 7, 4];
// λ* = max(0, m / T) for the single candidate (eq. 7), in twelfths.
export const STAR = (ADVANTAGE * STEPS) / SHIFTED;
// Two payers on the one original address: full reattachment needs 6; one can spend 5, the other 3.
export const FULL = SHIFTED;
export const PAYERS = [5, 3];
// λcap = min(1, avail / full) (eq. 8), in twelfths.
export const capOf = (avail) => Math.min(STEPS, (avail * STEPS) / FULL);

// Δ(λ) = m − λT (eq. 5), for the continuous motion.
export const deltaOf = (lambda) => ADVANTAGE - lambda * SHIFTED;

// The state at λ = step / 12 under a payer who can spend `avail`.
export function stateOf(step, avail) {
  const cap = capOf(avail);
  return {
    step,
    cap,
    delta2: 2 * ADVANTAGE - step, // Δ in halves: 2(m − λT) = 8 − step
    stock2: [2 * WAR[0] - step, 2 * WAR[1], 2 * WAR[2] + step], // stock in halves: (8 − 6λ, 7, 4 + 6λ)
    interval: cap >= STAR ? [STAR, cap] : null, // Λpeace = [λ*, λcap], empty when λcap < λ*
    shortfall: (STAR * FULL) / STEPS - avail, // λ*·full − avail: positive exactly when judgment-proof
  };
}

const gcd = (a, b) => (b ? gcd(b, a % b) : Math.abs(a));
export const fraction = (n, d = STEPS) => {
  const g = gcd(n, d) || 1;
  return d / g === 1 ? String(n / g) : n / g + "/" + d / g;
};
export const halves = (h) => (h < 0 ? "−" : "") + (Math.abs(h) % 2 ? (Math.abs(h) > 1 ? (Math.abs(h) - 1) / 2 : "") + "½" : String(Math.abs(h) / 2));
