// Truth model for the ghost-register figure: Definition 2.1, Lemma 2.2 and Proposition 2.3 of
// "1 Bit Is All You Need" (one-bit, OB2–OB3). Every state, number and line the figure shows comes from here.

// A finite visit of the root: the initial visit, then `steps` successor steps along next(c_i) = c_{i+1}.
export const initial = () => ({ steps: 0 });
export const next = (visit) => ({ steps: visit.steps + 1 });

// A legal world state w = finite(v). Its constructor takes a visit and nothing else: there is no
// constructor taking a visit and a Boolean (Proposition 2.3(3)).
export const finite = (visit) => ({ kind: "finite", visit });

// w₁ is the initial visit, w₂ one step on (Proposition 2.3).
export const indexOf = (w) => w.visit.steps + 1;

// The registered occurrence ⟨w, ε_R(w)⟩, Definition 2.1 (1); ε is the event the root generates at w.
export const occ = (w) => ({ w, event: { at: indexOf(w) } });

// The authoritative temporal evolution read from the same visit: the root's compiled successor.
export const auth = (w) => finite(next(w.visit));

// The raw carrier G = Law(R) × Bool and its admission projection, the first component.
export const raw = (w, bit) => ({ w, bit });
export const admit = (g) => g.w;

export const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);

// The k-th legal state along the run from the initial visit.
export const stateAt = (k) => {
  let visit = initial();
  for (let i = 1; i < k; i++) visit = next(visit);
  return finite(visit);
};

// What the register shows for a state: the counter's digits and the journal line it prints.
export const DIGITS = 4;
export const counterOf = (w) => String(indexOf(w) % 10 ** DIGITS).padStart(DIGITS, "0");
const SUB = "₀₁₂₃₄₅₆₇₈₉";
export const sub = (n) => String(n).replace(/\d/g, (d) => SUB[d]);
export const journalOf = (w) => `${counterOf(w)} w${sub(indexOf(w))} ε${sub(occ(w).event.at)}`;
