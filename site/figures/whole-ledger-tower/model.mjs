// Truth model for the whole-ledger tower: Definitions 5.1, 6.1, 10.2 and 11.1, Proposition 5.2,
// Theorem 6.2 and §15.1 of "Book-Balancing Magic Has Nowhere to Hide" (whole-ledger-accounting, WA7, WA8, WA10).
// Each page of the tower is the whole ledger at one tick; every debt, ring, seal and posting comes from here.

// A debt's identity is its lineage and claim (Definition 5.1); its bearer and budget may change.
export const sameDebt = (e, f) => e.lineage === f.lineage && e.claim === f.claim;

export const initialLedger = () => [
  { lineage: "a", claim: "target-six", bearer: "P", budget: 1 },
  { lineage: "b", claim: "old-1", bearer: "P", budget: 2 },
  { lineage: "c", claim: "old-2", bearer: "Q", budget: 3 },
  { lineage: "d", claim: "old-3", bearer: "Q", budget: 2 },
];

// One actual tick carries every live item with its identity, bearer and budget (original carriage),
// except debts the source's terminal continuation no longer activates.
export const tick = (ledger, inactive = []) => ledger.filter((e) => !inactive.some((d) => sameDebt(d, e))).map((e) => ({ ...e }));

// A transfer moves the bearer and keeps the debt: same lineage and claim, b(f) ≤ b(e) (Proposition 5.2).
// Equality is legal and unpaid.
export const transfer = (ledger, debt) => ledger.map((e) => (sameDebt(e, debt) ? { ...e, bearer: e.bearer === "P" ? "Q" : "P" } : e));

// The target-six action (§6.1): 4 is not prime, its least factor is 2, the left side becomes 2 + (2 − 1),
// and the total 6 fixes the right side.
export const isPrime = (n) => n > 1 && Array.from({ length: n - 2 }, (_, i) => i + 2).every((d) => n % d);
export const leastFactor = (n) => Array.from({ length: n - 1 }, (_, i) => i + 2).find((d) => n % d === 0);
export function act([left, right]) {
  if (isPrime(left) && isPrime(right)) return null;
  const d = leastFactor(right);
  const next = d + (d - 1);
  return [next, left + right - next];
}
// The target classifier is terminal exactly when both sides are prime.
export const terminal = ([left, right]) => isPrime(left) && isPrime(right);

// A payment strictly lowers the same debt's budget (Definition 10.2).
export const pay = (ledger, debt) => ledger.map((e) => (sameDebt(e, debt) ? { ...e, budget: e.budget - 1 } : e));

// Settlement (44): the local terminal receipt, and no same-debt item in the actual successor.
export const successorHas = (successor, debt) => successor.some((f) => sameDebt(debt, f));
export const settled = ({ receipt, successor, debt }) => Boolean(receipt) && !successorHas(successor, debt);

// The double-entry view (§15.1): every posting debits and credits the same amount, so each page balances.
export const posting = (kind) => ({ kind, debit: 1, credit: 1 });
export const balance = (postings) => postings.reduce((sum, p) => sum + p.debit - p.credit, 0);

// The run of pages. A page records the ledger after an event, its postings, and whether it carries
// the terminal receipt of the target-six debt.
export const A = initialLedger()[0];
export function firstPage() {
  return { event: "start", ledger: initialLedger(), postings: [], pair: [2, 4], receipt: false };
}
export function nextPage(page, event) {
  const pending = page.receipt && successorHas(page.ledger, A);
  // The terminal continuation follows the receipt: the next page no longer activates the debt.
  let ledger = tick(page.ledger, pending ? [A] : []);
  let postings = page.postings;
  let pair = page.pair;
  let receipt = false;
  if (event === "transfer" && successorHas(ledger, A)) {
    ledger = transfer(ledger, A);
    postings = [...postings, posting("transfer")];
  } else if (event === "act" && successorHas(ledger, A) && !terminal(pair)) {
    pair = act(pair);
    ledger = pay(ledger, A);
    postings = [...postings, posting("action")];
    receipt = terminal(pair);
  } else event = "carry";
  return { event, ledger, postings, pair, receipt };
}
