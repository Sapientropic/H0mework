// Checks the tower's model against Proposition 5.2, Theorem 6.2 and the settlement type (44).
import * as M from "./model.mjs";

let failures = 0;
const expect = (ok, message) => {
  if (!ok) {
    failures++;
    console.error("FAIL", message);
  }
};
const a = (page) => page.ledger.find((e) => M.sameDebt(e, M.A));

// The run the tour plays: carry, transfer, carry, act, carry.
const pages = [M.firstPage()];
for (const event of ["carry", "transfer", "carry", "act", "carry"]) pages.push(M.nextPage(pages[pages.length - 1], event));
const [p0, p1, p2, p3, p4, p5] = pages;
expect(a(p1).budget === 1 && a(p1).bearer === "P", "a tick carries the debt with its bearer and budget");
expect(M.sameDebt(a(p1), a(p2)) && a(p2).bearer === "Q" && a(p2).budget === a(p1).budget, "a transfer keeps the debt and its budget: legal, unpaid");
expect(pages.every((p) => M.balance(p.postings) === 0), "double entry balances on every page");
expect(p2.postings.length === 1 && p4.postings.length === 2 && p2.postings[0].debit === p4.postings[1].debit, "double entry posts the transfer and the action alike");
expect(p4.pair.join() === "3,3" && a(p4).budget === 0 && a(p4).budget < a(p3).budget, "the action repairs 2 + 4 to 3 + 3 and pays 1 → 0");
expect(p4.receipt && !p3.receipt, "3 + 3 is terminal: the receipt is on the page of the payment");
expect(!M.settled({ receipt: p4.receipt, successor: p4.ledger, debt: M.A }), "the receipt's own page still carries the debt");
expect(!a(p5) && M.settled({ receipt: p4.receipt, successor: p5.ledger, debt: M.A }), "the next page has no same debt: settled");
expect(p5.ledger.length === 3 && ["b", "c", "d"].every((l) => p5.ledger.some((e) => e.lineage === l)), "the old debts all ride on");
// Transfers alone never settle, however often they repeat.
let q = M.firstPage();
for (let i = 0; i < 5; i++) q = M.nextPage(q, "transfer");
expect(a(q).budget === 1 && !q.receipt && M.balance(q.postings) === 0, "five transfers leave the budget whole and no receipt, balanced all the way");
// A zero budget is not a receipt.
expect(!M.settled({ receipt: false, successor: p5.ledger, debt: M.A }), "an empty successor without a receipt does not settle");

if (failures) process.exit(1);
console.log(`model check passed: ${pages.map((p) => p.event).join(" → ")}; A b ${pages.map((p) => (a(p) ? a(p).budget : "–")).join(",")}; Δ 0 on every page`);
