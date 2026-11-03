// Truth model for the public water terrace: the four claims of "The Economic Constitution of Possibility"
// (Principles 2–4 and 6) on the results that support them: Result 4 (CF4, the whole-source receipt bound),
// Result 5 (S5, every leg actually performed) and Result 7 (PF1–PF3, duties continue, the term expires).

// --- basic participation: the spring serves whoever arrives; it reads no contribution and no token. ---
export const draw = (spring) => ({ draws: spring.draws + 1 });

// --- contribution: an account of slots, each keeping its original issue (origin), its holder, its
// remaining principal and what it has received. One origin occupies at most one slot (Appendix B.3).
export const Q = 6;
export function issue(account, origin, holder, quantity) {
  // A second admission of the same origin is the reissue the actual source fold excludes.
  if (account.slots.some((slot) => slot.origin === origin)) return { account, refused: true };
  return { account: { slots: [...account.slots, { origin, holder, issued: quantity, remaining: quantity, received: { [holder]: 0 } }] }, refused: false };
}
// A payment consumes the slot's own principal: remaining after + paid = remaining before (eq. 2).
export function pay(account, origin, amount) {
  let paid = 0;
  const slots = account.slots.map((slot) => {
    if (slot.origin !== origin) return slot;
    paid = Math.min(amount, slot.remaining);
    return { ...slot, remaining: slot.remaining - paid, received: { ...slot.received, [slot.holder]: (slot.received[slot.holder] ?? 0) + paid } };
  });
  return { account: { slots }, paid };
}
// A transfer changes who receives; it pays nothing and issues nothing.
export const transfer = (account, origin, holder) => ({
  slots: account.slots.map((slot) => (slot.origin === origin ? { ...slot, holder, received: { [holder]: 0, ...slot.received } } : slot)),
});
// Everything the same origin has paid out, summed over every slot and every holder (eq. 3's left side).
export const receivedFor = (account, origin) =>
  account.slots.filter((slot) => slot.origin === origin).reduce((sum, slot) => sum + Object.values(slot.received).reduce((a, b) => a + b, 0), 0);
export const remainingFor = (account, origin) => account.slots.filter((slot) => slot.origin === origin).reduce((sum, slot) => sum + slot.remaining, 0);

// --- a scarce request: the mill. Its trade has two legs, the user's payment and the mill's grinding;
// each leg settles its own slot, and one side performing never settles the other (Proposition A.5).
export const LEGS = ["pay", "grind"];
export const open = (performed) => LEGS.filter((leg) => !performed.includes(leg));
export const cleared = (performed) => open(performed).length === 0;

// --- governance: a seat held by a keeper for a term. Jurisdiction J(i, x) = holder(x) = i ∧ clock ≤ deadline
// (Appendix C.2). The clock never runs back, so once past the deadline no later state restores it; the
// duties and their history stay with the gate. A new seat is a new occurrence with its own deadline.
export const TERM = 5;
export const seatOf = (holder, granted) => ({ holder, granted, deadline: granted + TERM });
export const jurisdiction = (seat, holder, clock) => seat.holder === holder && clock <= seat.deadline;
export const renew = (log, holder, clock) => ({ seat: seatOf(holder, clock), log: [...log, { kind: "seat", holder, at: clock }] });
// A contribution tally is no key: the gate's lock reads only a seat in force.
export const opens = (credential, seat, clock) => credential.kind === "seat" && jurisdiction(seat, credential.holder, clock);
