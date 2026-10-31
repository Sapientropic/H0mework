import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)

def reviewDelta {claim : IssuedClaim input} (review : Review input claim)
    (amount : ℚ) (instrument : Instrument) (debtor creditor : Party) : ℚ :=
  if claim.instrument = instrument ∧ claim.debtor = debtor then
    match review.kind with
    | .payment holder => -(if holderParty input holder = creditor then amount else 0)
    | .assignment sender recipient =>
        -(if holderParty input sender = creditor then amount else 0) +
          if holderParty input recipient = creditor then amount else 0
  else 0

omit [DecidableEq Port] in
theorem reviewDelta_zero {claim : IssuedClaim input} (review : Review input claim)
    (instrument : Instrument) (debtor creditor : Party) :
    reviewDelta input review 0 instrument debtor creditor = 0 := by
  unfold reviewDelta
  split_ifs <;> cases review.kind <;> simp

omit [DecidableEq Port] in
theorem reviewDelta_add {claim : IssuedClaim input} (review : Review input claim)
    (left right : ℚ) (instrument : Instrument) (debtor creditor : Party) :
    reviewDelta input review (left + right) instrument debtor creditor =
      reviewDelta input review left instrument debtor creditor +
        reviewDelta input review right instrument debtor creditor := by
  unfold reviewDelta
  split_ifs <;> cases review.kind <;> (try simp only []) <;> (try split_ifs) <;> ring

theorem allocateLive_ledgerClaims (state : (process input).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input))
    (present : state.current.slots.get index = .live obligation)
    (review : Review input obligation.content) (available : ℚ) (nonnegative : 0 ≤ available)
    (instrument : Instrument) (debtor creditor : Party) :
    ledgerClaims input
        (allocateLive input state index obligation present review available nonnegative).after.current
        instrument debtor creditor =
      ledgerClaims input state.current instrument debtor creditor +
        reviewDelta input review
          ((allocateLive input state index obligation present review available nonnegative).used input)
          instrument debtor creditor := by
  let cap := min available review.quantity
  let sound := live_sound input state index obligation present
  let boundary := reviewBoundary input obligation sound.1 review cap sound.2
    (le_min nonnegative (review.quantity_nonnegative input)) (min_le_right _ _)
  change ledgerClaims input (cross input state index obligation present boundary).current
    instrument debtor creditor = _
  rw [cross_ledgerClaims]
  change ledgerClaims input state.current instrument debtor creditor -
      (if obligation.content.instrument = instrument ∧ obligation.content.debtor = debtor then
        shareAt input obligation.residual creditor else 0) +
      (if obligation.content.instrument = instrument ∧ obligation.content.debtor = debtor then
        shareAt input (review.after input obligation.residual cap) creditor else 0) = _
  have used : (allocateLive input state index obligation present review available nonnegative).used input =
      review.allocated input obligation.residual cap := by
    simp only [Allocation.used, allocateLive]
    ring
  rw [used]
  cases kind : review.kind with
  | payment holder =>
      simp only [Review.after, kind, shareAt_pay, reviewDelta]
      split_ifs <;> ring
  | assignment sender recipient =>
      simp only [Review.after, kind, shareAt_assign, reviewDelta]
      split_ifs <;> ring

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation
