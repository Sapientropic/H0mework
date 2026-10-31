import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation

open ResponsibilityLifecycle

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)

def reviewDelta {claim : Claim sources} (review : Review sources claim)
    (amount : ℚ) (instrument : Instrument) (debtor holder : Party) : ℚ :=
  if claim.2.instrument = instrument ∧ claim.2.debtor = debtor then
    -(if review.sender = holder then amount else 0) +
      match review.kind with
      | .payment => 0
      | .assignment => if review.recipient = holder then amount else 0
  else 0

theorem allocateLive_ledgerClaims (state : (process sources).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary sources))
    (present : state.current.slots.get index = .live obligation)
    (review : Review sources obligation.content) (available : ℚ) (nonnegative : 0 ≤ available)
    (instrument : Instrument) (debtor holder : Party) :
    ledgerClaims sources (allocateLive sources state index obligation present review available nonnegative).after.current
        instrument debtor holder =
      ledgerClaims sources state.current instrument debtor holder +
        reviewDelta sources review ((allocateLive sources state index obligation present review available nonnegative).used sources)
          instrument debtor holder := by
  let cap := min available review.quantity
  let sound := live_sound sources state index obligation present
  let boundary := reviewBoundary sources obligation review cap sound.2
    (le_min nonnegative (review.quantity_nonnegative sources)) (min_le_right _ _) sound.1
  change ledgerClaims sources (cross sources state index obligation present boundary).current instrument debtor holder = _
  rw [cross_ledgerClaims]
  change ledgerClaims sources state.current instrument debtor holder -
      (if obligation.content.2.instrument = instrument ∧ obligation.content.2.debtor = debtor then obligation.residual holder else 0) +
      (if obligation.content.2.instrument = instrument ∧ obligation.content.2.debtor = debtor then
        review.after sources obligation.residual cap holder else 0) = _
  have used : (allocateLive sources state index obligation present review available nonnegative).used sources =
      min cap (obligation.residual review.sender) := by
    simp only [Allocation.used, allocateLive]
    ring
  rw [used]
  by_cases relevant : obligation.content.2.instrument = instrument ∧ obligation.content.2.debtor = debtor
  · simp only [if_pos relevant]
    cases kind : review.kind with
    | payment =>
        have price := Financial.BalanceConservation.shareAt_pay (sources obligation.content.1)
          obligation.residual review.sender (min cap (obligation.residual review.sender)) holder
        simp only [Review.after, kind]
        change ledgerClaims sources state.current instrument debtor holder - obligation.residual holder +
          (pay (sources obligation.content.1) obligation.residual review.sender (min cap (obligation.residual review.sender))) holder = _
        rw [show (pay (sources obligation.content.1) obligation.residual review.sender (min cap (obligation.residual review.sender))) holder =
          obligation.residual holder - if review.sender = holder then min cap (obligation.residual review.sender) else 0 from price]
        simp only [reviewDelta, if_pos relevant, kind]
        ring
    | assignment =>
        have price := Financial.BalanceConservation.shareAt_assign (sources obligation.content.1)
          obligation.residual review.sender review.recipient (min cap (obligation.residual review.sender)) holder
        simp only [Review.after, kind]
        change ledgerClaims sources state.current instrument debtor holder - obligation.residual holder +
          (assign (sources obligation.content.1) obligation.residual review.sender review.recipient (min cap (obligation.residual review.sender))) holder = _
        rw [show (assign (sources obligation.content.1) obligation.residual review.sender review.recipient (min cap (obligation.residual review.sender))) holder =
          obligation.residual holder - (if review.sender = holder then min cap (obligation.residual review.sender) else 0) +
            if review.recipient = holder then min cap (obligation.residual review.sender) else 0 from price]
        simp only [reviewDelta, if_pos relevant, kind]
        ring
  · simp only [if_neg relevant, reviewDelta, sub_zero, add_zero]

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Family.BalanceConservation
