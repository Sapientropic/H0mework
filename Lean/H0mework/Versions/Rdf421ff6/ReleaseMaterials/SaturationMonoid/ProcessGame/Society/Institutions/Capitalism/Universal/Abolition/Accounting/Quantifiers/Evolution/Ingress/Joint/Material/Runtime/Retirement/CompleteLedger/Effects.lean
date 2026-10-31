import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger.Readout
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.BalanceConservation.Readout

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Epoch.Finance

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

open private allocateLive Allocation.append from
  H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Allocation
open Financial.BalanceConservation (shareAt shareAt_pay shareAt_assign)

theorem allocation_used_append {state : (process input depth count).GeneratedState} {available : ℚ}
    (first : Allocation input depth count state available)
    (second : Allocation input depth count first.after first.remaining) :
    (Allocation.append input depth count first second).used input depth count =
      first.used input depth count + second.used input depth count := by
  change available - second.remaining = (available - first.remaining) + (first.remaining - second.remaining)
  ring

def reviewDelta {claim : Claim input depth count} (review : Review input depth count claim)
    (amount : ℚ) (instrument : Instrument) (debtor creditor : Party) : ℚ :=
  if claim.instrument input depth count = instrument ∧ claim.debtor input depth count = debtor then
    match review.kind with
    | .payment holder => -(if Financial.holderParty input holder = creditor then amount else 0)
    | .assignment sender recipient =>
        -(if Financial.holderParty input sender = creditor then amount else 0) +
          if Financial.holderParty input recipient = creditor then amount else 0
  else 0

theorem reviewDelta_zero {claim : Claim input depth count} (review : Review input depth count claim)
    (instrument : Instrument) (debtor creditor : Party) :
    reviewDelta input depth count review 0 instrument debtor creditor = 0 := by
  unfold reviewDelta
  split_ifs <;> cases review.kind <;> simp

theorem reviewDelta_add {claim : Claim input depth count} (review : Review input depth count claim)
    (left right : ℚ) (instrument : Instrument) (debtor creditor : Party) :
    reviewDelta input depth count review (left + right) instrument debtor creditor =
      reviewDelta input depth count review left instrument debtor creditor +
        reviewDelta input depth count review right instrument debtor creditor := by
  unfold reviewDelta
  split_ifs <;> cases review.kind <;> (try simp only []) <;> (try split_ifs) <;> ring

theorem allocateLive_ledgerClaims (state : (process input depth count).GeneratedState)
    (index : Fin state.current.slots.length) (obligation : AdmittedObligation (vocabulary input depth count))
    (present : state.current.slots.get index = .live obligation)
    (review : Review input depth count obligation.content) (available : ℚ) (nonnegative : 0 ≤ available)
    (instrument : Instrument) (debtor creditor : Party) :
    ledgerClaims input depth count
        (allocateLive input depth count state index obligation present review available nonnegative).after.current
        instrument debtor creditor =
      ledgerClaims input depth count state.current instrument debtor creditor +
        reviewDelta input depth count review
          ((allocateLive input depth count state index obligation present review available nonnegative).used input depth count)
          instrument debtor creditor := by
  let cap := min available review.quantity
  let sound := live_sound input depth count state index obligation present
  let boundary := reviewBoundary input depth count obligation sound.1 review cap sound.2
    (le_min nonnegative (review.quantity_nonnegative input depth count)) (min_le_right _ _)
  change ledgerClaims input depth count (state.step (process input depth count) (.cross index obligation present boundary)).current
    instrument debtor creditor = _
  rw [cross_ledgerClaims]
  change ledgerClaims input depth count state.current instrument debtor creditor -
      (if obligation.content.instrument = instrument ∧ obligation.content.debtor = debtor then
        shareAt input obligation.residual creditor else 0) +
      (if obligation.content.instrument = instrument ∧ obligation.content.debtor = debtor then
        shareAt input (review.after input depth count obligation.residual cap) creditor else 0) = _
  have used : (allocateLive input depth count state index obligation present review available nonnegative).used input depth count =
      review.allocated input depth count obligation.residual cap := by
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


end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Retirement.CompleteLedger
