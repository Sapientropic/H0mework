import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Renewal.Decision
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Consumers.Renewal

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Renewal

open Source.Program Control.Scenario

def firstPeriodReleased : Bool := (firstProgramme.paidNextTrial? (discovery 1)).isSome

set_option maxHeartbeats 1800000 in
theorem the_original_paid_trial_passes_the_actual_period_renewal_gate : firstPeriodReleased = true := by
  decide +kernel

/-- A runnable future proposal does not pay the already occurred period. -/
abbrev onlyPromisedNeeds : Mechanism Party Good Bool Nat Unit :=
  { firstProgramme with policy := fun key _ => if key.2.val = 2 then commonWork else [] }

def oldTrialAccepts : Bool := match onlyPromisedNeeds.generate (discovery 1) with
  | .accepted _ => true
  | .failed _ => false

set_option maxHeartbeats 1800000 in
theorem a_future_payment_proposal_cannot_replace_the_actual_first_payment :
    oldTrialAccepts = true ∧
      ¬ Exit.Necessity.AllNeedsPaid onlyPromisedNeeds.code.law onlyPromisedNeeds.code.initial
        onlyPromisedNeeds.code.parties (onlyPromisedNeeds.word (discovery 1)) := by
  decide +kernel

theorem the_period_gate_keeps_the_unpaid_original_period_visible :
    onlyPromisedNeeds.paidNextTrial? (discovery 1) = none :=
  onlyPromisedNeeds.a_missing_actual_first_payment_cannot_be_hidden_in_the_next_trial (discovery 1)
    a_future_payment_proposal_cannot_replace_the_actual_first_payment.2

theorem a_released_trial_inherits_the_same_paid_successor (next : Mechanism Party Good Bool Nat Unit)
    (released : firstProgramme.paidNextTrial? (discovery 1) = some next) :
    next.code.initial = firstProgramme.next (discovery 1) ∧
      ∀ person, Exit.Necessity.BundlePaid firstProgramme.code.law firstProgramme.code.initial
        (firstProgramme.word (discovery 1)) person
        (firstProgramme.code.law.necessities firstProgramme.code.initial person) .necessity ∧
      Exit.Necessity.BundlePaid firstProgramme.code.law firstProgramme.code.initial
        (firstProgramme.word (discovery 1)) person
        (firstProgramme.code.law.mandatoryMaintenance firstProgramme.code.initial person) .maintenance := by
  obtain ⟨same,_,paid⟩ := firstProgramme.every_released_next_trial_has_paid_the_actual_first_period
    (discovery 1) next released
  exact ⟨same ▸ rfl, paid⟩

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Renewal
