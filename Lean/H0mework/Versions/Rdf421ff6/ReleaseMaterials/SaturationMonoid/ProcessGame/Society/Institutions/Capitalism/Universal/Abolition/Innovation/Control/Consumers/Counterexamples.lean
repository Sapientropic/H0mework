import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Effects

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Consumers

open Source.Program
open Scenario

theorem removing_only_a_rent_transfer_creates_no_material_output (good : Good) :
    net law (law.rawItems seed [rent]) good = net law (law.rawItems seed []) good := by
  cases good <;> decide +kernel

def extraCosts : RawEvent Party Good Bool Nat Unit :=
  [request 1 (.use 1 [(.material,18)] .external),
   request 0 (.use 0 [(.result,2)] .external),
   request 1 (.use 1 [(.result,1)] .external)]

def exhaustedWord := word true (discovery 2) retaliation ++ extraCosts
def exhaustedExecution := openLaw.execute seed 0 exhaustedWord

set_option maxHeartbeats 1600000 in
theorem the_additional_costs_are_real_paid_requests :
    ∀ item ∈ openLaw.rawItems (after true (discovery 2) retaliation) extraCosts,
      openLaw.Valid item.before item.request := by decide +kernel

set_option maxHeartbeats 2000000 in
theorem actual_additional_costs_can_exhaust_the_entire_physical_gain (good : Good) :
    controlLoss law openLaw (execution false (discovery 2) retaliation).items
      exhaustedExecution.items good = 0 := by
  cases good <;> decide +kernel

def observedBeforeContribution (opened : Bool) :=
  (code opened).rawAt seed ((mechanism opened).deliveredFrame (discovery 2))

def drainedContributionCash (opened : Bool) : RawEvent Party Good Bool Nat Unit :=
  [request 0 (.use 0 [(.material,(observedBeforeContribution opened).stock 0 .material)] .external),
   request 1 (.use 1 [(.material,(observedBeforeContribution opened).stock 1 .material)] .external)]

def observedLiabilityWord (opened : Bool) : RawEvent Party Good Bool Nat Unit :=
  match (mechanism opened).paidSignal (discovery 2) with
  | some signal => contributionLiabilityWord signal.val
  | none => []

def pendingContribution (opened : Bool) :=
  ((lawAt opened).execute (observedBeforeContribution opened) 0
    (drainedContributionCash opened ++ observedLiabilityWord opened)).final

set_option maxHeartbeats 1600000 in
theorem missing_cash_is_created_by_real_paid_original_costs :
    (∀ opened : Bool, ∀ item ∈ (lawAt opened).rawItems
      (observedBeforeContribution opened) (drainedContributionCash opened),
        (lawAt opened).Valid item.before item.request) ∧
      (pendingContribution true).stock 0 .material = 0 ∧
      (pendingContribution false).stock 1 .material = 0 := by decide +kernel

set_option maxHeartbeats 1600000 in
theorem refused_success_and_failure_payments_leave_the_native_claims_visible :
    ¬ openLaw.Valid (pendingContribution true) successPayment ∧
      ¬ law.Valid (pendingContribution false) failureCoverage ∧
      (openLaw.step (pendingContribution true) successPayment).claims () 0 1 = 9 / 2 ∧
      (law.step (pendingContribution false) failureCoverage).claims () 1 0 = 1 ∧
      (openLaw.step (pendingContribution true) successPayment).claims () 0 2 = 1 ∧
      (law.step (pendingContribution false) failureCoverage).claims () 0 2 = 1 := by decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Consumers
