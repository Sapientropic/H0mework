import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Consumers.Signal.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation.Schedule.Performance

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation

open Abolition.Root.Registered

def riskLiability (version : Nat) :=
  if version = 0 then Control.Scenario.failureLiability else Control.Scenario.successLiability

def firstSettlement (version : Nat) :=
  if version = 0 then Control.Scenario.failureCoverage else Control.Scenario.repay

def lastSettlement (version : Nat) :=
  if version = 0 then Control.Scenario.repay else Control.Scenario.successPayment

def performanceInputs (version : Nat) : List InputAt :=
  [.primitive (riskLiability version), .execute Control.Scenario.commonWork,
    .primitive (firstSettlement version), .primitive (lastSettlement version)]

theorem the_real_observed_signal_has_the_original_liability_and_finite_performance
    (version : Nat) (tested : version ∈ ([0,1,2] : List Nat)) :
    executionInputs (programme (discoverySignal version)) = performanceInputs version := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at tested
  rcases tested with rfl | rfl | rfl <;> rfl

theorem each_observed_risk_liability_is_one_of_the_original_source_requests (version : Nat) :
    riskLiability version ∈ [Control.Scenario.successLiability,Control.Scenario.failureLiability] := by
  unfold riskLiability
  split <;> simp

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Installation
