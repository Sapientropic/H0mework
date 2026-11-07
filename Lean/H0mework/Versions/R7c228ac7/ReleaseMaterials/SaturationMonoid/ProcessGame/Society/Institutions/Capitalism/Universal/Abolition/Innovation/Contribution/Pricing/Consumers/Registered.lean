import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Root.Contract
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Total.Consumers.Registered

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Registered

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered Abolition.Root.Registered.Macro
open Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Abolition.Accounting.Quantifiers.Joint.Consumers.Compact (seed grossClaim mechanism)
universe u v w x
noncomputable section

theorem the_original_registered_capital_root_consumes_source_native_risk_compensation :
    Root.CapitalRiskCompensationClosedAt.{u,v,w,x} seed grossClaim :=
  Root.the_original_capital_root_closes_the_risk_compensation_amount_and_authority seed grossClaim

abbrev actualSource := Evolving.Epoch.Source.initial Evolving.Consumers.original

theorem the_same_actual_paid_root_consumes_the_new_price_method :
    Root.SourceNativeRiskCompensationAt actualSource mechanism :=
  the_original_registered_capital_root_consumes_source_native_risk_compensation.{0,0,0,0}.everyActualRiskSource
    actualSource mechanism

def actualPreparation := Root.prepare actualSource mechanism
def actualAttempt (nature : Request Bool Bool Bool Unit Unit) (proposed : Option ℚ) :=
  Root.attempt actualSource mechanism nature proposed

set_option maxRecDepth 4096 in
theorem the_same_actual_root_returns_a_price_execution_or_its_exact_original_obstruction :
    Root.PreparationDisposition actualSource mechanism :=
  Root.SourceNativeRiskCompensationAt.generatedDisposition
    (source := actualSource) (mechanism := mechanism)
    the_same_actual_paid_root_consumes_the_new_price_method

theorem every_same_root_price_attempt_keeps_all_original_responsibilities
    (nature : Request Bool Bool Bool Unit Unit) (proposed : Option ℚ) :
    Root.Accounted actualSource (actualAttempt nature proposed) :=
  Root.SourceNativeRiskCompensationAt.everyAttemptAccounted
    (source := actualSource) (mechanism := mechanism)
    the_same_actual_paid_root_consumes_the_new_price_method nature proposed

theorem the_original_capital_and_cost_contract_is_retained :
    Characterization.Root.MinimalSupportAndEscapeAt.{u,v,w,x} seed grossClaim :=
  the_original_registered_capital_root_consumes_source_native_risk_compensation.toMinimalSupportAndEscapeAt

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Registered
