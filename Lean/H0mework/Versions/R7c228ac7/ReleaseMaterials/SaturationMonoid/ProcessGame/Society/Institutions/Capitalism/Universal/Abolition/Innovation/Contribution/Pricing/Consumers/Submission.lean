import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers.Prices
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Source.Submission

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers

def proposedRiskWord (proposed : Option ℚ) :=
  match schedule with
  | .ready source => (Source.submit source (nature 4) proposed).word source ()
  | _ => []

def requiredRiskAmount (proposed : Option ℚ) : Option ℚ :=
  match schedule with
  | .ready source => (Source.submit source (nature 4) proposed).net source
  | _ => none

def allBranchesChecked : Bool :=
  match schedule with
  | .ready source => match Source.preflight source () with
    | .clear _ => true
    | .failure .. => false
  | _ => false

theorem the_contract_is_checked_on_every_source_branch_before_nature_is_selected : allBranchesChecked = true := by
  decide +kernel

theorem the_default_and_exact_explicit_quote_generate_the_same_two_real_financial_requests :
    requiredRiskAmount none = some 4 ∧ requiredRiskAmount (some 4) = some 4 ∧
      proposedRiskWord none = proposedRiskWord (some 4) ∧ (proposedRiskWord none).length = 2 := by
  decide +kernel

theorem shortfall_safe_extra_and_overcharge_cannot_write_a_required_risk_claim :
    proposedRiskWord (some 3) = [] ∧ proposedRiskWord (some 7) = [] ∧ proposedRiskWord (some 100) = [] ∧
      requiredRiskAmount (some 3) = none ∧ requiredRiskAmount (some 7) = none ∧ requiredRiskAmount (some 100) = none := by
  decide +kernel

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Consumers
