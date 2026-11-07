import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Arithmetic.Floor

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Arithmetic

theorem excess_above_the_floor (rows : List RiskRow) (outside riskCost reward : ℚ)
    (possible : 0 < successMass rows) :
    reward - compensationFloor rows outside riskCost =
      (expectedChange rows reward - outside - riskCost) / successMass rows := by
  rw [expected_change_separates_actual_failure_losses, the_floor_has_no_independent_loading]
  rw [sub_div, sub_div, sub_div, mul_div_cancel_left₀ _ (ne_of_gt possible)]
  rw [add_div, add_div]
  ring

theorem the_entire_return_separates_compensation_and_excess
    (rows : List RiskRow) (outside riskCost reward : ℚ) (possible : 0 < successMass rows) :
    expectedChange rows reward = outside + riskCost +
      successMass rows * (reward - compensationFloor rows outside riskCost) := by
  rw [excess_above_the_floor rows outside riskCost reward possible]
  rw [mul_div_cancel₀ _ (ne_of_gt possible)]
  ring

theorem strictly_above_the_floor_iff (rows : List RiskRow) (outside riskCost reward : ℚ)
    (possible : 0 < successMass rows) :
    compensationFloor rows outside riskCost < reward ↔ outside + riskCost < expectedChange rows reward := by
  rw [the_entire_return_separates_compensation_and_excess rows outside riskCost reward possible]
  constructor <;> intro h <;> nlinarith

theorem a_declared_loading_exposes_its_exact_excess
    (rows : List RiskRow) (outside riskCost loading : ℚ) (possible : 0 < successMass rows) :
    contingentReward rows outside loading - compensationFloor rows outside riskCost =
      (loading - riskCost) / successMass rows := by
  rw [excess_above_the_floor rows outside riskCost _ possible,
    the_source_quote_pays_the_declared_ex_ante_return rows outside loading possible]
  congr 1
  ring

theorem a_loading_meets_the_requirement_iff (rows : List RiskRow) (outside riskCost loading : ℚ)
    (possible : 0 < successMass rows) :
    compensationFloor rows outside riskCost ≤ contingentReward rows outside loading ↔ riskCost ≤ loading := by
  rw [← meets_compensation_requirement_iff rows outside riskCost _ possible,
    the_source_quote_pays_the_declared_ex_ante_return rows outside loading possible]
  constructor <;> intro h <;> linarith

theorem zero_success_has_an_exact_return (rows : List RiskRow) (reward : ℚ)
    (noSuccess : successMass rows = 0) : expectedChange rows reward = -failureLoss rows := by
  rw [expected_change_separates_actual_failure_losses, noSuccess]
  ring

theorem zero_success_has_an_exact_feasibility_check (rows : List RiskRow) (requiredReturn reward : ℚ)
    (noSuccess : successMass rows = 0) :
    requiredReturn ≤ expectedChange rows reward ↔ requiredReturn ≤ -failureLoss rows := by
  rw [zero_success_has_an_exact_return rows reward noSuccess]

theorem zero_success_blocks_every_reward (rows : List RiskRow) (requiredReturn : ℚ)
    (noSuccess : successMass rows = 0) (uncovered : -failureLoss rows < requiredReturn) :
    ¬ ∃ reward, requiredReturn ≤ expectedChange rows reward := by
  rintro ⟨reward, sufficient⟩
  rw [zero_success_has_an_exact_return rows reward noSuccess] at sufficient
  exact (not_le_of_gt uncovered) sufficient

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Arithmetic
