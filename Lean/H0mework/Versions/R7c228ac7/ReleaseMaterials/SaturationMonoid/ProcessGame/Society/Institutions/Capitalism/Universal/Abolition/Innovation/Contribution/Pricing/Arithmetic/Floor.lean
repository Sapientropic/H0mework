import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.RiskMath

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Arithmetic

def requiredReward (rows : List RiskRow) (requiredReturn : ℚ) : ℚ :=
  contingentReward rows requiredReturn 0

def compensationFloor (rows : List RiskRow) (outside riskCost : ℚ) : ℚ :=
  requiredReward rows (outside + riskCost)

theorem meets_required_return_iff (rows : List RiskRow) (requiredReturn reward : ℚ)
    (possible : 0 < successMass rows) :
    requiredReturn ≤ expectedChange rows reward ↔ requiredReward rows requiredReturn ≤ reward := by
  rw [expected_change_separates_actual_failure_losses]
  unfold requiredReward contingentReward
  rw [div_le_iff₀ possible]
  constructor <;> intro h <;> nlinarith

theorem exact_required_return_iff (rows : List RiskRow) (requiredReturn reward : ℚ)
    (possible : 0 < successMass rows) :
    expectedChange rows reward = requiredReturn ↔ reward = requiredReward rows requiredReturn := by
  rw [expected_change_separates_actual_failure_losses]
  unfold requiredReward contingentReward
  rw [eq_div_iff (ne_of_gt possible)]
  constructor <;> intro h <;> nlinarith

theorem required_reward_attains_the_return (rows : List RiskRow) (requiredReturn : ℚ)
    (possible : 0 < successMass rows) :
    expectedChange rows (requiredReward rows requiredReturn) = requiredReturn := by
  exact (exact_required_return_iff rows requiredReturn _ possible).2 rfl

theorem required_reward_is_the_least_sufficient_payment (rows : List RiskRow) (requiredReturn : ℚ)
    (possible : 0 < successMass rows) :
    expectedChange rows (requiredReward rows requiredReturn) = requiredReturn ∧
      ∀ reward, requiredReturn ≤ expectedChange rows reward → requiredReward rows requiredReturn ≤ reward :=
  ⟨required_reward_attains_the_return rows requiredReturn possible,
    fun reward sufficient => (meets_required_return_iff rows requiredReturn reward possible).1 sufficient⟩

theorem meets_compensation_requirement_iff (rows : List RiskRow) (outside riskCost reward : ℚ)
    (possible : 0 < successMass rows) :
    outside + riskCost ≤ expectedChange rows reward ↔ compensationFloor rows outside riskCost ≤ reward :=
  meets_required_return_iff rows (outside + riskCost) reward possible

theorem exact_compensation_requirement_iff (rows : List RiskRow) (outside riskCost reward : ℚ)
    (possible : 0 < successMass rows) :
    expectedChange rows reward = outside + riskCost ↔ reward = compensationFloor rows outside riskCost :=
  exact_required_return_iff rows (outside + riskCost) reward possible

theorem the_floor_has_no_independent_loading (rows : List RiskRow) (outside riskCost : ℚ) :
    compensationFloor rows outside riskCost = (failureLoss rows + outside + riskCost) / successMass rows := by
  unfold compensationFloor requiredReward contingentReward
  congr 1
  ring

theorem the_original_quote_has_exactly_its_declared_loading (rows : List RiskRow) (outside loading : ℚ) :
    contingentReward rows outside loading = compensationFloor rows outside loading := by
  rw [the_floor_has_no_independent_loading]
  rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Arithmetic
