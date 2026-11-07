import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Arithmetic.Excess

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Arithmetic.Controls

def ordinaryRows : List RiskRow := [⟨1 / 2, false, 2⟩, ⟨1 / 2, true, 0⟩]
def rareRows : List RiskRow := [⟨99 / 100, false, 2⟩, ⟨1 / 100, true, 0⟩]
def hundredfoldRows : List RiskRow := [⟨100 / 101, false, 1⟩, ⟨1 / 101, true, 0⟩]
def failureOnly : List RiskRow := [⟨1, false, 2⟩]

theorem both_binary_forecasts_have_normalized_nonnegative_weights :
    (ordinaryRows.map RiskRow.weight).sum = 1 ∧
      (rareRows.map RiskRow.weight).sum = 1 ∧
      (∀ row ∈ ordinaryRows, 0 ≤ row.weight) ∧
      (∀ row ∈ rareRows, 0 ≤ row.weight) := by decide +kernel

theorem both_forecasts_have_the_same_failure_exposure :
    (ordinaryRows.map RiskRow.loss).head? = some 2 ∧
      (rareRows.map RiskRow.loss).head? = some 2 := by decide +kernel

theorem their_exact_break_even_floors_differ :
    compensationFloor ordinaryRows 0 0 = 2 ∧ compensationFloor rareRows 0 0 = 198 := by
  decide +kernel

theorem the_same_tenfold_payment_exceeds_or_misses_the_floor :
    compensationFloor ordinaryRows 0 0 < 20 ∧
      20 < compensationFloor rareRows 0 0 ∧
      expectedChange ordinaryRows 20 = 9 ∧
      expectedChange rareRows 20 = -(89 / 50) := by decide +kernel

theorem a_hundredfold_payment_can_be_exactly_break_even :
    (hundredfoldRows.map RiskRow.weight).sum = 1 ∧
      (∀ row ∈ hundredfoldRows, 0 ≤ row.weight) ∧
      compensationFloor hundredfoldRows 0 0 = 100 ∧
      expectedChange hundredfoldRows 100 = 0 := by decide +kernel

theorem loading_alone_can_raise_the_original_three_to_one_hundred :
    contingentReward ordinaryRows 0 (1 / 2) = 3 ∧
      contingentReward ordinaryRows 0 49 = 100 ∧
      expectedChange ordinaryRows 3 = 1 / 2 ∧
      expectedChange ordinaryRows 100 = 49 := by decide +kernel

theorem no_success_is_an_exact_blocker :
    ¬ ∃ reward, (0 : ℚ) ≤ expectedChange failureOnly reward :=
  zero_success_blocks_every_reward failureOnly 0 (by decide +kernel) (by decide +kernel)

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Contribution.Pricing.Arithmetic.Controls
