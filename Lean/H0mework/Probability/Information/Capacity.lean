import H0mework.Probability.Information.SeparationSpread
import H0mework.Chemistry.LAlanineRefillField.GibbsEnergy

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceUniformFibreInformation.Capacity

open SourceUniformFibreVariance SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery
open scoped Classical
noncomputable section

local notation "entropy" =>
  SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population.entropy

variable {Observed : Type*} [Fintype Observed] [DecidableEq Observed]

theorem output_entropy (bound : Nat) (query : Fin (bound + 1) → Observed) :
    entropy ((historyPMF bound).map query) = Real.log (bound + 1 : ℝ) - conditionalEntropy bound query := by
  have restrict :
      (∑ value ∈ outputs bound query, ((historyPMF bound).map query value).toReal *
        Real.log ((historyPMF bound).map query value).toReal) =
      ∑ value, ((historyPMF bound).map query value).toReal * Real.log ((historyPMF bound).map query value).toReal := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro value _ missing
    have zero : (historyPMF bound).map query value = 0 := by
      by_contra nonzero
      exact missing (supported_output bound query value nonzero)
    simp [zero]
  have expanded :
      (∑ value ∈ outputs bound query, ((fibre bound query value).card : ℝ) / (bound + 1) *
        Real.log (((fibre bound query value).card : ℝ) / (bound + 1))) =
      (∑ value ∈ outputs bound query, ((fibre bound query value).card : ℝ) / (bound + 1) *
        Real.log (fibre bound query value).card) - Real.log (bound + 1 : ℝ) := by
    calc
      _ = ∑ value ∈ outputs bound query,
        (((fibre bound query value).card : ℝ) / (bound + 1) * Real.log (fibre bound query value).card -
          ((fibre bound query value).card : ℝ) / (bound + 1) * Real.log (bound + 1 : ℝ)) := by
        apply Finset.sum_congr rfl
        intro value present
        rw [Real.log_div (positive_card bound query value present).ne' (by positivity : (bound + 1 : ℝ) ≠ 0)]
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, output_weights, one_mul]
  rw [conditional_entropy_formula]
  unfold SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population.entropy
  rw [← restrict]
  simp only [observed_weight]
  rw [expanded]
  ring

variable [MeasurableSpace Observed] [MeasurableSingletonClass Observed]

theorem information_lower (bound : Nat) (query : Fin (bound + 1) → Observed) :
    Real.log (bound + 1 : ℝ) - Real.log (Fintype.card Observed) ≤ conditionalEntropy bound query := by
  let : Nonempty Observed := ⟨query 0⟩
  have boundEntropy :=
    SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.GibbsEnergy.entropy_le_log_card
      ((historyPMF bound).map query)
  rw [output_entropy] at boundEntropy
  linarith

theorem exponential_information_lower (bound : Nat) (query : Fin (bound + 1) → Observed) :
    ((bound + 1 : ℝ) / Fintype.card Observed) ^ 2 ≤ Real.exp (2 * conditionalEntropy bound query) := by
  let : Nonempty Observed := ⟨query 0⟩
  have cardPositive : (0 : ℝ) < Fintype.card Observed := by exact_mod_cast Fintype.card_pos
  have totalPositive : (0 : ℝ) < bound + 1 := by positivity
  have generated := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left (information_lower bound query) (by norm_num : (0 : ℝ) ≤ 2))
  have left : Real.exp (2 * (Real.log (bound + 1 : ℝ) - Real.log (Fintype.card Observed))) =
      ((bound + 1 : ℝ) / Fintype.card Observed) ^ 2 := by
    rw [← Real.log_div totalPositive.ne' cardPositive.ne']
    rw [show 2 * Real.log ((bound + 1 : ℝ) / Fintype.card Observed) =
      Real.log ((bound + 1 : ℝ) / Fintype.card Observed) + Real.log ((bound + 1 : ℝ) / Fintype.card Observed) by ring,
      Real.exp_add, Real.exp_log (div_pos totalPositive cardPositive), pow_two]
  rw [left] at generated
  exact generated

theorem residual_capacity_lower (bound : Nat) (query : Fin (bound + 1) → Observed)
    (time : Fin (bound + 1) → ℝ) (scale : ℝ)
    (separated : ∀ left right, scale ^ 2 * ((right.val : ℝ) - (left.val : ℝ)) ^ 2 ≤
      (time right - time left) ^ 2) :
    scale ^ 2 / 12 * (((bound + 1 : ℝ) / Fintype.card Observed) ^ 2 - 1) ≤
      ‖residual (historyPMF bound) query (taskValue (historyPMF bound) (fun actor => (time actor : ℂ)))‖ ^ 2 := by
  have scaled := mul_le_mul_of_nonneg_left
    (sub_le_sub_right (exponential_information_lower bound query) 1) (by positivity : 0 ≤ scale ^ 2 / 12)
  exact scaled.trans (Separation.information_spread bound query time scale separated)

end
end SourceUniformFibreInformation.Capacity
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
