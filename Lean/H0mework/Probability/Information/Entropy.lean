import H0mework.Probability.Information.Conditional
import H0mework.Chemistry.LAlanineEntropy.FiniteGibbsPopulation
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceUniformFibreInformation

open SourceUniformFibreVariance SourceGeneratedRuntimeHistoryProbability
open scoped Classical
noncomputable section

local notation "entropy" =>
  SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population.entropy

variable {Observed : Type*} [DecidableEq Observed]

def conditionalEntropy (bound : Nat) (query : Fin (bound + 1) → Observed) : ℝ :=
  ∑ value : outputs bound query, ((historyPMF bound).map query value.val).toReal *
    entropy (SourceConditionalHistory.conditional (historyPMF bound) query value.val
      (output_supported bound query value.val value.property))

theorem fibre_entropy (bound : Nat) (query : Fin (bound + 1) → Observed) (value : Observed)
    (supported : value ∈ ((historyPMF bound).map query).support) :
    entropy (SourceConditionalHistory.conditional (historyPMF bound) query value supported) =
      Real.log (fibre bound query value).card := by
  have cardNonzero := (positive_card bound query value (supported_output bound query value supported)).ne'
  unfold SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Population.entropy
  simp_rw [conditional_weight]
  have restrict :
      (∑ index : Fin (bound + 1),
        (if index ∈ fibre bound query value then ((fibre bound query value).card : ℝ)⁻¹ else 0) *
          Real.log (if index ∈ fibre bound query value then ((fibre bound query value).card : ℝ)⁻¹ else 0)) =
      ∑ _index ∈ fibre bound query value,
        ((fibre bound query value).card : ℝ)⁻¹ * Real.log ((fibre bound query value).card : ℝ)⁻¹ := by
    rw [fibre, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro index _
    by_cases same : query index = value <;> simp [same]
  rw [restrict, Finset.sum_const, nsmul_eq_mul, Real.log_inv, ← mul_assoc,
    mul_inv_cancel₀ cardNonzero, one_mul, neg_neg]

theorem conditional_entropy_formula (bound : Nat) (query : Fin (bound + 1) → Observed) :
    conditionalEntropy bound query =
      ∑ value ∈ outputs bound query,
        ((fibre bound query value).card : ℝ) / (bound + 1) * Real.log (fibre bound query value).card := by
  simp only [conditionalEntropy, fibre_entropy, observed_weight]
  exact Finset.sum_coe_sort (outputs bound query)
    (fun value => ((fibre bound query value).card : ℝ) / (bound + 1) * Real.log (fibre bound query value).card)

theorem output_weights (bound : Nat) (query : Fin (bound + 1) → Observed) :
    (∑ value ∈ outputs bound query, ((fibre bound query value).card : ℝ) / (bound + 1)) = 1 := by
  rw [← Finset.sum_div]
  have count : (∑ value ∈ outputs bound query, ((fibre bound query value).card : ℝ)) = (bound + 1 : ℝ) := by
    exact_mod_cast fibre_card_sum bound query
  rw [count, div_self (by positivity : (bound + 1 : ℝ) ≠ 0)]

private theorem logarithmic_second_moment {Index : Type*} (indices : Finset Index)
    (weight count : Index → ℝ) (nonnegative : ∀ index ∈ indices, 0 ≤ weight index)
    (total : ∑ index ∈ indices, weight index = 1) (positive : ∀ index ∈ indices, 0 < count index) :
    Real.exp (2 * ∑ index ∈ indices, weight index * Real.log (count index)) ≤
      ∑ index ∈ indices, weight index * count index ^ 2 := by
  have jensen := convexOn_exp.map_sum_le (t := indices) (w := weight)
    (p := fun index => 2 * Real.log (count index)) nonnegative total (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at jensen
  have exponent : (∑ index ∈ indices, weight index * (2 * Real.log (count index))) =
      2 * ∑ index ∈ indices, weight index * Real.log (count index) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [exponent] at jensen
  apply jensen.trans_eq
  apply Finset.sum_congr rfl
  intro index inside
  congr 1
  rw [show 2 * Real.log (count index) = Real.log (count index) + Real.log (count index) by ring,
    Real.exp_add, Real.exp_log (positive index inside), pow_two]

theorem entropy_second_moment (bound : Nat) (query : Fin (bound + 1) → Observed) :
    Real.exp (2 * conditionalEntropy bound query) ≤
      ∑ value ∈ outputs bound query,
        ((fibre bound query value).card : ℝ) / (bound + 1) * ((fibre bound query value).card : ℝ) ^ 2 := by
  rw [conditional_entropy_formula]
  exact logarithmic_second_moment (outputs bound query)
    (fun value => ((fibre bound query value).card : ℝ) / (bound + 1))
    (fun value => ((fibre bound query value).card : ℝ))
    (fun _ _ => by positivity) (output_weights bound query) (positive_card bound query)

theorem conditional_entropy_zero_of_injective (bound : Nat) (query : Fin (bound + 1) → Observed)
    (injective : Function.Injective query) : conditionalEntropy bound query = 0 := by
  rw [conditional_entropy_formula]
  apply Finset.sum_eq_zero
  intro value present
  obtain ⟨index, _, same⟩ := Finset.mem_image.mp present
  have singleton : fibre bound query value = {index} := by
    ext other
    rw [fibre_mem, Finset.mem_singleton]
    exact ⟨fun equal => injective (equal.trans same.symm), fun equal => equal ▸ same⟩
  rw [singleton, Finset.card_singleton, Nat.cast_one, Real.log_one, mul_zero]

theorem entropy_spread_lower (bound : Nat) (query : Fin (bound + 1) → Observed) (scale : ℝ) :
    scale ^ 2 / 3 * (Real.exp (2 * conditionalEntropy bound query) - 1) ≤
      scale ^ 2 / (3 * (bound + 1 : ℝ)) *
        ∑ value ∈ outputs bound query,
          ((fibre bound query value).card : ℝ) * (((fibre bound query value).card : ℝ) ^ 2 - 1) := by
  have centered :
      (∑ value ∈ outputs bound query,
        ((fibre bound query value).card : ℝ) / (bound + 1) * ((fibre bound query value).card : ℝ) ^ 2) - 1 =
      (1 / (bound + 1 : ℝ)) *
        ∑ value ∈ outputs bound query,
          ((fibre bound query value).card : ℝ) * (((fibre bound query value).card : ℝ) ^ 2 - 1) := by
    calc
      _ = (∑ value ∈ outputs bound query,
          ((fibre bound query value).card : ℝ) / (bound + 1) * ((fibre bound query value).card : ℝ) ^ 2) -
          (∑ value ∈ outputs bound query, ((fibre bound query value).card : ℝ) / (bound + 1)) := by
        rw [output_weights bound query]
      _ = _ := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro value _
        ring
  have scaled := mul_le_mul_of_nonneg_left (sub_le_sub_right (entropy_second_moment bound query) 1)
    (by positivity : 0 ≤ scale ^ 2 / 3)
  rw [centered] at scaled
  apply scaled.trans_eq
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end
end SourceUniformFibreInformation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
