import H0mework.Probability.HistoryWord.Core

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceHistoryWord

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance
open SourceSuccessorBoundary SourceOwnedObservationHistory.SourceShift
open scoped Classical
noncomputable section

theorem hilbert_sum (bound : Nat) (value : Space (historyPMF bound)) :
    readWord (word bound value) = ∑ index : Fin (bound + 1),
      lp.single 2 index.val (coefficient bound index value) := by
  rw [word_sum, map_sum]
  simp only [readWord_single, basis, ← lp.single_smul, smul_eq_mul, mul_one]

theorem hilbert_norm_sq (bound : Nat) (value : Space (historyPMF bound)) :
    ‖readWord (word bound value)‖ ^ 2 = ‖value‖ ^ 2 := by
  let filled : Nat → ℂ := fun index =>
    if inside : index < bound + 1 then coefficient bound ⟨index, inside⟩ value else 0
  have filled_at (index : Fin (bound + 1)) : filled index.val = coefficient bound index value := dif_pos index.isLt
  have generated : readWord (word bound value) =
      ∑ index ∈ Finset.range (bound + 1), lp.single 2 index (filled index) := by
    rw [hilbert_sum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro index _
    rw [filled_at]
  have original := lp.norm_sum_single (E := fun _ : Nat => ℂ) (p := 2) (by norm_num)
    filled (Finset.range (bound + 1))
  rw [← generated, ← Fin.sum_univ_eq_sum_range] at original
  have energy : ‖readWord (word bound value)‖ ^ 2 =
      ∑ index : Fin (bound + 1), ‖coefficient bound index value‖ ^ 2 := by
    simpa [Real.rpow_two, filled_at] using original
  rw [energy, norm_source_sq]
  apply Finset.sum_congr rfl
  intro index _
  rw [coefficient_value, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt ENNReal.toReal_nonneg]

def hilbert (bound : Nat) : Space (historyPMF bound) →ₗᵢ[ℂ] H where
  toLinearMap := readWord.comp (word bound)
  norm_map' value :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hilbert_norm_sq bound value)

def joint (bound : Nat) : Space (historyPMF bound) →ₗ[ℂ] SourceMassCompletion.Joint :=
  SourceMassCompletion.jointRead.comp (word bound)

theorem first_joint (bound : Nat) (value : Space (historyPMF bound)) :
    SourceMassCompletion.firstRead (joint bound value) = hilbert bound value := rfl

theorem mass_joint (bound : Nat) (value : Space (historyPMF bound)) :
    SourceMassCompletion.massRead (joint bound value) = ∑ index : Fin (bound + 1),
      (Real.sqrt (historyPMF bound index).toReal : ℂ) * value index := mass_word bound value

end
end SourceHistoryWord
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
