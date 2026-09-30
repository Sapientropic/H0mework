import H0mework.Fock.CopyGraph.CorrectionMean
import H0mework.Fock.CopyGraph.DecoderEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalCorrection

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceGeneratedJointClock
open SourceCopyObservation (before after twoMaterial)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open scoped InnerProductSpace
noncomputable section
local instance effectParentMeasurable : MeasurableSpace ParentCarrier := ⊤
local notation "clockValue" => taskValue (historyPMF 3) (signal 3)

theorem after_update_zero (value : Space (historyPMF 3)) : update 3 3 twoMaterial (after 3 3 twoMaterial) value = 0 := by
  unfold update coefficient clockPair
  rw [SourceCopyObservation.after_residual_zero, inner_zero_left, mul_zero, zero_div, zero_smul]

theorem before_pair_ne_zero : clockPair 3 (before 3 3) clockValue ≠ 0 := by
  change inner ℂ _ _ ≠ 0
  rw [inner_self_ne_zero]
  exact SourceConditionalGraph.before_clock_residual_ne_zero

theorem before_coefficient_ne_zero : coefficient 3 3 twoMaterial (before 3 3) clockValue ≠ 0 := by
  unfold coefficient
  exact div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr (strength_pos 3 3 twoMaterial).ne') before_pair_ne_zero)
    (Complex.ofReal_ne_zero.mpr (denominator_pos 3 3 twoMaterial (before 3 3)).ne')

theorem before_clock_average : inner ℂ (one 3 (before 3 3)) (clockMean 3 (before 3 3)) = (5 / 2 : ℂ) := by
  rw [clock_average]
  simp only [SourceUniformFibreVariance.source_weight, signal_value]
  norm_num [Fin.sum_univ_succ, Complex.real_smul]

theorem before_optimal_mass_ne_zero :
    SourceSuccessorBoundary.mass ℂ (SourceHistoryWord.word 3
      (clockValue - pullback (historyPMF 3) (before 3 3)
        (SourceConditionalGraphDecoder.decode 3 3 twoMaterial (before 3 3)
          (SourceConditionalGraph.copyRead 3 3 twoMaterial clockValue)))) ≠ 0 := by
  rw [decoded_residual_mass, before_clock_average]
  apply mul_ne_zero
  · apply neg_ne_zero.mpr
    exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3 + 1)).ne'
  · exact div_ne_zero (mul_ne_zero before_coefficient_ne_zero (by norm_num)) (by norm_num)

theorem before_update_ne_zero : update 3 3 twoMaterial (before 3 3) clockValue ≠ 0 := by
  intro zero
  have source := decoder_formula 3 3 twoMaterial (before 3 3) clockValue
  rw [zero, add_zero] at source
  exact SourceConditionalGraphDecoder.old_conditional_not_decoder source.symm

end
end SourceConditionalCorrection
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
