import H0mework.Versions.X.Fock.CopyGraph.DecoderInteraction
import H0mework.Versions.X.Fock.CopyGraph.ConditionalEffect

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalGraphDecoder

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability SourceUniformFibreVariance
open SourceGeneratedJointClock SourceCopyObservation
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
noncomputable section
local instance clockParentMeasurable : MeasurableSpace ParentCarrier := ⊤

theorem before_transfer_ne_zero :
    transfer (historyPMF 3) (before 3 3) (taskValue (historyPMF 3) (signal 3)) ≠ 0 := by
  intro vanished
  have whole := IsometricRetainedTransfer.pullback_transfer_add_residual (pullback (historyPMF 3) (before 3 3))
    (taskValue (historyPMF 3) (signal 3))
  rw [vanished, map_zero, zero_add] at whole
  have mean := SourceConditionalGraph.residual_mean 3 (before 3 3) (taskValue (historyPMF 3) (signal 3))
  rw [whole, PMF.integral_eq_sum] at mean
  simp only [taskValue_at _ _ _ (source_positive _ _), signal_value, source_weight] at mean
  norm_num [Fin.sum_univ_succ, Complex.real_smul] at mean

theorem before_prediction_clock_ne_zero :
    SourceClockComplex.clock (SourceHistoryWord.word 3
      (pullback (historyPMF 3) (before 3 3)
        (transfer (historyPMF 3) (before 3 3) (taskValue (historyPMF 3) (signal 3))))) ≠ 0 := by
  intro vanished
  have realPart := congrArg Complex.re (clock_prediction 3 (before 3 3))
  rw [vanished, Complex.zero_re, Complex.smul_re] at realPart
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, smul_eq_mul] at realPart
  have positive : 0 < Real.sqrt (3 + 1 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have size := norm_pos_iff.mpr before_transfer_ne_zero
  have impossible := mul_pos positive (sq_pos_of_pos size)
  exact impossible.ne' realPart.symm

end
end SourceConditionalGraphDecoder
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
